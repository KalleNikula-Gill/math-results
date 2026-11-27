import Mathlib.Data.Real.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace K28

abbrev Point (R : Type*) := R × R
abbrev Drawing (n : Nat) (R : Type*) := Fin n → Point R

def orient {R : Type*} [Ring R] (a b c : Point R) : R :=
  (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)

/-- Distinct labels give distinct points, and every triple of distinct labels
has nonzero signed double area. -/
def GeneralPosition {n : Nat} {R : Type*} [Ring R] (p : Drawing n R) : Prop :=
  Function.Injective p ∧ ∀ i j k, i ≠ j → i ≠ k → j ≠ k → orient (p i) (p j) (p k) ≠ 0

def interpolate (a b : Point ℝ) (t : ℝ) : Point ℝ :=
  (a.1 + t * (b.1 - a.1), a.2 + t * (b.2 - a.2))

/-- Relative interiors intersect. Our use of this predicate on a drawing is
always on edges with four different endpoints. -/
def InteriorMeet (a b c d : Point ℝ) : Prop :=
  ∃ t u : ℝ, 0 < t ∧ t < 1 ∧ 0 < u ∧ u < 1 ∧ interpolate a b t = interpolate c d u

def Straddle {R : Type*} [Ring R] [LT R] (a b c d : Point R) : Prop :=
  orient a b c * orient a b d < 0 ∧ orient c d a * orient c d b < 0

private theorem orient_interp (a b c d : Point ℝ) (t : ℝ) :
    orient a b (interpolate c d t) = (1-t)*orient a b c + t*orient a b d := by
  unfold orient interpolate
  dsimp
  ring

private theorem orient_self_interp (a b : Point ℝ) (t : ℝ) :
    orient a b (interpolate a b t) = 0 := by
  unfold orient interpolate
  dsimp
  ring

private theorem opposite_of_interp {a b t : ℝ} (ha : a ≠ 0) (ht : 0 < t) (ht' : t < 1)
    (h : (1-t)*a + t*b = 0) : a*b < 0 := by
  have hpos : 0 < 1-t := sub_pos.mpr ht'
  rcases lt_or_gt_of_ne ha with ha' | ha'
  · apply mul_neg_of_neg_of_pos ha'
    by_contra! hb
    linarith [mul_neg_of_pos_of_neg hpos ha', mul_nonpos_of_nonneg_of_nonpos ht.le hb]
  · apply mul_neg_of_pos_of_neg ha'
    by_contra! hb
    linarith [mul_pos hpos ha', mul_nonneg ht.le hb]

private theorem ratio_inside {x y : ℝ} (h : x*y < 0) :
    0 < x/(x-y) ∧ x/(x-y) < 1 := by
  rcases mul_neg_iff.mp h with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · have hd : 0 < x-y := by linarith
    exact ⟨div_pos hx hd, (div_lt_one hd).mpr (by linarith)⟩
  · have hd : x-y < 0 := by linarith
    exact ⟨div_pos_of_neg_of_neg hx hd, (div_lt_one_of_neg hd).mpr (by linarith)⟩

theorem interiorMeet_iff_straddle (a b c d : Point ℝ)
    (h₁ : orient a b c ≠ 0) (h₂ : orient c d a ≠ 0) :
    InteriorMeet a b c d ↔ Straddle a b c d := by
  constructor
  · rintro ⟨t,u,ht,ht',hu,hu',eq⟩
    constructor
    · apply opposite_of_interp h₁ hu hu'
      rw [← orient_interp, ← eq, orient_self_interp]
    · apply opposite_of_interp h₂ ht ht'
      rw [← orient_interp, eq, orient_self_interp]
  · rintro ⟨hab,hcd⟩
    obtain ⟨ht,ht'⟩ := ratio_inside hcd
    obtain ⟨hu,hu'⟩ := ratio_inside hab
    refine ⟨_, _, ht, ht', hu, hu', ?_⟩
    have rel : orient c d a - orient c d b = -(orient a b c - orient a b d) := by
      unfold orient
      ring
    have hn : orient a b c - orient a b d ≠ 0 := by
      intro h
      have he := sub_eq_zero.mp h
      rw [he] at hab
      exact (not_lt_of_ge (mul_self_nonneg _)) hab
    rw [rel]
    apply Prod.ext <;> dsimp [interpolate] <;> field_simp [hn] <;> unfold orient <;> ring

/-- Each index below n is visited once. -/
def sumFin (n : Nat) (f : Fin n → Nat) : Nat := ((List.finRange n).map f).sum

/-- The summand is evaluated exactly for 0 ≤ i < j < k < l < n. -/
def sumQuads {n : Nat} (f : (i j k l : Fin n) → i < j → j < k → k < l → Nat) : Nat :=
  sumFin n fun l => sumFin l.val fun k => sumFin k.val fun j => sumFin j.val fun i =>
    let k' : Fin n := ⟨k.val, by omega⟩
    let j' : Fin n := ⟨j.val, by omega⟩
    let i' : Fin n := ⟨i.val, by omega⟩
    f i' j' k' l i.isLt j.isLt k.isLt

/-- Three unordered matchings of four labeled points. Each is a separate
edge pair, so concurrence of crossing points never changes the count. -/
def threeMatchings {α : Type*} (cost : α → α → α → α → Nat) (a b c d : α) : Nat :=
  cost a b c d + cost a c b d + cost a d b c

noncomputable def meetCost (a b c d : Point ℝ) : Nat := by
  classical
  exact if InteriorMeet a b c d then 1 else 0

noncomputable def crossings {n : Nat} (p : Drawing n ℝ) : Nat :=
  sumQuads (fun i j k l _ _ _ => threeMatchings meetCost (p i) (p j) (p k) (p l))

/-- The requested equality, expressed as both attainment and a universal bound. -/
def MinimumIs (v : Nat) : Prop :=
  (∃ p : Drawing 28 ℝ, GeneralPosition p ∧ crossings p = v) ∧
  (∀ p : Drawing 28 ℝ, GeneralPosition p → v ≤ crossings p)

def intCost (a b c d : Point ℤ) : Nat :=
  if orient a b c * orient a b d < 0 ∧ orient c d a * orient c d b < 0 then 1 else 0

def intCrossings {n : Nat} (p : Drawing n ℤ) : Nat :=
  sumQuads (fun i j k l _ _ _ => threeMatchings intCost (p i) (p j) (p k) (p l))

def toReal (a : Point ℤ) : Point ℝ := (a.1, a.2)

@[simp] theorem orient_toReal (a b c : Point ℤ) :
    orient (toReal a) (toReal b) (toReal c) = (orient a b c : ℤ) := by
  simp [toReal, orient]

theorem generalPosition_toReal {n : Nat} {p : Drawing n ℤ} (h : GeneralPosition p) :
    GeneralPosition (toReal ∘ p) := by
  constructor
  · apply Function.Injective.comp _ h.1
    intro a b hab
    apply Prod.ext
    · exact Int.cast_inj.mp (show (a.1 : ℝ) = (b.1 : ℝ) from congrArg Prod.fst hab)
    · exact Int.cast_inj.mp (show (a.2 : ℝ) = (b.2 : ℝ) from congrArg Prod.snd hab)
  · intro i j k hij hik hjk
    simpa using h.2 i j k hij hik hjk

private theorem castCost (a b c d : Point ℤ) (h₁ : orient a b c ≠ 0) (h₂ : orient c d a ≠ 0) :
    meetCost (toReal a) (toReal b) (toReal c) (toReal d) = intCost a b c d := by
  unfold meetCost intCost
  rw [interiorMeet_iff_straddle _ _ _ _ (by simpa using h₁) (by simpa using h₂)]
  simp [Straddle, ← Int.cast_mul, Int.cast_lt_zero]

theorem crossings_toReal {n : Nat} {p : Drawing n ℤ} (h : GeneralPosition p) :
    crossings (toReal ∘ p) = intCrossings p := by
  unfold crossings intCrossings
  apply congrArg sumQuads
  funext i j k l hij hjk hkl
  dsimp [threeMatchings]
  have hik := lt_trans hij hjk
  have hjl := lt_trans hjk hkl
  have hil := lt_trans hik hkl
  rw [castCost _ _ _ _ (h.2 i j k hij.ne hik.ne hjk.ne)
        (h.2 k l i hkl.ne hik.ne' hil.ne'),
      castCost _ _ _ _ (h.2 i k j hik.ne hij.ne hjk.ne')
        (h.2 j l i hjl.ne hij.ne' hil.ne'),
      castCost _ _ _ _ (h.2 i l j hil.ne hij.ne hjl.ne')
        (h.2 j k i hjk.ne hij.ne' hik.ne')]

end K28
