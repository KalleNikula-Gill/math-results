import Mathlib.Analysis.Convex.Segment
import Mathlib.Algebra.Group.Pointwise.Set.BigOperators
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Tactic

/-! Geometry of the weighted star in Question 9.4. Each element of `Leaf`
names exactly one edge. All Minkowski sums are taken in the ambient real vector space. -/
namespace WeightedStar
open scoped BigOperators Pointwise

abbrev Leaf := Fin 10 ⊕ Fin 96
abbrev Vertex := Unit ⊕ Leaf
abbrev center : Vertex := Sum.inl ()
abbrev leaf (i : Leaf) : Vertex := Sum.inr i

def base : Leaf → ℕ := Sum.elim (fun _ => 1) (fun _ => 30)
def mass : Leaf → ℕ := Sum.elim (fun _ => 23) (fun _ => 1)
def translation : Vertex → ℕ := Sum.elim (fun _ => 1) base

theorem mass_pos (i : Leaf) : 0 < mass i := by cases i <;> decide +revert
theorem base_pos (i : Leaf) : 0 < base i := by cases i <;> decide +revert
theorem translation_pos (v : Vertex) : 0 < translation v := by
  cases v with
  | inl _ => exact Nat.zero_lt_one
  | inr i => exact base_pos i

def graph := completeBipartiteGraph Unit Leaf
def spoke (i : Leaf) : Sym2 Vertex := s(center, leaf i)

theorem spoke_mem (i : Leaf) : spoke i ∈ graph.edgeSet := by
  change graph.Adj center (leaf i)
  simp [graph, completeBipartiteGraph]

theorem spoke_bijective : Function.Bijective
    (fun i : Leaf => (⟨spoke i, spoke_mem i⟩ : graph.edgeSet)) := by
  constructor
  · intro i j h
    have h' : spoke i = spoke j := congrArg Subtype.val h
    simpa [spoke, Sym2.eq_iff] using h'
  · rintro ⟨e, he⟩
    induction e using Sym2.ind with
    | h v w =>
      cases v with
      | inl u =>
        cases w with
        | inl u' => simp [graph, completeBipartiteGraph] at he
        | inr i => exact ⟨i, rfl⟩
      | inr i =>
        cases w with
        | inl u => exact ⟨i, Subtype.ext (Sym2.eq_swap)⟩
        | inr j => simp [graph, completeBipartiteGraph] at he

noncomputable def spokeEquiv : Leaf ≃ graph.edgeSet := Equiv.ofBijective _ spoke_bijective

theorem tree : graph.IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  constructor
  · apply (SimpleGraph.connected_iff_exists_forall_reachable graph).2
    refine ⟨center, ?_⟩
    rintro (u | i)
    · exact SimpleGraph.Reachable.refl _
    · exact (show graph.Adj center (leaf i) from spoke_mem i).reachable
  · rw [← Nat.card_congr spokeEquiv]
    simp [Nat.card_eq_fintype_card]

theorem vertex_count : Fintype.card Vertex = 107 := by simp

/-- Standard coordinate vector. -/
def unitVector (v : Vertex) : Vertex → ℝ := fun w => if v = w then 1 else 0

/-- The scalar dilation of the segment joining the two unit coordinate vectors. -/
noncomputable def edgeSegment (i : Leaf) : Set (Vertex → ℝ) :=
  (mass i : ℝ) • segment ℝ (unitVector center) (unitVector (leaf i))

/-- The translated Minkowski sum, with real rather than integral segment points. -/
noncomputable def zonotope : Set (Vertex → ℝ) :=
  {fun v => (translation v : ℝ)} + ∑ i : Leaf, edgeSegment i

noncomputable def edgeVector (i : Leaf) (t : ℝ) : Vertex → ℝ :=
  t • unitVector center + ((mass i : ℝ) - t) • unitVector (leaf i)

theorem mem_edgeSegment (i : Leaf) (z : Vertex → ℝ) :
    z ∈ edgeSegment i ↔ ∃ t ∈ Set.Icc (0 : ℝ) (mass i), edgeVector i t = z := by
  have hpos : (0 : ℝ) < mass i := by exact_mod_cast mass_pos i
  constructor
  · rintro ⟨_, ⟨a, b, ha, hb, hab, rfl⟩, rfl⟩
    refine ⟨mass i * a, ⟨mul_nonneg hpos.le ha, ?_⟩, ?_⟩
    · nlinarith [mul_nonneg hpos.le hb, congrArg (fun x : ℝ => (mass i : ℝ) * x) hab]
    · simp only [edgeVector, smul_add, smul_smul]
      have hm : (mass i : ℝ) - mass i * a = mass i * b := by
        linear_combination -(mass i : ℝ) * hab
      rw [hm]
  · rintro ⟨t, ⟨ht, htm⟩, rfl⟩
    let a := t / mass i
    let b := ((mass i : ℝ) - t) / mass i
    have ha : 0 ≤ a := div_nonneg ht hpos.le
    have hb : 0 ≤ b := div_nonneg (sub_nonneg.mpr htm) hpos.le
    have hab : a + b = 1 := by dsimp [a, b]; field_simp; ring
    refine ⟨_, ⟨a, b, ha, hb, hab, rfl⟩, ?_⟩
    simp only [smul_add, smul_smul, edgeVector, a, b, mul_div_cancel₀ _ hpos.ne']

noncomputable def realPoint (t : Leaf → ℝ) : Vertex → ℝ :=
  Sum.elim (fun _ => 1 + ∑ i, t i) (fun i => (base i : ℝ) + ((mass i : ℝ) - t i))

lemma sum_edgeVector (t : Leaf → ℝ) :
    (fun v => (translation v : ℝ)) + (∑ i, edgeVector i (t i)) = realPoint t := by
  funext v
  cases v with
  | inl u => simp [edgeVector, unitVector, translation, realPoint, Finset.sum_apply]
  | inr j => cases j <;> simp [edgeVector, unitVector, translation, realPoint, Finset.sum_apply, mul_ite]

theorem mem_zonotope (q : Vertex → ℝ) :
    q ∈ zonotope ↔ ∃ t : Leaf → ℝ, (∀ i, t i ∈ Set.Icc 0 (mass i : ℝ)) ∧ realPoint t = q := by
  classical
  constructor
  · rintro ⟨_, ha, b, hb, rfl⟩
    rcases Set.mem_singleton_iff.mp ha with rfl
    obtain ⟨g, hg, rfl⟩ := (Set.mem_fintype_sum _ _).1 hb
    choose t ht he using fun i => (mem_edgeSegment i _).1 (hg i)
    exact ⟨t, ht, (sum_edgeVector t).symm.trans (by simp_rw [he])⟩
  · rintro ⟨t, ht, rfl⟩
    rw [← sum_edgeVector]
    apply Set.add_mem_add (Set.mem_singleton _)
    exact (Set.mem_fintype_sum _ _).2
      ⟨_, fun i => (mem_edgeSegment i _).2 ⟨t i, ht i, rfl⟩, rfl⟩

theorem zonotope_positive {q : Vertex → ℝ} (hq : q ∈ zonotope) (v : Vertex) : 0 < q v := by
  obtain ⟨t, ht, rfl⟩ := (mem_zonotope _).1 hq
  cases v with
  | inl u => exact add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg fun i _ => (ht i).1)
  | inr i =>
    change 0 < (base i : ℝ) + ((mass i : ℝ) - t i)
    exact add_pos_of_pos_of_nonneg (by exact_mod_cast base_pos i) (sub_nonneg.mpr (ht i).2)

abbrev Allocation := (i : Leaf) → Fin (mass i + 1)
abbrev LatticePoint := {q : Vertex → ℤ // (fun v => (q v : ℝ)) ∈ zonotope}

/-- Integer coordinates, indexed by the mass sent to the center along each edge. -/
def coordinates (s : Allocation) : Vertex → ℕ :=
  Sum.elim (fun _ => 1 + ∑ i, (s i).val) (fun i => base i + (mass i - (s i).val))

lemma coord_pos (s : Allocation) (v : Vertex) : 0 < coordinates s v := by
  cases v with
  | inl u => simp [coordinates]
  | inr i => exact Nat.add_pos_left (base_pos i) _

lemma real_coordinates (s : Allocation) :
    realPoint (fun i => ((s i).val : ℝ)) = (fun v => (coordinates s v : ℝ)) := by
  funext v
  cases v with
  | inl u => simp only [realPoint, coordinates, Sum.elim_inl, Nat.cast_add, Nat.cast_one, Nat.cast_sum]
  | inr i => simp [realPoint, coordinates, Nat.cast_sub (Nat.le_of_lt_succ (s i).isLt)]

def latticeOf (s : Allocation) : LatticePoint :=
  ⟨fun v => (coordinates s v : ℤ), (mem_zonotope _).2 ⟨_, fun i =>
    ⟨Nat.cast_nonneg _, by exact_mod_cast Nat.le_of_lt_succ (s i).isLt⟩,
    by simpa using real_coordinates s⟩⟩

theorem lattice_bijective : Function.Bijective latticeOf := by
  constructor
  · intro s t h
    funext i
    have h' := congrArg (fun q : LatticePoint => q.val (leaf i)) h
    have hs := (s i).isLt
    have ht := (t i).isLt
    apply Fin.ext
    simp [latticeOf, coordinates] at h'
    omega
  · rintro ⟨q, hq⟩
    obtain ⟨t, ht, eq⟩ := (mem_zonotope _).1 hq
    let k (i : Leaf) : ℤ := (base i : ℤ) + (mass i : ℤ) - q (leaf i)
    have hk (i) : (k i : ℝ) = t i := by
      have hj := congrFun eq (leaf i)
      dsimp [realPoint] at hj
      dsimp [k]
      push_cast
      linarith
    have hk0 (i) : 0 ≤ k i := by exact_mod_cast (hk i ▸ (ht i).1 : (0 : ℝ) ≤ (k i : ℝ))
    have hkm (i) : k i ≤ mass i := by
      exact_mod_cast (hk i ▸ (ht i).2 : (k i : ℝ) ≤ (mass i : ℝ))
    let s : Allocation := fun i => ⟨(k i).toNat, by have := hkm i; omega⟩
    have hs (i) : ((s i).val : ℝ) = t i := by
      change ((k i).toNat : ℝ) = t i
      rw [← hk i]
      exact_mod_cast Int.toNat_of_nonneg (hk0 i)
    refine ⟨s, Subtype.ext (funext fun v => ?_)⟩
    change (coordinates s v : ℤ) = q v
    have h := congrFun ((real_coordinates s).symm.trans ((congrArg realPoint (funext hs)).trans eq)) v
    exact_mod_cast h

noncomputable def allocationEquiv : Allocation ≃ LatticePoint :=
  Equiv.ofBijective latticeOf lattice_bijective

noncomputable instance : Fintype LatticePoint := Fintype.ofEquiv Allocation allocationEquiv

theorem lattice_point_count : Fintype.card LatticePoint = 24^10 * 2^96 := by
  rw [← Fintype.card_congr allocationEquiv, Fintype.card_pi]
  simp [Fintype.prod_sum_type, mass]

end WeightedStar
