import QFibFinite

namespace QFibArrays

/-- Coefficients outside the lower end of the truncation have value zero. -/
def shift (k : Nat) (f : Nat → Int) (i : Nat) : Int :=
  if k ≤ i then f (i-k) else 0

def subShift (k : Nat) (f : Nat → Int) (i : Nat) : Int := f i - shift k f i

def Represents (h : Nat) (xs : Array Int) (f : Nat → Int) : Prop :=
  xs.size = h+1 ∧ ∀ i, i ≤ h → xs[i]! = f i

theorem read_set (a : Array Int) (j i : Nat) (v : Int) (hi : i < a.size) :
    (a.set! j v)[i]! = if j=i then v else a[i]! := by
  simp only [Array.set!_eq_setIfInBounds, getElem!_pos (a.setIfInBounds j v) i (by simpa using hi),
    getElem!_pos a i hi, Array.getElem_setIfInBounds hi]

theorem shift_sub (a b : Nat) (f : Nat → Int) :
    ∀ i, subShift a (subShift b f) i = subShift b (subShift a f) i := by
  intro i
  simp only [subShift, shift]
  by_cases ha : a ≤ i <;> by_cases hb : b ≤ i <;> by_cases hab : a+b ≤ i <;>
    simp_all [show (b ≤ i-a) ↔ (a+b ≤ i) ∨ (b=0 ∧ i<a) by omega,
      show (a ≤ i-b) ↔ (a+b ≤ i) ∨ (a=0 ∧ i<b) by omega,
      show i-a-b=i-b-a by omega] <;> omega

/-- Low-to-high mutation implements the unique formal solution of
    y - X^k y = f through degree h. -/
theorem divideShift_rep {h k : Nat} (hk : 0 < k) {xs : Array Int}
    {f g : Nat → Int} (hs : Represents h xs f)
    (he : ∀ i, i ≤ h → g i = f i + shift k g i) :
    Represents h (QFibFinite.divideShift h k xs) g := by
  let step (a : Array Int) (j : Nat) := a.set! (j+k) (a[j+k]! + a[j]!)
  let state (l : Nat) := (List.range l).foldl step xs
  have size (l : Nat) : (state l).size = h+1 := by
    change ((List.range l).foldl step xs).size = h+1
    rw [QFibFinite.foldSize _ step (by intros; simp [step]), hs.1]
  have inv (l : Nat) (hl : l ≤ h+1-k) (i : Nat) (hi : i ≤ h) :
      (state l)[i]! = if i < l+k then g i else f i := by
    induction l generalizing i with
    | zero =>
      change xs[i]! = _
      rw [hs.2 i hi]
      split
      · rename_i hlt
        rw [he i hi, shift, if_neg (by omega)]
        omega
      · rfl
    | succ l ih =>
      have hprev : l ≤ h+1-k := by omega
      have hb : l+k ≤ h := by omega
      have hi' : i < (state l).size := by rw [size]; omega
      have hh : state (l+1) = step (state l) l := by simp [state, List.range_succ, List.foldl_append]
      rw [hh, show step (state l) l = _ by rfl]
      rw [read_set _ _ _ _ hi']
      by_cases hj : l+k=i
      · subst i
        rw [if_pos rfl, if_pos (by omega : l+k < l+1+k),
          ih hprev _ hb, ih hprev _ (by omega), if_neg (by omega : ¬l+k<l+k),
          if_pos (by omega : l<l+k), he (l+k) hb]
        simp [shift]
      · rw [if_neg hj, ih hprev i hi]
        simp [show (i<l+k) ↔ i<l+1+k by omega]
  refine ⟨size _, fun i hi => ?_⟩
  change (state (h+1-k))[i]! = _
  rw [inv _ (by omega) i hi, if_pos (by omega)]

/-- High-to-low mutation multiplies by 1-X^k. -/
theorem multiplyShift_rep {h k : Nat} {xs : Array Int} {f : Nat → Int}
    (hs : Represents h xs f) :
    Represents h (QFibFinite.multiplyShift h k xs) (subShift k f) := by
  let step (a : Array Int) (j : Nat) := a.set! (h-j) (a[h-j]! - a[h-j-k]!)
  let state (l : Nat) := (List.range l).foldl step xs
  have size (l : Nat) : (state l).size = h+1 := by
    change ((List.range l).foldl step xs).size = h+1
    rw [QFibFinite.foldSize _ step (by intros; simp [step]), hs.1]
  have inv (l : Nat) (hl : l ≤ h+1-k) (i : Nat) (hi : i ≤ h) :
      (state l)[i]! = if h < i+l then subShift k f i else f i := by
    induction l generalizing i with
    | zero =>
      change xs[i]! = _
      simp [hs.2 i hi, show ¬ h<i by omega]
    | succ l ih =>
      have hprev : l ≤ h+1-k := by omega
      have hyl : k ≤ h-l := by omega
      have hi' : i < (state l).size := by rw [size]; omega
      have hh : state (l+1) = step (state l) l := by simp [state, List.range_succ, List.foldl_append]
      rw [hh]
      change ((state l).set! (h-l) _)[i]! = _
      rw [read_set _ _ _ _ hi']
      by_cases hj : h-l=i
      · subst i
        rw [if_pos rfl, if_pos (by omega : h < h-l+(l+1)),
          ih hprev _ (by omega), ih hprev _ (by omega),
          if_neg (by omega : ¬h < h-l+l), if_neg (by omega : ¬h < h-l-k+l)]
        simp [subShift,shift,hyl]
      · rw [if_neg hj, ih hprev i hi]
        simp [show (h<i+l) ↔ h<i+(l+1) by omega]
  refine ⟨size _, fun i hi => ?_⟩
  change (state (h+1-k))[i]! = _
  rw [inv _ (by omega) i hi]
  split
  · rfl
  · rename_i hu
    simp [subShift, shift, show ¬k≤i by omega]

def divSeries (k : Nat) (f : Nat → Int) (i : Nat) : Int :=
  if _h : 0 < k ∧ k ≤ i then f i + divSeries k f (i-k) else f i
termination_by i
decreasing_by omega

theorem divSeries_rec {k : Nat} (hk : 0<k) (f : Nat → Int) (i : Nat) :
    divSeries k f i = f i + shift k (divSeries k f) i := by
  rw [divSeries]
  by_cases hi : k ≤ i <;> simp [shift, hk, hi]

theorem subShift_div {k : Nat} (hk : 0<k) (f : Nat → Int) (i : Nat) :
    subShift k (divSeries k f) i = f i := by
  unfold subShift
  rw [divSeries_rec hk f i]
  omega

theorem subShift_injective {k : Nat} (hk : 0<k) {f g : Nat → Int}
    (h : ∀ i, subShift k f i = subShift k g i) : f = g := by
  funext i
  induction i using Nat.strongRecOn with
  | ind i ih =>
    have hh := h i
    by_cases hi : k ≤ i
    · have hprev := ih (i-k) (by omega)
      simp [subShift, shift, hi, hprev] at hh
      exact hh
    · simpa [subShift, shift, hi] using hh

end QFibArrays
