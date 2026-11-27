import Lean
namespace K28

def E (e : Nat → Nat) (k : Nat) : Nat :=
  ((List.range (k + 1)).map e).sum

def weighted (e : Nat → Nat) : Nat :=
  ((List.range 13).map fun k => (25-2*k)*E e k).sum

def lower : List Nat := [3,9,18,30,45,63,84,108,135,167,205,249,314]

def profile : List Nat := [3,6,9,12,15,18,21,24,27,32,38,44,65,64]

private theorem sum_map_add (l : List Nat) (f g : Nat → Nat) :
    (l.map (fun n => f n + g n)).sum =
    (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => rfl
  | cons a tl ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    omega

private theorem zero_of_mem_sum_zero (l : List Nat) (x : Nat)
    (hm : x ∈ l) (hz : l.sum = 0) : x = 0 := by
  induction l with
  | nil => simp at hm
  | cons a tl ih =>
    rw [List.sum_cons] at hz
    rcases List.mem_cons.mp hm with rfl | h
    · omega
    · exact ih h (by omega)

private theorem sum_append_singleton (l : List Nat) (x : Nat) :
    (l ++ [x]).sum = l.sum + x := by
  induction l with
  | nil => simp
  | cons a tl ih =>
    simp [ih, Nat.add_assoc]

private theorem E_succ (e : Nat → Nat) (k : Nat) :
    E e (k + 1) = E e k + e (k + 1) := by
  unfold E
  rw [List.range_succ, List.map_append]
  exact sum_append_singleton _ _

theorem all_cumulative_eq (e : Nat → Nat)
    (hb : ∀ k : Nat, k < 13 → lower[k]! ≤ E e k)
    (hC : weighted e = 9690) :
    ∀ k : Nat, k < 13 → E e k = lower[k]! := by
  let f := fun k => (25 - 2*k)*lower[k]!
  let g := fun k => (25 - 2*k)*(E e k - lower[k]!)
  have hbase : ((List.range 13).map f).sum = 9690 := by decide
  have hmaps : (List.range 13).map (fun k => (25 - 2*k)*E e k) =
      (List.range 13).map (fun k => f k + g k) := by
    apply List.map_congr_left
    intro k hk
    have hh := hb k (List.mem_range.mp hk)
    have hrs : lower[k]! + (E e k - lower[k]!) = E e k := by omega
    simp only [f, g, ← Nat.mul_add, hrs]
  unfold weighted at hC
  rw [hmaps, sum_map_add, hbase] at hC
  have hz : ((List.range 13).map g).sum = 0 := by omega
  intro k hk
  have hm : g k ∈ (List.range 13).map g :=
    List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩
  have hzero : g k = 0 := zero_of_mem_sum_zero _ _ hm hz
  have hpos : 0 < 25 - 2*k := by omega
  have heq : E e k - lower[k]! = 0 :=
    (Nat.mul_eq_zero.mp hzero).resolve_left (Nat.ne_of_gt hpos)
  have hh := hb k hk
  omega

theorem equality_profile (e : Nat → Nat)
    (hb : ∀ k : Nat, k < 13 → lower[k]! ≤ E e k)
    (ht : E e 13 = 378) (hC : weighted e = 9690) :
    ∀ k : Nat, k < 14 → e k = profile[k]! := by
  have he := all_cumulative_eq e hb hC
  intro k hk
  cases k with
  | zero => exact he 0 (by decide)
  | succ k =>
    have a : k < 13 := by omega
    have hstep := E_succ e k
    by_cases b : k+1 < 13
    · rw [he _ b, he _ a] at hstep
      have hval : lower[k+1]! = lower[k]! + profile[k+1]! := by
        have hc : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 := by omega
        rcases hc with hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc <;> subst k <;> decide
      omega
    · have hc : k = 12 := by omega
      subst k
      rw [ht, he 12 (by decide)] at hstep
      change 378 = 314 + e 13 at hstep
      change e 13 = 64
      omega

#print axioms equality_profile

def xyAtGate (x y g : Nat) : Nat := min g x - (g-y)

def externalGate (g : Nat) : Nat :=
  xyAtGate 10 9 g + xyAtGate 9 9 g + xyAtGate 9 10 g

def externalEdge (k : Nat) : Nat :=
  if k = 13 then externalGate 14 else externalGate (k+1) + externalGate (27-k)

def internalEdge (k : Nat) : Nat := profile[k]! - externalEdge k

theorem externalProfile :
    (List.range 14).map externalEdge =
    [3,6,9,12,15,18,21,24,27,28,28,28,28,14] := by decide

theorem internalProfile :
    (List.range 14).map internalEdge =
    [0,0,0,0,0,0,0,0,0,4,10,16,37,50] := by decide

theorem halving50 : internalEdge 13 = 50 := by decide

def choose2 (n : Nat) := n*(n-1)/2

def prefixBound (m d t : Nat) : Nat :=
  choose2 t + choose2 (m-t) + (2*d+1)*t

def groupBound (m d : Nat) : Nat :=
  ((List.range (m+1)).map (prefixBound m d)).foldl min (m*m+m*m)

def totalBound (d : Nat) : Nat := groupBound 10 d + 2*groupBound 9 d

def requiredInternal (d : Nat) : Nat :=
  ((List.range (d+1)).map fun k => internalEdge (13-k)).sum

theorem prefixBound10 : [1,2,3,4].map (groupBound 10) = [33,39,43,45] := by decide

theorem prefixBound9 : [1,2,3,4].map (groupBound 9) = [27,32,35,36] := by decide

theorem requiredEquality :
    [1,2,3,4].map totalBound = [1,2,3,4].map requiredInternal := by decide

theorem central_lower (e : Nat → Nat)
    (ht : E e 13 = 378) (h11 : 249 ≤ E e 11)
    (hc : e 13 ≤ e 12) : 314 ≤ E e 12 := by
  have h12 := E_succ e 11
  have h13 := E_succ e 12
  change E e 12 = E e 11 + e 12 at h12
  change E e 13 = E e 12 + e 13 at h13
  omega

#print axioms externalProfile
#print axioms requiredEquality
#print axioms central_lower


def minimizingCuts (m d : Nat) : List Nat :=
  (List.range (m+1)).filter (fun t => prefixBound m d t == groupBound m d)

theorem minimizingCuts10 :
    [1,2,3,4].map (minimizingCuts 10) = [[3,4],[2,3],[1,2],[0,1]] := by decide

theorem minimizingCuts9 :
    [1,2,3,4].map (minimizingCuts 9) = [[3],[2],[1],[0]] := by decide

theorem each_attains_bound {a b c A B C : Nat}
    (ha : a ≤ A) (hb : b ≤ B) (hc : c ≤ C)
    (h : a+b+c = A+B+C) : a = A ∧ b = B ∧ c = C := by omega

theorem profile_of_7233 (e : Nat → Nat)
    (hb : ∀ k : Nat, k < 12 → lower[k]! ≤ E e k)
    (ht : E e 13 = 378) (hc : e 13 ≤ e 12)
    (hC : weighted e = 7233 + 2457) :
    ∀ k : Nat, k < 14 → e k = profile[k]! := by
  apply equality_profile e _ ht hC
  intro k hk
  by_cases hk' : k < 12
  · exact hb k hk'
  · have h : k = 12 := by omega
    subst k
    exact central_lower e ht (hb 11 (by decide)) hc

#print axioms minimizingCuts10
#print axioms profile_of_7233

end K28
