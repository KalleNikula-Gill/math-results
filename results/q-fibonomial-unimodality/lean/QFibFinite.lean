import Std

namespace QFibFinite

/-- Fibonacci numbers computed by recursion on adjacent pairs. -/
def fibPair : Nat → Nat × Nat
  | 0 => (0, 1)
  | j+1 => let (a,b) := fibPair j; (b,a+b)
def fib (j : Nat) : Nat := (fibPair j).1

def fact (k : Nat) : Nat := (List.range k).foldl (fun x j => x*(j+1)) 1

/-- Trial divisors paired with their complementary divisors. -/
def ordersLoop (a d : Nat) : Nat → List Nat
  | 0 => []
  | fuel+1 =>
    if d*d > a then []
    else
      let tail := ordersLoop a (d+1) fuel
      if a % d == 0 then
        let e := a / d
        ([d,e].filter (· > 1)) ++ tail
      else tail

def orders (a : Nat) : List Nat := ordersLoop a 1 8192
def ordersFor (m : Nat) : List Nat :=
  orders (fib (m-2)) ++ orders (fib (m-1)) ++ orders (fib m)

def sCount (m e : Nat) : Nat :=
  ((List.range (m-3)).filter (fun j => fib (j+1) % e != 0)).length
def kCount (m e : Nat) : Nat :=
  ((List.range (m-4)).filter (fun j => 2 * fib (j+2) < e)).length

def lhs (m e : Nat) : Nat :=
  (2 * fib (max m 11 + 1)) ^ sCount m e * fact (kCount m e)
def rhs (m e : Nat) : Nat :=
  2 * fib (m-2) * fib (m-1) * fib m * fib m * e ^ sCount m e

def orderOK (m : Nat) : Bool :=
  (ordersFor m).all (fun e => decide (rhs m e < lhs m e))

def orderTests : List Nat := (List.range 36).map (· + 4)

def hIndex (m n : Nat) : Nat :=
  ((fib (m+n+2) + 1) - (fib (m+2) + fib (n+2))) / 2

/-- Truncated formal power series division by one minus a monomial:
    read an already-updated coefficient, traversing upward. -/
def divideShift (h k : Nat) (xs : Array Int) : Array Int :=
  (List.range (h+1-k)).foldl (fun a j =>
    let i := j+k
    a.set! i (a[i]! + a[j]!)) xs

/-- Truncated multiplication by one minus a monomial:
    read an untouched coefficient, traversing downward. -/
def multiplyShift (h k : Nat) (xs : Array Int) : Array Int :=
  (List.range (h+1-k)).foldl (fun a j =>
    let i := h-j
    a.set! i (a[i]! - a[i-k]!)) xs

def differences (m n : Nat) : Array Int :=
  let h := hIndex m n
  let start : Array Int := (Array.replicate (h+1) 0).set! 0 1
  (List.range m).foldl (fun a j =>
    let a := if j == 0 then a else divideShift h (fib (j+1)) a
    multiplyShift h (fib (n+j+1)) a) start

def pairOK (m n : Nat) : Bool := (differences m n).all (fun x => decide (0 ≤ x))

def pairTests : List (Nat × Nat) :=
  ((List.range 7).map (·+4)).flatMap (fun m =>
    (List.range (11-m)).map (fun j => (m, m+j)))

set_option maxRecDepth 100000
set_option maxHeartbeats 0

#eval ((orderTests.map (fun m => (ordersFor m).eraseDups.length)).sum, pairTests.length)
#eval orderTests.all orderOK
#eval pairTests.all (fun p => pairOK p.1 p.2)

theorem smallOrderCase : orderOK 4 = true := by decide
theorem smallPairCase : pairOK 4 4 = true := by decide
theorem allOrdersNative : orderTests.all orderOK = true := by native_decide
theorem allPairsNative : pairTests.all (fun p => pairOK p.1 p.2) = true := by native_decide
#print axioms allOrdersNative
#print axioms allPairsNative

theorem mem_ordersLoop (a b e : Nat) (_hb : 0 < b)
    (hba : b*b ≤ a) (hdiv : b ∣ a) (he : 1 < e)
    (heq : e = b ∨ e = a / b) :
    ∀ (fuel d : Nat), d ≤ b → b < d+fuel → e ∈ ordersLoop a d fuel := by
  intro fuel
  induction fuel with
  | zero => omega
  | succ fuel ih =>
      intro d hdb hdf
      have hstop : ¬ d*d > a := by
        exact Nat.not_lt_of_ge (Nat.le_trans (Nat.mul_self_le_mul_self hdb) hba)
      by_cases h : d = b
      · subst d
        have hmod := Nat.mod_eq_zero_of_dvd hdiv
        simp [ordersLoop, hstop, hmod]
        exact Or.inl ⟨heq, he⟩
      · have hnext := ih (d+1) (by omega) (by omega)
        simp only [ordersLoop, if_neg hstop]
        split
        · exact List.mem_append_right _ hnext
        · exact hnext

theorem orderCoverage (a e : Nat) (ha : 0 < a) (hc : a < 8192*8192)
    (he : 1 < e) (hd : e ∣ a) : e ∈ orders a := by
  obtain ⟨t, ht⟩ := hd
  have htpos : 0 < t := by
    cases t <;> simp_all
  by_cases het : e ≤ t
  · have hs : e*e ≤ a := ht ▸ Nat.mul_le_mul_left e het
    have he' : e < 8192 := by
      by_cases good : e < 8192
      · exact good
      have bad := good
      exact False.elim (Nat.not_lt_of_ge (Nat.le_trans (Nat.mul_self_le_mul_self (Nat.le_of_not_gt bad)) hs) hc)
    exact mem_ordersLoop _ e e (by omega) hs ⟨t, ht⟩ he (Or.inl rfl) 8192 1 (by omega) (by omega)
  · have ht' : t ≤ e := by omega
    have hsq : t*t ≤ a := ht ▸ Nat.mul_le_mul_right t ht'
    have ht'' : t < 8192 := by
      by_cases good : t < 8192
      · exact good
      have bad := good
      exact False.elim (Nat.not_lt_of_ge (Nat.le_trans (Nat.mul_self_le_mul_self (Nat.le_of_not_gt bad)) hsq) hc)
    have hdiv : t ∣ a := ⟨e, ht.trans (Nat.mul_comm e t)⟩
    have hq : e = a / t := (Nat.div_eq_of_eq_mul_left htpos ht).symm
    exact mem_ordersLoop _ t e htpos hsq hdiv he (Or.inr hq) 8192 1 (by omega) (by omega)


theorem mem_orderTests (m : Nat) (hm : 4 ≤ m) (hu : m < 40) : m ∈ orderTests := by
  apply List.mem_map.mpr
  exact ⟨m-4, List.mem_range.mpr (by omega), by omega⟩

def fitsTrial (a : Nat) : Bool := decide (0 < a ∧ a < 8192*8192)

def validOrderBounds (m : Nat) : Bool :=
  [fib (m-2), fib (m-1), fib m].all fitsTrial

theorem boundsForAll : orderTests.all validOrderBounds = true := by decide

theorem ordersFor_complete (m e : Nat) (hm : 4 ≤ m) (hu : m < 40)
    (he : 1 < e) (hdiv : e ∣ fib (m-2) ∨ e ∣ fib (m-1) ∨ e ∣ fib m) :
    e ∈ ordersFor m := by
  have hh := List.all_eq_true.mp boundsForAll m (mem_orderTests m hm hu)
  have checked := List.all_eq_true.mp hh
  have hA : fitsTrial (fib (m-2)) = true := checked _ (by simp)
  have hB : fitsTrial (fib (m-1)) = true := checked _ (by simp)
  have hC : fitsTrial (fib m) = true := checked _ (by simp)
  change decide (0 < fib (m-2) ∧ fib (m-2) < 8192*8192) = true at hA
  change decide (0 < fib (m-1) ∧ fib (m-1) < 8192*8192) = true at hB
  change decide (0 < fib m ∧ fib m < 8192*8192) = true at hC
  have hA := of_decide_eq_true hA
  have hB := of_decide_eq_true hB
  have hC := of_decide_eq_true hC
  simp only [ordersFor, List.mem_append]
  rcases hdiv with hD | hD | hD
  · exact Or.inl (Or.inl (orderCoverage _ e hA.1 hA.2 he hD))
  · exact Or.inl (Or.inr (orderCoverage _ e hB.1 hB.2 he hD))
  · exact Or.inr (orderCoverage _ e hC.1 hC.2 he hD)

theorem allOrderInequalities (m e : Nat) (hm : 4 ≤ m) (hu : m < 40)
    (he : 1 < e) (hd : e ∣ fib (m-2) ∨ e ∣ fib (m-1) ∨ e ∣ fib m) :
    rhs m e < lhs m e := by
  have h := List.all_eq_true.mp allOrdersNative m (mem_orderTests m hm hu)
  exact of_decide_eq_true (List.all_eq_true.mp h e (ordersFor_complete m e hm hu he hd))

theorem mem_pairTests (m n : Nat) (hm : 4 ≤ m) (hmn : m ≤ n) (hn : n ≤ 10) :
    (m,n) ∈ pairTests := by
  apply List.mem_flatMap.mpr
  refine ⟨m, List.mem_map.mpr ⟨m-4, List.mem_range.mpr (by omega), by omega⟩, ?_⟩
  exact List.mem_map.mpr ⟨n-m, List.mem_range.mpr (by omega), by congr 1 <;> omega⟩

theorem directCoefficientNonnegative (m n i : Nat)
    (hm : 4 ≤ m) (hmn : m ≤ n) (hn : n ≤ 10)
    (hi : i < (differences m n).size) :
    0 ≤ (differences m n)[i] := by
  have h := List.all_eq_true.mp allPairsNative (m,n) (mem_pairTests m n hm hmn hn)
  exact of_decide_eq_true (Array.all_eq_true.mp h i hi)

#print axioms orderCoverage
#print axioms allOrderInequalities
#print axioms directCoefficientNonnegative

theorem foldSize {β : Type} (l : List β)
    (f : Array Int → β → Array Int)
    (hf : ∀ a j, (f a j).size = a.size) (xs : Array Int) :
    (l.foldl f xs).size = xs.size := by
  induction l generalizing xs with
  | nil => rfl
  | cons j js h =>
    simp only [List.foldl_cons, h (f xs j), hf xs j]

theorem divideShift_size (h k : Nat) (xs : Array Int) :
    (divideShift h k xs).size = xs.size := by
  unfold divideShift
  apply foldSize
  intro a j
  simp [Array.set!]

theorem multiplyShift_size (h k : Nat) (xs : Array Int) :
    (multiplyShift h k xs).size = xs.size := by
  unfold multiplyShift
  apply foldSize
  intro a j
  simp [Array.set!]

theorem differences_size (m n : Nat) : (differences m n).size = hIndex m n + 1 := by
  unfold differences
  rw [foldSize]
  · simp [Array.set!]
  · intro a j
    rw [multiplyShift_size]
    split
    · rfl
    · apply divideShift_size

theorem allDirectDifferences (m n i : Nat)
    (hm : 4 ≤ m) (hmn : m ≤ n) (hn : n ≤ 10) (hi : i ≤ hIndex m n) :
    0 ≤ (differences m n)[i]'(by rw [differences_size]; omega) :=
  directCoefficientNonnegative m n i hm hmn hn (by rw [differences_size]; omega)

theorem testCounts :
    ((orderTests.map (fun m => (ordersFor m).eraseDups.length)).sum, pairTests.length) = (1424, 28) := by
  native_decide
#print axioms allDirectDifferences
#print axioms testCounts

end QFibFinite
