import QFibModel
import QFibArrays

open Polynomial
open scoped Polynomial
namespace QFib
open QFibArrays

noncomputable def delta (m n : ℕ) : ℤ[X] := (1-X) * poly m n

theorem subShift_coeff (p : ℤ[X]) (k i : ℕ) :
    ((1-X^k)*p).coeff i = subShift k p.coeff i := by
  simp [sub_mul, subShift, shift, coeff_X_pow_mul']

theorem delta_step (m n : ℕ) : (1-X^(Nat.fib (m+1))) * delta (m+1) n =
    (1-X^(Nat.fib (m+n+1))) * delta m n := by
  unfold delta
  calc
    _ = (1-X) * ((1-X^(Nat.fib (m+1))) * poly (m+1) n) := by ring
    _ = _ := by rw [poly_step]; ring

theorem delta_succ (m n i : ℕ) : (delta m n).coeff (i+1) =
    (poly m n).coeff (i+1) - (poly m n).coeff i := by
  simp [delta, sub_mul]

theorem delta_zero (m n : ℕ) : (delta m n).coeff 0 = 1 := by
  simp [delta, sub_mul, poly_zero_coeff]

private def runStart (h : ℕ) := (Array.replicate (h+1) (0 : Int)).set! 0 1
private def runStep (h n : ℕ) (a : Array Int) (j : ℕ) :=
  let b := if j = 0 then a else QFibFinite.divideShift h (QFibFinite.fib (j+1)) a
  QFibFinite.multiplyShift h (QFibFinite.fib (n+j+1)) b
private def runPrefix (h m n : ℕ) :=
  (List.range m).foldl (runStep h n) (runStart h)

private theorem prefix_succ (h m n : ℕ) :
    runPrefix h (m+1) n = runStep h n (runPrefix h m n) m := by
  simp [runPrefix, List.range_succ, List.foldl_append]

private theorem start_rep (h : ℕ) : Represents h (runStart h) (1 : ℤ[X]).coeff := by
  refine ⟨by simp [runStart], ?_⟩
  intro i hi
  have hai : i < (Array.replicate (h+1) (0 : Int)).size := by simp; omega
  simp only [runStart, read_set _ _ _ _ hai]
  by_cases hz : i=0
  · subst i; simp
  · simp [hz, Ne.symm hz, coeff_one, getElem!_pos (Array.replicate (h+1) (0 : Int)) i hai]

private theorem prefix_rep (h m n : ℕ) :
    Represents h (runPrefix h (m+1) n) (delta (m+1) n).coeff := by
  induction m with
  | zero =>
    rw [prefix_succ]
    change Represents h (QFibFinite.multiplyShift h (QFibFinite.fib (n+0+1)) (runStart h)) _
    simp only [finite_fib, Nat.add_zero]
    have hh := multiplyShift_rep (k := Nat.fib (n+1)) (start_rep h)
    have hP := poly_step 0 n
    simp only [zero_add, Nat.fib_one, pow_one, poly, mul_one] at hP
    have hEq : (delta 1 n).coeff = subShift (Nat.fib (n+1)) (1 : ℤ[X]).coeff := by
      funext i
      rw [← subShift_coeff, mul_one]
      exact congrArg (fun p : ℤ[X] => p.coeff i) hP
    rw [hEq]
    exact hh
  | succ m ih =>
    rw [prefix_succ]
    let k := Nat.fib (m+1+1)
    let A := Nat.fib ((m+1)+n+1)
    let f := (delta (m+1) n).coeff
    have hk : 0 < k := Nat.fib_pos.mpr (by omega)
    have hd := divideShift_rep (k:=k) hk ih (fun i _ => divSeries_rec hk f i)
    have hm := multiplyShift_rep (k:=A) hd
    have hEq : subShift A (divSeries k f) = (delta (m+1+1) n).coeff := by
      apply subShift_injective hk
      intro i
      rw [shift_sub]
      have he : subShift k (divSeries k f) = f := funext (subShift_div hk f)
      rw [he, ← subShift_coeff, ← subShift_coeff]
      exact congrArg (fun p : ℤ[X] => p.coeff i) (delta_step (m+1) n).symm
    rw [hEq] at hm
    simpa only [runStep, Nat.succ_ne_zero, if_false, finite_fib,
      Nat.add_comm n (m+1)] using hm

theorem array_coeff {m : ℕ} (hm : 0<m) (n i : ℕ) (hi : i ≤ QFibFinite.hIndex m n) :
    (QFibFinite.differences m n)[i]! = (delta m n).coeff i := by
  cases m with
  | zero => omega
  | succ m =>
    simpa only [QFibFinite.differences, runPrefix, runStep, runStart, beq_iff_eq] using
      (prefix_rep _ m n).2 i hi

/-- Symmetry supplies the falling half, including an odd-degree double peak. -/
theorem unimodal_of_left (m n : ℕ)
    (hleft : ∀ i, i ≤ (poly m n).natDegree/2 → 0 ≤ (delta m n).coeff i) :
    Unimodal (poly m n) := by
  let d := (poly m n).natDegree
  have rise (i : ℕ) (hi : i < d/2) : (poly m n).coeff i ≤ (poly m n).coeff (i+1) := by
    have hh := hleft (i+1) (by change i+1 ≤ d/2; omega)
    rw [delta_succ] at hh
    omega
  refine ⟨rise, ?_⟩
  intro i hl hi
  change d/2 ≤ i at hl
  change i < d at hi
  have rs := poly_symmetric m n (i+1) (by change i+1 ≤ d; omega)
  have rt := poly_symmetric m n i (by change i ≤ d; omega)
  change (poly m n).coeff (d-(i+1)) = _ at rs
  change (poly m n).coeff (d-i) = _ at rt
  by_cases hc : d-(i+1)=i
  · rw [← rs, hc]
  · rw [← rs, ← rt, show d-i=(d-(i+1))+1 by omega]
    exact rise _ (by omega)

theorem direct_unimodal (m n : ℕ) (hm : 4≤m) (hmn : m≤n) (hn : n≤10) :
    Unimodal (poly m n) := by
  apply unimodal_of_left
  intro i hi
  rw [← hIndex_eq] at hi
  rw [← array_coeff (by omega : 0<m) n i hi]
  have hs : i < (QFibFinite.differences m n).size := by
    rw [QFibFinite.differences_size]; omega
  rw [getElem!_pos (QFibFinite.differences m n) i hs]
  exact QFibFinite.allDirectDifferences m n i hm hmn hn hi

#print axioms array_coeff
#print axioms direct_unimodal
end QFib
