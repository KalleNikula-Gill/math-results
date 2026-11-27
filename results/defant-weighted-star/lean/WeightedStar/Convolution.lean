import WeightedStar.Circuit
import Mathlib.Data.List.GetD
import WeightedStar.Geometry

/-! Identifying the original grouped circuit with a sum over all allocations.
The auxiliary polynomial variable records the total mass sent to the center. -/
namespace WeightedStar
open Polynomial DefantCircuit
open scoped BigOperators
noncomputable section

abbrev R := ℚ[X]

lemma circuit_sum_list (v : List R) : DefantCircuit.sum polyOps v = v.sum := by
  induction v with
  | nil => rfl
  | cons a l ih => exact congrArg (a + ·) ih

lemma circuit_sum_range (n : ℕ) (f : ℕ → R) :
    DefantCircuit.sum polyOps ((List.range n).map f) = ∑ j ∈ Finset.range n, f j := by
  rw [circuit_sum_list]
  induction n with
  | zero => simp
  | succ n ih => rw [List.sum_range_succ, Finset.sum_range_succ, ih]

def encode (row : List R) : R[X] :=
  ∑ j ∈ Finset.range row.length, monomial j (row.getD j 0)

lemma coeff_encode (row : List R) (j : ℕ) : (encode row).coeff j = row.getD j 0 := by
  by_cases hj : j < row.length <;> simp [encode, finset_sum_coeff, coeff_monomial, hj]

def leafFactor (p : ℕ → R) (a m : ℕ) : R[X] :=
  ∑ s ∈ Finset.range (m + 1), monomial s (p (a - 1 + m - s))

lemma coeff_times_monomial (P : R[X]) (s j : ℕ) (c : R) :
    (P * monomial s c).coeff j = if s ≤ j then P.coeff (j-s) * c else 0 := by
  rw [← C_mul_X_pow_eq_monomial, ← mul_assoc, coeff_mul_X_pow', coeff_mul_C]

lemma coeff_leaf_step (p : ℕ → R) (a m j : ℕ) (row : List R) :
    (encode row * leafFactor p a m).coeff j =
      ∑ s ∈ Finset.range (min j m + 1), row.getD (j-s) 0 * p (a-1+m-s) := by
  simp only [leafFactor, Finset.mul_sum, finset_sum_coeff, coeff_times_monomial, coeff_encode]
  calc
    _ = ∑ s ∈ Finset.range (min j m + 1),
          (if s ≤ j then row.getD (j-s) 0 * p (a-1+m-s) else 0) := by
      symm
      apply Finset.sum_subset (Finset.range_mono (by omega))
      intro s h hm
      simp only [Finset.mem_range] at h hm
      exact if_neg (by omega)
    _ = _ := Finset.sum_congr rfl fun s hs => if_pos (by
      have := Finset.mem_range.mp hs
      omega)

lemma encode_step (p : ℕ → R) (a m : ℕ) (row : List R) :
    encode (step polyOps p a m row) = encode row * leafFactor p a m := by
  ext j : 1
  rw [coeff_encode, coeff_leaf_step]
  by_cases hj : j < row.length + m
  · rw [List.getD_eq_getElem _ _ (by simpa [step] using hj)]
    simp only [step, List.getElem_map, List.getElem_range]
    exact circuit_sum_range _ _
  · rw [List.getD_eq_default _ _ (by simpa [step] using Nat.le_of_not_gt hj)]
    symm
    apply Finset.sum_eq_zero
    intro s hs
    have := Finset.mem_range.mp hs
    rw [List.getD_eq_default row 0 (by omega), zero_mul]

lemma encode_iterate (p : ℕ → R) (a m n : ℕ) (row : List R) :
    encode ((List.replicate n ()).foldl (fun l _ => step polyOps p a m l) row) =
      encode row * leafFactor p a m ^ n := by
  induction n generalizing row with
  | zero => simp
  | succ n ih => rw [List.replicate_succ, List.foldl_cons, ih, encode_step, pow_succ]; ring

/-- Replace the mass marker of degree `j` by the center factor `p j`. -/
def contract (p : ℕ → R) : R[X] →ₗ[R] R :=
  Polynomial.lsum (fun j => (LinearMap.id : R →ₗ[R] R).smulRight (p j))

lemma contract_monomial (p : ℕ → R) (j : ℕ) (c : R) :
    contract p (monomial j c) = c * p j := by
  simp [contract, Polynomial.lsum_apply, sum_monomial_index]

lemma contract_encode (p : ℕ → R) (row : List R) :
    contract p (encode row) = ∑ j ∈ Finset.range row.length, row.getD j 0 * p j := by
  simp only [encode, map_sum, contract_monomial]

theorem star_contract (p : ℕ → R) :
    star polyOps p = contract p (leafFactor p 1 23 ^ 10 * leafFactor p 30 1 ^ 96) := by
  let row := (List.replicate 96 ()).foldl (fun l _ => step polyOps p 30 1 l)
    ((List.replicate 10 ()).foldl (fun l _ => step polyOps p 1 23 l) [polyOps.u])
  have h : encode [polyOps.u] = 1 := by simp [encode, polyOps, monomial_zero_left]
  have erow : encode row = leafFactor p 1 23 ^ 10 * leafFactor p 30 1 ^ 96 := by
    simp only [row, encode_iterate, h, one_mul]
  rw [← erow, contract_encode]
  exact circuit_sum_range row.length (fun j => row.getD j 0 * p j)

lemma prod_monomials {ι : Type*} (I : Finset ι) (d : ι → ℕ) (c : ι → R) :
    (∏ i ∈ I, monomial (d i) (c i)) =
      monomial (∑ i ∈ I, d i) (∏ i ∈ I, c i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | insert i I hi ih => simp [hi, ih, monomial_mul_monomial]

theorem allocation_expansion (p : ℕ → R) :
    star polyOps p = ∑ s : Allocation,
      (∏ i, p (base i - 1 + mass i - (s i).val)) * p (∑ i, (s i).val) := by
  classical
  rw [star_contract]
  have hf : (∏ i : Leaf, leafFactor p (base i) (mass i)) =
      leafFactor p 1 23 ^ 10 * leafFactor p 30 1 ^ 96 := by
    simp [Fintype.prod_sum_type, base, mass]
  rw [← hf]
  have hf' (i : Leaf) : leafFactor p (base i) (mass i) =
      ∑ s : Fin (mass i + 1), monomial s.val (p (base i - 1 + mass i - s.val)) := by
    exact (Fin.sum_univ_eq_sum_range (fun s => monomial s (p (base i - 1 + mass i - s))) _).symm
  simp_rw [hf']
  rw [Fintype.prod_sum, map_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [prod_monomials, contract_monomial]

end
end WeightedStar
