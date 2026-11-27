import WeightedStar.Convolution

namespace WeightedStar
open Polynomial DefantCircuit
open scoped BigOperators
noncomputable section

/-- The unshifted real Narayana polynomial of Defant, including the convention at zero. -/
def narayanaPolynomial (n : ℕ) : ℝ[X] :=
  if n = 0 then 1 else
    ∑ j ∈ Finset.Icc 1 n,
      C ((n : ℝ)⁻¹ * (n.choose j : ℝ) * (n.choose (j-1) : ℝ)) * X ^ j

/-- Defant's finite sum over the lattice of the real Minkowski sum. -/
def latticeSum : ℝ[X] :=
  ∑ q : LatticePoint, ∏ v : Vertex, narayanaPolynomial (q.val v).toNat

lemma narayana_succ (h : ℕ) :
    narayanaPolynomial (h + 1) = (X * nar h).map (Rat.castHom ℝ) := by
  rw [narayanaPolynomial, if_neg (by omega), ← Finset.Ico_succ_right_eq_Icc,
    Finset.sum_Ico_eq_sum_range]
  rw [Polynomial.map_mul, map_X, nar, circuit_sum_range, Polynomial.map_sum, Finset.mul_sum]
  simp only [Nat.add_sub_cancel, C_mul_X_pow_eq_monomial,
    map_monomial, X_mul_monomial, Nat.add_comm 1]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  simp [narCoeff, choose_spec, div_eq_mul_inv]
  ring

lemma factor_at_point (s : Allocation) (v : Vertex) :
    narayanaPolynomial (coordinates s v) =
      (X * nar (coordinates s v - 1)).map (Rat.castHom ℝ) := by
  have h : coordinates s v - 1 + 1 = coordinates s v := by have := coord_pos s v; omega
  simpa only [h] using narayana_succ (coordinates s v - 1)

lemma normalized_product (s : Allocation) :
    (∏ v : Vertex, nar (coordinates s v - 1)) =
    (∏ i, nar (base i - 1 + mass i - (s i).val)) * nar (∑ i, (s i).val) := by
  rw [Fintype.prod_sum_type, Fintype.prod_unique, mul_comm]
  change (∏ i : Leaf, nar ((base i + (mass i - (s i).val)) - 1)) *
    nar ((1 + ∑ i, (s i).val) - 1) = _
  rw [Nat.add_sub_cancel_left]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  have := base_pos i
  have := (s i).isLt
  congr 1
  omega

theorem latticeSum_eq : latticeSum = (X ^ 107 * normalizedStar).map (Rat.castHom ℝ) := by
  rw [latticeSum, ← allocationEquiv.sum_comp]
  change (∑ s : Allocation, ∏ v : Vertex, narayanaPolynomial ((coordinates s v : ℤ).toNat)) = _
  simp only [Int.toNat_natCast]
  simp_rw [factor_at_point, ← Polynomial.map_prod, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, vertex_count, normalized_product]
  rw [← Polynomial.map_sum, ← Finset.mul_sum, normalizedStar, allocation_expansion]

end
end WeightedStar
