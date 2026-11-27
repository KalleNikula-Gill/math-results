import WeightedStar.Polynomial
import DefantStar
import Mathlib.Analysis.Complex.Polynomial.Basic

namespace WeightedStar
open Polynomial
open scoped BigOperators
noncomputable section

/-- The real Narayana-product sum of this positive integral weighted tree does not split. -/
theorem question_9_4 :
    ¬ (∑ q : LatticePoint, ∏ v : Vertex, narayanaPolynomial (q.val v).toNat).Splits
      (RingHom.id ℝ) := by
  change ¬ latticeSum.Splits (RingHom.id ℝ)
  rw [latticeSum_eq]
  exact defant_weighted_star_counterexample

/-- Equivalently, the actual lattice-point polynomial has a zero off the real axis. -/
theorem exists_nonreal_zero :
    ∃ z : ℂ, (latticeSum.map Complex.ofRealHom).IsRoot z ∧ z.im ≠ 0 := by
  by_contra! h
  apply question_9_4
  apply Polynomial.splits_id_of_splits Complex.ofRealHom (IsAlgClosed.splits_codomain latticeSum)
  intro z hz
  refine ⟨z.re, Complex.ext ?_ ?_⟩
  · rfl
  · exact (h z (Polynomial.mem_roots'.1 hz).2).symm

#print axioms tree
#print axioms zonotope_positive
#print axioms lattice_bijective
#print axioms lattice_point_count
#print axioms latticeSum_eq
#print axioms DefantCircuit.exact_certificate
#print axioms question_9_4
#print axioms exists_nonreal_zero
end
end WeightedStar
