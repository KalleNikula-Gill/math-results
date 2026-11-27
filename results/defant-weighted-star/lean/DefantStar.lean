import WeightedStar.Arithmetic

namespace DefantCircuit

theorem exact_certificate : certificateBounds (jet normalizedStar) :=
  (congrArg certificateBounds star_eval).mpr (bounds_of_decide packed check_exact)

private theorem gap_of_certificate (s : Jet) (hs : certificateBounds s) :
    s.d^2 < s.v * s.dd := by
  obtain ⟨_, lower, _⟩ := hs
  have h := lt_of_le_of_lt (mul_nonneg (by decide : (0 : ℚ) ≤ 12223800) (sq_nonneg s.v)) lower
  exact sub_pos.mp (pos_of_mul_pos_right h (sq_nonneg x0))

theorem exact_gap :
    (normalizedStar.derivative.eval x0)^2 <
      normalizedStar.eval x0 * normalizedStar.derivative.derivative.eval x0 :=
  gap_of_certificate (jet normalizedStar) exact_certificate

#print axioms exact_certificate

#print axioms exact_gap

end DefantCircuit


open Polynomial

namespace Laguerre

noncomputable section

/-- The real Laguerre defect of a polynomial evaluated at one real point. -/
def defect (p : ℝ[X]) (x : ℝ) : ℝ :=
  (p.derivative.eval x)^2 - p.eval x * p.derivative.derivative.eval x

lemma defect_mul (p q : ℝ[X]) (x : ℝ) :
    defect (p * q) x = (q.eval x)^2 * defect p x + (p.eval x)^2 * defect q x := by
  simp only [defect, Polynomial.derivative_mul, Polynomial.derivative_add,
    Polynomial.eval_mul, Polynomial.eval_add]
  ring

lemma defect_linear (a x : ℝ) :
    defect (Polynomial.X - Polynomial.C a) x = 1 := by
  simp [defect]

lemma defect_const (a x : ℝ) :
    defect (Polynomial.C a) x = 0 := by
  simp [defect]

lemma defect_prod_linear_nonneg (roots : Multiset ℝ) (x : ℝ) :
    0 ≤ defect ((roots.map (fun r => Polynomial.X - Polynomial.C r)).prod) x := by
  induction roots using Multiset.induction_on with
  | empty => simp [defect]
  | cons r roots ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, defect_mul, defect_linear]
    exact add_nonneg (mul_nonneg (sq_nonneg _) zero_le_one) (mul_nonneg (sq_nonneg _) ih)

theorem eval_mul_eval_second_le_sq_of_splits (p : ℝ[X])
    (hp : p.Splits (RingHom.id ℝ)) (x : ℝ) :
    p.eval x * p.derivative.derivative.eval x ≤ (p.derivative.eval x)^2 := by
  apply sub_nonneg.mp
  change 0 ≤ defect p x
  have h := Polynomial.eq_prod_roots_of_splits_id hp
  calc
    0 ≤ (Polynomial.C p.leadingCoeff).eval x ^ 2 *
        defect ((p.roots.map (fun r => Polynomial.X - Polynomial.C r)).prod) x :=
      mul_nonneg (sq_nonneg _) (defect_prod_linear_nonneg p.roots x)
    _ = defect p x := by
      conv_rhs => rw [h]
      rw [defect_mul, defect_const, mul_zero, zero_add]

/-- A strictly positive reversed Laguerre gap at a rational input certifies
    that the real coefficient map does not split. -/
theorem not_splits_map_rat_of_laguerre_witness (p : ℚ[X]) (x : ℚ)
    (gap : (p.derivative.eval x)^2 < p.eval x * p.derivative.derivative.eval x) :
    ¬ (p.map (Rat.castHom ℝ)).Splits (RingHom.id ℝ) := by
  intro hp
  have h := eval_mul_eval_second_le_sq_of_splits
    (p.map (Rat.castHom ℝ)) hp ((Rat.castHom ℝ) x)
  simp only [Polynomial.derivative_map, Polynomial.eval_map, Polynomial.eval₂_at_apply] at h
  have hcast : (Rat.castHom ℝ) (p.eval x * p.derivative.derivative.eval x) ≤
      (Rat.castHom ℝ) ((p.derivative.eval x)^2) := by
    simpa only [map_mul, map_pow] using h
  exact (not_lt_of_ge (Rat.cast_le.mp hcast)) gap

/-- Restoring a nonzero polynomial factor cannot repair nonsplitting. -/
theorem not_splits_mul_left {p q : ℝ[X]} (hp : ¬ p.Splits (RingHom.id ℝ))
    (hq : q ≠ 0) : ¬ (q * p).Splits (RingHom.id ℝ) := by
  have hp0 : p ≠ 0 := by
    intro hz
    subst p
    exact hp (Polynomial.splits_zero _)
  intro h
  exact hp (Polynomial.splits_of_splits_mul (RingHom.id ℝ) (mul_ne_zero hq hp0) h).2

/-- The rational witness also rules out a monomial times the tested polynomial. -/
theorem not_splits_map_rat_X_pow_mul_of_laguerre_witness (p : ℚ[X]) (x : ℚ) (n : ℕ)
    (gap : (p.derivative.eval x)^2 < p.eval x * p.derivative.derivative.eval x) :
    ¬ ((Polynomial.X ^ n * p).map (Rat.castHom ℝ)).Splits (RingHom.id ℝ) := by
  rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X]
  exact not_splits_mul_left (not_splits_map_rat_of_laguerre_witness p x gap)
    (pow_ne_zero _ Polynomial.X_ne_zero)

#print axioms not_splits_map_rat_X_pow_mul_of_laguerre_witness

#print axioms not_splits_map_rat_of_laguerre_witness

#print axioms eval_mul_eval_second_le_sq_of_splits

end
end Laguerre

open Polynomial in
theorem defant_weighted_star_counterexample :
    ¬ ((X ^ 107 * DefantCircuit.normalizedStar).map (Rat.castHom ℝ)).Splits (RingHom.id ℝ) :=
  Laguerre.not_splits_map_rat_X_pow_mul_of_laguerre_witness
    DefantCircuit.normalizedStar DefantCircuit.x0 107 DefantCircuit.exact_gap

#print axioms defant_weighted_star_counterexample
