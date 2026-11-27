import QFibPoles

open Polynomial Finset
open scoped Polynomial BigOperators
namespace QFib.Roots

/-- The part of p through and including degree i. -/
noncomputable def trunc (p : ℂ[X]) (i : ℕ) : ℂ[X] :=
  ∑ k ∈ range (i+1), C (p.coeff k)*X^k

theorem trunc_coeff (p : ℂ[X]) (i j : ℕ) :
    (trunc p i).coeff j = if j≤ i then p.coeff j else 0 := by
  simp [trunc,finset_sum_coeff,coeff_C_mul,coeff_X_pow,mul_ite,Nat.lt_succ_iff]

theorem trunc_eq {p q : ℂ[X]} {i : ℕ} (hd : q.natDegree≤ i)
    (hl : ∀ j, j≤ i → p.coeff j=q.coeff j) : trunc p i = q := by
  ext j
  rw [trunc_coeff]
  split
  · exact hl _ (by omega)
  · exact (coeff_eq_zero_of_natDegree_lt (by omega)).symm

theorem trunc_linear (p : ℂ[X]) (z : ℂ) (i : ℕ) :
    trunc ((X-C z)*p) i = (X-C z)*trunc p i - C (p.coeff i)*X^(i+1) := by
  ext j
  cases j with
  | zero => simp [trunc_coeff,sub_mul, coeff_X_pow]
  | succ j =>
    simp only [trunc_coeff,sub_mul,coeff_sub,coeff_X_mul,coeff_C_mul,coeff_X_pow]
    rcases lt_trichotomy j i with hh | rfl | hh
    · simp [show j+1≤ i by omega, hh.le, hh.ne]
    · simp
    · simp [show ¬j≤ i by omega,show ¬j+1≤ i by omega, hh.ne']

theorem eval_trunc_linear (p : ℂ[X]) (z : ℂ) (i : ℕ) :
    (trunc ((X-C z)*p) i).eval z = -p.coeff i*z^(i+1) := by
  simp [trunc_linear]

theorem double_coeff (r : ℂ[X]) (i : ℕ) :
    let t := trunc ((X-1)*((X-1)*r)) i
    ((X-1)*r).coeff i = -t.eval 1 ∧
      r.coeff i = ((i:ℂ)+1)*t.eval 1 - t.derivative.eval 1 := by
  let t := trunc ((X-1)*((X-1)*r)) i
  let v := (X-1)*r
  have ht : t=(X-1)*trunc v i-C (v.coeff i)*X^(i+1) := by
    simpa [t,v] using trunc_linear ((X-1)*r) 1 i
  have hv : (trunc v i).eval 1 = -(r.coeff i) := by
    simpa [v] using eval_trunc_linear r 1 i
  have ht₀ : t.eval 1 = -v.coeff i := by simp [ht]
  change v.coeff i = -t.eval 1 ∧ r.coeff i = ((i:ℂ)+1)*t.eval 1 - t.derivative.eval 1
  constructor
  · rw [ht₀,neg_neg]
  · rw [ht₀, ht]
    simp [derivative_mul,hv]
    ring

/-- Coefficient extraction after the partial fraction decomposition. The
    numerator is the full denominator times g. Ordinary polynomial truncation
    suffices, even when g has very large degree. -/
theorem coefficient_decomposition (s : Finset ℂ) (hs : (1:ℂ)∉s) (hzero : (0:ℂ)∉s)
    (g : ℂ[X]) (i : ℕ) :
    let D := linearProduct s
    let T := trunc ((X-1)*((X-1)*(D*g))) i
    g.coeff i = (D.eval 1)⁻¹*(((i:ℂ)+1)*T.eval 1-T.derivative.eval 1) +
      (-(D.derivative.eval 1)*(D.eval 1)⁻¹^2)*(-T.eval 1) +
      ∑ z ∈ s, (-poleCoeff s z/z)*T.eval z*(z⁻¹)^i := by
  classical
  let D := linearProduct s
  let a := (D.eval 1)⁻¹
  let b := -(D.derivative.eval 1)*(D.eval 1)⁻¹^2
  let p := D*g
  let v := (X-1)*p
  let N := (X-1)*v
  let T := trunc N i
  let R (z : ℂ) := (X-1)^2*linearProduct (s.erase z)*g
  have hN (z : ℂ) (hz : z∈s) : N = (X-C z)*R z := by
    have hh : (X-C z)*linearProduct (s.erase z) = D := s.mul_prod_erase (fun y => X-C y) hz
    dsimp only [N,v,p,R]
    rw [←hh]; ring
  have hsimp (z : ℂ) (hz : z∈s) :
      poleCoeff s z*(R z).coeff i = (-poleCoeff s z/z)*T.eval z*(z⁻¹)^i := by
    have hnz : z≠0 := fun he => hzero (he ▸ hz)
    have ht : T.eval z = -(R z).coeff i*z^(i+1) := by
      dsimp only [T]
      rw [hN z hz, eval_trunc_linear]
    rw [ht, pow_succ, inv_pow]
    field_simp [hnz]
  have hp : g = C a * p + C b * v + ∑ z ∈ s, C (poleCoeff s z)*R z := by
    have hh : C a*D+(X-1)*(C b*D+(X-1)*simpleNumerator s)=1 := double_and_simple s hs
    calc
      _ = (C a*D+(X-1)*(C b*D+(X-1)*simpleNumerator s))*g := by rw [hh,one_mul]
      _ = C a*p + C b*v + ((X-1)^2*g)*simpleNumerator s := by dsimp [p,v]; ring
      _ = _ := by
        rw [simpleNumerator,Finset.mul_sum]
        congr 1
        apply sum_congr rfl
        intro z _
        dsimp [R]
        ring
  obtain ⟨h₁,h₂⟩ := double_coeff p i
  change v.coeff i = -T.eval 1 at h₁
  change p.coeff i = ((i:ℂ)+1)*T.eval 1-T.derivative.eval 1 at h₂
  calc
    _ = (C a * p + C b * v + ∑ z ∈ s, C (poleCoeff s z)*R z).coeff i := congrArg (fun f : ℂ[X] => f.coeff i) hp
    _ = _ := by
      simp only [coeff_add,coeff_C_mul,finset_sum_coeff,h₁,h₂]
      congr 1
      apply sum_congr rfl
      exact hsimp

#print axioms coefficient_decomposition
end QFib.Roots
