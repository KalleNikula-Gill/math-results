import QFibMidpoint
import QFibSurvivors

open Polynomial Finset
open scoped Polynomial BigOperators
namespace QFib.Roots

/-- Each factor is normalized by its length before specializing. -/
noncomputable def scaled (l : ℕ) : ℂ[X] := C (l:ℂ)⁻¹*(1-X^l)
noncomputable def normPoly (p n : ℕ) : ℂ[X] :=
  C ((complexPoly p n).eval 1)⁻¹*complexPoly p n

theorem scaled_step (p n : ℕ) :
    scaled (Nat.fib (p+1))*normPoly (p+1) n =
    scaled (Nat.fib (n+p+1))*normPoly p n := by
  have h := congrArg (Polynomial.map (Int.castRingHom ℂ)) (poly_step p n)
  simp only [Polynomial.map_mul,Polynomial.map_sub,Polynomial.map_pow,
    Polynomial.map_one,Polynomial.map_X] at h
  rw [Nat.add_comm p n] at h
  have h₁ := congrArg (fun f : ℤ[X] => f.eval 1) (poly_step_interval p n)
  simp only [eval_mul,eval_interval] at h₁
  have hc : (Nat.fib (p+1):ℂ)*(complexPoly (p+1) n).eval 1 =
      (Nat.fib (n+p+1):ℂ)*(complexPoly p n).eval 1 := by
    rw [complex_one,complex_one]; exact_mod_cast (by simpa only [Nat.add_comm p n] using h₁ :
      (Nat.fib (p+1):ℤ)*(poly (p+1) n).eval 1=(Nat.fib (n+p+1):ℤ)*(poly p n).eval 1)
  have combine (l : ℕ) (Q : ℂ[X]) : scaled l*(C (Q.eval 1)⁻¹*Q) =
      C (((l:ℂ)*Q.eval 1)⁻¹)*((1-X^l)*Q) := by
    simp only [scaled,mul_inv_rev,Polynomial.C_mul]; ring
  rw [normPoly,normPoly,combine,combine,hc]
  exact congrArg (fun f : ℂ[X] => C (((Nat.fib (n+p+1):ℂ)*(complexPoly p n).eval 1)⁻¹)*f) h

theorem normalized_relation (p n : ℕ) :
    normPoly p n*(∏ j ∈ range p, scaled (Nat.fib (0+j+1))) =
      ∏ j ∈ range p, scaled (Nat.fib (n+j+1)) := by
  induction p with
  | zero => simp [normPoly,complexPoly,poly]
  | succ p ih =>
    rw [prod_range_succ, prod_range_succ,zero_add]
    calc
      _ = (scaled (Nat.fib (p+1))*normPoly (p+1) n)*
            (∏ j ∈ range p, scaled (Nat.fib (0+j+1))) := by ring
      _ = _ := by rw [scaled_step,mul_assoc,ih,mul_comm]

/-- Remove exactly one common vanishing factor at each divisible length.
    The resulting factor takes value 1 at a primitive root. -/
noncomputable def regular (e l : ℕ) : ℂ[X] :=
    if e∣l then C ((l:ℂ)⁻¹*e) * ∑ j ∈ range (l/e), (X^e)^j else scaled l

theorem factor_one {e l : ℕ} (he : 0<e) (h : e∣l) :
    scaled l = scaled e*regular e l := by
  have he' : (e:ℂ)≠0 := by exact_mod_cast he.ne'
  have hh := geom_sum_mul_neg (X^e:ℂ[X]) (l/e)
  rw [← pow_mul,Nat.mul_div_cancel' h] at hh
  simp only [scaled,regular,if_pos h, Polynomial.C_mul]
  rw [← hh]
  have hc : C (e:ℂ)⁻¹*C (e:ℂ) = (1:ℂ[X]) := by rw [←Polynomial.C_mul,inv_mul_cancel₀ he',map_one]
  linear_combination -(C (l:ℂ)⁻¹*(1-X^e)*(∑ j ∈ range (l/e), (X^e)^j))*hc

noncomputable def regProduct (e n p : ℕ) := ∏ j ∈ range p, regular e (Nat.fib (n+j+1))

theorem factor_product (e n p : ℕ) (he : 0<e) :
    (∏ j ∈ range p, scaled (Nat.fib (n+j+1))) =
      scaled e^(p-(live e n p).card)*regProduct e n p := by
  induction p with
  | zero => simp [live,regProduct]
  | succ p ih =>
    have hl : (live e n p).card≤p := (card_le_card (filter_subset _ _)).trans_eq (card_range p)
    rw [prod_range_succ,ih,live_succ]
    have hr : regProduct e n (p+1)=regProduct e n p*regular e (Nat.fib (n+p+1)) := prod_range_succ ..
    rw [hr]
    by_cases h : e∣Nat.fib (n+p+1)
    · rw [if_pos h,show p+1-(live e n p).card=p-(live e n p).card+1 by omega,pow_succ,
        factor_one he h]
      ring
    · rw [if_neg h,card_insert_of_notMem (live_last e n p),Nat.add_sub_add_right]
      simp only [regular,if_neg h]
      ring

theorem eval_regular {e l : ℕ} {z : ℂ} (_he : 0<e) (hl : 0<l) (hz : z^e=1) :
    (regular e l).eval z = if e∣l then 1 else (1-z^l)/l := by
  by_cases h : e∣l
  · have hh := Nat.mul_div_cancel' h
    have hl' : (l:ℂ)≠0 := by exact_mod_cast hl.ne'
    simp only [regular,if_pos h,eval_mul,eval_C,eval_finset_sum,eval_pow,eval_X,hz,
      one_pow,sum_const,card_range,nsmul_eq_mul,mul_one]
    have hcast : (e:ℂ)*((l/e:ℕ):ℂ)=l := by exact_mod_cast hh
    field_simp [hl']
    exact hcast
  · simp [regular,scaled,h,div_eq_inv_mul]

theorem reg_nonzero {e : ℕ} {z : ℂ} (he : 0<e) (hz : IsPrimitiveRoot z e) (n p : ℕ) :
    (regProduct e n p).eval z ≠ 0 := by
  rw [regProduct,eval_prod]
  apply prod_ne_zero_iff.mpr
  intro j _
  have hf : 0<Nat.fib (n+j+1) := by simp
  rw [eval_regular he hf hz.pow_eq_one]
  split
  · exact one_ne_zero
  · rename_i h
    exact div_ne_zero (sub_ne_zero.mpr (Ne.symm (mt (hz.pow_eq_one_iff_dvd _).mp h)))
      (by exact_mod_cast hf.ne')

theorem reg_norm {e : ℕ} {z : ℂ} (he : 0<e) (hz : z^e=1) (n p : ℕ) :
    ‖(regProduct e n p).eval z‖ =
    ∏ j ∈ live e n p, ‖1-z^Nat.fib (n+j+1)‖/(Nat.fib (n+j+1):ℝ) := by
  rw [regProduct,eval_prod,norm_prod,live,Finset.prod_filter]
  apply prod_congr rfl
  intro j _
  rw [eval_regular he (by simp) hz]
  by_cases h : e∣Nat.fib (n+j+1) <;> simp [h]

/-- Exact normalized specialization. Any excess numerator zero forces value zero. -/
theorem specialization {e r : ℕ} {z : ℂ} (ep : 0<e) (hz : IsPrimitiveRoot z e)
    (rank : ∀ j, e∣Nat.fib j ↔ r∣j) (n p : ℕ) :
    (normPoly p n).eval z=0 ∨
    ((live e 0 p).card=(live e n p).card ∧
      ‖(normPoly p n).eval z‖*‖(regProduct e 0 p).eval z‖=‖(regProduct e n p).eval z‖) := by
  let a := p-(live e 0 p).card
  let b := p-(live e n p).card
  have hle := live_count_le e n p r rank
  have hab : a≤b := Nat.sub_le_sub_left hle _
  have hr := normalized_relation p n
  rw [factor_product e 0 p ep,factor_product e n p ep] at hr
  change normPoly p n*(scaled e^a*regProduct e 0 p)=scaled e^b*regProduct e n p at hr
  have hn : scaled e≠0 := by
    apply mul_ne_zero (Polynomial.C_ne_zero.mpr (inv_ne_zero (by exact_mod_cast ep.ne')))
    intro h
    have h0 := congrArg (fun q:ℂ[X] => q.coeff 0) h
    simp [coeff_X_pow,Ne.symm ep.ne'] at h0
  have hc : normPoly p n*regProduct e 0 p=scaled e^(b-a)*regProduct e n p := by
    apply mul_left_cancel₀ (a:=scaled e^a) (pow_ne_zero _ hn)
    calc
      _ = normPoly p n*(scaled e^a*regProduct e 0 p) := by ring
      _ = _ := hr.trans (by rw [←mul_assoc,←pow_add, Nat.add_sub_of_le hab])
  have hv := congrArg (fun q:ℂ[X] => q.eval z) hc
  simp only [eval_mul,eval_pow] at hv
  have hz₀ : (scaled e).eval z=0 := by simp [scaled,hz.pow_eq_one]
  by_cases heq : (live e 0 p).card=(live e n p).card
  · right
    refine ⟨heq,?_⟩
    have hba : b-a=0 := by simp [a,b,heq]
    rw [hba,pow_zero,one_mul] at hv
    simpa only [norm_mul] using congrArg norm hv
  · left
    have bound : (live e 0 p).card≤p := (card_le_card (filter_subset _ _)).trans_eq (card_range p)
    have hba : b-a≠0 := by dsimp [a,b]; omega
    rw [hz₀,zero_pow hba,zero_mul] at hv
    exact (mul_eq_zero.mp hv).resolve_right (reg_nonzero ep hz _ _)

#print axioms specialization
end QFib.Roots
