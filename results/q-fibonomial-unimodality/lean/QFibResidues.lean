import QFibError
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Finset.Max

open Finset Complex
open scoped BigOperators Real
namespace QFib.Roots

noncomputable def baseRoot (e : ℕ) := Complex.exp (2*Real.pi*Complex.I/e)

def distance (e t : ℕ) := min (t%e) (e-t%e)

theorem chord (x : ℝ) :
    ‖1-Complex.exp ((2*(x:ℂ))*I)‖ = 2*|Real.sin x| := by
  have ht := congrArg norm (Complex.two_sin (x:ℂ))
  rw [← Complex.ofReal_sin,norm_mul,Complex.norm_real,Real.norm_eq_abs] at ht
  norm_num only [Complex.norm_two, norm_mul, Complex.norm_I, mul_one] at ht
  calc
    _ = ‖Complex.exp ((x:ℂ)*I) *
          (Complex.exp (-(x:ℂ)*I)-Complex.exp ((x:ℂ)*I))‖ := by
        congr 1
        rw [mul_sub,←Complex.exp_add,←Complex.exp_add]
        ring_nf
        simp
        ring
    _ = _ := by rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]; exact ht.symm

theorem chord_half {e t : ℕ} (he : 0<e) (ht : 2*t≤e) :
    4*(t:ℝ)/e ≤ ‖1-(baseRoot e)^t‖ := by
  let x := Real.pi*t/e
  have ep : (0:ℝ)<e := by exact_mod_cast he
  have x₀ : 0≤x := by dsimp [x]; positivity
  have x₁ : x≤Real.pi/2 := by
    dsimp only [x]
    apply (div_le_iff₀ ep).mpr
    have ht' : 2*(t:ℝ)≤e := by exact_mod_cast ht
    nlinarith [mul_nonneg Real.pi_pos.le (sub_nonneg.mpr ht')]
  have hx : (baseRoot e)^t = Complex.exp ((2*(x:ℂ))*I) := by
    rw [baseRoot,←Complex.exp_nat_mul]
    congr 1
    dsimp [x]
    push_cast
    ring
  rw [hx,chord,abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi x₀ (by linarith))]
  have hb := Real.mul_le_sin x₀ x₁
  calc
    _ = 2*((2/Real.pi)*x) := by dsimp [x]; field_simp [Real.pi_ne_zero]; ring
    _ ≤ _ := by linarith

theorem chord_distance {e : ℕ} (he : 0<e) (j : ℕ) :
    4*(distance e j:ℝ)/e ≤ ‖1-(baseRoot e)^j‖ := by
  let z := baseRoot e
  have hpr : IsPrimitiveRoot z e := Complex.isPrimitiveRoot_exp e he.ne'
  have hpow := hpr.pow_eq_one
  have hz : ‖z‖=1 := unit_norm he hpow
  have hmod : z^(j%e)=z^j := by simpa [←hpr.eq_orderOf] using pow_mod_orderOf z j
  let l := j%e
  have hl : l<e := Nat.mod_lt _ he
  change 4*((min l (e-l):ℕ):ℝ)/e ≤ ‖1-z^j‖
  rw [← hmod]
  change 4*((min l (e-l):ℕ):ℝ)/e ≤ ‖1-z^l‖
  by_cases h : l≤e-l
  · rw [min_eq_left h]
    exact chord_half he (by omega)
  · rw [min_eq_right (by omega : e-l≤l)]
    have hnz : z≠0 := by intro h; simp [h] at hz
    have hi : z^(e-l)=(z^l)⁻¹ := by
      apply mul_left_cancel₀ (pow_ne_zero l hnz)
      rw [←pow_add, show l+(e-l)=e by omega, hpow, mul_inv_cancel₀ (pow_ne_zero l hnz)]
    rw [← norm_inverse (x:=z^l) (by simp [hz]), ←hi]
    exact chord_half he (by omega)

theorem distance_pos {e b x : ℕ} (he : 0<e) (cop : b.Coprime e) (h : ¬e∣x) :
    0<distance e (b*x) := by
  have h₁ : (b*x)%e ≠ 0 := by
    intro hmod
    exact h (cop.symm.dvd_of_dvd_mul_left (Nat.dvd_of_mod_eq_zero hmod))
  have h₂ := Nat.mod_lt (b*x) he
  unfold distance
  omega

theorem distance_injective {e b x y : ℕ} (he : 0<e) (cop : b.Coprime e)
    (hx : 0<x) (hy : 0<y) (hx' : 2*x<e) (hy' : 2*y<e)
    (h : distance e (b*x) = distance e (b*y)) : x=y := by
  have ha := Nat.mod_lt (b*x) he
  have hb := Nat.mod_lt (b*y) he
  unfold distance at h
  have hsign : (b*x)%e=(b*y)%e ∨ (b*x)%e+(b*y)%e=e := by omega
  rcases hsign with hEq|hSum
  · have hm : b*x ≡ b*y [MOD e] := hEq
    have ze := hm.cancel_left_of_coprime cop.symm.gcd_eq_one
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt (by omega : x<e),
      Nat.mod_eq_of_lt (by omega : y<e)] using ze
  · have hmod : b*(x+y)%e=0 := by rw [Nat.mul_add,Nat.add_mod,hSum,Nat.mod_self]
    have he' : e∣x+y := cop.symm.dvd_of_dvd_mul_left (Nat.dvd_of_mod_eq_zero hmod)
    have := Nat.le_of_dvd (by omega : 0<x+y) he'
    omega

theorem factorial_le_distinct_product (s : Finset ℕ) (h : ∀ j∈s, 0<j) :
    s.card.factorial ≤ ∏ j ∈ s, j := by
  induction s using Finset.induction_on_max with
  | h0 => simp
  | step a s hs ih =>
    have ha : a∉s := fun hh => lt_irrefl a (hs a hh)
    have hp : 0<a := h _ (mem_insert_self _ _)
    have sub : s ⊆ Ico 1 a := by
      intro j hj
      exact mem_Ico.mpr ⟨h j (mem_insert_of_mem hj), hs j hj⟩
    have card := Finset.card_le_card sub
    rw [Nat.card_Ico] at card
    rw [card_insert_of_notMem ha, Nat.factorial_succ, prod_insert ha]
    exact Nat.mul_le_mul (by omega) (ih (fun j hj => h _ (mem_insert_of_mem hj)))

#print axioms chord_distance
#print axioms distance_injective
end QFib.Roots
