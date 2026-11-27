import QFibError
import QFibPoles

open Polynomial Finset
open scoped Polynomial BigOperators
namespace QFib.Roots

noncomputable def totalRoots (u v w : ℕ) := rootsExceptOne u ∪ rootsExceptOne v ∪ rootsExceptOne w

theorem roots_disjoint {u v : ℕ} (hu : 0<u) (hv : 0<v) (hc : u.Coprime v) :
    Disjoint (rootsExceptOne u) (rootsExceptOne v) := by
  rw [disjoint_left]
  intro z hz₁ hz₂
  have a := (mem_except hu).mp hz₁
  have b := (mem_except hv).mp hz₂
  have h := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one a.2) (orderOf_dvd_of_pow_eq_one b.2)
  rw [hc.gcd_eq_one] at h
  exact a.1 (orderOf_eq_one_iff.mp (Nat.dvd_one.mp h))

theorem totalProduct {u v w : ℕ} (hu : 0<u) (hv : 0<v) (hw : 0<w)
    (huv : u.Coprime v) (hvw : v.Coprime w) (hwu : w.Coprime u) :
    linearProduct (totalRoots u v w) = geom u * geom v * geom w := by
  classical
  have hab := roots_disjoint hu hv huv
  have hac := roots_disjoint hu hw hwu.symm
  have hbc := roots_disjoint hv hw hvw
  simp only [totalRoots,linearProduct,prod_union (Finset.disjoint_union_left.mpr ⟨hac,hbc⟩),prod_union hab]
  exact congrArg₂ (·*·) (congrArg₂ (·*·) (geom_factor u hu) (geom_factor v hv)) (geom_factor w hw)

theorem total_values {u v w : ℕ} (hu : 0<u) (hv : 0<v) (hw : 0<w)
    (huv : u.Coprime v) (hvw : v.Coprime w) (hwu : w.Coprime u) :
    let p := linearProduct (totalRoots u v w)
    p.eval 1=(u:ℂ)*v*w ∧
      2*p.derivative.eval 1=((u:ℂ)*v*w)*(u+v+w-3) := by
  dsimp only
  rw [totalProduct hu hv hw huv hvw hwu]
  obtain ⟨h₀,h₁,-⟩ := geom_values u
  obtain ⟨i₀,i₁,-⟩ := geom_values v
  obtain ⟨j₀,j₁,-⟩ := geom_values w
  simp only [derivative_mul,eval_add,eval_mul,h₀,i₀,j₀,true_and]
  linear_combination (v:ℂ)*w*h₁+(u:ℂ)*w*i₁+(u:ℂ)*v*j₁

theorem eval_geom_relation (u : ℕ) (z : ℂ) : (z-1)*(geom u).eval z = z^u-1 := by
  have h := congrArg (fun p : ℂ[X] => p.eval z) (geom_sum_mul (X : ℂ[X]) u)
  simpa only [geom,eval_mul,eval_sub,eval_X,eval_one,eval_pow,mul_comm] using h

theorem geom_derivative_relation (u : ℕ) (z : ℂ) :
    (z-1)*(geom u).derivative.eval z + (geom u).eval z = (u:ℂ)*z^(u-1) := by
  have h := congrArg (fun p : ℂ[X] => p.derivative.eval z) (geom_sum_mul (X : ℂ[X]) u)
  simpa only [geom,one_mul,derivative_mul,derivative_sub,derivative_X,derivative_one,
    derivative_X_pow,sub_zero,mul_one,eval_add,eval_mul,eval_C,eval_sub,eval_X,
    eval_one,eval_pow,mul_comm] using h

theorem remainder_eval {s : Finset ℂ} {z : ℂ} (hz : z∈s) :
    (linearProduct (s.erase z)).eval z = (linearProduct s).derivative.eval z := by
  classical
  have h : (X-C z)*linearProduct (s.erase z) = linearProduct s :=
    s.mul_prod_erase (fun y => X-C y) hz
  rw [←h]
  simp [derivative_mul]

/-- Local simple residue after converting 1/(X-z) to 1/(1-X/z).
    The factorization hypothesis allows all cyclic permutations. -/
theorem simple_pole_value {s : Finset ℂ} {u v w : ℕ} (hu : 0<u)
    (hf : linearProduct s = geom u*geom v*geom w)
    {z : ℂ} (hm : z∈s) (hz : z∈rootsExceptOne u) (hV : z^v≠1) (hW : z^w≠1) :
    -poleCoeff s z/z = (1-z)/((u:ℂ)*(1-z^v)*(1-z^w)) := by
  have hmem := (mem_except hu).mp hz
  have hzn : z≠0 := by intro h; simp [h, hu.ne'] at hmem
  have hprev : z^(u-1)*z=1 := by rw [← pow_succ, Nat.sub_add_cancel (by omega : 1≤u),hmem.2]
  have hG : (geom u).eval z=0 := by rw [← geom_factor u hu]; exact eval_member hz
  have hder := geom_derivative_relation u z
  rw [hG,add_zero] at hder
  have hv := eval_geom_relation v z
  have hw := eval_geom_relation w z
  have hz1 : z-1≠0 := sub_ne_zero.mpr hmem.1
  have hv' : (geom v).eval z≠0 := by intro he; rw [he,mul_zero] at hv; exact hV (sub_eq_zero.mp hv.symm)
  have hw' : (geom w).eval z≠0 := by intro he; rw [he,mul_zero] at hw; exact hW (sub_eq_zero.mp hw.symm)
  have hn : (u:ℂ)≠0 := by exact_mod_cast hu.ne'
  have hd' : (geom u).derivative.eval z≠0 := by
    intro he; rw [he,mul_zero] at hder
    exact mul_ne_zero hn (pow_ne_zero _ hzn) hder.symm
  rw [poleCoeff,remainder_eval hm,hf]
  simp only [derivative_mul,eval_add,eval_mul,hG,zero_mul,add_zero]
  have hu' : (geom u).derivative.eval z*(z-1)*z=(u:ℂ) := by
    calc
      _ = ((z-1)*(geom u).derivative.eval z)*z := by ring
      _ = _ := by rw [hder,mul_assoc,hprev,mul_one]
  have hhV : 1-z^v = -(z-1)*(geom v).eval z := by linear_combination hv
  have hhW : 1-z^w = -(z-1)*(geom w).eval z := by linear_combination hw
  rw [hhV,hhW,←hu']
  field_simp [hz1,hzn,hv',hw',hd']
  ring

#print axioms simple_pole_value
end QFib.Roots
