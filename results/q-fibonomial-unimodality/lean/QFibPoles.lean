import QFibRoots
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic.GCongr

open Polynomial Finset
open scoped Polynomial BigOperators
namespace QFib.Roots

theorem linearProduct_eval (s : Finset ℂ) (x : ℂ) :
    (linearProduct s).eval x = ∏ z ∈ s, (x-z) := by
  simp [linearProduct,eval_prod]

theorem eval_member {s : Finset ℂ} {x : ℂ} (hx : x∈s) : (linearProduct s).eval x = 0 := by
  rw [linearProduct_eval]
  exact prod_eq_zero hx (sub_self _)

theorem eval_nonmember {s : Finset ℂ} {x : ℂ} (hx : x∉s) : (linearProduct s).eval x ≠ 0 := by
  rw [linearProduct_eval]
  exact prod_ne_zero_iff.mpr (fun z hz => sub_ne_zero.mpr (fun he => hx (he ▸ hz)))

theorem linearProduct_deg (s : Finset ℂ) : (linearProduct s).natDegree = s.card :=
  natDegree_multiset_prod_X_sub_C_eq_card s.val

theorem linearProduct_dvd (s : Finset ℂ) (p : ℂ[X]) (h : ∀ z∈s, p.eval z=0) :
    linearProduct s ∣ p := by
  classical
  induction s using Finset.induction_on generalizing p with
  | empty => simp [linearProduct]
  | @insert z s hz ih =>
    obtain ⟨q,hq⟩ := dvd_iff_isRoot.mpr (h z (mem_insert_self _ _))
    have hh : ∀ y∈s, q.eval y=0 := by
      intro y hy
      have hzero := h y (mem_insert_of_mem hy)
      rw [hq,eval_mul,eval_sub,eval_X,eval_C] at hzero
      exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr (fun he => hz (he ▸ hy)))
    obtain ⟨f,hf⟩ := ih q hh
    use f
    rw [hq,hf]
    simp [linearProduct,prod_insert,hz,mul_assoc]

private theorem degree_zeros {s : Finset ℂ} {p : ℂ[X]} (hs : (1:ℂ)∉s) (h1 : p.eval 1=0)
    (h2 : p.derivative.eval 1=0) (h : ∀ z∈s, p.eval z=0)
    (hd : p.natDegree≤s.card+1) : p=0 := by
  obtain ⟨q,hq⟩ := dvd_iff_isRoot.mpr h1
  have hq1 : q.eval 1=0 := by simpa [hq,derivative_mul] using h2
  obtain ⟨r,hr⟩ := dvd_iff_isRoot.mpr hq1
  have hroots : ∀ z∈s, r.eval z=0 := by
    intro z hz
    have hne : z-1≠0 := sub_ne_zero.mpr (fun he => hs (he ▸ hz))
    have hh := h z hz
    simpa [hq,hr,hne] using hh
  obtain ⟨f,hf⟩ := linearProduct_dvd s r hroots
  have hdvd : (X-C (1:ℂ))^2*linearProduct s ∣ p := by
    use f
    rw [hq,hr,hf]; ring
  by_contra hne
  have hlarge := natDegree_le_of_dvd hdvd hne
  have hp0 : linearProduct s≠0 := fun he => eval_nonmember hs (by simp [he])
  rw [natDegree_mul (pow_ne_zero _ (X_sub_C_ne_zero (1:ℂ))) hp0, natDegree_pow,
    natDegree_X_sub_C, linearProduct_deg] at hlarge
  omega

/-- Residue in the basis 1/(X-z). -/
noncomputable def poleCoeff (s : Finset ℂ) (z : ℂ) : ℂ :=
  ((z-1)^2*(linearProduct (s.erase z)).eval z)⁻¹

noncomputable def simpleNumerator (s : Finset ℂ) : ℂ[X] :=
  ∑ z ∈ s, C (poleCoeff s z)*linearProduct (s.erase z)

theorem eval_simple {s : Finset ℂ} {z : ℂ} (hz : z∈s) :
    (simpleNumerator s).eval z = poleCoeff s z*(linearProduct (s.erase z)).eval z := by
  classical
  rw [simpleNumerator,eval_finset_sum,Finset.sum_eq_single z]
  · simp
  · intro y hy hyz
    have hh : z∈s.erase y := mem_erase.mpr ⟨hyz.symm,hz⟩
    simp [eval_member hh]
  · exact fun h => (h hz).elim

theorem simple_deg (s : Finset ℂ) : (simpleNumerator s).natDegree ≤ s.card-1 := by
  classical
  apply natDegree_sum_le_of_forall_le
  intro z hz
  exact (natDegree_C_mul_le _ _).trans (by simp [linearProduct_deg,card_erase_of_mem hz])

/-- A polynomial identity for the partial fractions of
    1/((X-1)^2 P), where P has distinct roots away from 1. -/
theorem double_and_simple (s : Finset ℂ) (hs : (1:ℂ)∉s) :
    let p := linearProduct s
    let a := (p.eval 1)⁻¹
    let b := -(p.derivative.eval 1)*(p.eval 1)⁻¹^2
    C a*p + (X-1)*(C b*p+(X-1)*simpleNumerator s) = 1 := by
  classical
  let p := linearProduct s
  let a := (p.eval 1)⁻¹
  let b := -(p.derivative.eval 1)*(p.eval 1)⁻¹^2
  let f := C a*p + (X-1)*(C b*p+(X-1)*simpleNumerator s) - 1
  change C a*p + (X-1)*(C b*p+(X-1)*simpleNumerator s) = 1
  apply sub_eq_zero.mp
  change f=0
  have hpn : p.eval 1≠0 := eval_nonmember hs
  apply degree_zeros hs
  · simp [f,a,hpn]
  · simp [f,derivative_mul,a,b]; field_simp [hpn]; ring
  · intro z hz
    have zp : z-1≠0 := sub_ne_zero.mpr (fun he => hs (he ▸ hz))
    have op : (linearProduct (s.erase z)).eval z ≠ 0 := eval_nonmember (notMem_erase _ _)
    simp only [f,eval_sub,eval_one,eval_add,eval_mul,eval_C,eval_X,show p.eval z=0 from eval_member hz,
      mul_zero,zero_add,eval_simple hz,poleCoeff]
    field_simp [zp,op]
    ring
  · by_cases empty : s=∅
    · subst s; simp [f,p,simpleNumerator,linearProduct,a,b]
    have hnum : 0<s.card := card_pos.mpr (nonempty_iff_ne_empty.mpr empty)
    have hdeg : p.natDegree=s.card := linearProduct_deg _
    have hx : (X-1 : ℂ[X]).natDegree=1 := by simpa using natDegree_X_sub_C (1:ℂ)
    have hS := simple_deg s
    have h₁ := natDegree_C_mul_le a p
    have h₂ := natDegree_C_mul_le b p
    have h₃ := natDegree_mul_le (p:=(X-1 : ℂ[X])) (q:=simpleNumerator s)
    have h₄ := natDegree_add_le (C b*p) ((X-1)*simpleNumerator s)
    have h₅ := natDegree_mul_le (p:=(X-1 : ℂ[X])) (q:=C b*p+(X-1)*simpleNumerator s)
    have h₆ := natDegree_add_le (C a*p) ((X-1)*(C b*p+(X-1)*simpleNumerator s))
    have h₇ := natDegree_sub_le (C a*p+(X-1)*(C b*p+(X-1)*simpleNumerator s)) 1
    change f.natDegree ≤ _ at h₇
    rw [natDegree_one] at h₇
    omega

#print axioms double_and_simple
end QFib.Roots
