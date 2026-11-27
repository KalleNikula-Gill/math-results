import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

open Polynomial Finset
open scoped BigOperators Polynomial ComplexConjugate
namespace QFib.Roots

noncomputable def rootsExceptOne (u : ℕ) : Finset ℂ := (nthRootsFinset u (1:ℂ)).erase 1
noncomputable def geom (u : ℕ) : ℂ[X] := ∑ j ∈ range u, X^j
noncomputable def linearProduct (s : Finset ℂ) : ℂ[X] := ∏ z ∈ s, (X-C z)

theorem geom_factor (u : ℕ) (hu : 0<u) : linearProduct (rootsExceptOne u) = geom u := by
  classical
  let s := nthRootsFinset u (1:ℂ)
  have hz := Complex.isPrimitiveRoot_exp u hu.ne'
  have hfull : (∏ z ∈ s, (X-C z)) = X^u-C 1 := by
    change ((nthRoots u (1:ℂ)).dedup.map (fun z => X-C z)).prod = _
    rw [Multiset.dedup_eq_self.mpr hz.nthRoots_one_nodup]
    apply prod_multiset_X_sub_C_of_monic_of_roots_card_eq (monic_X_pow_sub_C _ hu.ne')
    rw [natDegree_X_pow_sub_C]
    exact hz.card_nthRoots_one
  have h1 : (1:ℂ) ∈ s := (mem_nthRootsFinset hu 1).mpr (one_pow _)
  have he := s.mul_prod_erase (fun z => X-C z) h1
  rw [hfull, C_1] at he
  change (X-1)*linearProduct (rootsExceptOne u)=X^u-1 at he
  apply mul_left_cancel₀ (a:=X-1) (by simpa using X_sub_C_ne_zero (1:ℂ))
  rw [he, mul_comm, geom]
  exact (geom_sum_mul X u).symm

theorem geom_values (u : ℕ) :
    (geom u).eval 1 = u ∧
    2*(geom u).derivative.eval 1 = (u:ℂ)*(u-1) ∧
    3*(geom u).derivative.derivative.eval 1 = (u:ℂ)*(u-1)*(u-2) := by
  induction u with
  | zero => simp [geom]
  | succ u ih =>
    have h : geom (u+1)=geom u+X^u := by simp [geom,sum_range_succ]
    rw [h]
    simp only [eval_add, eval_pow, eval_X, one_pow, derivative_add, derivative_X_pow,
      eval_mul, eval_C, mul_one, derivative_mul, derivative_C, zero_mul, zero_add, Nat.cast_succ]
    rcases ih with ⟨h₀,h₁,h₂⟩
    refine ⟨by rw [h₀], by linear_combination h₁, ?_⟩
    cases u with
    | zero => simp [geom]
    | succ u =>
      simp only [Nat.succ_sub_one, Nat.cast_succ] at h₂ ⊢
      linear_combination h₂

private theorem product_derivatives (s : Finset ℂ) (x : ℂ) (hx : x ∉ s) :
    (linearProduct s).derivative.eval x =
      (linearProduct s).eval x * ∑ z ∈ s, (x-z)⁻¹ ∧
    (linearProduct s).derivative.derivative.eval x =
      (linearProduct s).eval x *
        ((∑ z ∈ s, (x-z)⁻¹)^2 - ∑ z ∈ s, ((x-z)⁻¹)^2) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [linearProduct]
  | @insert z s hz ih =>
    have hxs : x∉s := fun hh => hx (mem_insert_of_mem hh)
    have hxz : x-z≠0 := sub_ne_zero.mpr (fun he => hx (he ▸ mem_insert_self z s))
    obtain ⟨h₁,h₂⟩ := ih hxs
    rw [show linearProduct (insert z s) = (X-C z)*linearProduct s by
      simp [linearProduct,prod_insert,hz]]
    simp only [derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul,
      derivative_add, eval_add, eval_mul, eval_sub, eval_X, eval_C,
      sum_insert hz, h₁, h₂]
    constructor <;> field_simp [hxz]
    all_goals ring

theorem unit_norm {z : ℂ} {u : ℕ} (hu : 0<u) (hz : z^u=1) : ‖z‖=1 := by
  have hh := congrArg norm hz
  simp only [norm_pow, norm_one] at hh
  exact (pow_left_inj₀ (norm_nonneg _) zero_le_one hu.ne').mp (by simpa using hh)

private theorem reciprocal_norm {z : ℂ} (hu : ‖z‖=1) (hz : z≠1) :
    (1-z)⁻¹ - ((1-z)⁻¹)^2 = ((‖1-z‖:ℂ)^2)⁻¹ := by
  have hn : z≠0 := by intro h; simp [h] at hu
  have hzz : z*conj z=1 := by rw [Complex.mul_conj',hu]; simp
  have hc : conj z = z⁻¹ := by apply mul_left_cancel₀ hn; simpa [hn] using hzz
  have h1 : (1-z)≠0 := sub_ne_zero.mpr hz.symm
  have hnorm := Complex.mul_conj' (1-z)
  rw [map_sub, map_one,hc] at hnorm
  rw [← hnorm]
  field_simp [h1,hn,sub_ne_zero.mpr hz]
  ring

theorem inverse_square_sum (u : ℕ) (hu : 0<u) :
    (∑ z ∈ rootsExceptOne u, (‖1-z‖^2)⁻¹) = ((u:ℝ)^2-1)/12 := by
  classical
  let s := rootsExceptOne u
  have h := product_derivatives s 1 (by simp [s,rootsExceptOne])
  rw [show linearProduct s = geom u from geom_factor u hu] at h
  obtain ⟨h₀,h₁,h₂⟩ := geom_values u
  rw [h₀] at h
  let L : ℂ := ∑ z ∈ s, (1-z)⁻¹
  let L₂ : ℂ := ∑ z ∈ s, ((1-z)⁻¹)^2
  have un : (u:ℂ)≠0 := by exact_mod_cast hu.ne'
  obtain ⟨hp₁,hp₂⟩ := h
  change (geom u).derivative.eval 1 = u*L at hp₁
  change (geom u).derivative.derivative.eval 1 = u*(L^2-L₂) at hp₂
  have hm₁ : 2*L=(u:ℂ)-1 := by
    apply mul_left_cancel₀ un
    change (u:ℂ)*(2*L)=_
    linear_combination h₁-2*hp₁
  have hm₂ : 3*(L^2-L₂) = ((u:ℂ)-1)*(u-2) := by
    apply mul_left_cancel₀ un
    linear_combination h₂-3*hp₂
  have hc : L-L₂=((u:ℂ)^2-1)/12 := by
    linear_combination (norm := ring) (-L/2+(3-(u:ℂ))/4)*hm₁ + hm₂/3
  apply Complex.ofReal_injective
  push_cast
  change (∑ z ∈ s, ((‖1-z‖:ℂ)^2)⁻¹) = _
  calc
    _ = ∑ z ∈ s, ((1-z)⁻¹ - ((1-z)⁻¹)^2) := by
      apply sum_congr rfl
      intro z hz
      have hz' := mem_erase.mp hz
      have he := (mem_nthRootsFinset hu (1:ℂ)).mp hz'.2
      exact (reciprocal_norm (unit_norm hu he) hz'.1).symm
    _ = _ := by rw [Finset.sum_sub_distrib]; exact hc

#print axioms inverse_square_sum
end QFib.Roots
