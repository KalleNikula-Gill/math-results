import QFibCentral
import QFibCutoff
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.LinearCombination

open Polynomial Finset
open scoped Polynomial BigOperators
namespace QFib

theorem eval_interval (a : ℕ) : (interval a).eval 1 = (a : ℤ) := by
  simp [interval,eval_finset_sum]

theorem eval_fibFact_pos (m : ℕ) : 0 < (fibFact m).eval 1 := by
  induction m with
  | zero => simp [fibFact]
  | succ m ih =>
    rw [fibFact, eval_mul, eval_interval]
    exact mul_pos ih (by exact_mod_cast Nat.fib_pos.mpr (by omega : 0 < m+1))

theorem eval_poly_pos (m n : ℕ) : 0 < (poly m n).eval 1 := by
  have hh := congrArg (fun p : ℤ[X] => p.eval 1) (factorial_identity m n)
  simp only [eval_mul] at hh
  have h : 0 < (poly m n).eval 1 * ((fibFact m).eval 1 * (fibFact n).eval 1) :=
    hh.symm ▸ eval_fibFact_pos (m+n)
  exact pos_of_mul_pos_left h (mul_pos (eval_fibFact_pos m) (eval_fibFact_pos n)).le

theorem sum_coeff_one (p : ℤ[X]) :
    (∑ j ∈ range (p.natDegree+1), p.coeff j) = p.eval 1 := by
  simp [eval_eq_sum_range]

/-- Twice the first moment of the coefficients of a reciprocal polynomial. -/
theorem moment (m n : ℕ) :
    2*(∑ j ∈ range ((poly m n).natDegree+1), (j:ℤ)*(poly m n).coeff j) =
      ((poly m n).natDegree:ℤ)*(poly m n).eval 1 := by
  let p := poly m n
  let d := p.natDegree
  let S := ∑ j ∈ range (d+1), (j:ℤ)*p.coeff j
  change 2*S = (d:ℤ)*p.eval 1
  have hs : (∑ j ∈ range (d+1), ((d:ℤ)-j)*p.coeff j) = S := by
    dsimp only [S]
    rw [← sum_range_reflect (fun j => (j:ℤ)*p.coeff j) (d+1)]
    apply sum_congr rfl
    intro j hj
    have hj' : j≤d := by have := mem_range.mp hj; omega
    have hr : p.coeff (d-j)=p.coeff j := poly_symmetric m n j hj'
    simp only [Nat.add_sub_cancel, Nat.cast_sub hj', hr]
  calc
    2*S = (∑ j ∈ range (d+1), ((d:ℤ)-j)*p.coeff j) + S := by rw [hs]; ring
    _ = ∑ j ∈ range (d+1), (d:ℤ)*p.coeff j := by
      dsimp [S]
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro j _
      ring
    _ = _ := by rw [← Finset.mul_sum, sum_coeff_one]

namespace Central

/- Use a=m-4. All Fibonacci indices in this namespace are nonnegative
   without relying on truncated subtraction at the bottom boundary. -/
abbrev u (a:ℕ) := Nat.fib (a+2)
abbrev v (a:ℕ) := Nat.fib (a+3)
abbrev w (a:ℕ) := Nat.fib (a+4)
abbrev C (a n:ℕ) := Nat.fib (a+n+2)
abbrev B (a n:ℕ) := Nat.fib (a+n+3)
abbrev A (a n:ℕ) := Nat.fib (a+n+4)
noncomputable abbrev T (a n:ℕ) := (poly (a+1) n).natDegree
noncomputable abbrev d (a n:ℕ) := (poly (a+4) n).natDegree

theorem deg_truncated (a n : ℕ) :
    T a n+Nat.fib (n+2)+v a = B a n+1 := by
  have hh := poly_degree (a+1) n
  simpa only [T,v,B,show a+1+n+2 = a+n+3 by omega, Nat.add_right_comm] using hh

theorem deg_full (a n : ℕ) : d a n+2*w a = T a n+2*A a n := by
  have h₁ := deg_truncated a n
  have h₂ := poly_degree (a+4) n
  rw [show a+4+n+2=a+n+6 by omega, Nat.fib_add_two (n:=a+n+4),
    Nat.fib_add_two (n:=a+n+3), Nat.fib_add_two (n:=a+4),
    Nat.fib_add_two (n:=a+3)] at h₂
  change T a n+Nat.fib (n+2)+v a=B a n+1 at h₁
  change d a n+(w a+(v a+w a))+Nat.fib (n+2) = A a n+(B a n+A a n)+1 at h₂
  omega

theorem central_support (a n i : ℕ) (hn : a+4≤n)
    (hip : i ≤ d a n/2) (hil : d a n/2 < i+w a) :
    B a n+T a n ≤ i ∧ i < A a n+C a n := by
  have hd := deg_full a n
  have ht := deg_truncated a n
  have hA : A a n=C a n+B a n := Nat.fib_add_two
  have hB : B a n=Nat.fib (a+n+1)+C a n := Nat.fib_add_two
  have hC : C a n=Nat.fib (a+n)+Nat.fib (a+n+1) := Nat.fib_add_two
  have hw : w a=u a+v a := Nat.fib_add_two
  have hv : v a=Nat.fib (a+1)+u a := Nat.fib_add_two
  have hlow : w a ≤ Nat.fib (a+n) := Nat.fib_mono (by omega)
  have hlower : Nat.fib (a+6) ≤ Nat.fib (n+2) := Nat.fib_mono (by omega)
  have hn₂ : Nat.fib (a+6)=w a+(v a+w a) := by
    rw [Nat.fib_add_two (n:=a+4),Nat.fib_add_two (n:=a+3)]
  have hvpos : 0<Nat.fib (a+1) := by simp
  have hpp : 0<Nat.fib (a+n) := Nat.fib_pos.mpr (by omega)
  have hu : 0<u a := Nat.fib_pos.mpr (by omega)
  omega

theorem three_factors (a n : ℕ) :
    ((1-X^(u a))*(1-X^(v a))*(1-X^(w a))) * poly (a+4) n =
    ((1-X^(C a n))*(1-X^(B a n))*(1-X^(A a n))) * poly (a+1) n := by
  have h₁ := poly_step (a+1) n
  have h₂ := poly_step (a+2) n
  have h₃ := poly_step (a+3) n
  rw [show a+1+n+1 = a+n+2 by omega] at h₁
  rw [show a+2+n+1 = a+n+3 by omega] at h₂
  rw [show a+3+n+1 = a+n+4 by omega] at h₃
  change (1-X^(u a))*poly (a+2) n = (1-X^(C a n))*poly (a+1) n at h₁
  change (1-X^(v a))*poly (a+3) n = (1-X^(B a n))*poly (a+2) n at h₂
  change (1-X^(w a))*poly (a+4) n = (1-X^(A a n))*poly (a+3) n at h₃
  linear_combination (1-X^(u a))*(1-X^(v a))*h₃ +
    (1-X^(u a))*(1-X^(A a n))*h₂ + (1-X^(B a n))*(1-X^(A a n))*h₁

theorem three_numerators (a n : ℕ) :
    (1-X^(C a n))*(1-X^(B a n))*(1-X^(A a n)) =
    (1-X^(C a n)-X^(B a n)+X^(A a n+C a n)+X^(A a n+B a n)-X^(2*A a n) : ℤ[X]) := by
  rw [show A a n=C a n+B a n from Nat.fib_add_two]
  simp only [two_mul,pow_add]
  ring

theorem truncate_numerators (a n i : ℕ) (hi : i<A a n+C a n) (p : ℤ[X]) :
    (((1-X^(C a n))*(1-X^(B a n))*(1-X^(A a n))) * p).coeff i =
    ((1-X^(C a n)-X^(B a n))*p).coeff i := by
  have hCB : C a n≤B a n := Nat.fib_le_fib_succ
  have hA : A a n=C a n+B a n := Nat.fib_add_two
  rw [three_numerators]
  simp [sub_mul,add_mul,coeff_X_pow_mul', show ¬ A a n+C a n≤i by omega,
    show ¬ A a n+B a n≤i by omega, show ¬ 2*A a n≤i by omega]

theorem linear_term (a n i : ℕ) :
    (∑ j ∈ range (T a n+1), (poly (a+1) n).coeff j *
      (2*(A a n:ℤ)-2*i+2*j-(2*(w a:ℤ)-1))) =
      (poly (a+1) n).eval 1 * ((d a n:ℤ)+1-2*i) := by
  let p := poly (a+1) n
  have hm := moment (a+1) n
  have hd : (d a n:ℤ)+2*w a=(T a n:ℤ)+2*A a n := by exact_mod_cast deg_full a n
  change 2*(∑ j ∈ range (T a n+1), (j:ℤ)*p.coeff j)=(T a n:ℤ)*p.eval 1 at hm
  calc
    _ = (2*(A a n:ℤ)-2*i-2*w a+1) * (∑ j ∈ range (T a n+1), p.coeff j) +
        2*(∑ j ∈ range (T a n+1), (j:ℤ)*p.coeff j) := by
          rw [Finset.mul_sum, Finset.mul_sum, ←Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro j _
          change p.coeff j * _ = _
          ring
    _ = _ := by rw [sum_coeff_one, hm]; change _ = p.eval 1 * _; linear_combination -(p.eval 1)*hd

theorem linear_term_pos (a n i : ℕ) (hi : i≤d a n/2) :
    0 < (poly (a+1) n).eval 1 * ((d a n:ℤ)+1-2*i) :=
  mul_pos (eval_poly_pos _ _) (by omega)

end Central
end QFib
