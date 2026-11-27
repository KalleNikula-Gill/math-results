import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic.Ring
import QFibFinite

open Polynomial Finset
open scoped Polynomial BigOperators

namespace QFib

/-- The interval polynomial at a possibly stretched variable. -/
noncomputable def stretch (a b : ℕ) : ℤ[X] :=
  ∑ i ∈ range b, (X ^ a) ^ i

noncomputable def interval (a : ℕ) : ℤ[X] := ∑ i ∈ range a, X ^ i

noncomputable def fibFact : ℕ → ℤ[X]
  | 0 => 1
  | j+1 => fibFact j * interval (Nat.fib (j+1))

theorem interval_add (a b : ℕ) :
    interval (a+b) = interval a + X^a * interval b := by
  simp [interval, Finset.sum_range_add, Finset.mul_sum, pow_add]

theorem interval_mul (a b : ℕ) : interval (a*b) = interval a * stretch a b := by
  induction b with
  | zero => simp [interval, stretch]
  | succ b ih =>
    rw [Nat.mul_succ, interval_add, ih]
    simp [stretch, sum_range_succ, pow_mul]
    ring

/-- Polynomial realization of the factorial quotient. The identity
    'factorial_identity' specifies it without any division convention. -/
noncomputable def poly : ℕ → ℕ → ℤ[X]
  | 0, _ => 1
  | _+1, 0 => 1
  | m+1, n+1 =>
    stretch (Nat.fib (m+1)) (Nat.fib (n+2)) * poly m (n+1) +
    X ^ (Nat.fib (m+1) * Nat.fib (n+2)) *
      stretch (Nat.fib (n+1)) (Nat.fib m) * poly (m+1) n
termination_by m n => m+n

theorem factorial_identity (m n : ℕ) :
    poly m n * (fibFact m * fibFact n) = fibFact (m+n) := by
  induction m generalizing n with
  | zero => simp [poly, fibFact]
  | succ m im =>
    induction n with
    | zero => simp [poly, fibFact]
    | succ n jn =>
      let a := Nat.fib (m+1)
      let b := Nat.fib (n+2)
      let c := Nat.fib (n+1)
      let e := Nat.fib m
      have hab : Nat.fib ((m+1)+(n+1)) = a*b + c*e := by
        simpa [a,b,c,e,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,
          Nat.mul_comm] using Nat.fib_add m (n+1)
      have hn := im (n+1)
      have hprev : (m+1)+n = m+(n+1) := by omega
      rw [hprev] at jn
      rw [poly]
      change (stretch a b * poly m (n+1) +
          X^(a*b) * stretch c e * poly (m+1) n) *
        (fibFact (m+1) * fibFact (n+1)) = _
      calc
        _ = (interval a * stretch a b) * (poly m (n+1) * (fibFact m * fibFact (n+1))) +
            X^(a*b) * (interval c * stretch c e) * (poly (m+1) n * (fibFact (m+1) * fibFact n)) := by
              simp only [fibFact, a, c]
              ring
        _ = (interval (a*b) + X^(a*b) * interval (c*e)) * fibFact (m+(n+1)) := by
              rw [hn, jn, interval_mul a b, interval_mul c e]
              ring
        _ = _ := by
              rw [← interval_add, ← hab]
              change interval _ * fibFact (m+(n+1)) = fibFact ((m+1)+n) * interval _
              rw [hprev, mul_comm]
              congr 3

theorem interval_coeff (a i : ℕ) : (interval a).coeff i = if i < a then 1 else 0 := by
  simp [interval, finset_sum_coeff, coeff_X_pow]

theorem interval_zero_coeff {a : ℕ} (ha : 0 < a) : (interval a).coeff 0 = 1 := by
  simp [interval_coeff, ha]

theorem fibFact_zero_coeff (m : ℕ) : (fibFact m).coeff 0 = 1 := by
  induction m with
  | zero => simp [fibFact]
  | succ j ih => simp [fibFact, mul_coeff_zero, ih, interval_zero_coeff (Nat.fib_pos.mpr (by omega : 0 < j+1))]

theorem fibFact_ne_zero (m : ℕ) : fibFact m ≠ 0 := by
  intro h
  have hh := fibFact_zero_coeff m
  simp [h] at hh

theorem poly_eq_of_factorial_identity {p : ℤ[X]} {m n : ℕ}
    (hp : p * (fibFact m * fibFact n) = fibFact (m+n)) : p = poly m n := by
  exact mul_right_cancel₀ (mul_ne_zero (fibFact_ne_zero _) (fibFact_ne_zero _))
    (hp.trans (factorial_identity m n).symm)

theorem poly_comm (m n : ℕ) : poly m n = poly n m := by
  apply poly_eq_of_factorial_identity
  simpa [Nat.add_comm, mul_comm] using factorial_identity m n

theorem poly_ne_zero (m n : ℕ) : poly m n ≠ 0 := by
  intro hz
  have hh := factorial_identity m n
  exact fibFact_ne_zero _ (by simpa [hz] using hh.symm)

theorem poly_zero_coeff (m n : ℕ) : (poly m n).coeff 0 = 1 := by
  have hh := congrArg (fun p : ℤ[X] => p.coeff 0) (factorial_identity m n)
  simpa [mul_coeff_zero, fibFact_zero_coeff] using hh

theorem finite_fib_pair (n : ℕ) :
    QFibFinite.fibPair n = (Nat.fib n, Nat.fib (n+1)) := by
  induction n with
  | zero => rfl
  | succ k ih => simp [QFibFinite.fibPair, ih, Nat.fib_add_two]

@[simp] theorem finite_fib (n : ℕ) : QFibFinite.fib n = Nat.fib n := by
  simp [QFibFinite.fib, finite_fib_pair]


theorem interval_ne_zero {a : ℕ} (ha : 0 < a) : interval a ≠ 0 := by
  intro he
  have h := interval_zero_coeff ha
  simp [he] at h

theorem interval_degree (a : ℕ) : (interval a).natDegree = a-1 := by
  cases a with
  | zero => simp [interval]
  | succ a =>
    apply natDegree_eq_of_le_of_coeff_ne_zero
    · apply natDegree_le_iff_coeff_eq_zero.mpr
      intro i hi
      simp [interval_coeff, show ¬ i < a+1 by omega]
    · simp [interval_coeff]

theorem interval_reverse (a : ℕ) : (interval a).reverse = interval a := by
  ext i
  rw [coeff_reverse, interval_degree, interval_coeff, interval_coeff]
  by_cases hi : i ≤ a-1
  · rw [revAt_le hi]
    by_cases ha : a=0
    · simp [ha]
    · simp [show a-1-i < a by omega, show i<a by omega]
  · rw [revAt_eq_self_of_lt (by omega : a-1 < i)]

theorem fibFact_reverse (m : ℕ) : (fibFact m).reverse = fibFact m := by
  induction m with
  | zero => simp [fibFact, Polynomial.reverse, reflect_one]
  | succ m ih => rw [fibFact, reverse_mul_of_domain, ih, interval_reverse]

theorem poly_reverse (m n : ℕ) : (poly m n).reverse = poly m n := by
  apply poly_eq_of_factorial_identity
  simpa only [reverse_mul_of_domain, fibFact_reverse] using
    congrArg Polynomial.reverse (factorial_identity m n)

theorem poly_symmetric (m n i : ℕ) (hi : i ≤ (poly m n).natDegree) :
    (poly m n).coeff ((poly m n).natDegree-i) = (poly m n).coeff i := by
  simpa only [coeff_reverse, revAt_le hi] using
    congrArg (fun p : ℤ[X] => p.coeff i) (poly_reverse m n)

theorem fibFact_degree (m : ℕ) :
    (fibFact m).natDegree + (m+1) = Nat.fib (m+2) := by
  induction m with
  | zero => simp [fibFact]
  | succ m ih =>
    rw [fibFact, natDegree_mul (fibFact_ne_zero m)
      (interval_ne_zero (Nat.fib_pos.mpr (by omega))), interval_degree]
    have hp : 0 < Nat.fib (m+1) := Nat.fib_pos.mpr (by omega)
    have hh : Nat.fib (m+1+2) = Nat.fib (m+1) + Nat.fib (m+2) := Nat.fib_add_two
    omega

theorem poly_degree (m n : ℕ) :
    (poly m n).natDegree + Nat.fib (m+2) + Nat.fib (n+2) = Nat.fib (m+n+2)+1 := by
  have hh := congrArg Polynomial.natDegree (factorial_identity m n)
  simp only [natDegree_mul (poly_ne_zero _ _) (mul_ne_zero (fibFact_ne_zero _) (fibFact_ne_zero _)),
    natDegree_mul (fibFact_ne_zero _) (fibFact_ne_zero _)] at hh
  have h1 := fibFact_degree m
  have h2 := fibFact_degree n
  have h3 := fibFact_degree (m+n)
  omega

theorem hIndex_eq (m n : ℕ) : QFibFinite.hIndex m n = (poly m n).natDegree / 2 := by
  simp only [QFibFinite.hIndex, finite_fib]
  have hh := poly_degree m n
  omega

/-- Removing one numerator and one denominator interval. -/
theorem poly_step_interval (m n : ℕ) :
    interval (Nat.fib (m+1)) * poly (m+1) n =
    interval (Nat.fib (m+n+1)) * poly m n := by
  apply mul_right_cancel₀ (b := fibFact m * fibFact n) (mul_ne_zero (fibFact_ne_zero m) (fibFact_ne_zero n))
  have h₁ := factorial_identity (m+1) n
  have h₂ := factorial_identity m n
  rw [show m+1+n = (m+n)+1 by omega] at h₁
  simp only [fibFact] at h₁
  calc
    _ = poly (m+1) n * ((fibFact m * interval (Nat.fib (m+1))) * fibFact n) := by ring
    _ = _ := h₁
    _ = interval (Nat.fib (m+n+1)) * poly m n * (fibFact m * fibFact n) := by
      rw [← h₂]
      ring

theorem interval_times (a : ℕ) : interval a * (1-X) = 1 - X^a :=
  geom_sum_mul_neg X a

theorem poly_step (m n : ℕ) :
    (1-X^(Nat.fib (m+1))) * poly (m+1) n =
    (1-X^(Nat.fib (m+n+1))) * poly m n := by
  rw [← interval_times, ← interval_times]
  calc
    _ = (1-X) * (interval (Nat.fib (m+1)) * poly (m+1) n) := by ring
    _ = _ := by rw [poly_step_interval]; ring

/-- Adjacent coefficient inequalities at the central peak, including degree zero. -/
def Unimodal (p : ℤ[X]) : Prop :=
  (∀ i, i < p.natDegree / 2 → p.coeff i ≤ p.coeff (i+1)) ∧
  (∀ i, p.natDegree / 2 ≤ i → i < p.natDegree → p.coeff (i+1) ≤ p.coeff i)

end QFib
