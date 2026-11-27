import QFibBounds
import Mathlib.Algebra.Polynomial.Div

open Polynomial
open scoped Polynomial
namespace QFib

/-- The original all-dimensions statement, using the polynomial uniquely
    characterized by factorial_identity and poly_eq_of_factorial_identity. -/
def Conjecture : Prop := ∀ m n, Unimodal (poly m n)

private theorem small_oriented (m n : ℕ) (hmn : m≤n) (h : m≤3 ∨ n≤10) :
    Unimodal (poly m n) := by
  match m with
  | 0 => exact zero_width n
  | 1 => exact one_width n
  | 2 => exact two_width n
  | 3 => exact three_width n
  | k+4 => exact direct_unimodal _ n (by omega) hmn (by omega)

/-- All pairs with a dimension at most three or both dimensions at most ten. -/
theorem supported_dimensions (m n : ℕ) (h : min m n≤3 ∨ max m n≤10) :
    Unimodal (poly m n) := by
  by_cases hmn : m≤n
  · apply small_oriented m n hmn
    simpa [min_eq_left hmn, max_eq_right hmn] using h
  · rw [poly_comm]
    have hnm : n≤m := by omega
    apply small_oriented n m hnm
    simpa [min_eq_right hnm, max_eq_left hnm] using h

/-- The only central signs left after the certified cases. -/
def RemainingWindows : Prop :=
  ∀ m n, 4≤m → m≤n → 11≤n → ∀ i,
    i≤(poly m n).natDegree/2 → (poly m n).natDegree/2 < i+Nat.fib m →
    0 ≤ (delta m n).coeff i

theorem conjecture_iff_remaining_windows : Conjecture ↔ RemainingWindows := by
  constructor
  · intro h m n _ _ _ i hi _
    exact head_nonnegative (h m n) hi
  · intro hw
    have oriented (m n : ℕ) (h : m≤n) : Unimodal (poly m n) := by
      induction m with
      | zero => exact zero_width n
      | succ m ih =>
        by_cases hs : m+1≤3 ∨ n≤10
        · exact small_oriented _ n h hs
        · apply reduce_to_window m n (ih (by omega))
          exact hw (m+1) n (by omega) h (by omega)
    intro m n
    by_cases h : m≤n
    · exact oriented m n h
    · rw [poly_comm]; exact oriented n m (by omega)


/-- The positive double-pole term dominates the error at every remaining index. -/
theorem central_nonnegative (a n i : ℕ) (hn : a+4≤n) (hb : 11≤n)
    (hip : i≤Central.d a n/2) (hil : Central.d a n/2 < i+Central.w a) :
    0 ≤ (delta (a+4) n).coeff i := by
  let v₀ := (((poly (a+1) n).eval 1:ℤ):ℝ)
  let u := Central.u a
  let v := Central.v a
  let w := Central.w a
  let K := v₀/(2*(u:ℝ)*v*w*w)
  let main := v₀*((Central.d a n:ℝ)+1-2*i)/(2*(u:ℝ)*v*w)
  have hq : 0<v₀ := by dsimp only [v₀]; exact_mod_cast eval_poly_pos (a+1) n
  have hup : (0:ℝ)<u := by exact_mod_cast (show 0<u from Nat.fib_pos.mpr (by omega))
  have hvp : (0:ℝ)<v := by exact_mod_cast (show 0<v from Nat.fib_pos.mpr (by omega))
  have hwp : (0:ℝ)<w := by exact_mod_cast (show 0<w from Nat.fib_pos.mpr (by omega))
  have hk : 0≤K := by dsimp only [K]; positivity
  have hr := Roots.three_residues a n i (complexPoly (a+1) n) K hk (fun U hU z hz =>
    Roots.root_bound a n hn hb hU hz)
  change ‖Central.remainder a n i‖ ≤ (w:ℝ)*K at hr
  have hm : (w:ℝ)*K≤main := by
    have hd : (2:ℝ)*i≤Central.d a n := by exact_mod_cast (show 2*i≤Central.d a n by omega)
    have hbase : (w:ℝ)*K=v₀/(2*(u:ℝ)*v*w) := by dsimp only [K]; field_simp
    rw [hbase]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hh := mul_le_mul_of_nonneg_left (show (1:ℝ)≤(Central.d a n:ℝ)+1-2*i by linarith) hq.le
    simpa using hh
  have hf := Central.midpoint_formula a n i hn hip hil
  rw [complex_one] at hf
  have hval : (↑(((delta (a+4) n).coeff i:ℤ):ℝ):ℂ) =
      (main:ℂ)+Central.remainder a n i := by
    dsimp only [main,v₀,u,v,w]
    push_cast
    exact hf
  have he := congrArg Complex.re hval
  simp only [Complex.ofReal_re,Complex.add_re] at he
  have hlow := (abs_le.mp (Complex.abs_re_le_norm (Central.remainder a n i))).1
  have hp : (0:ℝ)≤(((delta (a+4) n).coeff i:ℤ):ℝ) := by linarith
  exact_mod_cast hp

/-- Unconditional, all-dimensions form, with no analytic or arithmetic premises. -/
theorem all_unimodal : Conjecture := by
  apply conjecture_iff_remaining_windows.mpr
  intro m n hm hn hb i hi hj
  obtain ⟨a,rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [Nat.add_comm 4 a] at hn hi hj ⊢
  exact central_nonnegative a n i hn hb hi hj

/-- The factorial quotient literally as polynomial division over the integers. -/
noncomputable def qFibonomial (m n : ℕ) : ℤ[X] :=
  fibFact (m+n) /ₘ (fibFact m* fibFact n)

theorem fibFact_monic (m : ℕ) : (fibFact m).Monic := by
  have h := congrArg (fun p : ℤ[X] => p.coeff 0) (fibFact_reverse m)
  change (fibFact m).coeff (fibFact m).natDegree = 1
  simpa only [coeff_reverse,revAt_le (Nat.zero_le _),Nat.sub_zero,fibFact_zero_coeff] using h

theorem qFibonomial_eq (m n : ℕ) : qFibonomial m n=poly m n := by
  rw [qFibonomial,←factorial_identity, mul_comm (poly m n)]
  exact mul_divByMonic_cancel_left _ ((fibFact_monic m).mul (fibFact_monic n))

/-- The fixed midpoint in the literal factorial quotient. -/
theorem qFibonomial_midpoint (m n : ℕ) : Unimodal (qFibonomial m n) :=
  qFibonomial_eq m n ▸ all_unimodal m n

/-- The existential peak of the original conjecture, in the literal quotient. -/
theorem qFibonomial_unimodal (m n : ℕ) :
    ∃ k ≤ (qFibonomial m n).natDegree,
      (∀ i, i<k → (qFibonomial m n).coeff i ≤ (qFibonomial m n).coeff (i+1)) ∧
      (∀ i, k≤ i → i<(qFibonomial m n).natDegree →
        (qFibonomial m n).coeff (i+1) ≤ (qFibonomial m n).coeff i) := by
  exact ⟨(qFibonomial m n).natDegree/2,Nat.div_le_self ..,qFibonomial_midpoint m n⟩

#print axioms factorial_identity
#print axioms poly_symmetric
#print axioms array_coeff
#print axioms reduce_to_window
#print axioms all_order_bounds
#print axioms Central.linear_term
#print axioms Roots.inverse_square_sum
#print axioms supported_dimensions
#print axioms conjecture_iff_remaining_windows
#print axioms Central.midpoint_formula
#print axioms Roots.specialization
#print axioms Roots.normalized_bound
#print axioms central_nonnegative
#print axioms all_unimodal
#check qFibonomial_unimodal
#print axioms qFibonomial_eq
#print axioms qFibonomial_midpoint
#print axioms qFibonomial_unimodal
end QFib
