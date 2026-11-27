import QFibBridge

open Polynomial
open scoped Polynomial
open QFibArrays
namespace QFib

/-- A length-w window suffices for a sequence that increases and then
    decreases on each residue class. Nat subtraction is used only after
    checking index bounds. -/
theorem window_suffices {D H w : ℕ} (hw : 0<w) {G : ℕ → ℤ}
    (early : ∀ i, i≤D/2 → shift w G i ≤ G i)
    (late : ∀ i, D/2<i → i≤H → G i ≤ shift w G i)
    (lastBlock : ∀ i, i≤H → H<i+w → 0≤G i) :
    ∀ i, i≤H → 0≤G i := by
  have front (i : ℕ) (hi : i≤D/2) : 0≤G i := by
    induction i using Nat.strong_induction_on with
    | h i ih =>
      have hh := early i hi
      by_cases hw' : w≤i
      · simp [shift,hw'] at hh
        exact le_trans (ih (i-w) (by omega) (by omega)) hh
      · simpa [shift,hw'] using hh
  have back (t i : ℕ) (ht : H-i=t) (hi : i≤H) (hc : D/2<i) : 0≤G i := by
    induction t using Nat.strong_induction_on generalizing i with
    | h t ih =>
      by_cases he : H<i+w
      · exact lastBlock i hi he
      · have hnext := ih (H-(i+w)) (by omega) (i+w) rfl (by omega) (by omega)
        have hh := late (i+w) (by omega) (by omega)
        simp [shift] at hh
        exact le_trans hnext hh
  intro i hi
  by_cases hc : i≤D/2
  · exact front i hc
  · exact back _ i rfl hi (by omega)

theorem degree_step (m n : ℕ) : (poly (m+1) n).natDegree + Nat.fib (m+1) =
    (poly m n).natDegree + Nat.fib (m+n+1) := by
  have h := congrArg Polynomial.natDegree (poly_step_interval m n)
  have hw : 0 < Nat.fib (m+1) := by simp
  have hA : 0 < Nat.fib (m+n+1) := by simp
  simp only [natDegree_mul (interval_ne_zero hw) (poly_ne_zero _ _),
    natDegree_mul (interval_ne_zero hA) (poly_ne_zero _ _), interval_degree] at h
  omega

theorem degree_lt_twice_top (m n : ℕ) : (poly m n).natDegree < 2*Nat.fib (m+n+1) := by
  have hh := poly_degree m n
  have hA := Nat.fib_le_fib_succ (n:=m+n)
  have hu : 0<Nat.fib (m+2) := by simp
  have hv : 0<Nat.fib (n+2) := by simp
  rw [Nat.fib_add_two (n:=m+n)] at hh
  omega

theorem head_nonnegative {m n : ℕ} (hp : Unimodal (poly m n)) {i : ℕ}
    (hi : i≤(poly m n).natDegree/2) : 0≤(delta m n).coeff i := by
  cases i with
  | zero => simp [delta_zero]
  | succ i =>
    rw [delta_succ]
    have hh := hp.1 i (by omega)
    omega

theorem tail_nonpositive {m n : ℕ} (hp : Unimodal (poly m n)) {i : ℕ}
    (hi : (poly m n).natDegree/2<i) : (delta m n).coeff i≤0 := by
  cases i with
  | zero => omega
  | succ i =>
    rw [delta_succ]
    by_cases hi' : i < (poly m n).natDegree
    · have hh := hp.2 i (by omega) hi'
      omega
    · rw [coeff_eq_zero_of_natDegree_lt (by omega : (poly m n).natDegree < i+1)]
      by_cases htop : i=(poly m n).natDegree
      · subst i
        have hr := poly_symmetric m n 0 (by omega)
        simp only [Nat.sub_zero, poly_zero_coeff] at hr
        omega
      · rw [coeff_eq_zero_of_natDegree_lt (by omega : (poly m n).natDegree < i)]
        omega

/-- The induction step expressed for the actual polynomial. -/
theorem reduce_to_window (m n : ℕ) (hp : Unimodal (poly m n))
    (hc : ∀ i, i≤(poly (m+1) n).natDegree/2 →
      (poly (m+1) n).natDegree/2 < i+Nat.fib (m+1) → 0≤(delta (m+1) n).coeff i) :
    Unimodal (poly (m+1) n) := by
  let A := Nat.fib (m+n+1)
  let w := Nat.fib (m+1)
  let D := (poly m n).natDegree
  let d := (poly (m+1) n).natDegree
  let f := (delta m n).coeff
  let g := (delta (m+1) n).coeff
  have hw : 0<w := Nat.fib_pos.mpr (by omega)
  have hdeg : d+w=D+A := degree_step m n
  have hD : D<2*A := degree_lt_twice_top m n
  have step (i : ℕ) : g i - shift w g i = f i - shift A f i := by
    have hh := congrArg (fun p : ℤ[X] => p.coeff i) (delta_step m n)
    simpa only [subShift_coeff, subShift] using hh
  apply unimodal_of_left
  apply window_suffices (D:=D) hw (G:=g) (H:=d/2) _ _ hc
  · intro i hi
    have hh := step i
    have hlow : 0≤f i := head_nonnegative hp hi
    simp [shift, show ¬A≤i by omega] at hh
    change (if w≤i then g (i-w) else 0) ≤ g i
    omega
  · intro i hi hh
    have hs := step i
    have hup : f i≤0 := tail_nonpositive hp hi
    have hd : 0≤shift A f i := by
      by_cases hx : A≤i
      · rw [shift, if_pos hx]
        exact head_nonnegative hp (by change i-A ≤ D/2; omega)
      · simp [shift,hx]
    omega

theorem zero_width (n : ℕ) : Unimodal (poly 0 n) := by
  simp [poly, Unimodal]

theorem one_poly (n : ℕ) : poly 1 n = interval (Nat.fib (n+1)) := by
  simpa [interval, poly] using poly_step_interval 0 n

theorem one_width (n : ℕ) : Unimodal (poly 1 n) := by
  rw [one_poly]
  simp only [Unimodal, interval_degree, interval_coeff]
  constructor <;> intro i hi
  · simp [show i+1 < Nat.fib (n+1) by omega, show i<Nat.fib (n+1) by omega]
  · intro hi'
    simp [show i<Nat.fib (n+1) by omega, show i+1<Nat.fib (n+1) by omega]

theorem two_delta (n : ℕ) : delta 2 n = (1-X^(Nat.fib (n+2))) * interval (Nat.fib (n+1)) := by
  have hh := poly_step 1 n
  simpa only [show Nat.fib 2=1 by decide, pow_one, show 1+n+1=n+2 by omega, one_poly] using hh

theorem two_width (n : ℕ) : Unimodal (poly 2 n) := by
  apply unimodal_of_left
  intro i hi
  have hd := degree_step 1 n
  rw [one_poly, interval_degree, show Nat.fib 2=1 by decide, show 1+n+1=n+2 by omega] at hd
  change (poly 2 n).natDegree + 1 = Nat.fib (n+1)-1 + Nat.fib (n+2) at hd
  have hab : Nat.fib (n+1) ≤ Nat.fib (n+2) := Nat.fib_le_fib_succ
  have ha : 0<Nat.fib (n+1) := by simp
  have hb : i<Nat.fib (n+2) := by omega
  simp [two_delta,subShift_coeff,subShift,shift,show ¬Nat.fib (n+2)≤i by omega,interval_coeff]
  split <;> omega

def halfCount (i : ℕ) : ℤ := (i/2 : ℕ)+1

theorem halfCount_two (i : ℕ) : subShift 2 halfCount i = 1 := by
  simp only [subShift, shift, halfCount]
  split <;> omega

theorem interval_shift_one (k : ℕ) : subShift k (fun _ => 1) = (interval k).coeff := by
  funext i
  simp [subShift, shift, interval_coeff]
  split <;> split <;> omega

theorem three_delta (n : ℕ) :
    (delta 3 n).coeff = subShift (Nat.fib (n+3)) (subShift (Nat.fib (n+2))
      (subShift (Nat.fib (n+1)) halfCount)) := by
  apply subShift_injective (k:=2) (by decide)
  intro i
  let A := Nat.fib (n+3)
  let B := Nat.fib (n+2)
  let C := Nat.fib (n+1)
  change subShift 2 (delta 3 n).coeff i = subShift 2 (subShift A (subShift B (subShift C halfCount))) i
  have commute (a b : ℕ) (f : ℕ→ℤ) : subShift a (subShift b f) = subShift b (subShift a f) :=
    funext (shift_sub a b f)
  rw [commute 2 A, commute 2 B, commute 2 C, show subShift 2 halfCount = fun _ => 1 from funext halfCount_two,
    interval_shift_one, ← show (delta 2 n).coeff = subShift B (interval C).coeff from
      funext (fun i => by rw [two_delta]; apply subShift_coeff)]
  rw [←subShift_coeff, ←subShift_coeff]
  have hh := delta_step 2 n
  rw [show Nat.fib (2+1)=2 by decide, show 2+n+1=n+3 by omega] at hh
  exact congrArg (fun p : ℤ[X] => p.coeff i) hh

theorem three_width (n : ℕ) : Unimodal (poly 3 n) := by
  apply unimodal_of_left
  intro i hi
  let B := Nat.fib (n+2)
  let C := Nat.fib (n+1)
  have hBC : C≤B := Nat.fib_le_fib_succ
  have hC : 0<C := Nat.fib_pos.mpr (by omega)
  have hA : Nat.fib (n+3)=C+B := Nat.fib_add_two
  have hd₁ := degree_step 1 n
  have hd₂ := degree_step 2 n
  rw [one_poly, interval_degree, show Nat.fib (1+1)=1 by decide, show 1+n+1=n+2 by omega] at hd₁
  rw [show Nat.fib (2+1)=2 by decide, show 2+n+1=n+3 by omega,hA] at hd₂
  change (poly 2 n).natDegree+1 = C-1+B at hd₁
  change (poly 3 n).natDegree+2 = (poly 2 n).natDegree+(C+B) at hd₂
  have hmax : i+2≤C+B := by omega
  rw [three_delta, hA]
  change 0≤subShift (C+B) (subShift B (subShift C halfCount)) i
  simp only [subShift, shift, halfCount, if_neg (by omega : ¬C+B≤i), sub_zero]
  split <;> split <;> (try split) <;> omega

#print axioms reduce_to_window
#print axioms three_width
end QFib
