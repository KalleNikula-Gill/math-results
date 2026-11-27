import QFibModel
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.GCongr

namespace QFib
open QFibFinite (sCount kCount)

def PossibleOrder (m e : ℕ) : Prop := 1 < e ∧
  (e ∣ Nat.fib (m-2) ∨ e ∣ Nat.fib (m-1) ∨ e ∣ Nat.fib m)

theorem rank_exists {e : ℕ} (he : 1<e) (hex : ∃ j, 0<j ∧ e ∣ Nat.fib j) :
    ∃ r, 3≤r ∧ ∀ j, e ∣ Nat.fib j ↔ r ∣ j := by
  let r := Nat.find hex
  have hs : 0<r ∧ e ∣ Nat.fib r := Nat.find_spec hex
  have hmin {j : ℕ} (h : 0<j ∧ e∣Nat.fib j) : r≤j := Nat.find_min' hex h
  have h3 : 3≤r := by
    by_contra! hl
    have hh : r=1 ∨ r=2 := by omega
    rcases hh with hh | hh <;> rw [hh] at hs <;> simp at hs <;> omega
  refine ⟨r, h3, fun j => ⟨?_, fun hj => hs.2.trans (Nat.fib_dvd _ _ hj)⟩⟩
  intro hj
  have hg : e ∣ Nat.fib (r.gcd j) := by
    rw [Nat.fib_gcd]; exact Nat.dvd_gcd hs.2 hj
  have hr := hmin ⟨Nat.gcd_pos_of_pos_left j hs.1, hg⟩
  have hr' := Nat.le_of_dvd hs.1 (Nat.gcd_dvd_left r j)
  have hh : r.gcd j = r := by omega
  exact hh ▸ Nat.gcd_dvd_right r j

theorem rank_for_order (m e : ℕ) (hm : 4≤m) (ho : PossibleOrder m e) :
    ∃ r, 3≤r ∧ ∀ j, e ∣ Nat.fib j ↔ r ∣ j := by
  apply rank_exists ho.1
  rcases ho.2 with h | h | h
  · exact ⟨m-2, by omega, h⟩
  · exact ⟨m-1, by omega, h⟩
  · exact ⟨m, by omega, h⟩

theorem sCount_rank (m e r : ℕ) (hr : ∀ j, e ∣ Nat.fib j ↔ r ∣ j) :
    sCount m e + (m-3)/r = m-3 := by
  have hh (p : ℕ) :
      ((List.range p).filter (fun j => QFibFinite.fib (j+1) % e != 0)).length + p/r = p := by
    induction p with
    | zero => simp
    | succ p ih =>
      rw [List.range_succ, List.filter_append, List.length_append, Nat.succ_div]
      by_cases h : r ∣ p+1
      · have ha : QFibFinite.fib (p+1) % e=0 := by
          rw [finite_fib]; exact Nat.mod_eq_zero_of_dvd ((hr _).mpr h)
        simp [-finite_fib, ha, h]
        omega
      · have ha : ¬QFibFinite.fib (p+1) % e=0 := by
          rw [finite_fib]; exact fun ht => h ((hr _).mp (Nat.dvd_of_mod_eq_zero ht))
        simp [-finite_fib, ha, h]
        omega
  exact hh _

theorem fact_eq (k : ℕ) : QFibFinite.fact k = k.factorial := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (List.range (k+1)).foldl _ 1 = _
    rw [List.range_succ, List.foldl_append]
    change QFibFinite.fact k * (k+1) = _
    rw [ih,Nat.factorial_succ,Nat.mul_comm]

/-- The parameter n appears only in the numerator growth term. -/
def OrderInequality (m n e : ℕ) : Prop :=
  2 * Nat.fib (m-2) * Nat.fib (m-1) * Nat.fib m * Nat.fib m * e^(sCount m e) <
    (2*Nat.fib (n+1))^(sCount m e) * (kCount m e).factorial

theorem finite_cutoff (m n e : ℕ) (hm : 4≤m) (hu : m<40) (hn : max m 11 ≤ n)
    (ho : PossibleOrder m e) : OrderInequality m n e := by
  have hh := QFibFinite.allOrderInequalities m e hm hu ho.1 (by simpa using ho.2)
  simp only [QFibFinite.lhs, QFibFinite.rhs, finite_fib, fact_eq] at hh
  apply lt_of_lt_of_le hh
  exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left
    (Nat.mul_le_mul_left 2 (Nat.fib_mono (by omega : max m 11+1 ≤ n+1))) _)

theorem fib_fourth (m : ℕ) : Nat.fib m ^ 4 ≤ 8^m := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    match m with
    | 0 | 1 | 2 | 3 | 4 => decide
    | n+5 =>
      have h₀ := Nat.fib_le_fib_succ (n:=n)
      have h₁ : Nat.fib (n+5) ≤ 8*Nat.fib (n+1) := by
        simp only [Nat.fib_add_two (n:=n+3), Nat.fib_add_two (n:=n+2),
          Nat.fib_add_two (n:=n+1), Nat.fib_add_two (n:=n)]
        omega
      calc
        _ ≤ (8*Nat.fib (n+1))^4 := Nat.pow_le_pow_left h₁ _
        _ = 8^4 * Nat.fib (n+1)^4 := mul_pow _ _ _
        _ ≤ 8^4 * 8^(n+1) := Nat.mul_le_mul_left _ (ih (n+1) (by omega))
        _ = _ := by rw [←pow_add]; congr 1; omega

theorem factorial_threshold (m : ℕ) (hm : 40≤m) :
    2*8^m < 2^(m-11) * (m-11).factorial := by
  obtain ⟨t,rfl⟩ := Nat.exists_eq_add_of_le hm
  induction t with
  | zero => decide
  | succ t ih =>
    have hs : 40+(t+1)-11 = (40+t-11)+1 := by omega
    rw [hs, pow_succ, Nat.factorial_succ, show 40+(t+1) = (40+t)+1 by omega, pow_succ]
    calc
      _ = (2*8^(40+t))*8 := by ring
      _ < (2^(40+t-11)*(40+t-11).factorial)*8 := Nat.mul_lt_mul_of_pos_right (ih (by omega)) (by decide)
      _ ≤ (2^(40+t-11)*(40+t-11).factorial)*(2*((40+t-11)+1)) :=
        Nat.mul_le_mul_left _ (by omega)
      _ = _ := by ring

private theorem count_prefix (p : ℕ → Bool) (k l : ℕ) (hkl : k≤l)
    (hb : ∀ j, j<k → p j = true) :
    k ≤ ((List.range l).filter p).length := by
  induction l with
  | zero => simp_all
  | succ l ih =>
    rw [List.range_succ, List.filter_append, List.length_append]
    by_cases ha : k≤l
    · have := ih ha
      omega
    · have heq : k=l+1 := by omega
      have hf : ((List.range l).filter p).length = l := by
        apply Eq.trans _ (List.length_range (n:=l))
        apply List.length_filter_eq_length_iff.mpr
        intro j hj
        exact hb j (by have := List.mem_range.mp hj; omega)
      simp [hb l (by omega), hf, heq]

theorem large_order_cutoff (m n e : ℕ) (hm : 40≤m) (hn : m≤n)
    (ho : PossibleOrder m e) : OrderInequality m n e := by
  obtain ⟨r,hr,hrank⟩ := rank_for_order m e (by omega) ho
  have hc := sCount_rank m e r hrank
  have hdiv := Nat.div_le_div_left (a:=m-3) hr (by decide)
  have hs₃ : 2*(m-3) ≤ 3*sCount m e := by omega
  have hmu : Nat.fib (m-2) ≤ Nat.fib m := Nat.fib_mono (by omega)
  have hmv : Nat.fib (m-1) ≤ Nat.fib m := Nat.fib_mono (by omega)
  have hew : e≤Nat.fib m := by
    rcases ho.2 with h | h | h
    · exact le_trans (Nat.le_of_dvd (Nat.fib_pos.mpr (by omega)) h) hmu
    · exact le_trans (Nat.le_of_dvd (Nat.fib_pos.mpr (by omega)) h) hmv
    · exact Nat.le_of_dvd (Nat.fib_pos.mpr (by omega)) h
  have htot : 2*Nat.fib (m-2)*Nat.fib (m-1)*Nat.fib m*Nat.fib m ≤ 2*8^m := by
    calc
      _ ≤ 2*Nat.fib m*Nat.fib m*Nat.fib m*Nat.fib m := by gcongr
      _ = 2*(Nat.fib m)^4 := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (fib_fourth m)
  have hnF : Nat.fib m ≤ Nat.fib (n+1) := Nat.fib_mono (by omega)
  have hepos : 0<e := by have := ho.1; omega
  let s := sCount m e
  let k := kCount m e
  have key : 2*8^m * e^s < (2*Nat.fib (n+1))^s * k.factorial := by
    by_cases small : 32*e ≤ Nat.fib m
    · have hp : 2*8^m < 64^s := by
        calc
          _ = 2^(3*m+1) := by rw [pow_succ, pow_mul]; ring
          _ < 2^(6*s) := Nat.pow_lt_pow_right (by decide) (by dsimp [s]; omega)
          _ = 64^s := by rw [pow_mul]; rfl
      calc
        _ < 64^s * e^s := Nat.mul_lt_mul_of_pos_right hp (pow_pos hepos _)
        _ = (64*e)^s := (mul_pow _ _ _).symm
        _ ≤ (2*Nat.fib (n+1))^s := Nat.pow_le_pow_left (by omega) _
        _ ≤ _ := Nat.le_mul_of_pos_right _ (Nat.factorial_pos _)
    · have hbig : 2*Nat.fib (m-10)<e := by
        have hform : (m-11)+10+1=m := by omega
        have hh := Nat.fib_add (m-11) 10
        rw [hform, show m-11+1=m-10 by omega] at hh
        have h89 : Nat.fib (10+1) = 89 := by decide
        rw [h89] at hh
        omega
      have hk : m-11 ≤ k := by
        apply count_prefix _ _ _ (by omega)
        intro j hj
        simp only [finite_fib, decide_eq_true_eq]
        exact lt_of_le_of_lt (Nat.mul_le_mul_left 2 (Nat.fib_mono (by omega))) hbig
      have hfac := Nat.factorial_le hk
      -- At large orders all of F_1,...,F_(m-10) are strictly below e.
      have hpre : m-11 ≤ s := by
        apply count_prefix _ _ _ (by omega)
        intro j hj
        have hl : Nat.fib (j+1) ≤ Nat.fib (m-10) := Nat.fib_mono (by omega)
        have hp : 0<Nat.fib (j+1) := Nat.fib_pos.mpr (by omega)
        simp [finite_fib, Nat.mod_eq_of_lt (by omega : Nat.fib (j+1)<e), Nat.ne_of_gt hp]
      calc
        _ < (2^(m-11)*(m-11).factorial)*e^s :=
          Nat.mul_lt_mul_of_pos_right (factorial_threshold m hm) (pow_pos hepos _)
        _ ≤ (2^s * k.factorial)*e^s := Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.pow_le_pow_right (by decide : 0<2) hpre) hfac)
        _ = (2*e)^s*k.factorial := by rw [mul_pow]; ring
        _ ≤ _ := by gcongr; omega
  exact lt_of_le_of_lt (Nat.mul_le_mul_right _ htot) key

/-- All orders in all non-direct dimensions, with the finite branch
    explicitly using the divisor certificate from QFibFinite. -/
theorem all_order_bounds (m n e : ℕ) (hm : 4≤m) (hmn : m≤n)
    (hn : 11≤n) (ho : PossibleOrder m e) : OrderInequality m n e := by
  by_cases hs : m<40
  · exact finite_cutoff m n e hm hs (by omega) ho
  · exact large_order_cutoff m n e (by omega) hmn ho

#print axioms large_order_cutoff
#print axioms all_order_bounds
end QFib
