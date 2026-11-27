import QFibResidues
import Mathlib.Data.Nat.ModEq

open Finset
open scoped BigOperators
namespace QFib.Roots

/-- Zero-based positions whose Fibonacci factor survives specialization. -/
def live (e n p : ℕ) := (range p).filter fun j => ¬ e ∣ Nat.fib (n+j+1)

theorem mem_live {e n p j : ℕ} :
    j∈live e n p ↔ j<p ∧ ¬e∣Nat.fib (n+j+1) := by simp [live]

theorem live_succ (e n p : ℕ) :
    live e n (p+1) = if e∣Nat.fib (n+p+1) then live e n p else insert p (live e n p) := by
  by_cases h : e∣Nat.fib (n+p+1) <;> simp [live,range_add_one,filter_insert,h]

theorem live_last (e n p : ℕ) : p∉live e n p := by simp [live]

/-- Counting zeros in an arbitrary interval of Fibonacci indices. -/
theorem live_count (e n p r : ℕ) (hr : ∀ j, e∣Nat.fib j ↔ r∣j) :
    (live e n p).card + (n+p)/r = p+n/r := by
  induction p with
  | zero => simp [live]
  | succ p ih =>
    rw [live_succ, show n+(p+1)=(n+p)+1 by omega, Nat.succ_div]
    by_cases h : r∣n+p+1
    · simp [h,(hr _).mpr h]; omega
    · simp [h,show ¬e∣Nat.fib (n+p+1) from fun hh => h ((hr _).mp hh),live_last]; omega

theorem live_count_le (e n p r : ℕ) (hr : ∀ j, e∣Nat.fib j ↔ r∣j) :
    (live e n p).card ≤ (live e 0 p).card := by
  have hd := live_count e 0 p r hr
  have hn := live_count e n p r hr
  simp only [zero_add,Nat.zero_div,add_zero] at hd
  have := Nat.add_div_le_add_div n p r
  omega

/-- Prefix dominance of survivor positions, expressed as a product inequality.
    The temporary excess of denominator positions is charged at the largest
    Fibonacci number seen in that prefix. -/
theorem live_weights (e n p r : ℕ) (hr : ∀ j, e∣Nat.fib j ↔ r∣j) :
    (∏ j ∈ live e 0 p, Nat.fib (j+1)) ≤ (∏ j ∈ live e n p, Nat.fib (j+1))*
      Nat.fib p^((live e 0 p).card-(live e n p).card) := by
  induction p with
  | zero => simp [live]
  | succ p ih =>
    let D := live e 0 p
    let N := live e n p
    let f := Nat.fib (p+1)
    have hf : Nat.fib p≤f := Nat.fib_le_fib_succ
    have step : (∏ j ∈ D, Nat.fib (j+1)) ≤ (∏ j ∈ N, Nat.fib (j+1))*f^(D.card-N.card) :=
      ih.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hf _))
    have h₀ : N.card≤D.card := live_count_le e n p r hr
    have h₁ := live_count_le e n (p+1) r hr
    rw [live_succ, live_succ] at h₁ ⊢
    simp only [zero_add] at h₁ ⊢
    have nd : p∉D := live_last e 0 p
    have nn : p∉N := live_last e n p
    change (if _ then D else insert p D).card ≥ (if _ then N else insert p N).card at h₁
    change (∏ j ∈ (if _ then D else insert p D), Nat.fib (j+1)) ≤
      (∏ j ∈ (if _ then N else insert p N), Nat.fib (j+1))*f^(
        (if e∣Nat.fib (p+1) then D else insert p D).card -
        (if e∣Nat.fib (n+p+1) then N else insert p N).card)
    by_cases hd : e∣Nat.fib (p+1) <;> by_cases hn : e∣Nat.fib (n+p+1) <;>
      simp only [hd,hn,if_true,if_false,card_insert_of_notMem nd,card_insert_of_notMem nn,
        prod_insert nd,prod_insert nn] at h₁ ⊢
    · exact step
    · rw [show D.card-N.card=(D.card-(N.card+1))+1 by omega,pow_succ] at step
      simpa [f,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using step
    · rw [show D.card+1-N.card=(D.card-N.card)+1 by omega,pow_succ]
      simpa [f,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using Nat.mul_le_mul_left f step
    · simpa [f,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using Nat.mul_le_mul_left f step

theorem growth_weights (e n p r : ℕ) (hr : ∀ j, e∣Nat.fib j ↔ r∣j)
    (hc : (live e 0 p).card=(live e n p).card) :
    Nat.fib (n+1)^(live e 0 p).card*(∏ j ∈ live e 0 p, Nat.fib (j+1)) ≤
      ∏ j ∈ live e n p, Nat.fib (n+j+1) := by
  have hh := live_weights e n p r hr
  rw [hc,Nat.sub_self,pow_zero,mul_one] at hh
  calc
    _ ≤ Nat.fib (n+1)^(live e n p).card*(∏ j ∈ live e n p, Nat.fib (j+1)) := by
      rw [hc]; exact Nat.mul_le_mul_left _ hh
    _ = ∏ j ∈ live e n p, Nat.fib (n+1)*Nat.fib (j+1) := by simp [prod_mul_distrib]
    _ ≤ _ := by
      apply Finset.prod_le_prod'
      intro j _
      rw [Nat.fib_add n j]
      omega

theorem list_card (p : ℕ) (f : ℕ → Bool) :
    ((List.range p).filter f).length = ((range p).filter fun j => f j = true).card := by
  induction p with
  | zero => simp
  | succ p ih =>
    have hp : p∉(range p).filter (fun j => f j=true) := by simp
    rw [List.range_succ,List.filter_append,List.length_append,Finset.range_add_one,filter_insert]
    cases h : f p <;> simp [h,ih,hp]

theorem card_s (a e : ℕ) : (live e 0 (a+1)).card=QFibFinite.sCount (a+4) e := by
  simp only [QFibFinite.sCount,show a+4-3=a+1 by omega,list_card,live,zero_add,finite_fib]
  congr 1
  ext j
  simp [Nat.dvd_iff_mod_eq_zero]

def smalls (a e : ℕ) := (range a).filter fun j => 2*Nat.fib (j+2)<e

theorem card_k (a e : ℕ) : (smalls a e).card=QFibFinite.kCount (a+4) e := by
  simp [smalls,QFibFinite.kCount,list_card,finite_fib]

theorem factorial_gain (a e b : ℕ) (ep : 0<e) (cop : b.Coprime e) :
    (QFibFinite.kCount (a+4) e).factorial ≤
      ∏ j ∈ live e 0 (a+1), distance e (b*Nat.fib (j+1)) := by
  classical
  let f := fun j => distance e (b*Nat.fib (j+2))
  let S := smalls a e
  have key {j : ℕ} (hj : j∈S) : j<a ∧ 2*Nat.fib (j+2)<e := by simpa [S,smalls] using hj
  have liveS {j : ℕ} (hj : j∈S) : j+1∈live e 0 (a+1) := by
    have h := key hj
    have hp : 0<Nat.fib (j+2) := by simp
    apply mem_live.mpr ⟨by omega,?_⟩
    simp only [zero_add]; exact fun he => by have := Nat.le_of_dvd hp he; omega
  have inj : Set.InjOn f S := by
    intro x hx y hy hh
    exact Nat.fib_add_two_strictMono.injective (distance_injective ep cop (by simp) (by simp)
      (key hx).2 (key hy).2 hh)
  have pos {j : ℕ} (h : j∈live e 0 (a+1)) : 0<distance e (b*Nat.fib (j+1)) := by
    apply distance_pos ep cop
    simpa only [zero_add] using (mem_live.mp h).2
  have fac := factorial_le_distinct_product (S.image f) (by
    intro j hj; obtain ⟨t,ht,rfl⟩ := mem_image.mp hj; exact pos (liveS ht))
  rw [card_image_of_injOn inj, Finset.prod_image inj] at fac
  rw [←card_k]
  apply fac.trans
  let Z := S.image (fun j => j+1)
  have sub : Z ⊆ live e 0 (a+1) := by
    intro j hj; obtain ⟨t,ht,rfl⟩ := mem_image.mp hj; exact liveS ht
  have hpr : (∏ j ∈ S, f j) = ∏ j ∈ Z, distance e (b*Nat.fib (j+1)) := by
    rw [Finset.prod_image (by intro x _ y _ hh; exact Nat.succ.inj hh)]
  rw [hpr]
  exact Finset.prod_le_prod_of_subset_of_one_le' sub (fun j hj _ => pos hj)

#print axioms growth_weights
#print axioms factorial_gain
end QFib.Roots
