import QFibSpecialization

open Polynomial Finset
open scoped BigOperators Polynomial
namespace QFib.Roots

noncomputable def lengths (s : Finset ℕ) (n : ℕ) : ℝ :=
  ∏ j ∈ s, (Nat.fib (n+j+1):ℝ)

noncomputable def chords (s : Finset ℕ) (n : ℕ) (z : ℂ) : ℝ :=
  ∏ j ∈ s, ‖1-z^Nat.fib (n+j+1)‖

theorem lengths_pos (s : Finset ℕ) (n : ℕ) : 0<lengths s n := by
  apply prod_pos
  intro j _
  exact_mod_cast (show 0<Nat.fib (n+j+1) by simp)

theorem chord_upper (s : Finset ℕ) (n : ℕ) {z : ℂ} (hz : ‖z‖=1) : chords s n z≤2^s.card := by
  calc
    _ ≤ ∏ _j ∈ s, (2:ℝ) := by
      apply Finset.prod_le_prod (fun j _ => norm_nonneg _)
      intro j _
      have hh := norm_sub_le (1:ℂ) (z^Nat.fib (n+j+1))
      simpa [norm_pow,hz,one_add_one_eq_two] using hh
    _ = _ := by simp

theorem chord_lower (a e b : ℕ) {z : ℂ} (ep : 0<e) (cop : b.Coprime e)
    (hzb : (baseRoot e)^b=z) :
    let D := live e 0 (a+1)
    (4:ℝ)^D.card*(QFibFinite.kCount (a+4) e).factorial ≤
      (e:ℝ)^D.card*chords D 0 z := by
  let D := live e 0 (a+1)
  let dist := fun j => distance e (b*Nat.fib (j+1))
  dsimp only
  have ep' : (0:ℝ)<e := by exact_mod_cast ep
  have df : ((QFibFinite.kCount (a+4) e).factorial:ℝ) ≤ ∏ j ∈ D, (dist j:ℝ) := by
    exact_mod_cast factorial_gain a e b ep cop
  calc
    _ ≤ (4:ℝ)^D.card*(∏ j ∈ D, (dist j:ℝ)) := mul_le_mul_of_nonneg_left df (by positivity)
    _ = ∏ j ∈ D, 4*(dist j:ℝ) := by simp [prod_mul_distrib]
    _ ≤ ∏ j ∈ D, (e:ℝ)*‖1-z^Nat.fib (j+1)‖ := by
      apply Finset.prod_le_prod (fun j _ => by positivity)
      intro j _
      have h := (div_le_iff₀ ep').mp (chord_distance ep (b*Nat.fib (j+1)))
      rw [pow_mul,hzb] at h
      simpa [dist,mul_comm] using h
    _ = _ := by simp [chords,D,prod_mul_distrib]

/-- The root-of-unity bound, with the original verifier's exact multiplicities. -/
theorem normalized_bound (a n e : ℕ) {z : ℂ} (ep : 0<e) (hz : IsPrimitiveRoot z e)
    (rank : ∃ r, ∀ j, e∣Nat.fib j ↔ r∣j) :
    ‖(normPoly (a+1) n).eval z‖*
      (2*(Nat.fib (n+1):ℝ))^(QFibFinite.sCount (a+4) e)*
      (QFibFinite.kCount (a+4) e).factorial ≤ (e:ℝ)^(QFibFinite.sCount (a+4) e) := by
  letI : NeZero e := ⟨ep.ne'⟩
  let D := live e 0 (a+1)
  let N := live e n (a+1)
  let q := ‖(normPoly (a+1) n).eval z‖
  let k := QFibFinite.kCount (a+4) e
  have hnq : 0≤q := norm_nonneg _
  obtain ⟨r,hr⟩ := rank
  obtain ⟨b,-,cop,hb⟩ := (IsPrimitiveRoot.isPrimitiveRoot_iff
    (show IsPrimitiveRoot (baseRoot e) e from Complex.isPrimitiveRoot_exp e ep.ne')).mp hz
  rcases specialization ep hz hr n (a+1) with h₀ | ⟨hc,heq⟩
  · simp [h₀]
  · change D.card=N.card at hc
    have hdn := chord_lower a e b ep cop hb
    have hnu := chord_upper N n (unit_norm ep hz.pow_eq_one)
    rw [←hc] at hnu
    have hg : (Nat.fib (n+1):ℝ)^D.card*lengths D 0≤lengths N n := by
      dsimp only [lengths]
      simp only [zero_add]
      exact_mod_cast growth_weights e n (a+1) r hr hc
    have ed := reg_norm ep hz.pow_eq_one 0 (a+1)
    have en := reg_norm ep hz.pow_eq_one n (a+1)
    rw [Finset.prod_div_distrib] at ed en
    change _=chords D 0 z/lengths D 0 at ed
    change _=chords N n z/lengths N n at en
    rw [ed,en] at heq
    change q*(chords D 0 z/lengths D 0)=chords N n z/lengths N n at heq
    have hlD := lengths_pos D 0
    have hlN := lengths_pos N n
    have hid : q*(chords D 0 z)*lengths N n=chords N n z*lengths D 0 := by
      field_simp at heq
      linear_combination heq
    rw [←card_s]
    change q*(2*(Nat.fib (n+1):ℝ))^D.card*k.factorial≤(e:ℝ)^D.card
    have hpos : 0<lengths D 0*(2:ℝ)^D.card := by positivity
    apply le_of_mul_le_mul_of_pos_right _ hpos
    calc
      _ = q*((4:ℝ)^D.card*k.factorial)*((Nat.fib (n+1):ℝ)^D.card*lengths D 0) := by
        rw [show (4:ℝ)=2*2 by norm_num,mul_pow,mul_pow]; ring
      _ ≤ q*((e:ℝ)^D.card*chords D 0 z)*lengths N n := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hdn hnq) hg (by positivity)
        exact mul_nonneg hnq (mul_nonneg (by positivity) (Finset.prod_nonneg (fun _ _ => norm_nonneg _)))
      _ = (e:ℝ)^D.card*(chords N n z*lengths D 0) := by rw [←hid]; ring
      _ ≤ _ := by
        calc
          _ ≤ (e:ℝ)^D.card*((2:ℝ)^D.card*lengths D 0) := by gcongr
          _ = _ := by ring

/-- Apply the certified order inequality at the actual order of each root. -/
theorem root_bound (a n : ℕ) (hmn : a+4≤n) (hn : 11≤n)
    {U : ℕ} (hU : U∈[Central.u a,Central.v a,Central.w a])
    {z : ℂ} (hmem : z∈rootsExceptOne U) :
    ‖(complexPoly (a+1) n).eval z‖ ≤
      (((poly (a+1) n).eval 1:ℤ):ℝ)/(2*(Central.u a:ℝ)*Central.v a*Central.w a*Central.w a) := by
  have hUs : U=Central.u a ∨ U=Central.v a ∨ U=Central.w a := by simpa using hU
  have hp : 0<U := by rcases hUs with rfl|rfl|rfl <;> exact Nat.fib_pos.mpr (by omega)
  have hm := (mem_except hp).mp hmem
  let e := orderOf z
  have ep : 0<e := orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨U,hp,hm.2⟩)
  have e1 : 1<e := by
    have ne : e≠1 := fun h => hm.1 (orderOf_eq_one_iff.mp h)
    omega
  have dd : e∣U := orderOf_dvd_of_pow_eq_one hm.2
  have ho : PossibleOrder (a+4) e := by
    refine ⟨e1,?_⟩
    rcases hUs with rfl|rfl|rfl
    · exact Or.inl (by simpa using dd)
    · exact Or.inr (Or.inl (by simpa using dd))
    · exact Or.inr (Or.inr dd)
  obtain ⟨r,-,rank⟩ := rank_for_order (a+4) e (by omega) ho
  have qb := normalized_bound a n e ep (IsPrimitiveRoot.orderOf z) ⟨r,rank⟩
  have cutoff := all_order_bounds (a+4) n e (by omega) hmn hn ho
  let K := 2*(Central.u a:ℝ)*Central.v a*Central.w a*Central.w a
  let s := QFibFinite.sCount (a+4) e
  let t := (2*(Nat.fib (n+1):ℝ))^s*(QFibFinite.kCount (a+4) e).factorial
  have hcu : K*(e:ℝ)^s<t := by
    dsimp only [K,t,s]
    exact_mod_cast (show 2*Central.u a*Central.v a*Central.w a*Central.w a*e^s <
      (2*Nat.fib (n+1))^s*(QFibFinite.kCount (a+4) e).factorial from by simpa [OrderInequality] using cutoff)
  have hk : 0<K := by
    have hp (j:ℕ) : (0:ℝ)<Nat.fib (a+j+1) := by exact_mod_cast (show 0<Nat.fib (a+j+1) by simp)
    exact mul_pos (mul_pos (mul_pos (mul_pos (by norm_num) (hp 1)) (hp 2)) (hp 3)) (hp 3)
  have ht : 0<t := lt_of_lt_of_le (mul_pos hk (pow_pos (by exact_mod_cast ep) s)) hcu.le
  have hnorm : ‖(normPoly (a+1) n).eval z‖*K ≤ 1 := by
    apply le_of_mul_le_mul_of_pos_right _ ht
    calc
      _ = K*(‖(normPoly (a+1) n).eval z‖*(2*(Nat.fib (n+1):ℝ))^s*
            (QFibFinite.kCount (a+4) e).factorial) := by dsimp [t]; ring
      _ ≤ K*(e:ℝ)^s := mul_le_mul_of_nonneg_left qb hk.le
      _ ≤ _ := by simpa using hcu.le
  let v := (((poly (a+1) n).eval 1:ℤ):ℝ)
  have hv : 0<v := by dsimp only [v]; exact_mod_cast eval_poly_pos (a+1) n
  have hq := hnorm
  simp only [normPoly,eval_mul,eval_C,norm_mul,norm_inv,complex_one,Complex.norm_intCast] at hq
  change (|v|⁻¹*‖(complexPoly (a+1) n).eval z‖)*K ≤ 1 at hq
  rw [abs_of_pos hv] at hq
  apply (le_div_iff₀ hk).mpr
  change ‖(complexPoly (a+1) n).eval z‖*K≤v
  apply (le_of_mul_le_mul_of_pos_left (a:=v⁻¹) _ (inv_pos.mpr hv))
  simpa [mul_assoc,hv.ne'] using hq

#print axioms normalized_bound
#print axioms root_bound
end QFib.Roots
