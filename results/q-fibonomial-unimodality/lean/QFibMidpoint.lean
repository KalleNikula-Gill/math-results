import QFibTruncate
import QFibFamilies

open Polynomial Finset
open scoped Polynomial BigOperators
namespace QFib
noncomputable def complexPoly (m n : ℕ) := (poly m n).map (Int.castRingHom ℂ)

@[simp] theorem complex_one (m n : ℕ) :
    (complexPoly m n).eval 1 = (((poly m n).eval 1:ℤ):ℂ) := by
  simp [complexPoly,eval_map]

theorem complex_moment (m n : ℕ) :
    2*(complexPoly m n).derivative.eval 1 =
    ((poly m n).natDegree:ℂ)*(complexPoly m n).eval 1 := by
  let p := poly m n
  have he : p.derivative.eval 1 = ∑ j ∈ range (p.natDegree+1), (j:ℤ)*p.coeff j := by
    rw [derivative_eval, sum_over_range' _ _ (p.natDegree+1) (by omega)]
    · simp [mul_comm]
    · simp
  simp only [complexPoly,derivative_map,eval_map,eval₂_at_one,Int.coe_castRingHom]
  exact_mod_cast (show 2*p.derivative.eval 1=(p.natDegree:ℤ)*p.eval 1 by rw [he]; exact moment m n)

namespace Central
noncomputable def short (a n : ℕ) : ℂ[X] := (1-X^C a n-X^B a n)*complexPoly (a+1) n
noncomputable def full (a n : ℕ) : ℂ[X] :=
  (1-X^C a n)*(1-X^B a n)*(1-X^A a n)*complexPoly (a+1) n

theorem short_trunc (a n i : ℕ) (hl : B a n+T a n≤ i) (hu : i<A a n+C a n) :
    Roots.trunc (full a n) i = short a n := by
  have cb : C a n≤B a n := Nat.fib_le_fib_succ
  have d1 : (1-X^C a n : ℂ[X]).natDegree ≤ B a n := by
    exact (natDegree_sub_le ..).trans (max_le (by simp) (by simpa using cb))
  have d2 : (1-X^C a n-X^B a n : ℂ[X]).natDegree ≤ B a n := by
    exact (natDegree_sub_le ..).trans (max_le d1 (by simp))
  apply Roots.trunc_eq
  · exact (natDegree_mul_le ..).trans ((Nat.add_le_add d2 (natDegree_map_le ..)).trans hl)
  · intro j hj
    have h := congrArg (Int.castRingHom ℂ) (truncate_numerators a n j (by omega) (poly (a+1) n))
    rw [← coeff_map, ← coeff_map] at h
    simpa only [full,short,complexPoly,Polynomial.map_mul,Polynomial.map_sub,Polynomial.map_one,
      Polynomial.map_pow,Polynomial.map_X] using h

theorem full_identity (a n : ℕ) :
    (X-1)*((X-1)*((Roots.geom (u a)*Roots.geom (v a)*Roots.geom (w a))*
      ((delta (a+4) n).map (Int.castRingHom ℂ)))) = full a n := by
  have h := congrArg (Polynomial.map (Int.castRingHom ℂ)) (three_factors a n)
  simp only [Polynomial.map_mul,Polynomial.map_sub,Polynomial.map_one,
    Polynomial.map_pow,Polynomial.map_X] at h
  unfold full complexPoly
  rw [←h]
  simp only [delta,Polynomial.map_mul,Polynomial.map_sub,Polynomial.map_one,Polynomial.map_X]
  have hg (k : ℕ) : Roots.geom k*(1-X) = 1-X^k := geom_sum_mul_neg (X:ℂ[X]) k
  rw [←hg,←hg,←hg]
  ring

theorem short_value (a n : ℕ) (z : ℂ) :
    (short a n).eval z = (1-z^C a n-z^B a n)*(complexPoly (a+1) n).eval z := by
  simp [short]

theorem short_derivative (a n : ℕ) :
    (short a n).derivative.eval 1 = -(A a n:ℂ)*(complexPoly (a+1) n).eval 1 -
      (complexPoly (a+1) n).derivative.eval 1 := by
  have he : (A a n:ℂ)=(C a n:ℂ)+B a n := by exact_mod_cast (show A a n=C a n+B a n from Nat.fib_add_two)
  simp [short,derivative_mul,derivative_X_pow,he]
  ring

noncomputable def remainder (a n i : ℕ) : ℂ :=
  let R := fun U V W => ∑ z ∈ Roots.rootsExceptOne U,
    Roots.residue U V W (B a n) (C a n) i (complexPoly (a+1) n) z
  R (u a) (v a) (w a) + R (v a) (w a) (u a) + R (w a) (u a) (v a)

private theorem cyclic_sum {u v w : ℕ} (hu : 0<u) (hv : 0<v) (hw : 0<w)
    (huv : u.Coprime v) (hwu : w.Coprime u) (s : Finset ℂ) (hin : Roots.rootsExceptOne u ⊆ s)
    (hf : Roots.linearProduct s=Roots.geom u*Roots.geom v*Roots.geom w)
    (a n i : ℕ) :
    ∑ z ∈ Roots.rootsExceptOne u, (-Roots.poleCoeff s z/z)*(short a n).eval z*(z⁻¹)^i =
    ∑ z ∈ Roots.rootsExceptOne u, Roots.residue u v w (B a n) (C a n) i (complexPoly (a+1) n) z := by
  apply sum_congr rfl
  intro z hz
  have hz1 := ((Roots.mem_except hu).mp hz).1
  have hV : z^v≠1 := fun h => (disjoint_left.mp (Roots.roots_disjoint hu hv huv)) hz
    ((Roots.mem_except hv).mpr ⟨hz1,h⟩)
  have hW : z^w≠1 := fun h => (disjoint_left.mp (Roots.roots_disjoint hu hw hwu.symm)) hz
    ((Roots.mem_except hw).mpr ⟨hz1,h⟩)
  rw [Roots.simple_pole_value hu hf (hin hz) hz hV hW, short_value,Roots.residue]
  ring

/-- Exact complex formula for an actual integer coefficient difference. -/
theorem midpoint_formula (a n i : ℕ) (hn : a+4≤n)
    (hip : i ≤ d a n/2) (hil : d a n/2 < i+w a) :
    ((delta (a+4) n).coeff i:ℂ) =
    (complexPoly (a+1) n).eval 1*((d a n:ℂ)+1-2*i) /
      (2*(u a:ℂ)*v a*w a) + remainder a n i := by
  classical
  let s := Roots.totalRoots (u a) (v a) (w a)
  have hu : 0<u a := Nat.fib_pos.mpr (by omega)
  have hv : 0<v a := Nat.fib_pos.mpr (by omega)
  have hw : 0<w a := Nat.fib_pos.mpr (by omega)
  have hwb : w a=u a+v a := Nat.fib_add_two
  have huv : (u a).Coprime (v a) := Nat.fib_coprime_fib_succ _
  have hvw : (v a).Coprime (w a) := Nat.fib_coprime_fib_succ _
  have hwu : (w a).Coprime (u a) := by simpa [hwb,Nat.coprime_add_self_left] using huv.symm
  have hf := Roots.totalProduct hu hv hw huv hvw hwu
  have ex (x : ℂ) (hx : x=0 ∨ x=1) : x∉s := by
    dsimp only [s,Roots.totalRoots]
    simp only [mem_union, Roots.mem_except hu,Roots.mem_except hv,Roots.mem_except hw]
    rcases hx with rfl|rfl <;> simp [hu.ne',hv.ne',hw.ne']
  have hdec := Roots.coefficient_decomposition s (ex 1 (Or.inr rfl)) (ex 0 (Or.inl rfl))
    ((delta (a+4) n).map (Int.castRingHom ℂ)) i
  dsimp only at hdec
  have ⟨hL,hU⟩ := central_support a n i hn hip hil
  have ht : Roots.trunc ((X-1)*((X-1)*(Roots.linearProduct s*
      ((delta (a+4) n).map (Int.castRingHom ℂ))))) i = short a n := by
    rw [show Roots.linearProduct s = _ from hf,full_identity,short_trunc a n i hL hU]
  rw [ht,coeff_map] at hdec
  change ((delta (a+4) n).coeff i:ℂ)=_ at hdec
  rw [hdec]
  congr 1
  · obtain ⟨d₀,d₁⟩ := Roots.total_values hu hv hw huv hvw hwu
    change (Roots.linearProduct s).eval 1 = _ at d₀
    change 2*(Roots.linearProduct s).derivative.eval 1 = _ at d₁
    have hu' : (u a:ℂ)≠0 := by exact_mod_cast hu.ne'
    have hv' : (v a:ℂ)≠0 := by exact_mod_cast hv.ne'
    have hw' : (w a:ℂ)≠0 := by exact_mod_cast hw.ne'
    have dm := complex_moment (a+1) n
    change 2*(complexPoly (a+1) n).derivative.eval 1=(T a n:ℂ)*_ at dm
    have dg : (d a n:ℂ)+2*w a=(T a n:ℂ)+2*A a n := by exact_mod_cast deg_full a n
    have wb : (w a:ℂ)=(u a:ℂ)+v a := by exact_mod_cast hwb
    have d₂ : (Roots.linearProduct s).derivative.eval 1=
        ((u a:ℂ)*v a*w a)*(u a+v a+w a-3)/2 := by linear_combination d₁/2
    have dm₂ : (complexPoly (a+1) n).derivative.eval 1=(T a n:ℂ)*(complexPoly (a+1) n).eval 1/2 := by linear_combination dm/2
    have dg₂ : (d a n:ℂ)=(T a n:ℂ)+2*A a n-2*w a := by linear_combination dg
    rw [d₀,d₂,short_derivative,short_value,dm₂,dg₂]
    simp only [one_pow,sub_self,zero_sub,neg_one_mul,neg_neg]
    field_simp [hu',hv',hw']
    rw [wb]
    ring
  · dsimp only [remainder,s,Roots.totalRoots]
    rw [sum_union (Finset.disjoint_union_left.mpr ⟨Roots.roots_disjoint hu hw hwu.symm,
      Roots.roots_disjoint hv hw hvw⟩),sum_union (Roots.roots_disjoint hu hv huv)]
    have su : Roots.rootsExceptOne (u a) ⊆ s := fun _ h => mem_union_left _ (mem_union_left _ h)
    have sv : Roots.rootsExceptOne (v a) ⊆ s := fun _ h => mem_union_left _ (mem_union_right _ h)
    have sw : Roots.rootsExceptOne (w a) ⊆ s := fun _ h => mem_union_right _ h
    exact congrArg₂ (·+·) (congrArg₂ (·+·)
      (cyclic_sum hu hv hw huv hwu s su hf a n i)
      (cyclic_sum hv hw hu hvw huv s sv (hf.trans (by ring)) a n i))
      (cyclic_sum hw hu hv hwu hvw s sw (hf.trans (by ring)) a n i)

#print axioms midpoint_formula
end Central
end QFib
