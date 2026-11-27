import QFibRoots
import QFibAnalytic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

open Polynomial Finset
open scoped Polynomial BigOperators
namespace QFib.Roots

theorem mem_except {u : ℕ} (hu : 0<u) {z : ℂ} :
    z ∈ rootsExceptOne u ↔ z ≠ 1 ∧ z^u=1 := by
  classical
  simp [rootsExceptOne,mem_nthRootsFinset hu]

private theorem common_root {u v : ℕ} {z : ℂ} (h : u.Coprime v)
    (hu : z^u=1) (hv : z^v=1) : z=1 := by
  apply orderOf_eq_one_iff.mp
  apply Nat.dvd_one.mp
  rw [←h.gcd_eq_one]
  exact Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hu) (orderOf_dvd_of_pow_eq_one hv)

theorem powered_inverse_square_sum {u v : ℕ} (hu : 0<u) (h : u.Coprime v) :
    (∑ z ∈ rootsExceptOne u, (‖1-z^v‖^2)⁻¹) = ((u:ℝ)^2-1)/12 := by
  classical
  let s := rootsExceptOne u
  have inj : Set.InjOn (fun z : ℂ => z^v) (s : Set ℂ) := by
    intro x hx y hy hxy
    change x^v=y^v at hxy
    have hx' := (mem_except hu).mp hx
    have hy' := (mem_except hu).mp hy
    have hyn : y≠0 := by intro he; simp [he, hu.ne'] at hy'
    have h₁ : (x/y)^u=1 := by rw [div_pow,hx'.2,hy'.2,div_one]
    have h₂ : (x/y)^v=1 := by rw [div_pow,hxy,div_self (pow_ne_zero _ hyn)]
    exact (div_eq_one_iff_eq hyn).mp (common_root h h₁ h₂)
  have him : s.image (fun z : ℂ => z^v)=s := by
    apply eq_of_subset_of_card_le _ (le_of_eq (card_image_of_injOn inj).symm)
    intro y hy
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hy
    have hz' := (mem_except hu).mp hz
    apply (mem_except hu).mpr
    refine ⟨fun he => hz'.1 (common_root h hz'.2 he), ?_⟩
    rw [← pow_mul,mul_comm,pow_mul,hz'.2,one_pow]
  calc
    _ = ∑ z ∈ s.image (fun z : ℂ => z^v), (‖1-z‖^2)⁻¹ := (Finset.sum_image inj).symm
    _ = _ := by rw [him]; exact inverse_square_sum u hu

/-- Simple-pole contribution, with the three retained numerator monomials
    and the evaluation of the smaller polynomial included. -/
noncomputable def residue (u v w b c i : ℕ) (q : ℂ[X]) (z : ℂ) : ℂ :=
  (1-z)*(1-z^c-z^b)*q.eval z*(z⁻¹)^i /
    ((u:ℂ)*(1-z^v)*(1-z^w))

theorem residue_sum_norm {u v w : ℕ} (hu : 0<u) (cop : u.Coprime v)
    (equalNorm : ∀ z ∈ rootsExceptOne u, ‖1-z^w‖=‖1-z^v‖)
    (b c i : ℕ) (q : ℂ[X]) (K : ℝ) (hK : 0≤K)
    (hq : ∀ z ∈ rootsExceptOne u, ‖q.eval z‖≤K) :
    ‖∑ z ∈ rootsExceptOne u, residue u v w b c i q z‖ ≤ (u:ℝ)*K/2 := by
  let s := rootsExceptOne u
  have up : (0:ℝ)<u := by exact_mod_cast hu
  calc
    _ ≤ ∑ z ∈ s, ‖residue u v w b c i q z‖ := norm_sum_le _ _
    _ ≤ ∑ z ∈ s, (6*K/(u:ℝ))*(‖1-z^v‖^2)⁻¹ := by
      apply sum_le_sum
      intro z hz
      have hr := (mem_except hu).mp hz
      have hz1 := unit_norm hu hr.2
      have hnorm (j : ℕ) : ‖z^j‖=1 := by simp [hz1]
      have hzn : ‖1-z‖≤2 := by have hh := norm_sub_le (1:ℂ) z; rw [norm_one,hz1] at hh; linarith
      have hnum : ‖1-z^c-z^b‖≤3 := by
        have h₁ := norm_sub_le (1:ℂ) (z^c)
        have h₂ := norm_sub_le (1-z^c) (z^b)
        rw [hnorm,norm_one] at h₁
        rw [hnorm] at h₂
        linarith
      have hs := equalNorm z hz
      have hqn := hq z hz
      simp only [residue,norm_div,norm_mul,norm_pow,norm_inv,hz1,inv_one,one_pow,
        mul_one,Complex.norm_natCast, hs]
      calc
        _ ≤ (2*3*K) / ((u:ℝ)*‖1-z^v‖*‖1-z^v‖) := by gcongr
        _ = _ := by ring
    _ = (6*K/(u:ℝ))*(((u:ℝ)^2-1)/12) := by rw [←Finset.mul_sum, powered_inverse_square_sum hu cop]
    _ ≤ _ := by
      field_simp
      nlinarith

theorem norm_inverse {x : ℂ} (hx : ‖x‖=1) : ‖1-x⁻¹‖=‖1-x‖ := by
  have h : x≠0 := by intro hh; simp [hh] at hx
  rw [show (1-x⁻¹)=(x-1)/x by field_simp, norm_div,hx,div_one,norm_sub_rev]

theorem three_residues (a n i : ℕ) (q : ℂ[X]) (K : ℝ) (hK : 0≤K)
    (hq : ∀ U ∈ [Central.u a, Central.v a, Central.w a],
      ∀ z∈rootsExceptOne U, ‖q.eval z‖≤K) :
    let u := Central.u a
    let v := Central.v a
    let w := Central.w a
    let R := fun U V W => ∑ z ∈ rootsExceptOne U, residue U V W (Central.B a n) (Central.C a n) i q z
    ‖R u v w + R v w u + R w u v‖ ≤ (w:ℝ)*K := by
  let u := Central.u a
  let v := Central.v a
  let w := Central.w a
  let R := fun U V W => ∑ z ∈ rootsExceptOne U, residue U V W (Central.B a n) (Central.C a n) i q z
  change ‖R u v w + R v w u + R w u v‖ ≤ (w:ℝ)*K
  have hup : 0<u := Nat.fib_pos.mpr (by omega)
  have hvp : 0<v := Nat.fib_pos.mpr (by omega)
  have hwp : 0<w := Nat.fib_pos.mpr (by omega)
  have hw : w=u+v := Nat.fib_add_two
  have huv : u.Coprime v := Nat.fib_coprime_fib_succ _
  have hvw : v.Coprime w := Nat.fib_coprime_fib_succ _
  have hwu : w.Coprime u := by simpa [hw, Nat.coprime_add_self_left] using huv.symm
  have h₁ : ‖R u v w‖ ≤ (u:ℝ)*K/2 := by
    apply residue_sum_norm hup huv _ _ _ _ _ _ hK (hq u (by simp [u]))
    intro z hz
    rw [hw,pow_add,((mem_except hup).mp hz).2,one_mul]
  have h₂ : ‖R v w u‖ ≤ (v:ℝ)*K/2 := by
    apply residue_sum_norm hvp hvw _ _ _ _ _ _ hK (hq v (by simp [v]))
    intro z hz
    rw [hw,pow_add,((mem_except hvp).mp hz).2,mul_one]
  have h₃ : ‖R w u v‖ ≤ (w:ℝ)*K/2 := by
    apply residue_sum_norm hwp hwu _ _ _ _ _ _ hK (hq w (by simp [w]))
    intro z hz
    have hp := ((mem_except hwp).mp hz).2
    have hm := unit_norm hwp hp
    have hn : z≠0 := by intro h; simp [h,hwp.ne'] at hp
    rw [hw,pow_add] at hp
    have he : z^v=(z^u)⁻¹ := by apply mul_left_cancel₀ (pow_ne_zero u hn); simpa [hn] using hp
    rw [he,norm_inverse (by simp [hm])]
  have hreal : (w:ℝ)=u+v := by exact_mod_cast hw
  have l₁ := norm_add_le (R u v w) (R v w u)
  have l₂ := norm_add_le (R u v w + R v w u) (R w u v)
  rw [hreal] at h₃ ⊢
  linarith

end QFib.Roots
