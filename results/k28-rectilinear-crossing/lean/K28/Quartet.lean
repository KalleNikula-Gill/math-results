import K28.Geometry

namespace K28

/-- Points on opposite open sides of the first pair's supporting line. -/
noncomputable def sep (a b c d : Point ℝ) : Nat := by
  classical
  exact if orient a b c * orient a b d < 0 then 1 else 0

private theorem cyc (a b c : Point ℝ) : orient b c a = orient a b c := by
  unfold orient
  ring
private theorem antisymm (a b c : Point ℝ) : orient a c b = -orient a b c := by
  unfold orient
  ring

private theorem sameSigns (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
    (0 < x*y) ↔ (decide (x<0) = decide (y<0)) := by
  rcases lt_or_gt_of_ne hx with hx | hx <;> rcases lt_or_gt_of_ne hy with hy | hy <;>
    simp [hx, hy, hx.not_gt, hy.not_gt, mul_pos_iff]

private theorem oppositeSigns (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
    (x*y < 0) ↔ (decide (x<0) ≠ decide (y<0)) := by
  rcases lt_or_gt_of_ne hx with hx | hx <;> rcases lt_or_gt_of_ne hy with hy | hy <;>
    simp [hx, hy, hx.not_gt, hy.not_gt, mul_neg_iff]

private theorem signCount (a b c d : Bool)
    (h : ¬ (a = c ∧ b = d ∧ a ≠ b)) :
    (if a ≠ b ∧ c ≠ d then 1 else 0) +
    (if a = c ∧ b = d then 1 else 0) +
    (if b ≠ c ∧ a ≠ d then 1 else 0) +
    ((if a ≠ b then 1 else 0) + (if c ≠ d then 1 else 0) +
     (if a = c then 1 else 0) + (if b = d then 1 else 0) +
     (if b ≠ c then 1 else 0) + (if a ≠ d then 1 else 0)) = (3:Nat) := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all

/-- On a quartet, crossing pairs plus choices of a line that strictly
separates the other two points total three. -/
theorem quartet_identity (a b c d : Point ℝ)
    (hx : orient a b c ≠ 0) (hy : orient a b d ≠ 0)
    (hz : orient a c d ≠ 0) (hw : orient b c d ≠ 0) :
    threeMatchings meetCost a b c d +
      (sep a b c d + sep c d a b + sep a c b d + sep b d a c +
       sep a d b c + sep b c a d) = 3 := by
  let x := orient a b c
  let y := orient a b d
  let z := orient a c d
  let w := orient b c d
  have lin : x + z = y + w := by dsimp [x,y,z,w,orient]; ring
  have signs : ¬(decide (x<0) = decide (z<0) ∧ decide (y<0) = decide (w<0) ∧
      decide (x<0) ≠ decide (y<0)) := by
    rintro ⟨h₁,h₂,h₃⟩
    by_cases ax : x<0 <;> by_cases ay : y<0 <;> by_cases az : z<0 <;> by_cases aw : w<0 <;>
      simp_all only [decide_true, decide_false, Bool.false_eq_true, Bool.true_eq_false] <;> first | contradiction | linarith
  have cd_a : orient c d a = z := cyc a c d
  have cd_b : orient c d b = w := cyc b c d
  have ac_b : orient a c b = -x := antisymm a b c
  have bd_a : orient b d a = y := cyc a b d
  have bd_c : orient b d c = -w := antisymm b c d
  have ad_b : orient a d b = -y := antisymm a b d
  have ad_c : orient a d c = -z := antisymm a c d
  have bc_a : orient b c a = x := cyc a b c
  unfold threeMatchings meetCost sep
  rw [interiorMeet_iff_straddle a b c d hx (cd_a ▸ hz),
      interiorMeet_iff_straddle a c b d (by rw [ac_b]; exact neg_ne_zero.mpr hx) (bd_a ▸ hy),
      interiorMeet_iff_straddle a d b c (by rw [ad_b]; exact neg_ne_zero.mpr hy) (bc_a ▸ hx)]
  simp only [Straddle, cd_a, cd_b, ac_b, bd_a, bd_c, ad_b, ad_c, bc_a, neg_mul, mul_neg,
    neg_neg, neg_lt_zero]
  change (if x*y<0 ∧ z*w<0 then 1 else 0) + (if 0<x*z ∧ 0<y*w then 1 else 0) +
    (if y*z<0 ∧ x*w<0 then 1 else 0) +
    ((if x*y<0 then 1 else 0) + (if z*w<0 then 1 else 0) +
     (if 0<x*z then 1 else 0) + (if 0<y*w then 1 else 0) +
     (if y*z<0 then 1 else 0) + (if x*w<0 then 1 else 0)) = 3
  simpa only [oppositeSigns x y hx hy, oppositeSigns z w hz hw, sameSigns x z hx hz,
    sameSigns y w hy hw, oppositeSigns y z hy hz, oppositeSigns x w hx hw] using
    (signCount (decide (x<0)) (decide (y<0)) (decide (z<0)) (decide (w<0)) signs)

end K28
