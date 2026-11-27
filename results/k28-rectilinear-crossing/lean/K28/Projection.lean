import K28.Incidence

namespace K28.Projection

/-- Relative order under projection onto the vector (-s,1). As s runs
from negative to positive infinity this describes an open half-turn. -/
def value (s : ℝ) (a : Point ℝ) : ℝ := a.2 - s*a.1
noncomputable def event (a b : Point ℝ) : ℝ := (b.2-a.2)/(b.1-a.1)

theorem difference (s : ℝ) (a b : Point ℝ) (dx : b.1 ≠ a.1) :
    value s b - value s a = (b.1-a.1)*(event a b-s) := by
  unfold event value
  field_simp [sub_ne_zero.mpr dx]
  ring

theorem passes_right (s : ℝ) (a b : Point ℝ) (dx : a.1 < b.1) :
    (value s a < value s b ↔ s < event a b) ∧
    (value s a = value s b ↔ s = event a b) ∧
    (value s b < value s a ↔ event a b < s) := by
  have h := difference s a b dx.ne'
  have pos := sub_pos.mpr dx
  constructor
  · rw [←sub_pos, h, mul_pos_iff_of_pos_left pos, sub_pos]
  constructor
  · rw [eq_comm, ←sub_eq_zero,h,mul_eq_zero]
    simp only [ne_of_gt pos,false_or,sub_eq_zero]
    exact eq_comm
  · rw [←sub_neg,h,mul_neg_iff]
    simp [pos,pos.not_gt,sub_neg]

theorem tie (a b : Point ℝ) (dx : a.1 ≠ b.1) :
    value (event a b) a = value (event a b) b := by
  have h := difference (event a b) a b dx.symm
  rw [sub_self,mul_zero] at h
  exact (sub_eq_zero.mp h).symm

/-- Signed side of the line a,b equals its signed projection displacement
multiplied by the horizontal coordinate difference at the swap. -/
theorem side_at_event (a b c : Point ℝ) (dx : a.1 ≠ b.1) :
    (b.1-a.1)*(value (event a b) c - value (event a b) a) = orient a b c := by
  unfold value event orient
  field_simp [sub_ne_zero.mpr dx.symm]
  ring

/-- Each X label passes every Y label before every Z label. -/
theorem event_order (a b c : Point ℝ) (ab : a.1 < b.1) (ac : a.1 < c.1) :
    event a b < event a c ↔ 0 < orient a b c := by
  unfold event orient
  rw [div_lt_div_iff₀ (sub_pos.mpr ab) (sub_pos.mpr ac)]
  constructor <;> intro h <;> linarith only [h]

/-- At the XY event all Z points lie to the right; at XZ all Y
points lie to the left. Each conclusion holds for every transversal. -/
theorem other_group_at_event (a b c : Point ℝ) (ab : a.1 < b.1) (ac : a.1 < c.1)
    (ccw : 0 < orient a b c) :
    value (event a b) a < value (event a b) c ∧
    value (event a c) b < value (event a c) a := by
  have order := (event_order a b c ab ac).mpr ccw
  exact ⟨((passes_right _ a c ac).1).mpr order,((passes_right _ a b ab).2.2).mpr order⟩

/-- Every X point is on the same side of a YZ event, including when
the horizontal order of its two endpoints is reversed. -/
theorem common_side (b c a a' : Point ℝ) (dx : b.1 ≠ c.1)
    (pos : 0 < orient b c a) (pos' : 0 < orient b c a') :
    0 < (value (event b c) a - value (event b c) b) *
        (value (event b c) a' - value (event b c) b) := by
  have q := side_at_event b c a dx
  have q' := side_at_event b c a' dx
  have h : 0 < ((c.1-b.1)^2) *
      ((value (event b c) a-value (event b c) b)*(value (event b c) a'-value (event b c) b)) := by
    calc _ < orient b c a * orient b c a' := mul_pos pos pos'
         _ = _ := by rw [←q,←q']; ring
  exact (mul_pos_iff_of_pos_left (sq_pos_of_ne_zero (sub_ne_zero.mpr dx.symm))).mp h

end K28.Projection
