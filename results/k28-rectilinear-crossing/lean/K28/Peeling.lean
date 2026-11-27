import K28.Geometry

namespace K28

def trianglePoint (a b c : Point ℝ) (u v : ℝ) : Point ℝ :=
  ((1-u-v)*a.1 + u*b.1 + v*c.1, (1-u-v)*a.2 + u*b.2 + v*c.2)

def InTriangle (a b c p : Point ℝ) : Prop :=
  ∃ u v : ℝ, 0 ≤ u ∧ 0 ≤ v ∧ u+v ≤ 1 ∧ p = trianglePoint a b c u v

def StrictlyInside (a b c p : Point ℝ) : Prop :=
  ∃ u v : ℝ, 0 < u ∧ 0 < v ∧ u+v < 1 ∧ p = trianglePoint a b c u v

private theorem orient_triangle (a b x y z : Point ℝ) (u v : ℝ) :
    orient a b (trianglePoint x y z u v) =
      (1-u-v)*orient a b x + u*orient a b y + v*orient a b z := by
  unfold orient trianglePoint
  dsimp
  ring

private theorem incidentL (a b : Point ℝ) : orient a b a = 0 := by simp [orient]
private theorem incidentR (a b : Point ℝ) : orient a b b = 0 := by unfold orient; ring

/-- The common survivors of two peeling prefixes would all have to lie
on the line through the exposed point x and the third hull vertex c. -/
theorem shared_apex_line {a b c x p : Point ℝ} (abc : orient a b c ≠ 0)
    (inside : StrictlyInside a b c x)
    (left : InTriangle x b c p) (right : InTriangle a x c p) : orient x c p = 0 := by
  rcases inside with ⟨u,v,hu,_,hs,hx⟩
  have hA : orient x c a = u*orient a b c := by rw [hx]; unfold orient trianglePoint; dsimp; ring
  have hB : orient x c b = -(1-u-v)*orient a b c := by rw [hx]; unfold orient trianglePoint; dsimp; ring
  have sign : orient x c a * orient x c b < 0 := by
    rw [hA,hB]
    have ht : 0 < 1-u-v := by linarith
    calc _ = -(u*(1-u-v)*(orient a b c)^2) := by ring
         _ < 0 := neg_neg_of_pos (mul_pos (mul_pos hu ht) (sq_pos_of_ne_zero abc))
  obtain ⟨s,t,hs',_,_,hl⟩ := left
  obtain ⟨w,z,_,_,hw,hr⟩ := right
  have hl' : orient x c p = s*orient x c b := by rw [hl,orient_triangle]; simp [incidentL,incidentR]
  have hr' : orient x c p = (1-w-z)*orient x c a := by rw [hr,orient_triangle]; simp [incidentL,incidentR]
  have ha : 0 ≤ 1-w-z := by linarith
  have hp : (orient x c p)^2 ≤ 0 := calc
    _ = ((1-w-z)*orient x c a) * (s*orient x c b) := by
      rw [← hr',← hl',pow_two]
    _ = ((1-w-z)*s) * (orient x c a * orient x c b) := by ring
    _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg ha hs') sign.le
  by_contra hn
  exact (not_lt_of_ge hp) (sq_pos_of_ne_zero hn)

/-- On a hull triangle, the affine height above the opposite side attains
its strict maximum at the apex. -/
theorem apex_height {a b c p : Point ℝ} (positive : 0 < orient b c a)
    (h : InTriangle a b c p) (different : p ≠ a) : orient b c p < orient b c a := by
  obtain ⟨u,v,hu,hv,_,hp⟩ := h
  have s : 0 < u+v := by
    by_contra! hzero
    have u0 : u=0 := by linarith
    have v0 : v=0 := by linarith
    apply different
    simpa [u0,v0,trianglePoint] using hp
  rw [hp,orient_triangle,incidentL,incidentR]
  nlinarith [mul_pos s positive]

#print axioms shared_apex_line
end K28
