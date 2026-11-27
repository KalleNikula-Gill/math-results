import K28.PhysicalClash

namespace K28.Projection
open K28.Edges

private theorem shared_intersection (a b c d : Point ℝ)
    (nz : orient a b c - orient a b d ≠ 0) :
    interpolate a b (orient c d a / (orient c d a - orient c d b)) =
    interpolate c d (orient a b c / (orient a b c - orient a b d)) := by
  have rel : orient c d a - orient c d b = -(orient a b c - orient a b d) := by unfold orient; ring
  rw [rel]; apply Prod.ext <;> dsimp [interpolate] <;> field_simp [nz] <;> unfold orient <;> ring

private theorem inside_ratio {x y : ℝ} (opp : x*y<0) : 0<x/(x-y) ∧ x/(x-y)<1 := by
  rcases mul_neg_iff.mp opp with ⟨xp,yn⟩|⟨xn,yp⟩
  · have h : 0<x-y := by linarith
    exact ⟨div_pos xp h,(div_lt_one h).mpr (by linarith)⟩
  · have h : x-y<0 := by linarith
    exact ⟨div_pos_of_neg_of_neg xn h,(div_lt_one_of_neg h).mpr (by linarith)⟩

private theorem middle_before {s a b d : ℝ} (lo : 0<s) (hi : s<1) (ad : a<d) (bd : b<d) :
    a+s*(b-a)<d := by nlinarith only [mul_pos (sub_pos.mpr hi) (sub_pos.mpr ad),mul_pos lo (sub_pos.mpr bd)]

/-- A line through two Y points that splits X has opposite horizontal
orders in frames starting with X and with Y. Its intersection with a
straddling X segment has the same affine parameter in the two frames. -/
theorem axis_flips {q w : Drawing 28 ℝ}
    (areas : ∀ i j k, orient (q i) (q j) (q k)=orient (w i) (w j) (w k))
    {a b c d : V} (cb : (q c).1<(q a).1) (db : (q d).1<(q a).1)
    (ca : (w a).1<(w c).1) (da : (w a).1<(w d).1)
    (strad : orient (w a) (w b) (w c)*orient (w a) (w b) (w d)<0) :
    ((q b).1-(q a).1)*((w b).1-(w a).1)<0 := by
  let u := orient (w a) (w b) (w c)/(orient (w a) (w b) (w c)-orient (w a) (w b) (w d))
  let t := orient (w c) (w d) (w a)/(orient (w c) (w d) (w a)-orient (w c) (w d) (w b))
  have nz : orient (w a) (w b) (w c)-orient (w a) (w b) (w d)≠0 := by
    intro h; rw [sub_eq_zero.mp h] at strad; exact (mul_self_nonneg _).not_gt strad
  have hitW := shared_intersection (w a) (w b) (w c) (w d) nz
  have hitQ := shared_intersection (q a) (q b) (q c) (q d) (by simpa only [areas] using nz)
  simp only [areas] at hitQ
  have xw := congrArg Prod.fst hitW
  have xq := congrArg Prod.fst hitQ
  change (w a).1+t*((w b).1-(w a).1) = (w c).1+u*((w d).1-(w c).1) at xw
  change (q a).1+t*((q b).1-(q a).1) = (q c).1+u*((q d).1-(q c).1) at xq
  have ⟨lo,hi⟩ : 0<u ∧ u<1 := inside_ratio strad
  have low := middle_before lo hi cb db
  have high := middle_before lo hi (neg_lt_neg ca) (neg_lt_neg da)
  have n : t*((q b).1-(q a).1)<0 := by linarith only [low,xq]
  have p : 0<t*((w b).1-(w a).1) := by linarith only [high,xw]
  rcases mul_neg_iff.mp n with ⟨tp,qn⟩|⟨tn,qp⟩
  · exact mul_neg_of_neg_of_pos qn ((mul_pos_iff_of_pos_left tp).mp p)
  · exact mul_neg_of_pos_of_neg qp (((mul_pos_iff.mp p).resolve_left (fun h => tn.not_gt h.1)).2)

theorem split_of_sides {w : Drawing 28 ℝ} (ix : Function.Injective (fun i => (w i).1))
    {e : Pair} (ep : e.1≠e.2) {c d : V}
    (low : value (timeOf w e) (w c)<value (timeOf w e) (w e.1))
    (high : value (timeOf w e) (w e.1)<value (timeOf w e) (w d)) :
    orient (w e.1) (w e.2) (w c)*orient (w e.1) (w e.2) (w d)<0 := by
  have x := side_at_event (w e.1) (w e.2) (w c) (ix.ne ep)
  have y := side_at_event (w e.1) (w e.2) (w d) (ix.ne ep)
  have dx := sq_pos_of_ne_zero (sub_ne_zero.mpr (ix.ne ep).symm)
  have neg := mul_neg_of_neg_of_pos (sub_neg.mpr low) (sub_pos.mpr high)
  rw [←x,←y]
  calc _ = ((w e.2).1-(w e.1).1)^2 *
      ((value (timeOf w e) (w c)-value (timeOf w e) (w e.1))*(value (timeOf w e) (w d)-value (timeOf w e) (w e.1))) := by unfold timeOf; ring
       _ < 0 := mul_neg_of_pos_of_neg dx neg

theorem flip_side {q w : Drawing 28 ℝ} (iq : Function.Injective (fun i => (q i).1))
    (iw : Function.Injective (fun i => (w i).1))
    (areas : ∀ i j k, orient (q i) (q j) (q k)=orient (w i) (w j) (w k))
    {e : Pair} (ep : e.1≠e.2) (flip : ((q e.2).1-(q e.1).1)*((w e.2).1-(w e.1).1)<0)
    (T : Finset V) : openSide q T e=T \ closedSide w T e := by
  classical
  ext i
  simp only [openSide,closedSide,Finset.mem_filter,Finset.mem_sdiff]
  by_cases h : i∈T
  · simp only [h,true_and,not_le]
    let vq := value (timeOf q e) (q i)-value (timeOf q e) (q e.1)
    let vw := value (timeOf w e) (w i)-value (timeOf w e) (w e.1)
    have eq : ((q e.2).1-(q e.1).1)*vq=((w e.2).1-(w e.1).1)*vw :=
      (side_at_event _ _ _ (iq.ne ep)).trans ((areas _ _ _).trans (side_at_event _ _ _ (iw.ne ep)).symm)
    suffices hn : vq<0 ↔ 0<vw by simpa [vq,vw,sub_neg,sub_pos] using hn
    rcases mul_neg_iff.mp flip with ⟨qp,wn⟩|⟨qn,wp⟩
    · have h : ((q e.2).1-(q e.1).1)*vq < 0 ↔ ((w e.2).1-(w e.1).1)*vw < 0 := by rw [eq]
      simpa only [mul_neg_iff,qp,wn,not_lt_of_ge qp.le,not_lt_of_ge wn.le,true_and,false_and,false_or,or_false] using h
    · have h : 0 < ((q e.2).1-(q e.1).1)*vq ↔ 0 < ((w e.2).1-(w e.1).1)*vw := by rw [eq]
      simpa only [mul_pos_iff,qn,wp,not_lt_of_ge qn.le,not_lt_of_ge wp.le,true_and,false_and,false_or,or_false] using h
  · simp [h]

end K28.Projection
