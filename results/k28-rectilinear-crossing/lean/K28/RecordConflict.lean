import K28.FrameReversal

namespace K28.Projection
open K28.Edges

set_option maxHeartbeats 1600000
attribute [local irreducible] pairs

/-- A record is defined by the actual line through two group points.
Its two integers are the full and restricted one-based gates. -/
noncomputable def physicalRecord (q : Drawing 28 ℝ) (X : Finset V) (g r : Nat) :=
  ∃ e ∈ edgeSet X, gateAt q Finset.univ e=g ∧ gateAt q X e=r

private theorem open_three (q : Drawing 28 ℝ) {X Y Z : Finset V}
    (xy : Disjoint X Y) (yz : Disjoint Y Z) (zx : Disjoint Z X) (cover : X∪Y∪Z=Finset.univ)
    (e : Pair) : (openSide q Finset.univ e).card =
      (openSide q X e).card+(openSide q Y e).card+(openSide q Z e).card := by
  have join (A B : Finset V) (dis : Disjoint A B) :
      (openSide q (A∪B) e).card=(openSide q A e).card+(openSide q B e).card := by
    have sets : openSide q (A∪B) e=openSide q A e ∪ openSide q B e := by
      ext i; simp only [openSide,Finset.mem_filter,Finset.mem_union]; tauto
    have split : Disjoint (openSide q A e) (openSide q B e) :=
      Finset.disjoint_left.mpr fun i a b => Finset.disjoint_left.mp dis (Finset.mem_filter.mp a).1 (Finset.mem_filter.mp b).1
    rw [sets,Finset.card_union_of_disjoint split]
  have xz : Disjoint (X∪Y) Z := Finset.disjoint_union_left.mpr ⟨zx.symm,yz⟩
  rw [←cover,join _ _ xz,join _ _ xy]

/-- The reflected records (g,g-y+l) for X and (28-g,l) for Y cannot
both be used. The proof compares oriented sides directly, allowing
independent choices of starting direction and ties in event times. -/
theorem physical_record_conflict {q w : Drawing 28 ℝ} (gp : GeneralPosition q) (gw : GeneralPosition w)
    (iq : Function.Injective (fun i => (q i).1)) (iw : Function.Injective (fun i => (w i).1))
    (area : ∀ i j k, orient (q i) (q j) (q k)=orient (w i) (w j) (w k))
    {X Y Z : Finset V} (xy : Disjoint X Y) (yz : Disjoint Y Z) (zx : Disjoint Z X)
    (cover : X∪Y∪Z=Finset.univ) (size : X.card+Y.card+Z.card=28)
    (ccw : ∀ j∈Y, ∀ k∈Z, ∀ i∈X, 0<orient (w j) (w k) (w i))
    (fx : StartsFirst q Finset.univ X) (fy : StartsFirst w Finset.univ Y)
    {g l : Nat} (yg : Y.card≤g) (pos : 0<l) (cut : l<X.card+Y.card-g)
    (xx : physicalRecord q X g (g-Y.card+l)) (yy : physicalRecord w Y (28-g) l) : False := by
  classical
  obtain ⟨e,he,eg,er⟩ := xx
  obtain ⟨f,hf,fg,fr⟩ := yy
  have ⟨ex,ex',et,_⟩ := normalized he
  have ⟨fy1,fy2,ft,_⟩ := normalized hf
  have nf1 : f.1∉X := Finset.disjoint_left.mp xy.symm fy1
  have nf2 : f.2∉X := Finset.disjoint_left.mp xy.symm fy2
  change (openSide w Finset.univ f).card+1=28-g at fg
  change (openSide w Y f).card+1=l at fr
  have three := open_three w xy yz zx cover f
  have zmax : (openSide w Z f).card≤Z.card := Finset.card_le_card (Finset.filter_subset _ _)
  have xpos : 0<(openSide w X f).card := by omega
  obtain ⟨c,hc⟩ := Finset.card_pos.mp xpos
  obtain ⟨cx,cs⟩ := Finset.mem_filter.mp hc
  have zfull : openSide w Z f=Z := by
    apply Finset.Subset.antisymm (Finset.filter_subset _ _)
    intro k kz
    have nyc : c∉Y := Finset.disjoint_left.mp xy cx
    have nyk : k∉Y := Finset.disjoint_left.mp yz.symm kz
    have yc := fy f.1 fy1 c (Finset.mem_univ _) nyc
    have yk := fy f.1 fy1 k (Finset.mem_univ _) nyk
    have ycTime := ((passes_right (timeOf w f) (w f.1) (w c) yc).2.2).mp cs
    have zk := (event_order _ _ _ yk yc).mpr (ccw _ fy1 _ kz _ cx)
    exact Finset.mem_filter.mpr ⟨kz,((passes_right _ _ _ yk).2.2).mpr (zk.trans ycTime)⟩
  rw [zfull] at three
  have small : (openSide w X f).card<X.card := by omega
  have existsHigh : ∃ d ∈ X, d∉openSide w X f := by
    by_contra! h; exact small.not_ge (Finset.card_le_card h)
  obtain ⟨d,dx,dm⟩ := existsHigh
  have dh : value (timeOf w f) (w f.1)<value (timeOf w f) (w d) := by
    by_contra! h
    rw [←closed_outside gw iw ft.ne nf1 nf2] at dm
    exact dm (Finset.mem_filter.mpr ⟨dx,h⟩)
  have flip := axis_flips area (fx c cx _ (Finset.mem_univ _) nf1) (fx d dx _ (Finset.mem_univ _) nf1)
    (fy _ fy1 _ (Finset.mem_univ _) (Finset.disjoint_left.mp xy cx))
    (fy _ fy1 _ (Finset.mem_univ _) (Finset.disjoint_left.mp xy dx)) (split_of_sides iw ft.ne cs dh)
  have openU := flip_side iq iw area ft.ne flip Finset.univ
  have openX := flip_side iq iw area ft.ne flip X
  have countU := congrArg Finset.card openU
  have countX := congrArg Finset.card openX
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),closed_inside gw iw ft.ne (Finset.mem_univ _) (Finset.mem_univ _)] at countU
  rw [closed_outside gw iw ft.ne nf1 nf2,Finset.card_sdiff_of_subset (show openSide w X f⊆X from Finset.filter_subset _ _)] at countX
  change (openSide q Finset.univ f).card=28-((openSide w Finset.univ f).card+2) at countU
  have yPos : 0<Y.card := Finset.card_pos.mpr ⟨_,fy1⟩
  apply physical_gate_clash gp iq fx et.ne ft.ne ex ex' nf1 nf2
  · rw [eg]; change g=(openSide q Finset.univ f).card+1; omega
  · rw [er]; omega

end K28.Projection
