import K28.InternalProfile

namespace K28.Projection
open K28.Edges

set_option maxHeartbeats 1200000
attribute [local irreducible] pairs

/-- For an open or a closed projection sublevel, each witness to an
increase in the number of group labels and a simultaneous decrease in
the number of outside labels would force an outside point to move right
past a group point. -/
theorem no_reverse_cut {q : Drawing 28 ℝ} {X : Finset V} (first : StartsFirst q Finset.univ X)
    {s t u v : ℝ} (st : s≤t) (closed : Bool) :
    let accept := fun a b : ℝ => if closed then a≤b else a<b
    let A := X.filter (fun i => accept (value s (q i)) u)
    let B := X.filter (fun i => accept (value t (q i)) v)
    let C := Xᶜ.filter (fun i => accept (value s (q i)) u)
    let D := Xᶜ.filter (fun i => accept (value t (q i)) v)
    ¬ (A.card<B.card ∧ D.card<C.card) := by
  classical
  dsimp only
  rintro ⟨hX,hO⟩
  have source {L R : Finset V} (h : L.card<R.card) : ∃ i ∈ R, i∉L := by
    by_contra! no
    exact h.not_ge (Finset.card_le_card no)
  obtain ⟨i,it,is⟩ := source hX
  obtain ⟨j,js,jt⟩ := source hO
  obtain ⟨ix,belowT⟩ := Finset.mem_filter.mp it
  obtain ⟨jx,belowS⟩ := Finset.mem_filter.mp js
  have aboveS := fun h => is (Finset.mem_filter.mpr ⟨ix,h⟩)
  have aboveT := fun h => jt (Finset.mem_filter.mpr ⟨jx,h⟩)
  have ord := first i ix j (Finset.mem_univ _) (Finset.mem_compl.mp jx)
  have h : value s (q j) < value s (q i) ∧ value t (q i) < value t (q j) := by
    cases closed
    · exact ⟨lt_of_lt_of_le belowS (le_of_not_gt aboveS),lt_of_lt_of_le belowT (le_of_not_gt aboveT)⟩
    · exact ⟨lt_of_le_of_lt belowS (lt_of_not_ge aboveS),lt_of_le_of_lt belowT (lt_of_not_ge aboveT)⟩
  have before := ((passes_right s _ _ ord).2.2).mp h.1
  have after := ((passes_right t _ _ ord).1).mp h.2
  linarith

noncomputable def openSide (q : Drawing 28 ℝ) (T : Finset V) (e : Pair) :=
  T.filter (fun i => value (timeOf q e) (q i) < value (timeOf q e) (q e.1))
noncomputable def closedSide (q : Drawing 28 ℝ) (T : Finset V) (e : Pair) :=
  T.filter (fun i => value (timeOf q e) (q i) ≤ value (timeOf q e) (q e.1))

theorem side_partition (q : Drawing 28 ℝ) (X : Finset V) (e : Pair) :
    (openSide q Finset.univ e).card = (openSide q X e).card + (openSide q Xᶜ e).card := by
  classical
  have split : openSide q Finset.univ e = openSide q X e ∪ openSide q Xᶜ e := by
    ext i; simp only [openSide,Finset.mem_filter,Finset.mem_union,Finset.mem_univ,true_and,Finset.mem_compl]
    by_cases h : i∈X <;> simp [h]
  have dis : Disjoint (openSide q X e) (openSide q Xᶜ e) := Finset.disjoint_left.mpr
    fun i a b => Finset.mem_compl.mp (Finset.mem_filter.mp b).1 (Finset.mem_filter.mp a).1
  rw [split,Finset.card_union_of_disjoint dis]

theorem only_ties {q : Drawing 28 ℝ} (gp : GeneralPosition q) (ix : Function.Injective (fun i => (q i).1))
    {e : Pair} (ne : e.1≠e.2) (i : V) :
    value (timeOf q e) (q i)=value (timeOf q e) (q e.1) ↔ i=e.1 ∨ i=e.2 := by
  constructor
  · intro eq; by_contra! diff
    have area := side_at_event (q e.1) (q e.2) (q i) (ix.ne ne)
    change (_ : ℝ)*(value (timeOf q e) (q i)-value (timeOf q e) (q e.1)) = _ at area
    rw [eq,sub_self,mul_zero] at area
    exact (gp.2 _ _ _ ne diff.1.symm diff.2.symm) area.symm
  · rintro (rfl|rfl)
    · rfl
    · exact (tie _ _ (ix.ne ne)).symm

theorem closed_inside {q : Drawing 28 ℝ} (gp : GeneralPosition q) (ix : Function.Injective (fun i => (q i).1))
    {X : Finset V} {e : Pair} (ne : e.1≠e.2) (a : e.1∈X) (b : e.2∈X) :
    (closedSide q X e).card = (openSide q X e).card+2 := by
  classical
  let U := openSide q X e
  have h : closedSide q X e=insert e.1 (insert e.2 U) := by
    ext i; simp only [closedSide,U,openSide,Finset.mem_filter,Finset.mem_insert]
    rw [le_iff_lt_or_eq,only_ties gp ix ne i]
    constructor
    · rintro ⟨m,lt|x|y⟩
      · exact Or.inr (Or.inr ⟨m,lt⟩)
      · exact Or.inl x
      · exact Or.inr (Or.inl y)
    · rintro (x|y|⟨m,lt⟩)
      · subst i; exact ⟨a,Or.inr (Or.inl rfl)⟩
      · subst i; exact ⟨b,Or.inr (Or.inr rfl)⟩
      · exact ⟨m,Or.inl lt⟩
  have x : e.1∉U := fun m => lt_irrefl _ (Finset.mem_filter.mp m).2
  have y : e.2∉U := fun m => (Finset.mem_filter.mp m).2.ne ((only_ties gp ix ne _).mpr (Or.inr rfl))
  rw [h,Finset.card_insert_of_notMem (by simp [ne,x]),Finset.card_insert_of_notMem y]

theorem closed_outside {q : Drawing 28 ℝ} (gp : GeneralPosition q) (ix : Function.Injective (fun i => (q i).1))
    {X : Finset V} {e : Pair} (ne : e.1≠e.2) (a : e.1∉X) (b : e.2∉X) :
    closedSide q X e=openSide q X e := by
  ext i
  simp only [closedSide,openSide,Finset.mem_filter]
  constructor
  · rintro ⟨m,h⟩; refine ⟨m,h.lt_of_ne ?_⟩
    intro eq; rcases (only_ties gp ix ne i).mp eq with x|y
    · exact a (x ▸ m)
    · exact b (y ▸ m)
  · exact fun h => ⟨h.1,h.2.le⟩

/-- Two ties at the same full gate in one real half-turn cannot realize
an occupied and an empty gate with the same group prefix count. -/
theorem physical_gate_clash {q : Drawing 28 ℝ} (gp : GeneralPosition q)
    (ix : Function.Injective (fun i => (q i).1)) {X : Finset V}
    (first : StartsFirst q Finset.univ X) {e f : Pair}
    (ep : e.1≠e.2) (fp : f.1≠f.2) (a : e.1∈X) (b : e.2∈X) (c : f.1∉X) (d : f.2∉X)
    (gate : gateAt q Finset.univ e=gateAt q Finset.univ f)
    (rank : gateAt q X e=(openSide q X f).card) : False := by
  change (openSide q Finset.univ e).card+1=(openSide q Finset.univ f).card+1 at gate
  change (openSide q X e).card+1=(openSide q X f).card at rank
  have x := side_partition q X e
  have y := side_partition q X f
  rcases le_total (timeOf q e) (timeOf q f) with earlier|earlier
  · have no := no_reverse_cut first (u:=value (timeOf q e) (q e.1)) (v:=value (timeOf q f) (q f.1)) earlier false
    change ¬ ((openSide q X e).card < (openSide q X f).card ∧ (openSide q Xᶜ f).card < (openSide q Xᶜ e).card) at no
    exact no ⟨by omega,by omega⟩
  · have no := no_reverse_cut first (u:=value (timeOf q f) (q f.1)) (v:=value (timeOf q e) (q e.1)) earlier true
    change ¬ ((closedSide q X f).card < (closedSide q X e).card ∧ (closedSide q Xᶜ e).card < (closedSide q Xᶜ f).card) at no
    rw [closed_inside gp ix ep a b,closed_outside gp ix fp c d,
        closed_inside gp ix fp (Finset.mem_compl.mpr c) (Finset.mem_compl.mpr d),
        closed_outside gp ix ep (fun h => Finset.mem_compl.mp h a) (fun h => Finset.mem_compl.mp h b)] at no
    exact no ⟨by omega,by omega⟩

end K28.Projection
