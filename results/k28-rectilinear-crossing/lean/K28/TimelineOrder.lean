import K28.Reduction

namespace K28.Projection
open K28.Edges

set_option maxHeartbeats 1200000
attribute [local irreducible] pairs

theorem earlier_asymm {q : Drawing 28 ℝ} {D : Finset Pair} {i j : V} :
    Earlier q D i j → ¬Earlier q D j i := by
  have e : endpoints j i=endpoints i j := same_edge.mpr (Or.inr ⟨rfl,rfl⟩)
  simp only [Earlier,e]
  split <;> exact LT.lt.not_gt

theorem earlier_total {q : Drawing 28 ℝ} (ix : Function.Injective (fun i => (q i).1))
    (D : Finset Pair) {i j : V} (ne : i≠j) : Earlier q D i j ∨ Earlier q D j i := by
  have e : endpoints j i=endpoints i j := same_edge.mpr (Or.inr ⟨rfl,rfl⟩)
  simp only [Earlier,e]
  split <;> rcases lt_or_gt_of_ne (ix.ne ne) with h|h <;> first | exact Or.inl h | exact Or.inr h

structure StrictOrderOn (q : Drawing 28 ℝ) (T : Finset V) (D : Finset Pair) : Prop where
  transitive : ∀ i∈T, ∀ j∈T, ∀ k∈T, Earlier q D i j → Earlier q D j k → Earlier q D i k

theorem frontier_order {q : Drawing 28 ℝ} (gp : GeneralPosition q)
    (ix : Function.Injective (fun i => (q i).1)) {T D s} (front : Frontier q T D s) : StrictOrderOn q T D := by
  have nondec {i j : V} (hi : i∈T) (hj : j∈T) (o : Earlier q D i j) : value s (q i)≤value s (q j) := by
    by_contra! bad; exact bad.not_gt ((relative_order ix front hi hj bad.ne.symm).mp o)
  refine ⟨?_⟩
  intro i hi j hj k hk a b
  have ij := nondec hi hj a
  have jk := nondec hj hk b
  have ne (u : V) : ¬Earlier q D u u := by simp [Earlier]
  have ij' : i≠j := fun eq => ne j (eq ▸ a)
  have jk' : j≠k := fun eq => ne k (eq ▸ b)
  have ik' : i≠k := fun eq => earlier_asymm a (eq ▸ b)
  have strict : value s (q i)<value s (q k) := by
    by_contra! rev
    have eq1 := ij.antisymm (jk.trans rev)
    have eq2 := (ij.trans jk).antisymm rev
    have diff := difference s (q i) (q j) (ix.ne ij').symm
    rw [eq1,sub_self,zero_eq_mul] at diff
    have time : event (q i) (q j)=s := sub_eq_zero.mp (diff.resolve_left (sub_ne_zero.mpr (ix.ne ij').symm))
    have e : value (timeOf q (i,j)) (q k)=value (timeOf q (i,j)) (q i) := by simpa only [timeOf,time] using eq2.symm
    rcases (only_ties gp ix ij' k).mp e with eq|eq
    · exact ik' eq.symm
    · exact jk' eq.symm
  exact (relative_order ix front hi hk strict.ne).mpr strict

theorem order_at {q : Drawing 28 ℝ} (gp : GeneralPosition q) (ix : Function.Injective (fun i => (q i).1))
    (T : Finset V) (t : Nat) : StrictOrderOn q T (seenAt q T t) := by
  by_cases ht : t<(schedule q T).length
  · let L := schedule q T
    let e := L[t]'ht
    have split : schedule q T=L.take t ++ e :: L.drop (t+1) := by
      rw [List.getElem_cons_drop_succ_eq_drop,List.take_append_drop]
    exact frontier_order gp ix (frontier_at_split split).1
  · have full : seenAt q T t=edgeSet T := by
      ext e; simp [seenAt,List.take_of_length_le (le_of_not_gt ht),schedule_mem]
    rw [full]
    refine ⟨?_⟩; intro i hi j hj k hk a b
    have ne (u : V) : ¬ Earlier q (edgeSet T) u u := by simp [Earlier]
    have ia : i≠j := fun eq => ne j (eq ▸ a)
    have jb : j≠k := fun eq => ne k (eq ▸ b)
    have ic : i≠k := fun eq => earlier_asymm a (eq ▸ b)
    simpa only [Earlier,in_edgeSet hi hk ic,if_true] using
      lt_trans (show (q k).1<(q j).1 by simpa [Earlier,in_edgeSet hj hk jb] using b)
        (show (q j).1<(q i).1 by simpa [Earlier,in_edgeSet hi hj ia] using a)

theorem StrictOrderOn.restrict {q : Drawing 28 ℝ} {T X D} (o : StrictOrderOn q T D) (sub : X ⊆ T) :
    StrictOrderOn q X D := ⟨fun i hi j hj k hk => o.transitive i (sub hi) j (sub hj) k (sub hk)⟩

theorem ranks_order {q : Drawing 28 ℝ} (ix : Function.Injective (fun i => (q i).1)) {T D}
    (o : StrictOrderOn q T D) {i j : V} (hi : i∈T) (hj : j∈T) :
    rank q T D i < rank q T D j ↔ Earlier q D i j := by
  have forward {i j : V} (hi : i∈T) (hj : j∈T) (h : Earlier q D i j) : rank q T D i<rank q T D j := by
    apply Finset.card_lt_card
    have sub : prior q T D i⊆prior q T D j := by
      intro k hk; have ⟨m,r⟩ := Finset.mem_filter.mp hk
      exact Finset.mem_filter.mpr ⟨m,o.transitive k m i hi j hj r h⟩
    exact (Finset.ssubset_iff_of_subset sub).mpr ⟨i,Finset.mem_filter.mpr ⟨hi,h⟩,by simp [prior,Earlier]⟩
  refine ⟨fun lt => ?_,forward hi hj⟩
  have ne : i≠j := fun h => lt.ne (h ▸ rfl)
  exact (earlier_total ix D ne).resolve_right (fun r => lt.not_gt (forward hj hi r))

theorem rank_injective {q : Drawing 28 ℝ} (ix : Function.Injective (fun i => (q i).1)) {T D}
    (o : StrictOrderOn q T D) : Set.InjOn (rank q T D) T := by
  intro i hi j hj eq
  by_contra ne
  rcases earlier_total ix D ne with h|h
  · exact ((ranks_order ix o hi hj).mpr h).ne eq
  · exact ((ranks_order ix o hj hi).mpr h).ne eq.symm

theorem image_ranks {q : Drawing 28 ℝ} (ix : Function.Injective (fun i => (q i).1)) {T D}
    (o : StrictOrderOn q T D) : T.image (rank q T D) = Finset.range T.card := by
  apply Finset.eq_of_subset_of_card_le
  · intro g m; obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp m
    apply Finset.mem_range.mpr
    apply Finset.card_lt_card
    exact (Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)).mpr ⟨i,hi,by simp [Earlier]⟩
  · rw [Finset.card_image_iff.mpr (rank_injective ix o),Finset.card_range]

end K28.Projection
