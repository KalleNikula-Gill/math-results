import K28.PhysicalState

namespace K28.Projection
open K28.Edges K28.Finite

set_option maxHeartbeats 1200000
attribute [local irreducible] pairs

theorem mass_increment {q : Drawing 28 ℝ} (gp : GeneralPosition q) (ix : Function.Injective (fun i => (q i).1))
    (X : Finset V) (t g : Nat) :
    mass q Finset.univ X t (g+1) = mass q Finset.univ X t g +
    if ∃ i∈X, rankAt q Finset.univ t i=g then 1 else 0 := by
  classical
  let r := rankAt q Finset.univ t
  by_cases hit : ∃ i∈X, r i=g
  · rw [if_pos hit]
    obtain ⟨i,hi,eq⟩ := hit
    have sets : X.filter (fun k => r k<g+1) = insert i (X.filter (fun k => r k<g)) := by
      ext j; simp only [Finset.mem_filter,Finset.mem_insert]
      constructor
      · rintro ⟨m,h⟩; by_cases low : r j<g
        · exact Or.inr ⟨m,low⟩
        · exact Or.inl (rank_injective ix (order_at gp ix Finset.univ t) (Finset.mem_univ _) (Finset.mem_univ _)
             (show r j=r i by omega))
      · rintro (h|⟨m,h⟩)
        · subst j; exact ⟨hi,by omega⟩
        · exact ⟨m,by omega⟩
    exact (congrArg Finset.card sets).trans (Finset.card_insert_of_notMem (by simp [eq]))
  · rw [if_neg hit,Nat.add_zero]
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro i hi
    have ne : r i≠g := fun eq => hit ⟨i,hi,eq⟩
    change r i<g+1 ↔ r i<g
    omega

theorem mass_rank {q : Drawing 28 ℝ} (gp : GeneralPosition q) (ix : Function.Injective (fun i => (q i).1))
    (X : Finset V) (t : Nat) (a : V) :
    mass q Finset.univ X t (rankAt q Finset.univ t a) = localRank q X t a := by
  apply congrArg Finset.card
  ext i
  simp only [Finset.mem_filter,prior]
  exact and_congr_right (fun _ => ranks_order ix (order_at gp ix Finset.univ t) (Finset.mem_univ _) (Finset.mem_univ _))

theorem actual_counts_valid {q : Drawing 28 ℝ} (gp : GeneralPosition q) (ix : Function.Injective (fun i => (q i).1))
    (X : Finset V) (t : Nat) : validCounts X.card (realState q X t).prefixes=true := by
  let f := fun g => mass q Finset.univ X t g
  have cap (g : Nat) : f g≤X.card := Finset.card_le_card (Finset.filter_subset _ _)
  have inc (g : Nat) : f g≤f (g+1) ∧ f (g+1)≤f g+1 := by
    have h := mass_increment gp ix X t g
    change f (g+1)=f g+_ at h
    split_ifs at h <;> omega
  change validCounts X.card [f 10,f 11,f 12,f 13,f 14,f 15,f 16,f 17,f 18]=true
  simp [validCounts,cap,inc 10,inc 11,inc 12,inc 13,inc 14,inc 15,inc 16,inc 17]

/-- A scheduled pair with its initial left-to-right order and the
frontier on each side of the event. -/
structure FullEvent (q : Drawing 28 ℝ) (t : Nat) (e : Pair) (a b : V) : Prop where
  key : endpoints a b=e
  order : (q a).1<(q b).1
  front : Frontier q Finset.univ (seenAt q Finset.univ t) (event (q a) (q b))
  pending : endpoints a b ∉ seenAt q Finset.univ t
  afterSeen : seenAt q Finset.univ (t+1)=insert (endpoints a b) (seenAt q Finset.univ t)

theorem full_event {q : Drawing 28 ℝ} (ix : Function.Injective (fun i => (q i).1)) (t : Nat)
    (ht : t<(schedule q Finset.univ).length) : ∃ a b, FullEvent q t ((schedule q Finset.univ)[t]) a b := by
  let L := schedule q Finset.univ
  let e := L[t]'ht
  have split : schedule q Finset.univ=L.take t ++e::L.drop (t+1) := by
    rw [List.getElem_cons_drop_succ_eq_drop,List.take_append_drop]
  obtain ⟨front,missing,mem⟩ := frontier_at_split split
  have ⟨_,_,lt,norm⟩ := normalized mem
  have after : seenAt q Finset.univ (t+1)=insert e (seenAt q Finset.univ t) := by
    change (L.take (t+1)).toFinset = insert e (L.take t).toFinset
    rw [List.take_succ_eq_append_getElem ht]
    ext k; simp only [List.mem_toFinset,List.mem_append,List.mem_singleton,Finset.mem_insert]; exact or_comm
  have make (a b : V) (ab : (q a).1<(q b).1) (key : endpoints a b=e) : FullEvent q t e a b := by
    have time : event (q a) (q b)=timeOf q e := by rw [←key,normalized_time]
    exact ⟨key,ab,time ▸ front,key ▸ missing,key ▸ after⟩
  rcases lt_or_gt_of_ne (ix.ne lt.ne) with h|h
  · exact ⟨_,_,make _ _ h norm⟩
  · exact ⟨_,_,make _ _ h ((same_edge.mpr (Or.inr ⟨rfl,rfl⟩)).trans norm)⟩

theorem FullEvent.gate {q : Drawing 28 ℝ} (gp : GeneralPosition q) (ix : Function.Injective (fun i => (q i).1))
    {t e a b} (ev : FullEvent q t e a b) (X : Finset V) :
    localRank q X t a+1=gateAt q X e := by
  have ab : a≠b := fun eq => ev.order.ne (eq ▸ rfl)
  have full := (prior_at_event gp ix (Finset.mem_univ a) (Finset.mem_univ b) ev.order ev.front ev.pending).1
  have cut : prior q X (seenAt q Finset.univ t) a=openSide q X (a,b) := by
    ext i
    have same := Finset.ext_iff.mp full i
    simp only [prior,Finset.mem_filter,Finset.mem_univ,true_and] at same
    simp only [prior,openSide,Finset.mem_filter]
    exact and_congr_right (fun _ => same)
  calc _ = gateAt q X (a,b) := congrArg (fun s : Finset V => s.card+1) cut
       _ = _ := (normalized_gate ix X ab).symm.trans (congrArg (gateAt q X) ev.key)

theorem FullEvent.ranks {q : Drawing 28 ℝ} (gp : GeneralPosition q) (ix : Function.Injective (fun i => (q i).1))
    {t e a b} (ev : FullEvent q t e a b) {X : Finset V} (ha : a∈X) (hb : b∈X) :
    localRank q X t b=localRank q X t a+1 ∧
    localRank q X (t+1) a=localRank q X t b ∧ localRank q X (t+1) b=localRank q X t a ∧
    ∀ i, i≠a → i≠b → localRank q X (t+1) i=localRank q X t i := by
  have narrow : Frontier q X (seenAt q Finset.univ t) (event (q a) (q b)) :=
    ⟨fun i _ j _ => ev.front.past i (Finset.mem_univ _) j (Finset.mem_univ _),
     fun i _ j _ => ev.front.future i (Finset.mem_univ _) j (Finset.mem_univ _)⟩
  simpa only [localRank,ev.afterSeen] using rank_step gp ix ha hb ev.order narrow ev.pending

theorem FullEvent.other_ranks {q : Drawing 28 ℝ} {t e a b} (ev : FullEvent q t e a b) {X : Finset V}
    (absent : ¬(a∈X ∧ b∈X)) {i : V} (hi : i∈X) : localRank q X (t+1) i=localRank q X t i := by
  unfold localRank; rw [ev.afterSeen]
  apply congrArg Finset.card; ext j
  simp only [prior,Finset.mem_filter]; apply and_congr_right
  intro hj
  have diff : endpoints j i≠endpoints a b := by
    intro eq; rcases same_edge.mp eq with ⟨x,y⟩|⟨x,y⟩
    · exact absent ⟨x ▸ hj,y ▸ hi⟩
    · exact absent ⟨y ▸ hi,x ▸ hj⟩
  simp [Earlier,diff]

end K28.Projection
