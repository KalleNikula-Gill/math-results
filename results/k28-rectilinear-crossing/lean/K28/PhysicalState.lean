import K28.TimelineOrder

namespace K28.Projection
open K28.Edges K28.Finite

set_option maxHeartbeats 1000000
attribute [local irreducible] pairs

noncomputable def initialLabel (q : Drawing 28 ℝ) (X : Finset V) := lowerRank (fun i => (q i).1) X
noncomputable def localRank (q : Drawing 28 ℝ) (X : Finset V) (t : Nat) :=
  rank q X (seenAt q Finset.univ t)

theorem local_order {q : Drawing 28 ℝ} (gp : GeneralPosition q) (ix : Function.Injective (fun i => (q i).1))
    (X : Finset V) (t : Nat) : StrictOrderOn q X (seenAt q Finset.univ t) :=
  (order_at gp ix _ t).restrict (Finset.subset_univ _)

theorem local_bound {q : Drawing 28 ℝ} (gp : GeneralPosition q) (ix : Function.Injective (fun i => (q i).1))
    {X : Finset V} {i : V} (hi : i∈X) (t : Nat) : localRank q X t i<X.card := by
  have h := Finset.mem_image_of_mem (localRank q X t) hi
  change localRank q X t i∈X.image (rank q X (seenAt q Finset.univ t)) at h
  rw [image_ranks ix (local_order gp ix X t)] at h
  exact Finset.mem_range.mp h

theorem local_surjective {q : Drawing 28 ℝ} (gp : GeneralPosition q) (ix : Function.Injective (fun i => (q i).1))
    {X : Finset V} (t : Nat) {k : Nat} (hk : k<X.card) : ∃ i∈X, localRank q X t i=k := by
  have h := Finset.mem_range.mpr hk
  rw [←image_ranks ix (local_order gp ix X t)] at h
  exact Finset.mem_image.mp h

noncomputable def labelAt (q : Drawing 28 ℝ) (X : Finset V) (t k : Nat) : Nat := by
  classical
  exact if existsLabel : ∃ i∈X, localRank q X t i=k then initialLabel q X existsLabel.choose else 0

noncomputable def realState (q : Drawing 28 ℝ) (X : Finset V) (t : Nat) : PlainState :=
  ⟨(List.range X.card).map (labelAt q X t),
   (List.range 9).map (fun j => mass q Finset.univ X t (10+j))⟩

theorem at_label {q : Drawing 28 ℝ} (gp : GeneralPosition q) (ix : Function.Injective (fun i => (q i).1))
    {X : Finset V} (t : Nat) {i : V} (hi : i∈X) : labelAt q X t (localRank q X t i)=initialLabel q X i := by
  classical
  unfold labelAt
  have pr : ∃ j∈X, localRank q X t j=localRank q X t i := ⟨i,hi,rfl⟩
  rw [dif_pos pr]
  exact congrArg (initialLabel q X) (rank_injective ix (local_order gp ix X t) pr.choose_spec.1 hi pr.choose_spec.2)

theorem lookup_perm {q : Drawing 28 ℝ} (gp : GeneralPosition q) (ix : Function.Injective (fun i => (q i).1))
    {X : Finset V} (t : Nat) {i : V} (hi : i∈X) :
    (realState q X t).permutation[localRank q X t i]! = initialLabel q X i := by
  have lt := local_bound gp ix hi t
  have h : localRank q X t i < (realState q X t).permutation.length := by simpa [realState] using lt
  rw [getElem!_pos (realState q X t).permutation (localRank q X t i) h]
  simp [realState,at_label gp ix t hi]

theorem lookup_count (q : Drawing 28 ℝ) (X : Finset V) (t j : Nat) (hj : j<9) :
    (realState q X t).prefixes[j]! = mass q Finset.univ X t (10+j) := by
  rw [getElem!_pos (realState q X t).prefixes j (show j<(realState q X t).prefixes.length by simpa [realState] using hj)]
  simp [realState]

theorem initial_local (q : Drawing 28 ℝ) (X : Finset V) (i : V) : localRank q X 0 i=initialLabel q X i := by
  apply congrArg Finset.card
  ext j; simp [prior,seenAt,Earlier,lowerRank]

theorem reverse_local {q : Drawing 28 ℝ} (ix : Function.Injective (fun i => (q i).1))
    {X : Finset V} {i : V} (hi : i∈X) (t := (schedule q Finset.univ).length) (h : t=(schedule q Finset.univ).length := by rfl) :
    localRank q X t i + initialLabel q X i + 1 = X.card := by
  classical
  subst t
  let P := X.filter (fun j => (q j).1<(q i).1)
  have psub : P ⊆ X.erase i := by
    intro j h; have ⟨jx,ord⟩ := Finset.mem_filter.mp h
    exact Finset.mem_erase.mpr ⟨fun eq => ord.ne (eq ▸ rfl),jx⟩
  have same : prior q X (edgeSet Finset.univ) i = X.erase i \ P := by
    ext j
    by_cases ji : j=i
    · subst j; simp [prior,Earlier]
    · have key := in_edgeSet (Finset.mem_univ j) (Finset.mem_univ i) ji
      have neq := ix.ne ji
      simp only [prior,Finset.mem_filter,Earlier,key,if_true,Finset.mem_sdiff,Finset.mem_erase,ji,not_false_eq_true,true_and,P]
      by_cases jx : j∈X
      · simp [jx,ji,not_lt]; exact ⟨le_of_lt,fun h => h.lt_of_ne neq.symm⟩
      · simp [jx]
  change (prior q X (seenAt q Finset.univ _) i).card+P.card+1=X.card
  rw [all_seen,same,Finset.card_sdiff_of_subset psub]
  have le := Finset.card_le_card psub
  have total := Finset.card_erase_add_one hi
  omega

private theorem state_eq {s u : PlainState} (hp : s.permutation=u.permutation) (hc : s.prefixes=u.prefixes) : s=u := by
  cases s; cases u; simp_all

theorem starting_state {p : Drawing 28 ℝ} (gp : GeneralPosition p) {X : Finset V} (F : GroupFrame p X)
    (size : X.card≤10) : realState F.q X 0=plainStart X.card := by
  have qg := F.gp gp
  apply state_eq
  · apply List.ext_getElem (by simp [realState,plainStart])
    intro k h _
    have lt : k<X.card := by simpa [realState] using h
    obtain ⟨i,hi,r⟩ := local_surjective qg F.horizontal 0 lt
    have src := (at_label qg F.horizontal 0 hi).trans (initial_local F.q X i).symm
    rw [r] at src
    simp [realState,plainStart,src]
  · apply List.ext_getElem (by simp [realState,plainStart])
    intro j h _
    simp only [realState,plainStart,List.getElem_map,List.getElem_range,List.getElem_replicate,first_mass _ F.horizontal (Finset.subset_univ _) F.first]
    omega

theorem ending_state {p : Drawing 28 ℝ} (gp : GeneralPosition p) {X : Finset V} (F : GroupFrame p X)
    (size : X.card≤10) : realState F.q X (schedule F.q Finset.univ).length=plainEnd X.card := by
  let t := (schedule F.q Finset.univ).length
  have qg := F.gp gp
  apply state_eq
  · apply List.ext_getElem (by simp [realState,plainEnd])
    intro k h _
    have lt : k<X.card := by simpa [realState] using h
    obtain ⟨i,hi,r⟩ := local_surjective qg F.horizontal t lt
    have src := at_label qg F.horizontal t hi
    have rev := reverse_local F.horizontal hi
    change localRank F.q X t i+initialLabel F.q X i+1=X.card at rev
    rw [r] at src rev
    simp only [realState,plainEnd,List.getElem_map,List.getElem_range,List.getElem_reverse,List.length_range]
    change labelAt F.q X t k=_
    omega
  · apply List.ext_getElem (by simp [realState,plainEnd])
    intro j h _
    have lt : j<9 := by simpa [realState] using h
    have complement : (Finset.univ \ X).card=28-X.card := by rw [Finset.card_sdiff_of_subset (Finset.subset_univ X)]; rfl
    simp only [realState,plainEnd,List.getElem_map,List.getElem_range,List.getElem_replicate,last_mass _ F.horizontal (Finset.subset_univ _) F.first,complement]
    omega

end K28.Projection
