import K28.InternalProfile

namespace K28.Projection
open K28.Edges

set_option maxHeartbeats 1600000

theorem pairs_in_set (X : Finset V) : (edgeSet X).card = choose2 X.card := by
  classical
  have recur (m : Nat) : choose2 (m+1)=choose2 m+m := by
    simp only [choose2,← Nat.choose_two_right]
    rw [Nat.choose_succ_succ]; simp [Nat.add_comm]
  induction X using Finset.induction_on with
  | empty => simp [edgeSet,choose2]
  | @insert a X ax ih =>
    let E := X.image (endpoints a)
    have image : E.card=X.card := by
      apply Finset.card_image_iff.mpr
      intro b _ c _ h
      rcases same_edge.mp h with h|h <;> rcases h with ⟨h,k⟩ <;> simp_all
    have dis : Disjoint (edgeSet X) E := by
      apply Finset.disjoint_left.mpr
      intro e old new
      obtain ⟨b,hb,ab⟩ := Finset.mem_image.mp new
      have norm := normalized old
      rcases same_edge.mp (ab.trans norm.2.2.2.symm) with ⟨h,_⟩|⟨h,_⟩
      · exact ax (h ▸ norm.1)
      · exact ax (h ▸ norm.2.1)
    have union : edgeSet (insert a X)=edgeSet X∪E := by
      ext e
      constructor
      · intro hi
        have ⟨h,j,lt,eq⟩ := normalized hi
        rcases Finset.mem_insert.mp h with h|h <;> rcases Finset.mem_insert.mp j with j|j
        · exact False.elim (lt.ne (h.trans j.symm))
        · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e.2,j,h ▸ eq⟩)
        · apply Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e.1,h,?_⟩)
          exact (congrArg (fun b => endpoints b e.1) j.symm).trans ((same_edge.mpr (Or.inr ⟨rfl,rfl⟩)).trans eq)
        · exact Finset.mem_union_left _ (eq ▸ in_edgeSet h j lt.ne)
      · intro hi
        rcases Finset.mem_union.mp hi with old|new
        · have h := Finset.mem_filter.mp old
          exact Finset.mem_filter.mpr ⟨h.1,Finset.mem_insert_of_mem h.2.1,Finset.mem_insert_of_mem h.2.2⟩
        · obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp new
          exact in_edgeSet (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hb) (fun eq => ax (eq ▸ hb))
    rw [union,Finset.card_union_of_disjoint dis,ih,image,Finset.card_insert_of_notMem ax,recur]

noncomputable def firstLabels (q : Drawing 28 ℝ) (X : Finset V) (t : Nat) :=
  X.filter fun i => lowerRank (fun i => (q i).1) X i < t

theorem prefix_info {q : Drawing 28 ℝ} (ix : Function.Injective (fun i => (q i).1))
    {X : Finset V} (first : StartsFirst q Finset.univ X) {t : Nat} (ht : t≤X.card) :
    firstLabels q X t ⊆ X ∧ (firstLabels q X t).card=t ∧ StartsFirst q Finset.univ (firstLabels q X t) := by
  refine ⟨Finset.filter_subset _ _,(ranks_below _ ix _ _).trans (min_eq_right ht),?_⟩
  intro i hi j _ hj
  obtain ⟨inX,small⟩ := Finset.mem_filter.mp hi
  by_cases jx : j∈X
  · have large : ¬lowerRank (fun i => (q i).1) X j<t := fun h => hj (Finset.mem_filter.mpr ⟨jx,h⟩)
    by_contra! rev
    have sub : X.filter (fun a => (q a).1 < (q j).1) ⊆ X.filter (fun a => (q a).1 < (q i).1) := by
      intro a ha
      have h := Finset.mem_filter.mp ha
      exact Finset.mem_filter.mpr ⟨h.1,h.2.trans_le rev⟩
    exact large (lt_of_le_of_lt (Finset.card_le_card sub) small)
  · exact first i inX j (Finset.mem_univ _) jx

def gateBand (d : Nat) := (List.range' (14-d) (2*d+1)).toFinset
noncomputable def InBand (p : Drawing 28 ℝ) (d : Nat) (e : Pair) := 13-d ≤ edgeType p e

theorem band_at_gate {p q : Drawing 28 ℝ} (gp : GeneralPosition p)
    (ix : Function.Injective (fun i => (q i).1))
    (area : ∀ i j k, orient (q i) (q j) (q k)=orient (p i) (p j) (p k))
    {e : Pair} (mem : e∈pairs) {d : Nat} (hd : d≤4) :
    InBand p d e ↔ gateAt q Finset.univ e ∈ gateBand d := by
  have ⟨lo,hi,ty⟩ := gate_center_view gp ix area mem
  simp only [InBand,ty,le_min_iff,gateBand,List.mem_toFinset,List.mem_range'_1]
  omega

end K28.Projection
