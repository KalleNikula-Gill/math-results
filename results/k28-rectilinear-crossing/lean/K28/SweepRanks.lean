import K28.Schedule

namespace K28.Projection
open K28.Edges

noncomputable def lowerRank (f : V → ℝ) (T : Finset V) (a : V) := (T.filter (fun i => f i<f a)).card

private theorem ranks_increase {f : V → ℝ} {T : Finset V} {i j : V}
    (hi : i∈T) (lt : f i<f j) : lowerRank f T i < lowerRank f T j := by
  apply Finset.card_lt_card
  have sub : T.filter (fun a => f a<f i) ⊆ T.filter (fun a => f a<f j) := by
    intro a h; obtain ⟨atT,small⟩ := Finset.mem_filter.mp h
    exact Finset.mem_filter.mpr ⟨atT,small.trans lt⟩
  exact (Finset.ssubset_iff_of_subset sub).mpr ⟨i,Finset.mem_filter.mpr ⟨hi,lt⟩,by simp⟩

private theorem rank_inj (f : V → ℝ) (ix : Function.Injective f) (T : Finset V) :
    Set.InjOn (lowerRank f T) T := by
  intro i hi j hj eq
  rcases lt_trichotomy (f i) (f j) with h|h|h
  · exact False.elim ((ranks_increase hi h).ne eq)
  · exact ix h
  · exact False.elim ((ranks_increase hj h).ne eq.symm)

theorem rank_image (f : V → ℝ) (ix : Function.Injective f) (T : Finset V) :
    T.image (lowerRank f T) = Finset.range T.card := by
  classical
  apply Finset.eq_of_subset_of_card_le
  · intro n hn
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hn
    apply Finset.mem_range.mpr
    apply Finset.card_lt_card
    exact (Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)).mpr ⟨i,hi,by simp⟩
  · rw [Finset.card_image_iff.mpr (rank_inj f ix T),Finset.card_range]

theorem ranks_below (f : V → ℝ) (ix : Function.Injective f) (T : Finset V) (g : Nat) :
    (T.filter (fun i => lowerRank f T i < g)).card = min T.card g := by
  classical
  let r := lowerRank f T
  let U := T.filter (fun i => r i<g)
  have inj : Set.InjOn r U := (rank_inj f ix T).mono (Finset.filter_subset _ _)
  have image : U.image r = (T.image r).filter (fun i => i<g) := by
    ext t
    simp only [U,Finset.mem_image,Finset.mem_filter]
    constructor
    · rintro ⟨i,⟨hi,low⟩,rfl⟩; exact ⟨⟨i,hi,rfl⟩,low⟩
    · rintro ⟨⟨i,hi,rfl⟩,h⟩; exact ⟨i,⟨hi,h⟩,rfl⟩
  have both : (Finset.range T.card).filter (fun i => i<g) = Finset.range (min T.card g) := by
    ext t; simp [lt_min_iff]
  change U.card = _
  rw [←Finset.card_image_iff.mpr inj,image,rank_image _ ix T,both,Finset.card_range]

def StartsFirst (q : Drawing 28 ℝ) (T X : Finset V) :=
  ∀ i∈X, ∀ j∈T, j∉X → (q i).1 < (q j).1

noncomputable def mass (q : Drawing 28 ℝ) (T X : Finset V) (t gate : Nat) :=
  (X.filter (fun i => rankAt q T t i < gate)).card

theorem first_rank (q : Drawing 28 ℝ) {T X : Finset V} (sub : X⊆T) (first : StartsFirst q T X)
    {i : V} (hi : i∈X) : rankAt q T 0 i = lowerRank (fun i => (q i).1) X i := by
  apply congrArg Finset.card; ext j
  simp only [prior,rankAt,seenAt,List.take_zero,List.toFinset_nil,Earlier,Finset.notMem_empty,if_false,
    Finset.mem_filter]
  constructor
  · rintro ⟨jt,lt⟩
    refine ⟨?_,lt⟩
    by_contra jx; exact (first i hi j jt jx).not_gt lt
  · rintro ⟨jx,lt⟩; exact ⟨sub jx,lt⟩

theorem all_seen (q : Drawing 28 ℝ) (T : Finset V) :
    seenAt q T (schedule q T).length = edgeSet T := by
  ext e; simp [seenAt,schedule_mem]

theorem last_rank (q : Drawing 28 ℝ) {T X : Finset V} (sub : X⊆T) (first : StartsFirst q T X)
    {i : V} (hi : i∈X) : rankAt q T (schedule q T).length i =
      (T \ X).card + lowerRank (fun i => -(q i).1) X i := by
  classical
  let S := X.filter (fun j => -(q j).1 < -(q i).1)
  have dis : Disjoint (T \ X) S := Finset.disjoint_left.mpr fun j jt jx =>
    (Finset.mem_sdiff.mp jt).2 (Finset.mem_filter.mp jx).1
  have setEq : prior q T (edgeSet T) i = (T \ X) ∪ S := by
    ext j
    by_cases jt : j∈T
    · by_cases ji : j=i
      · subst j; simp [prior,Earlier,hi,S]
      have paired := in_edgeSet jt (sub hi) ji
      by_cases jx : j∈X
      · simp [prior,Earlier,paired,jt,jx,S]
      · simp [prior,Earlier,paired,jt,jx,S,first i hi j jt jx]
    · have jx : j∉X := fun h => jt (sub h)
      simp [prior,jt,jx,S]
  change (prior q T (seenAt q T _) i).card = _
  rw [all_seen,setEq,Finset.card_union_of_disjoint dis]; rfl

theorem first_mass (q : Drawing 28 ℝ) (ix : Function.Injective (fun i => (q i).1))
    {T X : Finset V} (sub : X⊆T) (first : StartsFirst q T X) (g : Nat) :
    mass q T X 0 g = min X.card g := by
  unfold mass
  rw [Finset.filter_congr (fun i hi => by rw [first_rank q sub first hi])]
  exact ranks_below _ ix X g

theorem last_mass (q : Drawing 28 ℝ) (ix : Function.Injective (fun i => (q i).1))
    {T X : Finset V} (sub : X⊆T) (first : StartsFirst q T X) (g : Nat) :
    mass q T X (schedule q T).length g = min X.card (g-(T \ X).card) := by
  unfold mass
  have eq : X.filter (fun i => rankAt q T (schedule q T).length i<g) =
      X.filter (fun i => lowerRank (fun j => -(q j).1) X i < g-(T \ X).card) := by
    apply Finset.filter_congr
    intro i hi
    rw [last_rank q sub first hi]; omega
  rw [eq]
  exact ranks_below _ (fun a b h => ix (neg_inj.mp h)) X _

end K28.Projection
