import K28.CutFlux

namespace K28.Projection
open K28.Edges

set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

attribute [local irreducible] pairs

def Inside (X : Finset V) (e : Pair) := e.1∈X ∧ e.2∈X
noncomputable def bandInside (p : Drawing 28 ℝ) (d : Nat) (X : Finset V) :=
  number (fun e => InBand p d e ∧ Inside X e)
noncomputable def bandBetween (p : Drawing 28 ℝ) (d : Nat) (X Y : Finset V) :=
  number (fun e => InBand p d e ∧ Between X Y e)

theorem inside_filter (p : Drawing 28 ℝ) (d : Nat) (X : Finset V) :
    bandInside p d X = ((edgeSet X).filter (fun e => 13-d ≤ edgeType p e)).card := by
  classical
  unfold bandInside number
  apply congrArg Finset.card
  ext e
  simp only [Finset.mem_filter,edgeSet,Inside,InBand]
  exact ⟨fun h => ⟨⟨h.1,h.2.2⟩,h.2.1⟩,fun h => ⟨h.1.1,h.2,h.1.2⟩⟩

theorem inside_cap (p : Drawing 28 ℝ) (d : Nat) (X : Finset V) :
    bandInside p d X ≤ choose2 X.card ∧
    (bandInside p d X=choose2 X.card → ∀ e ∈ edgeSet X, InBand p d e) := by
  classical
  rw [inside_filter,←pairs_in_set]
  refine ⟨Finset.card_le_card (Finset.filter_subset _ _),?_⟩
  intro equal e mem
  have same := Finset.eq_of_subset_of_card_le (Finset.filter_subset _ (edgeSet X)) equal.ge
  have he : e∈(edgeSet X).filter (fun z => 13-d ≤ edgeType p z) := by rw [same]; exact mem
  exact (Finset.mem_filter.mp he).2

theorem cut_decomposition (p : Drawing 28 ℝ) (d : Nat) {P X : Finset V} (sub : P ⊆ X) :
    bandInside p d X = bandInside p d P + bandInside p d (X \ P) + bandBetween p d P (X \ P) ∧
    number (fun e => InBand p d e ∧ Mixed P e) =
      bandBetween p d P (X \ P) + bandBetween p d P (Finset.univ \ X) := by
  classical
  have classify (i : V) : (i∈P ∧ i∈X) ∨ (i∉P ∧ i∈X) ∨ (i∉P ∧ i∉X) := by
    by_cases h : i∈P
    · exact Or.inl ⟨h,sub h⟩
    · by_cases j : i∈X
      · exact Or.inr (Or.inl ⟨h,j⟩)
      · exact Or.inr (Or.inr ⟨h,j⟩)
  unfold bandInside bandBetween
  simp only [number_sum,← Finset.sum_add_distrib]
  constructor <;> apply Finset.sum_congr rfl <;> intro e _ <;>
    rcases classify e.1 with ⟨a,b⟩|⟨a,b⟩|⟨a,b⟩ <;>
    rcases classify e.2 with ⟨c,f⟩|⟨c,f⟩|⟨c,f⟩ <;> simp [flag,Inside,Between,Mixed,a,b,c,f]

/-- Both rules in a tight band refer to actual geometric point pairs. -/
structure CutRules (p : Drawing 28 ℝ) (d : Nat) (P X : Finset V) : Prop where
  prefixPairs : ∀ e ∈ edgeSet P, InBand p d e
  suffixPairs : ∀ e ∈ edgeSet (X \ P), InBand p d e
  outsidePairs : ∀ e ∈ pairs, Between P (Finset.univ \ X) e → ¬ InBand p d e

theorem physical_cut_bound {p q : Drawing 28 ℝ} (gp : GeneralPosition p)
    (gq : GeneralPosition q) (ix : Function.Injective (fun i => (q i).1))
    (area : ∀ i j k, orient (q i) (q j) (q k)=orient (p i) (p j) (p k))
    {X : Finset V} (first : StartsFirst q Finset.univ X) (size : X.card≤10)
    {d t : Nat} (hd : d≤4) (ht : t≤X.card) :
    bandInside p d X ≤ prefixBound X.card d t ∧
    (bandInside p d X=prefixBound X.card d t → CutRules p d (firstLabels q X t) X) := by
  classical
  let P := firstLabels q X t
  have ⟨sub,ct,pfirst⟩ := prefix_info ix first ht
  have flux := actual_band_flux gp gq ix area pfirst (show (firstLabels q X t).card≤10 by rw [ct]; exact ht.trans size) hd
  have ⟨total,mixed⟩ := cut_decomposition p d sub
  have ⟨pbound,pairsP⟩ := inside_cap p d P
  have ⟨sbound,pairsS⟩ := inside_cap p d (X \ P)
  have cs : (X \ P).card=X.card-t := (Finset.card_sdiff_of_subset sub).trans (congrArg _ ct)
  change number (fun e => InBand p d e ∧ Mixed P e) = (2*d+1)*P.card at flux
  rw [show P.card=t from ct] at flux pbound pairsP
  rw [cs] at sbound pairsS
  change bandInside p d X = bandInside p d P + bandInside p d (X \ P) + bandBetween p d P (X \ P) at total
  change number (fun e => InBand p d e ∧ Mixed P e) = bandBetween p d P (X \ P) + bandBetween p d P (Finset.univ \ X) at mixed
  unfold prefixBound
  rw [mixed] at flux
  constructor
  · omega
  · intro tight
    have zero : bandBetween p d P (Finset.univ \ X)=0 := by omega
    refine ⟨pairsP (by omega),pairsS (by omega),?_⟩
    intro e he between hin
    unfold bandBetween number at zero
    apply (Finset.eq_empty_iff_forall_notMem.mp (Finset.card_eq_zero.mp zero)) e
    exact (@Finset.mem_filter _ _ (fun a => Classical.propDecidable _) _ _).mpr ⟨List.mem_toFinset.mpr he,hin,between⟩

end K28.Projection
