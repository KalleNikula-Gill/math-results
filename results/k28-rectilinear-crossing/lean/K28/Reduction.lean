import K28.CandidateTraces
import K28.PlainExclusion
import K28.Witness

namespace K28.Projection
open K28.Edges K28.Finite

attribute [local irreducible] pairs

/-- Local data that an ordinary list implementation of a geometric
sweep can use at each event. Gates and initial cuts are defined by the
real coordinates in the frame. -/
structure LocalRules {p : Drawing 28 ℝ} {X : Finset V} (F : GroupFrame p X) : Prop where
  tracked : ∀ e ∈ edgeSet X, 10≤gateAt F.q Finset.univ e ∧ gateAt F.q Finset.univ e≤18
  cuts : ∀ d : Nat, 1≤d ∧ d≤4 → ∀ t∈minimizingCuts X.card d, CutRules p d (firstLabels F.q X t) X

theorem candidate_local_rules {p : Drawing 28 ℝ} (gp : GeneralPosition p) (G : ThreeGroups p)
    (profile : ∀ k : Nat, k<14 → withinEdges G k=internalEdge k)
    {X : Finset V} (group : X=G.A ∨ X=G.B ∨ X=G.C) (F : GroupFrame p X) : LocalRules F := by
  classical
  refine ⟨?_,fun _ hd _ ht => all_minimizing_cuts gp G profile group F.horizontal F.areas F.first hd ht⟩
  intro e he
  have mem := Finset.mem_filter.mp he
  have bt : Within G e := by
    rcases group with rfl|rfl|rfl
    · exact Or.inl mem.2
    · exact Or.inr (Or.inl mem.2)
    · exact Or.inr (Or.inr mem.2)
  have ⟨lo,hi,ty⟩ := gate_center_view gp F.horizontal F.areas (List.mem_toFinset.mp mem.1)
  have bound : 9≤edgeType p e := by
    by_contra! small
    have table : ∀ k : Fin 9, internalEdge k.val=0 := by decide +kernel
    have zero := (profile (edgeType p e) (by omega)).trans (table ⟨_,small⟩)
    unfold withinEdges at zero
    apply (Finset.eq_empty_iff_forall_notMem.mp (Finset.card_eq_zero.mp zero)) e
    exact Finset.mem_filter.mpr ⟨mem.1,rfl,bt⟩
  omega

/-- Factor the argument into two geometric estimates and the conversion of
real event lists into ordinary paths. Realization, CentralBound, and Minimum
supply all three proofs in the final development. -/
theorem minimum_reduction
    (low : ∀ p : Drawing 28 ℝ, GeneralPosition p → ∀ k : Nat, k<12 → lower[k]! ≤ E (counts p) k)
    (central : ∀ p : Drawing 28 ℝ, GeneralPosition p → counts p 13 ≤ counts p 12)
    (realize : ∀ (p : Drawing 28 ℝ), GeneralPosition p → ∀ (X : Finset V) (F : GroupFrame p X),
      (X.card=9 ∨ X.card=10) → LocalRules F →
      PlainPath X.card (plainStart X.card) (realTrace F.q X)) : MinimumIs 7234 := by
  refine ⟨drawing_with_7234,?_⟩
  intro p gp
  have lowerBound := drawing_lower p gp (low p gp) (central p gp)
  by_contra! bad
  have eq : crossings p=7233 := by omega
  obtain ⟨G,A,B,C,profile,compat,weight⟩ := candidate_real_traces p gp (low p gp) (central p gp) eq
  have a := realize p gp _ A (Or.inr G.sizeA) (candidate_local_rules gp G profile (Or.inl rfl) A)
  have b := realize p gp _ B (Or.inl G.sizeB) (candidate_local_rules gp G profile (Or.inr (Or.inl rfl)) B)
  have c := realize p gp _ C (Or.inl G.sizeC) (candidate_local_rules gp G profile (Or.inr (Or.inr rfl)) C)
  rw [G.sizeA] at a
  rw [G.sizeB] at b
  rw [G.sizeC] at c
  have no := plain_paths_below_fifty (groupTraces A B C) a b c compat
  omega

end K28.Projection
