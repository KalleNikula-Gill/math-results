import K28.BetweenTypes

namespace K28.Projection
open K28.Edges

def Within {p : Drawing 28 ℝ} (G : ThreeGroups p) (e : Pair) : Prop :=
  (e.1∈G.A ∧ e.2∈G.A) ∨ (e.1∈G.B ∧ e.2∈G.B) ∨ (e.1∈G.C ∧ e.2∈G.C)
instance {p : Drawing 28 ℝ} (G : ThreeGroups p) (e : Pair) : Decidable (Within G e) := by
  unfold Within; infer_instance
noncomputable def withinEdges {p : Drawing 28 ℝ} (G : ThreeGroups p) (k : Nat) :=
  (pairs.toFinset.filter (fun e => edgeType p e=k ∧ Within G e)).card

theorem group_partition {p : Drawing 28 ℝ} (G : ThreeGroups p) (k : Nat) :
    counts p k = withinEdges G k + betweenEdges p G.A G.B k +
      betweenEdges p G.B G.C k + betweenEdges p G.C G.A k := by
  classical
  have classify (i : V) : (i∈G.A ∧ i∉G.B ∧ i∉G.C) ∨
      (i∉G.A ∧ i∈G.B ∧ i∉G.C) ∨ (i∉G.A ∧ i∉G.B ∧ i∈G.C) := by
    have hi : i∈G.A∪G.B∪G.C := G.exhaust ▸ Finset.mem_univ _
    rcases Finset.mem_union.mp hi with h|c
    · rcases Finset.mem_union.mp h with a|b
      · exact Or.inl ⟨a,Finset.disjoint_left.mp G.disAB a,Finset.disjoint_left.mp G.disCA.symm a⟩
      · exact Or.inr (Or.inl ⟨Finset.disjoint_left.mp G.disAB.symm b,b,Finset.disjoint_left.mp G.disBC b⟩)
    · exact Or.inr (Or.inr ⟨Finset.disjoint_left.mp G.disCA c,Finset.disjoint_left.mp G.disBC.symm c,c⟩)
  rw [counts,ls_finset pairs _ (show pairs.Nodup from pairs_nodup)]
  unfold withinEdges betweenEdges
  simp only [← natBoole,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  rcases classify e.1 with ⟨a,b,c⟩|⟨a,b,c⟩|⟨a,b,c⟩ <;>
    rcases classify e.2 with ⟨d,f,h⟩|⟨d,f,h⟩|⟨d,f,h⟩ <;>
    simp [Between,Within,a,b,c,d,f,h]

theorem internal_edge_counts {p : Drawing 28 ℝ} (gp : GeneralPosition p)
    (G : ThreeGroups p) (pos : ∀ i ∈ G.A, ∀ j ∈ G.B, ∀ k ∈ G.C, 0 < orient (p i) (p j) (p k))
    (eq : ∀ k : Nat, k<14 → counts p k = profile[k]!) (k : Nat) (hk : k<14) :
    withinEdges G k = internalEdge k := by
  have cyc (a b c : Point ℝ) : orient a b c=orient b c a := by unfold orient; ring
  have na := Finset.card_pos.mp (show 0<G.A.card by rw [G.sizeA]; decide)
  have nb := Finset.card_pos.mp (show 0<G.B.card by rw [G.sizeB]; decide)
  have nc := Finset.card_pos.mp (show 0<G.C.card by rw [G.sizeC]; decide)
  have ab := separated_edge_count gp G.disAB G.disCA G.exhaust G.sepA na nb pos k hk
  have bc := separated_edge_count gp G.disBC G.disAB
    (show G.B∪G.C∪G.A=Finset.univ by simpa only [Finset.union_assoc,Finset.union_comm,Finset.union_left_comm] using G.exhaust)
    G.sepB nb nc (fun i hi j hj l hl => (cyc (p l) (p i) (p j)) ▸ pos l hl i hi j hj) k hk
  have ca := separated_edge_count gp G.disCA G.disBC
    (show G.C∪G.A∪G.B=Finset.univ by simpa only [Finset.union_assoc,Finset.union_comm,Finset.union_left_comm] using G.exhaust)
    G.sepC nc na (fun i hi j hj l hl => (cyc (p i) (p j) (p l)).symm ▸ pos j hj l hl i hi) k hk
  have sum := group_partition G k
  rw [ab,bc,ca,eq k hk,G.sizeA,G.sizeB,G.sizeC] at sum
  unfold internalEdge externalEdge externalGate
  unfold betweenFormula at sum
  split_ifs at * <;> omega

/-- For an equality drawing satisfying the two geometric estimates, the three
actual separated groups have the stated internal edge types. In particular
fifty same-group point pairs split the remaining twenty-six labels evenly. -/
theorem internal_profile_of_7233 (p : Drawing 28 ℝ) (gp : GeneralPosition p)
    (low : ∀ k : Nat, k<12 → lower[k]! ≤ E (counts p) k)
    (central : counts p 13 ≤ counts p 12) (eq : crossings p=7233) :
    ∃ G : ThreeGroups p,
      (∀ i ∈ G.A, ∀ j ∈ G.B, ∀ l ∈ G.C, 0 < orient (p i) (p j) (p l)) ∧
      (∀ k : Nat, k<14 → withinEdges G k = internalEdge k) ∧ withinEdges G 13=50 := by
  obtain ⟨G,pos⟩ := oriented_groups_of_7233 p gp low central eq
  have h := internal_edge_counts gp G pos (drawing_profile p gp low central eq)
  exact ⟨G,pos,h,(h 13 (by decide)).trans halving50⟩

end K28.Projection
