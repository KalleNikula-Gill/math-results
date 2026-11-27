import K28.RealTraces

namespace K28.Projection
open K28.Edges K28.Finite

set_option maxHeartbeats 1400000
attribute [local irreducible] pairs

noncomputable def groupTraces {p : Drawing 28 ℝ} {G : ThreeGroups p}
    (A : GroupFrame p G.A) (B : GroupFrame p G.B) (C : GroupFrame p G.C) : Traces :=
  fun i => if i=0 then realTrace A.q G.A else if i=1 then realTrace B.q G.B else realTrace C.q G.C

private theorem pair_compatible {p : Drawing 28 ℝ} (gp : GeneralPosition p)
    {X Y Z : Finset V} (A : GroupFrame p X) (B : GroupFrame p Y)
    (xy : Disjoint X Y) (yz : Disjoint Y Z) (zx : Disjoint Z X)
    (cover : X∪Y∪Z=Finset.univ) (size : X.card+Y.card+Z.card=28)
    (ccw : ∀ j∈Y, ∀ k∈Z, ∀ i∈X, 0<orient (p j) (p k) (p i))
    (i j : Group) (si : X.card=sizeOfGroup i) (sj : Y.card=sizeOfGroup j)
    (τ : Traces) (xi : τ i=realTrace A.q X) (yj : τ j=realTrace B.q Y)
    {c : Conflict} (hc : c∈pairConflicts i j) (hx : c.tx∈τ c.x) (hy : c.ty∈τ c.y) : False := by
  obtain ⟨g,hg,mem⟩ := List.mem_flatMap.mp hc
  obtain ⟨l,hl,eq⟩ := List.mem_map.mp mem
  subst c
  change tag g (g-sizeOfGroup j+l)∈τ i at hx
  change tag (28-g) l∈τ j at hy
  rw [xi,←sj] at hx
  rw [yj] at hy
  have rg := List.mem_range'_1.mp hg
  have range := List.mem_range'_1.mp hl
  rw [←si,←sj] at range
  have xmax : X.card≤10 := si ▸ (show sizeOfGroup i≤10 by unfold sizeOfGroup; split <;> decide)
  have ymax : Y.card≤10 := sj ▸ (show sizeOfGroup j≤10 by unfold sizeOfGroup; split <;> decide)
  have x := recorded_tag (A.gp gp) A.horizontal xmax (by omega : 10≤g ∧ g≤18)
    (by omega : 0<g-Y.card+l ∧ g-Y.card+l<10) hx
  have y := recorded_tag (B.gp gp) B.horizontal ymax (by omega : 10≤28-g ∧ 28-g≤18)
    (by omega : 0<l ∧ l<10) hy
  exact physical_record_conflict (A.gp gp) (B.gp gp) A.horizontal B.horizontal
    (fun u v w => (A.areas u v w).trans (B.areas u v w).symm) xy yz zx cover size
    (fun u hu v hv w hw => (B.areas u v w) ▸ ccw u hu v hv w hw)
    A.first B.first (by omega) (by omega) (by omega) x y

theorem real_compatibility {p : Drawing 28 ℝ} (gp : GeneralPosition p) (G : ThreeGroups p)
    (ccw : ∀ i∈G.A, ∀ j∈G.B, ∀ k∈G.C, 0<orient (p i) (p j) (p k))
    (A : GroupFrame p G.A) (B : GroupFrame p G.B) (C : GroupFrame p G.C) :
    Compatible (groupTraces A B C) := by
  let τ := groupTraces A B C
  have cyc (a b c : Point ℝ) : orient a b c=orient b c a := by unfold orient; ring
  have size : G.A.card+G.B.card+G.C.card=28 := by rw [G.sizeA,G.sizeB,G.sizeC]
  have rotate := fun (i : V) (hi : i∈G.B) (j : V) (hj : j∈G.C) (k : V) (hk : k∈G.A) =>
    (cyc (p k) (p i) (p j)) ▸ ccw k hk i hi j hj
  have rotate' := fun (i : V) (hi : i∈G.C) (j : V) (hj : j∈G.A) (k : V) (hk : k∈G.B) =>
    (cyc (p i) (p j) (p k)).symm ▸ ccw j hj k hk i hi
  intro c hc hx hy
  simp only [conflicts,List.mem_append] at hc
  rcases hc with (ha|hb)|hc
  · exact pair_compatible gp A B G.disAB G.disBC G.disCA G.exhaust size rotate 0 1 G.sizeA G.sizeB
      τ rfl rfl ha hx hy
  · exact pair_compatible gp B C G.disBC G.disCA G.disAB
      (by simpa only [Finset.union_assoc,Finset.union_comm,Finset.union_left_comm] using G.exhaust)
      (by omega) rotate' 1 2 G.sizeB G.sizeC τ rfl rfl hb hx hy
  · exact pair_compatible gp C A G.disCA G.disAB G.disBC
      (by simpa only [Finset.union_assoc,Finset.union_comm,Finset.union_left_comm] using G.exhaust)
      (by omega) ccw 2 0 G.sizeC G.sizeA τ rfl rfl hc hx hy

theorem total_score {p : Drawing 28 ℝ} (gp : GeneralPosition p) (G : ThreeGroups p)
    (A : GroupFrame p G.A) (B : GroupFrame p G.B) (C : GroupFrame p G.C) :
    score (realTrace A.q G.A)+score (realTrace B.q G.B)+score (realTrace C.q G.C)=withinEdges G 13 := by
  classical
  rw [real_score gp A (by rw [G.sizeA]),real_score gp B (by rw [G.sizeB]; decide),
      real_score gp C (by rw [G.sizeC]; decide)]
  unfold typeInside withinEdges
  simp only [number_sum,←Finset.sum_add_distrib,←natBoole]
  apply Finset.sum_congr rfl
  intro e _
  by_cases a : Inside G.A e
  · have b : ¬Inside G.B e := fun b => Finset.disjoint_left.mp G.disAB a.1 b.1
    have c : ¬Inside G.C e := fun c => Finset.disjoint_left.mp G.disCA c.1 a.1
    have w : Within G e := Or.inl a
    simp [flag,a,b,c,w]
  by_cases b : Inside G.B e
  · have c : ¬Inside G.C e := fun c => Finset.disjoint_left.mp G.disBC b.1 c.1
    have w : Within G e := Or.inr (Or.inl b)
    simp [flag,a,b,c,w]
  by_cases c : Inside G.C e
  · have w : Within G e := Or.inr (Or.inr c)
    simp [flag,a,b,c,w]
  · have w : ¬Within G e := fun h => h.elim a (fun h => h.elim b c)
    simp [flag,a,b,c,w]

theorem candidate_real_traces (p : Drawing 28 ℝ) (gp : GeneralPosition p)
    (low : ∀ k : Nat, k<12 → lower[k]! ≤ E (counts p) k)
    (central : counts p 13 ≤ counts p 12) (eq : crossings p=7233) :
    ∃ (G : ThreeGroups p) (A : GroupFrame p G.A) (B : GroupFrame p G.B) (C : GroupFrame p G.C),
      (∀ k : Nat, k<14 → withinEdges G k=internalEdge k) ∧ Compatible (groupTraces A B C) ∧
      score (groupTraces A B C 0)+score (groupTraces A B C 1)+score (groupTraces A B C 2)=50 := by
  obtain ⟨G,pos,prof,fifty⟩ := internal_profile_of_7233 p gp low central eq
  obtain ⟨A⟩ := exists_frame gp G.sepA (Or.inr G.sizeA)
  obtain ⟨B⟩ := exists_frame gp G.sepB (Or.inl G.sizeB)
  obtain ⟨C⟩ := exists_frame gp G.sepC (Or.inl G.sizeC)
  exact ⟨G,A,B,C,prof,real_compatibility gp G pos A B C,(total_score gp G A B C).trans fifty⟩

end K28.Projection
