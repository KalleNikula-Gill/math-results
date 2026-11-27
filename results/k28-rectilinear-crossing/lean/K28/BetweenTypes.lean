import K28.Between

namespace K28.Projection
open K28.Edges

set_option maxHeartbeats 1800000

theorem gate_center_view {p q : Drawing 28 ℝ} (gp : GeneralPosition p)
    (ix : Function.Injective (fun i => (q i).1))
    (area : ∀ i j k, orient (q i) (q j) (q k)=orient (p i) (p j) (p k))
    {e : Pair} (mem : e∈pairs) :
    1 ≤ gateAt q Finset.univ e ∧ gateAt q Finset.univ e ≤ 27 ∧
    edgeType p e = min (gateAt q Finset.univ e - 1) (27 - gateAt q Finset.univ e) := by
  obtain ⟨a,b⟩ := e
  have edge : (a,b)∈edgeSet Finset.univ := Finset.mem_filter.mpr
    ⟨List.mem_toFinset.mpr mem,Finset.mem_univ _,Finset.mem_univ _⟩
  have ne := (normalized edge).2.2.1.ne
  have ss := sides p gp (a,b) mem
  have h := counts_at_event (a:=a) (b:=b) ix area ne
  rw [all_gate]
  refine ⟨by omega,?_,gate_type gp ix area ne mem⟩
  rcases h with h|h <;> rw [h.1] <;> omega

def betweenFormula (x y k : Nat) :=
  if k=13 then xyAtGate x y 14 else xyAtGate x y (k+1) + xyAtGate x y (27-k)

/-- The two-group edge profile follows from projection of the point
coordinates. The middle gate is counted only once. -/
theorem separated_edge_count {p : Drawing 28 ℝ} (gp : GeneralPosition p)
    {X Y Z : Finset V} (dis : Disjoint X Y) (dz : Disjoint Z X)
    (cover : X ∪ Y ∪ Z = Finset.univ) (sep : StrictlySeparated p X)
    (nx : X.Nonempty) (ny : Y.Nonempty)
    (ccw : ∀ i ∈ X, ∀ j ∈ Y, ∀ k ∈ Z, 0 < orient (p i) (p j) (p k))
    (k : Nat) (hk : k<14) : betweenEdges p X Y k = betweenFormula X.card Y.card k := by
  classical
  obtain ⟨b,hb⟩ := ny
  obtain ⟨q,ix,first,area⟩ := starting_frame gp sep nx ⟨b,fun h => Finset.disjoint_left.mp dis h hb⟩
  have gq : GeneralPosition q := ⟨fun i j h => ix (congrArg Prod.fst h),
    fun i j l a c d => (area i j l) ▸ gp.2 i j l a c d⟩
  have cf := between_gate_formula gq ix dis dz cover first
    (fun i hi j hj l hl => (area i j l) ▸ ccw i hi j hj l hl)
  let F := fun g => pairs.toFinset.filter (fun e => gateAt q Finset.univ e=g ∧ Between X Y e)
  have size (g : Nat) : (F g).card = xyAtGate X.card Y.card g := cf g
  let S := pairs.toFinset.filter (fun e => edgeType p e=k ∧ Between X Y e)
  change S.card=_
  by_cases central : k=13
  · have eq : S=F 14 := by
      ext e
      simp only [S,F,Finset.mem_filter,List.mem_toFinset]
      by_cases mem : e∈pairs
      · have ⟨lo,hi,ty⟩ := gate_center_view gp ix area mem
        have iff : edgeType p e=k ↔ gateAt q Finset.univ e=14 := by omega
        rw [iff]
      · simp [mem]
    rw [eq,size]; simp [betweenFormula,central]
  · have eq : S=F (k+1)∪F (27-k) := by
      ext e
      simp only [S,F,Finset.mem_union,Finset.mem_filter,List.mem_toFinset]
      by_cases mem : e∈pairs
      · have ⟨lo,hi,ty⟩ := gate_center_view gp ix area mem
        have iff : edgeType p e=k ↔ gateAt q Finset.univ e=k+1 ∨ gateAt q Finset.univ e=27-k := by omega
        rw [iff]
        constructor
        · rintro ⟨he,h,b⟩
          exact h.elim (fun v => Or.inl ⟨he,v,b⟩) (fun v => Or.inr ⟨he,v,b⟩)
        · rintro (⟨he,v,b⟩|⟨he,v,b⟩)
          · exact ⟨he,Or.inl v,b⟩
          · exact ⟨he,Or.inr v,b⟩
      · simp [mem]
    have diff : Disjoint (F (k+1)) (F (27-k)) := by
      apply Finset.disjoint_left.mpr
      intro e ha hb
      have u := (Finset.mem_filter.mp ha).2.1
      have v := (Finset.mem_filter.mp hb).2.1
      omega
    rw [eq,Finset.card_union_of_disjoint diff,size,size]
    simp [betweenFormula,central]

end K28.Projection
