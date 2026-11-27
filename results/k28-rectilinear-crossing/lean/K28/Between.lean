import K28.PhysicalGates

namespace K28.Projection
open K28.Edges

def Between (X Y : Finset V) (e : Pair) : Prop :=
  (e.1∈X ∧ e.2∈Y) ∨ (e.2∈X ∧ e.1∈Y)
instance (X Y : Finset V) (e : Pair) : Decidable (Between X Y e) := by
  unfold Between; infer_instance

noncomputable def betweenGate (q : Drawing 28 ℝ) (X Y : Finset V) (g : Nat) :=
  (pairs.toFinset.filter (fun e => gateAt q Finset.univ e=g ∧ Between X Y e)).card
noncomputable def betweenEdges (p : Drawing 28 ℝ) (X Y : Finset V) (k : Nat) :=
  (pairs.toFinset.filter (fun e => edgeType p e=k ∧ Between X Y e)).card

theorem all_gate (q : Drawing 28 ℝ) (e : Pair) : gateAt q Finset.univ e = below q e + 1 := by
  classical
  have labs : labels.toFinset=Finset.univ := by ext; simp [labels]
  rw [below,ls_finset labels _ (show labels.Nodup from List.nodup_finRange 28),labs]
  apply congrArg (fun n : Nat => n+1)
  exact (natBoole Finset.univ (fun i => value (timeOf q e) (q i) < value (timeOf q e) (q e.1))).symm

private theorem restrict_between {q : Drawing 28 ℝ} {X Y Z : Finset V}
    (dis : Disjoint X Y) (dz : Disjoint Z X)
    (cover : X ∪ Y ∪ Z = Finset.univ)
    (first : ∀ i ∈ X, ∀ j ∉ X, (q i).1 < (q j).1)
    (ccw : ∀ i ∈ X, ∀ j ∈ Y, ∀ k ∈ Z, 0 < orient (q i) (q j) (q k))
    {e : Pair} (mix : Between X Y e) :
    gateAt q (X∪Y) e=gateAt q Finset.univ e := by
  classical
  have outside {i j k : V} (hi : i∈X) (hj : j∈Y) (hk : k∉X∪Y) :
      value (event (q i) (q j)) (q i)<value (event (q i) (q j)) (q k) := by
    have all : k∈X∪Y∪Z := cover ▸ Finset.mem_univ _
    have kz := (Finset.mem_union.mp all).resolve_left hk
    exact (other_group_at_event _ _ _ (first i hi j (fun h => Finset.disjoint_left.mp dis h hj))
      (first i hi k (Finset.disjoint_left.mp dz kz)) (ccw i hi j hj k kz)).1
  unfold gateAt
  congr 2
  ext k
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  refine ⟨And.right,fun lt => ⟨?_,lt⟩⟩
  by_contra bad
  rcases mix with ⟨hx,hy⟩|⟨hx,hy⟩
  · exact (outside hx hy bad).not_gt lt
  · have dx := (first _ hx _ (fun h => Finset.disjoint_left.mp dis h hy)).ne
    change value (event _ _) _ < value (event _ _) _ at lt
    rw [event_symm (q e.1) (q e.2),←tie (q e.2) (q e.1) dx] at lt
    exact (outside hx hy bad).not_gt lt

theorem between_gate_formula {q : Drawing 28 ℝ} (gp : GeneralPosition q)
    (ix : Function.Injective (fun i => (q i).1)) {X Y Z : Finset V}
    (dis : Disjoint X Y) (dz : Disjoint Z X)
    (cover : X ∪ Y ∪ Z = Finset.univ)
    (first : ∀ i ∈ X, ∀ j ∉ X, (q i).1 < (q j).1)
    (ccw : ∀ i ∈ X, ∀ j ∈ Y, ∀ k ∈ Z, 0 < orient (q i) (q j) (q k))
    (g : Nat) : betweenGate q X Y g = xyAtGate X.card Y.card g := by
  classical
  let T := X ∪ Y
  have diff : T \ X=Y := by
    ext i
    simp only [T,Finset.mem_sdiff,Finset.mem_union]
    exact ⟨fun h => h.1.resolve_left h.2,fun h => ⟨Or.inr h,fun hx => Finset.disjoint_left.mp dis hx h⟩⟩
  have flux := physical_gate_count gp ix (show X⊆T from Finset.subset_union_left)
    (fun i hi j _ hj => first i hi j hj) g
  rw [ls_finset _ _ (schedule_nodup q T),diff] at flux
  have S : (schedule q T).toFinset = edgeSet T := by ext i; simp [schedule_mem]
  rw [S] at flux
  unfold charge at flux
  rw [natBoole] at flux
  have same : (edgeSet T).filter (fun e => gateAt q T e=g ∧ Mixed X e) =
       pairs.toFinset.filter (fun e => gateAt q Finset.univ e=g ∧ Between X Y e) := by
    ext e
    simp only [edgeSet,Finset.mem_filter,T,Finset.mem_union]
    constructor
    · rintro ⟨⟨mem,su,sv⟩,hg,m⟩
      have b : Between X Y e := by
        rcases m with ⟨a,b⟩|⟨a,b⟩
        · exact Or.inl ⟨a,sv.resolve_left b⟩
        · exact Or.inr ⟨a,su.resolve_left b⟩
      exact ⟨mem,(restrict_between dis dz cover first ccw b).symm.trans hg,b⟩
    · rintro ⟨mem,hg,b⟩
      have eqg := restrict_between dis dz cover first ccw b
      rcases b with ⟨a,b⟩|⟨a,b⟩
      · exact ⟨⟨mem,Or.inl a,Or.inr b⟩,eqg.trans hg,Or.inl ⟨a,fun hx => Finset.disjoint_left.mp dis hx b⟩⟩
      · exact ⟨⟨mem,Or.inr b,Or.inl a⟩,eqg.trans hg,Or.inr ⟨a,fun hx => Finset.disjoint_left.mp dis hx b⟩⟩
  rw [same] at flux
  unfold betweenGate xyAtGate
  omega

end K28.Projection
