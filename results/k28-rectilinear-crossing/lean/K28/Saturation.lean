import K28.TightCuts

namespace K28.Projection
open K28.Edges

set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
attribute [local irreducible] pairs

private theorem num_levels (d k : Nat) (hd : d≤4) (hk : k≤13) :
    (if 13-d≤k then 1 else 0 : Nat) =
    ls (List.range (d+1)) (fun j => if k=13-j then 1 else 0) := by
  have table : ∀ i : Fin 5, ∀ h : Fin 14, (if 13-i.val≤h.val then 1 else 0 : Nat) =
    ls (List.range (i.val+1)) (fun j => if h.val=13-j then 1 else 0) := by decide +kernel
  exact table ⟨d,by omega⟩ ⟨k,by omega⟩

private theorem within_sum {p : Drawing 28 ℝ} (G : ThreeGroups p) (k : Nat) :
  withinEdges G k = ∑ e ∈ pairs.toFinset, flag (edgeType p e=k ∧ Within G e) := by
  classical
  unfold withinEdges
  rw [←natBoole]
  apply Finset.sum_congr rfl
  intro e _
  by_cases h : edgeType p e=k ∧ Within G e <;> simp [flag,h]

theorem band_total {p : Drawing 28 ℝ} (gp : GeneralPosition p) (G : ThreeGroups p)
    (profile : ∀ k : Nat, k<14 → withinEdges G k=internalEdge k)
    {d : Nat} (hd : d≤4) :
    bandInside p d G.A+bandInside p d G.B+bandInside p d G.C=requiredInternal d := by
  classical
  let J := List.range (d+1)
  have localEq (e : Pair) (he : e∈pairs.toFinset) :
      flag (InBand p d e ∧ Inside G.A e) + flag (InBand p d e ∧ Inside G.B e) +
        flag (InBand p d e ∧ Inside G.C e) =
        ∑ j ∈ J.toFinset, flag (edgeType p e=13-j ∧ Within G e) := by
    have s := sides p gp e (List.mem_toFinset.mp he)
    have k : edgeType p e≤13 := by unfold edgeType; omega
    have num := num_levels d (edgeType p e) hd k
    change _ = ls J _ at num
    rw [ls_finset _ _ List.nodup_range] at num
    by_cases a : Inside G.A e
    · have b : ¬Inside G.B e := fun b => Finset.disjoint_left.mp G.disAB a.1 b.1
      have c : ¬Inside G.C e := fun c => Finset.disjoint_left.mp G.disCA c.1 a.1
      have w : Within G e := Or.inl a
      simpa only [a,b,c,w,and_true,and_false,flag,InBand,if_false,Nat.add_zero] using num
    by_cases b : Inside G.B e
    · have c : ¬Inside G.C e := fun c => Finset.disjoint_left.mp G.disBC b.1 c.1
      have w : Within G e := Or.inr (Or.inl b)
      simpa only [a,b,c,w,and_true,and_false,flag,InBand,if_false,Nat.add_zero,Nat.zero_add] using num
    by_cases c : Inside G.C e
    · have w : Within G e := Or.inr (Or.inr c)
      simpa only [a,b,c,w,and_true,and_false,flag,InBand,if_false,Nat.add_zero,Nat.zero_add] using num
    · have w : ¬Within G e := fun z => z.elim a (fun z => z.elim b c)
      simp [a,b,c,w,flag]
  unfold bandInside
  simp only [number_sum,←Finset.sum_add_distrib]
  calc _ = ∑ e ∈ pairs.toFinset, ∑ j ∈ J.toFinset, flag (edgeType p e=13-j ∧ Within G e) :=
             Finset.sum_congr rfl localEq
       _ = ∑ j ∈ J.toFinset, ∑ e ∈ pairs.toFinset, flag (edgeType p e=13-j ∧ Within G e) := Finset.sum_comm
       _ = ∑ j ∈ J.toFinset, internalEdge (13-j) := Finset.sum_congr rfl (fun j _ =>
             (within_sum G (13-j)).symm.trans (profile _ (by omega)))
       _ = requiredInternal d := (ls_finset J _ List.nodup_range).symm

private theorem chosen_cut {m d : Nat} (size : m=9 ∨ m=10) (hd : 1≤d ∧ d≤4) :
    ∃ t ≤ m, prefixBound m d t=groupBound m d := by
  refine ⟨(m-(2*d+1))/2,by omega,?_⟩
  have cases : d=1 ∨ d=2 ∨ d=3 ∨ d=4 := by omega
  rcases size with rfl|rfl <;> rcases cases with rfl|rfl|rfl|rfl <;> decide +kernel

private theorem saturation {d : Nat} (hd : 1≤d ∧ d≤4) : totalBound d=requiredInternal d := by
  have cases : d=1 ∨ d=2 ∨ d=3 ∨ d=4 := by omega
  rcases cases with rfl|rfl|rfl|rfl <;> decide +kernel

theorem group_band_cap {p : Drawing 28 ℝ} (gp : GeneralPosition p) {X : Finset V}
    (sep : StrictlySeparated p X) (size : X.card=9 ∨ X.card=10) {d : Nat} (hd : 1≤d ∧ d≤4) :
    bandInside p d X≤groupBound X.card d := by
  have left : X.Nonempty := Finset.card_pos.mp (by omega)
  have outside : ∃ j : V, j∉X := by
    by_contra! bad
    have eq : X=Finset.univ := Finset.eq_univ_of_forall bad
    have ca : X.card=28 := eq ▸ rfl
    omega
  obtain ⟨q,ix,first,area⟩ := starting_frame gp sep left outside
  obtain ⟨t,ht,best⟩ := chosen_cut size hd
  have gq : GeneralPosition q := ⟨fun i j h => ix (congrArg Prod.fst h),
    fun i j k a b c => (area i j k) ▸ gp.2 i j k a b c⟩
  exact best ▸ (physical_cut_bound gp gq ix area (fun i hi j _ hj => first i hi j hj)
    (by omega) hd.2 ht).1

theorem group_band_equality {p : Drawing 28 ℝ} (gp : GeneralPosition p) (G : ThreeGroups p)
    (profile : ∀ k : Nat, k<14 → withinEdges G k=internalEdge k) {d : Nat} (hd : 1≤d ∧ d≤4) :
    bandInside p d G.A=groupBound G.A.card d ∧ bandInside p d G.B=groupBound G.B.card d ∧
    bandInside p d G.C=groupBound G.C.card d := by
  have a := group_band_cap gp G.sepA (Or.inr G.sizeA) hd
  have b := group_band_cap gp G.sepB (Or.inl G.sizeB) hd
  have c := group_band_cap gp G.sepC (Or.inl G.sizeC) hd
  have sum := band_total gp G profile hd.2
  have eq := saturation hd
  unfold totalBound at eq
  rw [G.sizeA] at a ⊢
  rw [G.sizeB] at b ⊢
  rw [G.sizeC] at c ⊢
  omega

/-- In any starting frame for any of the three actual groups, every
minimizing cut satisfies the two per-pair restrictions of the state graph. -/
theorem all_minimizing_cuts {p q : Drawing 28 ℝ} (gp : GeneralPosition p) (G : ThreeGroups p)
    (profile : ∀ k : Nat, k<14 → withinEdges G k=internalEdge k)
    {X : Finset V} (group : X=G.A ∨ X=G.B ∨ X=G.C)
    (ix : Function.Injective (fun i => (q i).1))
    (area : ∀ i j k, orient (q i) (q j) (q k)=orient (p i) (p j) (p k))
    (first : StartsFirst q Finset.univ X) {d t : Nat} (hd : 1≤d ∧ d≤4)
    (ht : t∈minimizingCuts X.card d) : CutRules p d (firstLabels q X t) X := by
  have tight := group_band_equality gp G profile hd
  have size : X.card≤10 := by rcases group with rfl|rfl|rfl <;> simp [G.sizeA,G.sizeB,G.sizeC]
  have matchX : bandInside p d X=groupBound X.card d := by
    rcases group with rfl|rfl|rfl
    · exact tight.1
    · exact tight.2.1
    · exact tight.2.2
  have mem := List.mem_filter.mp ht
  have small := List.mem_range.mp mem.1
  have best := beq_iff_eq.mp mem.2
  have gq : GeneralPosition q := ⟨fun i j h => ix (congrArg Prod.fst h),
    fun i j k a b c => (area i j k) ▸ gp.2 i j k a b c⟩
  exact (physical_cut_bound gp gq ix area first size hd.2 (by omega : t≤X.card)).2 (matchX.trans best.symm)

end K28.Projection
