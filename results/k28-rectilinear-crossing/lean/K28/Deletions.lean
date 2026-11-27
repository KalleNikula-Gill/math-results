import K28.Incidence
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

namespace K28.Edges

set_option maxHeartbeats 1200000

private theorem cleanChoose {α : Type*} [DecidableEq α] (allowed forced : Finset α)
    (h : forced ⊆ allowed) (d : Nat) :
    ((allowed.powersetCard d).filter (fun D => forced ⊆ D)).card =
    if forced.card ≤ d then (allowed.card-forced.card).choose (d-forced.card) else 0 := by
  split_ifs with le
  · rw [←Finset.card_sdiff_of_subset h, ←Finset.card_powersetCard]
    apply Finset.card_bij (fun D _ => D \ forced)
    · intro D hD
      obtain ⟨hd,hf⟩ := Finset.mem_filter.mp hD
      obtain ⟨sub,dcard⟩ := Finset.mem_powersetCard.mp hd
      exact Finset.mem_powersetCard.mpr ⟨fun _ hmem => Finset.mem_sdiff.mpr ⟨sub (Finset.mem_sdiff.mp hmem).1,(Finset.mem_sdiff.mp hmem).2⟩,
        by rw [Finset.card_sdiff_of_subset hf,dcard]⟩
    · intro D hD E hE eq
      have hD' := (Finset.mem_filter.mp hD).2
      have hE' := (Finset.mem_filter.mp hE).2
      ext x
      by_cases hx : x ∈ forced
      · exact ⟨fun _ => hE' hx,fun _ => hD' hx⟩
      · have hm := Finset.ext_iff.mp eq x
        simpa [hx] using hm
    · intro T hT
      obtain ⟨sub,tc⟩ := Finset.mem_powersetCard.mp hT
      have dis : Disjoint forced T := Finset.disjoint_left.mpr fun x hx ht =>
        (Finset.mem_sdiff.mp (sub ht)).2 hx
      refine ⟨forced ∪ T, Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨?_,?_⟩,
        Finset.subset_union_left⟩, ?_⟩
      · exact Finset.union_subset h (sub.trans Finset.sdiff_subset)
      · rw [Finset.card_union_of_disjoint dis,tc]; omega
      · ext x
        by_cases hx : x ∈ forced
        · have hnt : x ∉ T := fun ht => Finset.disjoint_left.mp dis hx ht
          simp [hx,hnt]
        · simp [hx]
  · apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro T ht
    obtain ⟨mem,sub⟩ := Finset.mem_filter.mp ht
    exact le ((Finset.mem_powersetCard.mp mem).2 ▸ Finset.card_le_card sub)

theorem natBoole {α : Type*} (s : Finset α) (q : α → Prop) [DecidablePred q] :
    (∑ x ∈ s, if q x then 1 else 0 : Nat) = (s.filter q).card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a t ha ih => by_cases h : q a <;> simp [ha,h,ih,Finset.filter_insert,Nat.add_comm]

theorem ls_finset {α : Type*} [DecidableEq α] (s : List α) (f : α → Nat)
    (nd : s.Nodup) : ls s f = ∑ i ∈ s.toFinset, f i := by
  induction s with
  | nil => simp [ls]
  | cons a t ih =>
    obtain ⟨ha,ht⟩ := List.nodup_cons.mp nd
    rw [List.toFinset_cons, Finset.sum_insert (by simpa using ha), ←ih ht]
    rfl

private theorem exchange {α β : Type*} (S : Finset α) (l : List β) (f : α → β → Nat) :
    (∑ x ∈ S, ls l (f x)) = ls l (fun y => ∑ x ∈ S, f x y) := by
  induction l with
  | nil => simp [ls]
  | cons a l ih =>
    change (∑ x ∈ S, (f x a + ls l (f x))) = _ + _
    rw [Finset.sum_add_distrib,ih]
    rfl

private theorem labelSet : labels.toFinset = Finset.univ := by ext; simp [labels]

noncomputable def positive (p : Drawing 28 ℝ) (e : Pair) : Finset V :=
  Finset.univ.filter fun c => 0 < orient (p e.1) (p e.2) (p c)
noncomputable def negative (p : Drawing 28 ℝ) (e : Pair) : Finset V :=
  Finset.univ.filter fun c => orient (p e.1) (p e.2) (p c) < 0

private theorem poscard (p : Drawing 28 ℝ) (e : Pair) : (positive p e).card = left p e := by
  classical
  rw [left,ls_finset labels _ (show labels.Nodup from List.nodup_finRange 28),labelSet]
  exact (natBoole _ _).symm
private theorem negcard (p : Drawing 28 ℝ) (e : Pair) : (negative p e).card = right p e := by
  classical
  rw [right,ls_finset labels _ (show labels.Nodup from List.nodup_finRange 28),labelSet]
  exact (natBoole _ _).symm

def available (e : Pair) : Finset V := Finset.univ \ {e.1,e.2}
noncomputable def smallSide (p : Drawing 28 ℝ) (e : Pair) :=
  if left p e ≤ right p e then positive p e else negative p e

private theorem smallcard (p : Drawing 28 ℝ) (e : Pair) : (smallSide p e).card = edgeType p e := by
  unfold smallSide edgeType; split_ifs with h
  · rw [min_eq_left h,poscard]
  · rw [min_eq_right (by omega),negcard]

private theorem endpoints_excluded (p : Drawing 28 ℝ) (e : Pair) :
    positive p e ⊆ available e ∧ negative p e ⊆ available e := by
  have ol : orient (p e.1) (p e.2) (p e.1) = 0 := by simp [orient]
  have ot : orient (p e.1) (p e.2) (p e.2) = 0 := by unfold orient; ring
  constructor <;> intro x hx <;> simp only [positive,negative,Finset.mem_filter,Finset.mem_univ,true_and] at hx <;>
    simp only [available,Finset.mem_sdiff,Finset.mem_univ,true_and, Finset.mem_insert,Finset.mem_singleton] <;>
    rintro (rfl|rfl) <;> simp_all

/-- The two endpoints survive and the line they span supports all
surviving points in a closed half-plane. -/
def OnHull (p : Drawing 28 ℝ) (D : Finset V) (e : Pair) : Prop :=
  e.1 ∉ D ∧ e.2 ∉ D ∧ (positive p e ⊆ D ∨ negative p e ⊆ D)

noncomputable instance hullDec (p : Drawing 28 ℝ) (D : Finset V) (e : Pair) :
    Decidable (OnHull p D e) := Classical.propDecidable _

noncomputable def hullEdges (p : Drawing 28 ℝ) (D : Finset V) : Nat := by
  classical exact ls pairs (fun e => if OnHull p D e then 1 else 0)

private theorem hull_small (p : Drawing 28 ℝ) (gp : GeneralPosition p) {e : Pair} (he : e ∈ pairs)
    {D : Finset V} (hd : D.card ≤ 9) :
    OnHull p D e ↔ D ⊆ available e ∧ smallSide p e ⊆ D := by
  have sidesum := sides p gp e he
  have surv : (e.1 ∉ D ∧ e.2 ∉ D) ↔ D ⊆ available e := by
    constructor
    · rintro ⟨h1,h2⟩ z hz
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      simp only [Finset.mem_insert,Finset.mem_singleton]
      rintro (h|h)
      · exact h1 (h ▸ hz)
      · exact h2 (h ▸ hz)
    · intro sub
      constructor
      · intro h; exact (Finset.mem_sdiff.mp (sub h)).2 (Finset.mem_insert_self _ _)
      · intro h; exact (Finset.mem_sdiff.mp (sub h)).2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  unfold OnHull
  rw [←and_assoc,surv]
  apply and_congr_right
  intro _
  unfold smallSide; split_ifs with ord
  · have cannot : ¬ negative p e ⊆ D := by
      intro h
      have cc := Finset.card_le_card h
      rw [negcard] at cc; omega
    simp [cannot]
  · have cannot : ¬ positive p e ⊆ D := by
      intro h
      have cc := Finset.card_le_card h
      rw [poscard] at cc; omega
    simp [cannot]

private theorem different_ends : pairs.all (fun e => e.1 != e.2) = true := by decide +kernel

private theorem available_card {e : Pair} (he : e ∈ pairs) : (available e).card = 26 := by
  have ne : e.1 ≠ e.2 := by simpa using List.all_eq_true.mp different_ends e he
  simp [available,Finset.card_sdiff_of_subset,ne]

def deletionWeight (d j : Nat) : Nat := if j ≤ d then (26-j).choose (d-j) else 0

theorem deletions_per_edge (p : Drawing 28 ℝ) (gp : GeneralPosition p) (d : Nat) (hd : d ≤ 9)
    {e : Pair} (he : e ∈ pairs) :
    ((Finset.univ.powersetCard d).filter (fun D => OnHull p D e)).card =
      deletionWeight d (edgeType p e) := by
  classical
  have eq : ((Finset.univ.powersetCard d).filter (fun D => OnHull p D e)) =
      (((available e).powersetCard d).filter (fun D => smallSide p e ⊆ D)) := by
    ext D
    simp only [Finset.mem_filter,Finset.mem_powersetCard,Finset.subset_univ,true_and]
    constructor
    · rintro ⟨hc,h⟩
      obtain ⟨sub,f⟩ := (hull_small p gp he (hc.trans_le hd)).mp h
      exact ⟨⟨sub,hc⟩,f⟩
    · rintro ⟨⟨sub,hc⟩,f⟩
      exact ⟨hc,(hull_small p gp he (hc.trans_le hd)).mpr ⟨sub,f⟩⟩
  have small : smallSide p e ⊆ available e := by
    unfold smallSide; split_ifs <;> first | exact (endpoints_excluded p e).1 | exact (endpoints_excluded p e).2
  rw [eq,cleanChoose _ _ small, smallcard,available_card he,deletionWeight]

/-- Count all supporting segment endpoints over all deletions of a fixed
size by first choosing the line and the remaining free deletions. -/
theorem hull_mass (p : Drawing 28 ℝ) (gp : GeneralPosition p) (d : Nat) (hd : d ≤ 9) :
    (∑ D ∈ (Finset.univ : Finset V).powersetCard d, hullEdges p D) =
    ∑ j ∈ Finset.range 10, counts p j * deletionWeight d j := by
  classical
  let ds := (Finset.univ : Finset V).powersetCard d
  calc
    _ = ls pairs (fun e => ∑ D ∈ ds, if OnHull p D e then 1 else 0) :=
      exchange ds pairs (fun D e => if OnHull p D e then 1 else 0)
    _ = ls pairs (fun e => deletionWeight d (edgeType p e)) := by
      apply congr_summands
      intro e he
      rw [natBoole]
      exact deletions_per_edge p gp d hd he
    _ = ls pairs (fun e => ∑ j ∈ Finset.range 10,
          (if edgeType p e = j then 1 else 0) * deletionWeight d j) := by
      apply congr_summands
      intro e _
      let k := edgeType p e
      change deletionWeight d k = ∑ j ∈ Finset.range 10, (if k = j then 1 else 0)*deletionWeight d j
      simp only [ite_mul,one_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_range]
      by_cases h : k < 10
      · simp [h]
      · simp [h,deletionWeight,show ¬ k ≤ d by omega]
    _ = ∑ j ∈ Finset.range 10, ls pairs (fun e =>
          (if edgeType p e = j then 1 else 0) * deletionWeight d j) :=
      (exchange _ pairs _).symm
    _ = _ := Finset.sum_congr rfl (fun j _ => mulR pairs _ _)

private theorem profile_mass : ∀ d : Fin 10,
    (∑ j ∈ Finset.range 10, profile[j]! * deletionWeight d.val j) =
      3 * (Nat.choose 28 d.val) + (if d.val=9 then 2 else 0) := by decide +kernel

/-- For a drawing with the equality edge profile, the sum of the
supporting-edge counts equals the triangular baseline, plus two at nine. -/
theorem mass_of_profile (p : Drawing 28 ℝ) (gp : GeneralPosition p)
    (edgeProfile : ∀ k : Nat, k < 10 → counts p k = profile[k]!)
    (d : Nat) (hd : d ≤ 9) :
    (∑ D ∈ (Finset.univ : Finset V).powersetCard d, hullEdges p D) =
      3 * (Nat.choose 28 d) + (if d=9 then 2 else 0) := by
  rw [hull_mass p gp d hd]
  exact (Finset.sum_congr rfl (fun i hi => by rw [edgeProfile i (Finset.mem_range.mp hi)])).trans
    (profile_mass ⟨d,by omega⟩)

end K28.Edges
