import K28.Middle

namespace K28.Projection
open K28.Edges

set_option maxHeartbeats 1400000
attribute [local irreducible] pairs

private theorem changes_exist {q : Drawing 28 ℝ} (gp : GeneralPosition q) (ix : Function.Injective (fun i => (q i).1)) :
    ∃ t<(schedule q Finset.univ).length, middle q (t+1)≠middle q t := by
  classical
  let U : Finset V := Finset.univ
  have start : StartsFirst q U U := fun _ _ _ h n => False.elim (n h)
  let X := firstLabels q U 13
  have small : 13≤U.card := by decide +kernel
  obtain ⟨sub,size,first⟩ := prefix_info ix start small
  have f := physical_gate_count gp ix sub first 13
  change ls (schedule q U) (charge q U X 13) = min X.card 13 - min X.card (13-(U \ X).card) at f
  have complement : (U \ X).card=15 := by rw [Finset.card_sdiff_of_subset sub,show X.card=13 from size]; decide +kernel
  rw [complement,show X.card=13 from size] at f
  have used : ∃ e∈schedule q U, gateAt q U e=13 := by
    by_contra! bad
    have z : ls (schedule q U) (charge q U X 13)=0 := by
      calc _ = ls (schedule q U) (fun _ => 0) := congr_summands (fun e he => by simp [charge,bad e he])
           _ = 0 := by simp [ls]
    omega
  obtain ⟨e,he,g⟩ := used
  obtain ⟨t,lt,ev⟩ := List.getElem_of_mem he
  obtain ⟨a,b,actual⟩ := full_event ix t lt
  exact ⟨t,lt,(middle_changes gp ix actual).mpr (Or.inl (ev ▸ g))⟩

private theorem unordered_injective : Set.InjOn unordered pairs.toFinset := by
  intro e he f hf eq
  have canon (x : Pair) (hx : x∈pairs.toFinset) : x.1<x.2 :=
    (normalized (show x∈edgeSet Finset.univ from Finset.mem_filter.mpr ⟨hx,Finset.mem_univ _,Finset.mem_univ _⟩)).2.2.1
  have p := canon e he
  have q := canon f hf
  have a : e.1∈unordered f := eq ▸ Finset.mem_insert_self _ _
  have b : e.2∈unordered f := eq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  simp only [unordered,Finset.mem_insert,Finset.mem_singleton] at a b
  rcases a with h|h <;> rcases b with k|k
  · exact False.elim (p.ne (h.trans k.symm))
  · exact Prod.ext h k
  · exact False.elim (p.not_gt (by simpa only [h,k] using q))
  · exact False.elim (p.ne (h.trans k.symm))

/-- The universal central inequality follows from counting distinct
middle pairs in a closed real sweep. A middle pair can change only at
gate 13 or 15. Every halving pair occurs as a middle pair. -/
theorem central_edge_bound (p : Drawing 28 ℝ) (gp : GeneralPosition p) : counts p 13≤counts p 12 := by
  classical
  obtain ⟨q,ix,area⟩ := unrestricted_frame gp
  have gq : GeneralPosition q := ⟨fun i j h => ix (congrArg Prod.fst h),
    fun i j k a b c => (area i j k) ▸ gp.2 i j k a b c⟩
  let L := schedule q Finset.univ
  let n := L.length
  let atTime := fun t : Nat => L[t]!
  let jumps := (Finset.range n).filter (fun k => middle q (k+1)≠middle q k)
  let arrivals := jumps.image (fun t => middle q (t+1))
  let edges := fun k => pairs.toFinset.filter (fun e => edgeType p e=k)
  have c (k : Nat) : counts p k=(edges k).card := by
    rw [counts,ls_finset pairs _ (show pairs.Nodup from pairs_nodup),natBoole]
  have seen := visited_after_change (middle q) n (middle_closes ix) (changes_exist gq ix)
  have inL (e : Pair) : e∈L ↔ e∈pairs.toFinset := by simp [L,schedule_mem,edgeSet]
  have members : (edges 13).image unordered ⊆ arrivals := by
    intro mid hm
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hm
    have ⟨hp,ty⟩ := Finset.mem_filter.mp he
    obtain ⟨t,lt,eq⟩ := List.getElem_of_mem ((inL e).mpr hp)
    have ⟨lo,hi,view⟩ := gate_center_view gp ix area (List.mem_toFinset.mp hp)
    have g : gateAt q Finset.univ e=14 := by omega
    obtain ⟨a,b,ev⟩ := full_event ix t lt
    have md := middle_at_center gq ix ev (eq ▸ g)
    change middle q t=unordered L[t] at md
    rw [eq] at md
    exact md ▸ seen t lt.le
  have maps : jumps.image atTime⊆edges 12 := by
    intro e he
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp he
    have ⟨time,ch⟩ := Finset.mem_filter.mp ht
    have lt := Finset.mem_range.mp time
    have real := (full_event ix t lt)
    obtain ⟨a,b,ev⟩ := real
    have near := (middle_changes gq ix ev).mp ch
    have mem : L[t]∈pairs.toFinset := (inL _).mp (List.getElem_mem lt)
    have ⟨lo,hi,view⟩ := gate_center_view gp ix area (List.mem_toFinset.mp mem)
    change gateAt q Finset.univ L[t]=13 ∨ gateAt q Finset.univ L[t]=15 at near
    have ty : edgeType p L[t]=12 := by omega
    change L[t]!∈pairs.toFinset.filter (fun e => edgeType p e=12)
    rw [getElem!_pos L t lt]
    exact Finset.mem_filter.mpr ⟨mem,ty⟩
  have inj : Set.InjOn atTime jumps := by
    intro i hi j hj eq
    have il := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
    have jl := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
    change L[i]! = L[j]! at eq
    rw [getElem!_pos L i il,getElem!_pos L j jl] at eq
    exact (schedule_nodup q Finset.univ).getElem_inj_iff.mp eq
  rw [c 13,c 12]
  calc (edges 13).card = ((edges 13).image unordered).card :=
          (Finset.card_image_iff.mpr (unordered_injective.mono (Finset.filter_subset _ _))).symm
       _ ≤ arrivals.card := Finset.card_le_card members
       _ ≤ jumps.card := Finset.card_image_le
       _ = (jumps.image atTime).card := (Finset.card_image_iff.mpr inj).symm
       _ ≤ (edges 12).card := Finset.card_le_card maps

/-- Assemble the minimum from the cumulative edge bounds for the twelve
orders needed at n=28 and the proved central inequality. -/
theorem minimum_from_low_edges
    (low : ∀ p : Drawing 28 ℝ, GeneralPosition p → ∀ k : Nat, k<12 → lower[k]! ≤ E (counts p) k) :
    MinimumIs 7234 := minimum_from_edge_bounds low central_edge_bound

/-- The numerical formula in Theorem 11 of Aichholzer, García, Orden and
Ramos at n = 28. Terms with j < 9 are outside the published summation. -/
def publishedLow (k : Nat) :=
  3 * (k+2).choose 2 + ((List.range (k+1)).map (fun j => if 9≤j then 3*j-25 else 0)).sum

theorem published_values : ∀ k : Fin 12, publishedLow k.val=lower[k.val]! := by decide +kernel

/-- Source-level form of the cumulative estimate. K28.Low.cumulative_bound_28
proves this estimate from the real drawing in the final assembly. -/
theorem minimum_using_theorem11
    (low : ∀ p : Drawing 28 ℝ, GeneralPosition p → ∀ k : Nat, k<12 → publishedLow k ≤ E (counts p) k) :
    MinimumIs 7234 :=
  minimum_from_low_edges (fun p gp k hk => (published_values ⟨k,hk⟩) ▸ low p gp k hk)

end K28.Projection
