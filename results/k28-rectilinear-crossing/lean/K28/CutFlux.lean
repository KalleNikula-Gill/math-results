import K28.CutTools

namespace K28.Projection
open K28.Edges

set_option maxHeartbeats 1600000

noncomputable def number (F : Pair → Prop) : Nat := by
  classical exact (pairs.toFinset.filter F).card

theorem number_sum (F : Pair → Prop) : number F = ∑ e ∈ pairs.toFinset, flag (F e) := by
  classical exact (natBoole _ F).symm

theorem actual_band_flux {p q : Drawing 28 ℝ} (gp : GeneralPosition p)
    (gq : GeneralPosition q) (ix : Function.Injective (fun i => (q i).1))
    (area : ∀ i j k, orient (q i) (q j) (q k)=orient (p i) (p j) (p k))
    {X : Finset V} (first : StartsFirst q Finset.univ X) (size : X.card ≤ 10)
    {d : Nat} (hd : d≤4) :
    number (fun e => InBand p d e ∧ Mixed X e) = (2*d+1)*X.card := by
  classical
  let S := gateBand d
  let U : Finset V := Finset.univ
  have full : (schedule q U).toFinset=pairs.toFinset := by
    ext e; simp [schedule_mem,edgeSet,U]
  have atgate (g : Nat) (hg : g∈S) : (∑ e ∈ pairs.toFinset, charge q U X g e)=X.card := by
    have h := physical_gate_count gq ix (Finset.subset_univ X) first g
    rw [ls_finset _ _ (schedule_nodup q U),full] at h
    have cardT : (U \ X).card = 28-X.card := by rw [Finset.card_sdiff_of_subset (Finset.subset_univ X)]; rfl
    change _ = min X.card g - min X.card (g-(U \ X).card) at h
    rw [cardT] at h
    have range := List.mem_range'_1.mp (List.mem_toFinset.mp hg)
    change 14-d ≤ g ∧ g < 14-d + (2*d+1) at range
    have lower : X.card ≤ g := by omega
    have upper : g ≤ 28-X.card := by omega
    simpa only [min_eq_left lower,Nat.sub_eq_zero_of_le upper,Nat.min_zero,Nat.sub_zero] using h
  have every (e : Pair) (he : e∈pairs.toFinset) :
      flag (InBand p d e ∧ Mixed X e) = ∑ g ∈ S, charge q U X g e := by
    have matchGate := band_at_gate gp ix area (List.mem_toFinset.mp he) hd
    by_cases mixed : Mixed X e
    · simp only [charge,mixed,and_true]
      simp only [flag,matchGate,Finset.sum_ite_eq]
      rfl
    · simp [charge,mixed,flag]
  calc number (fun e => InBand p d e ∧ Mixed X e) =
        ∑ e ∈ pairs.toFinset, ∑ g ∈ S, charge q U X g e :=
          (number_sum _).trans (Finset.sum_congr rfl every)
       _ = ∑ g ∈ S, ∑ e ∈ pairs.toFinset, charge q U X g e := Finset.sum_comm
       _ = ∑ _g ∈ S, X.card := Finset.sum_congr rfl atgate
       _ = (2*d+1)*X.card := by simp [S,gateBand,List.toFinset_card_of_nodup (List.nodup_range' 1)]

end K28.Projection
