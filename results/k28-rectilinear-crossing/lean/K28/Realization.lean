import K28.PhysicalMove

namespace K28.Projection
open K28.Edges K28.Finite

/-- The actual tagged projection sequence is an accepting walk in the
ordinary list-state checker. Off-band or irrelevant events are omitted. -/
theorem realize_sweep (p : Drawing 28 ℝ) (gp : GeneralPosition p) (X : Finset V) (F : GroupFrame p X)
    (size : X.card=9 ∨ X.card=10) (rules : LocalRules F) :
    PlainPath X.card (plainStart X.card) (realTrace F.q X) := by
  let L := schedule F.q Finset.univ
  have cap : X.card≤10 := by omega
  have rest (n t : Nat) (len : t+n=L.length) :
      PlainPath X.card (realState F.q X t) ((L.drop t).filterMap (mark F.q X)) := by
    induction n generalizing t with
    | zero =>
      have h : t=L.length := by omega
      rw [h,List.drop_length,List.filterMap_nil]
      exact (ending_state gp F cap) ▸ PlainPath.done
    | succ n ih =>
      have bound : t<L.length := by omega
      obtain ⟨a,b,ev⟩ := full_event F.horizontal t bound
      have step := physical_move gp F rules size ev
      have next := ih (t+1) (by omega)
      have advance : L[t]::L.drop (t+1) = L.drop t := List.getElem_cons_drop_succ_eq_drop bound
      rw [←advance,List.filterMap_cons]
      change (match mark F.q X L[t] with
        | none => realState F.q X (t+1)=realState F.q X t
        | some w => (realState F.q X (t+1),w)∈plainMoves X.card (plainRules X.card) (realState F.q X t)) at step
      cases eq : mark F.q X L[t] with
      | none => rw [eq] at step; exact step ▸ next
      | some w => rw [eq] at step; exact PlainPath.step step next
  have all := rest L.length 0 (by omega)
  rw [starting_state gp F cap,List.drop_zero] at all
  exact all

/-- The full geometric reduction and the computer-assisted exclusion,
relative only to the two published universal bounds on numbers of edges. -/
theorem minimum_from_edge_bounds
    (low : ∀ p : Drawing 28 ℝ, GeneralPosition p → ∀ k : Nat, k<12 → lower[k]! ≤ E (counts p) k)
    (central : ∀ p : Drawing 28 ℝ, GeneralPosition p → counts p 13 ≤ counts p 12) : MinimumIs 7234 :=
  minimum_reduction low central realize_sweep

/-- The novel exclusion for an actual real drawing given the historically
forced profile. This version has no sweep or search premise. -/
theorem no_drawing_with_profile (p : Drawing 28 ℝ) (gp : GeneralPosition p)
    (profile : ∀ k : Nat, k<14 → counts p k=K28.profile[k]!) : False := by
  have low : ∀ k : Nat, k<12 → lower[k]! ≤ E (counts p) k := by
    intro k hk
    have eq : E (counts p) k=E (fun j => K28.profile[j]!) k := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro j hj
      exact profile j (by have := List.mem_range.mp hj; omega)
    rw [eq]
    have table : ∀ k : Fin 12, lower[k.val]! ≤ E (fun j => K28.profile[j]!) k.val := by decide +kernel
    exact table ⟨k,hk⟩
  have cent : counts p 13≤counts p 12 := by rw [profile 13 (by decide),profile 12 (by decide)]; decide
  have wt : weighted (counts p)=weighted (fun j => K28.profile[j]!) := by
    apply congrArg List.sum; apply List.map_congr_left
    intro k hk; apply congrArg (fun n => (25-2*k)*n); apply congrArg List.sum; apply List.map_congr_left
    intro j hj; have a := List.mem_range.mp hk; have b := List.mem_range.mp hj
    exact profile j (by omega)
  have num : weighted (fun j => K28.profile[j]!)=9690 := by decide +kernel
  have rel := weighted_identity p gp
  have eq : crossings p=7233 := by omega
  obtain ⟨G,A,B,C,prof,compat,fifty⟩ := candidate_real_traces p gp low cent eq
  have hA := realize_sweep p gp _ A (Or.inr G.sizeA) (candidate_local_rules gp G prof (Or.inl rfl) A)
  have hB := realize_sweep p gp _ B (Or.inl G.sizeB) (candidate_local_rules gp G prof (Or.inr (Or.inl rfl)) B)
  have hC := realize_sweep p gp _ C (Or.inl G.sizeC) (candidate_local_rules gp G prof (Or.inr (Or.inr rfl)) C)
  rw [G.sizeA] at hA; rw [G.sizeB] at hB; rw [G.sizeC] at hC
  have contradiction := plain_paths_below_fifty (groupTraces A B C) hA hB hC compat
  omega

end K28.Projection
