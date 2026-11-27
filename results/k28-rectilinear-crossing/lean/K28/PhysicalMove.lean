import K28.RuleTests
import K28.StateUpdates

namespace K28.Projection
open K28.Edges K28.Finite

private theorem list_exit {m j : Nat} {S : PlainState} (hj : j<9) {r a : Nat}
    (n : 0<r) (ru : S.prefixes[j]! = r) (av : S.permutation[r-1]! = a)
    (shape : validCounts m (S.prefixes.set j (r-1))=true)
    (allow : (plainRules m).exitsOK[j]![a]! = true) :
    (⟨S.permutation,S.prefixes.set j (r-1)⟩,0)∈plainMoves m (plainRules m) S := by
  apply List.mem_flatMap.mpr
  refine ⟨j,List.mem_range.mpr hj,?_⟩
  dsimp only
  rw [ru,if_neg (by omega : r≠0),av]
  apply List.mem_append_left
  simp [shape,allow]

private theorem list_swap {m j : Nat} {S : PlainState} (hj : j<9) {r a b : Nat}
    (n : 0<r) (lt : r<m) (ru : S.prefixes[j]! = r) (av : S.permutation[r-1]! = a)
    (bv : S.permutation[r]! = b) (left : j=0 ∨ S.prefixes[j-1]!+1=r)
    (right : j=8 ∨ S.prefixes[j+1]! =r+1) (allow : (plainRules m).swapsOK[j]![a]![b]! = true) :
    (⟨(S.permutation.set (r-1) b).set r a,S.prefixes⟩,tag (10+j) r)∈plainMoves m (plainRules m) S := by
  apply List.mem_flatMap.mpr
  refine ⟨j,List.mem_range.mpr hj,?_⟩
  dsimp only
  rw [ru,if_neg (by omega : r≠0),av]
  apply List.mem_append_right
  have le : (decide (j=0) || S.prefixes[j-1]!+1 == r)=true := by simpa using left
  have ri : (decide (j=8) || S.prefixes[j+1]! == r+1)=true := by simpa using right
  simp [le,ri,lt,bv,allow]
  simpa using And.intro left right

private theorem state_eq {s u : PlainState} (p : s.permutation=u.permutation) (c : s.prefixes=u.prefixes) : s=u := by
  cases s; cases u; simp_all

private theorem inside_iff {X : Finset V} {e : Pair} {a b : V} (key : endpoints a b=e) : Inside X e ↔ a∈X ∧ b∈X := by
  rw [←key]; rcases le_total a b with h|h
  · simp [Inside,endpoints,min_eq_left h,max_eq_right h]
  · simp [Inside,endpoints,min_eq_right h,max_eq_left h,and_comm]

/-- An actual event either has no effect on the projected list state,
or its exact tag and exact successor occur among the ordinary moves. -/
theorem physical_move {p : Drawing 28 ℝ} (gp : GeneralPosition p) {X : Finset V}
    (F : GroupFrame p X) (rules : LocalRules F) (size : X.card=9 ∨ X.card=10)
    {t e a b} (ev : FullEvent F.q t e a b) :
    match mark F.q X e with
    | none => realState F.q X (t+1)=realState F.q X t
    | some w => (realState F.q X (t+1),w)∈plainMoves X.card (plainRules X.card) (realState F.q X t) := by
  classical
  let q := F.q
  let S := realState q X t
  let N := realState q X (t+1)
  let g := gateAt q Finset.univ e
  have i_eq := inside_iff (X:=X) ev.key
  have mix_eq : Mixed X e ↔ Mixed X (a,b) := ev.key ▸ normal_mixed X a b
  have ab : a≠b := fun eq => ev.order.ne (eq ▸ rfl)
  by_cases range : 10≤g ∧ g≤18
  · let j := g-10
    have hj : j<9 := by dsimp [j]; omega
    have gate : gateAt q Finset.univ e=10+j := by change g=10+(g-10); omega
    by_cases ax : a∈X
    · have occ := ev.occupancy (F.gp gp) F.horizontal ax
      let r := localRank q X t a+1
      have er : gateAt q X e=r := (ev.gate (F.gp gp) F.horizontal X).symm
      have n : 0<r := Nat.zero_lt_succ _
      have massR : mass q Finset.univ X t (10+j)=r := gate ▸ occ.2.1
      have ru : S.prefixes[j]! = r := (lookup_count q X t j hj).trans massR
      have av : S.permutation[r-1]! = initialLabel q X a := by
        change (realState q X t).permutation[localRank q X t a+1-1]! = _
        simpa only [Nat.add_sub_cancel] using lookup_perm (F.gp gp) F.horizontal t ax
      by_cases bx : b∈X
      · have inner := i_eq.mpr ⟨ax,bx⟩
        have mixed : ¬Mixed X e := fun h => by rcases mix_eq.mp h with h|h; exact h.2 bx; exact h.2 ax
        have rb : r<X.card := (rank_bounds (F.gp gp) F.horizontal (ev.key ▸ in_edgeSet ax bx ab)).2 |> fun h => er ▸ h
        have lr : localRank q X t b=r := (ev.ranks (F.gp gp) F.horizontal ax bx).1
        have bv : S.permutation[r]! = initialLabel q X b := lr ▸ lookup_perm (F.gp gp) F.horizontal t bx
        have left : j=0 ∨ S.prefixes[j-1]!+1=r := by
          by_cases z : j=0; exact Or.inl z
          right
          rw [show S.prefixes[j-1]! = _ from lookup_count q X t (j-1) (by omega)]
          rw [show 10+(j-1)=g-1 by omega]
          exact occ.1.trans occ.2.1
        have right : j=8 ∨ S.prefixes[j+1]! =r+1 := by
          by_cases z : j=8; exact Or.inl z
          right
          rw [show S.prefixes[j+1]! = _ from lookup_count q X t (j+1) (by omega)]
          rw [show 10+(j+1)=g+1 by omega,occ.2.2 bx,occ.2.1]
        have afterP := perm_swapped (F.gp gp) F.horizontal ev ax bx
        have next : N=⟨(S.permutation.set (r-1) (initialLabel q X b)).set r (initialLabel q X a),S.prefixes⟩ :=
          state_eq afterP (pref_same gp F ev (Or.inl mixed))
        have move := list_swap hj n rb ru av bv left right (permitted_swap gp F rules size ev ax bx hj gate)
        change (match mark F.q X e with | none => N=S | some w => (N,w)∈plainMoves _ _ S)
        simp only [mark,show 10≤gateAt F.q Finset.univ e ∧ gateAt F.q Finset.univ e≤18 from range,inner,if_true]
        rw [show gateAt F.q Finset.univ e=10+j from gate,show gateAt F.q X e=r from er,next]
        exact move
      · have inner : ¬Inside X e := fun h => bx (i_eq.mp h).2
        have mix : Mixed X e := mix_eq.mpr (Or.inl ⟨ax,bx⟩)
        have hp := perm_unchanged (F.gp gp) F.horizontal ev (fun h => bx h.2)
        have hc := pref_drops gp F ev mix hj gate
        change N.prefixes=S.prefixes.set j (mass q Finset.univ X t (10+j)-1) at hc
        rw [massR] at hc
        have ok := actual_counts_valid (F.gp gp) F.horizontal X (t+1)
        change validCounts X.card N.prefixes=true at ok
        rw [hc] at ok
        have next : N=⟨S.permutation,S.prefixes.set j (r-1)⟩ := state_eq hp hc
        have move := list_exit hj n ru av ok (permitted_exit gp F rules size ev ax bx hj gate)
        change (match mark F.q X e with | none => N=S | some w => (N,w)∈plainMoves _ _ S)
        simp only [mark,show 10≤gateAt F.q Finset.univ e ∧ gateAt F.q Finset.univ e≤18 from range,inner,if_false,mix,if_true,next]
        exact move
    · have bx : b∉X := fun h => ev.order.not_gt (F.first b h a (Finset.mem_univ _) ax)
      have inn : ¬Inside X e := fun h => ax (i_eq.mp h).1
      have mix : ¬Mixed X e := fun h => by rcases mix_eq.mp h with h|h; exact ax h.1; exact bx h.1
      simp only [mark,show 10≤gateAt F.q Finset.univ e ∧ gateAt F.q Finset.univ e≤18 from range,if_true,inn,if_false,mix]
      exact state_eq (perm_unchanged (F.gp gp) F.horizontal ev (fun h => ax h.1)) (pref_same gp F ev (Or.inl mix))
  · have inn : ¬(a∈X ∧ b∈X) := fun h => range (rules.tracked e (ev.key ▸ in_edgeSet h.1 h.2 ab))
    simp only [mark,show ¬(10≤gateAt F.q Finset.univ e ∧ gateAt F.q Finset.univ e≤18) from range,if_false]
    exact state_eq (perm_unchanged (F.gp gp) F.horizontal ev inn) (pref_same gp F ev (Or.inr range))

end K28.Projection
