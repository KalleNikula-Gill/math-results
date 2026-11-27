import K28.StateEvents

namespace K28.Projection
open K28.Edges K28.Finite

set_option maxHeartbeats 1200000
attribute [local irreducible] pairs

private def exitTest (m g a : Nat) := bands.all fun d =>
  if 14-d≤g ∧ g≤14+d then (minimizingCuts m d).all (fun t => decide (t≤a)) else true
private def swapTest (m g a b : Nat) := decide (a<b) && bands.all fun d =>
  if 14-d≤g ∧ g≤14+d then true else (minimizingCuts m d).all (fun t => decide (a<t ∧ t≤b))

private theorem exit_tables : ∀ n : Fin 2, ∀ j : Fin 9, ∀ a : Fin (9+n.val),
    (plainRules (9+n.val)).exitsOK[j.val]![a.val]! = exitTest (9+n.val) (10+j.val) a.val := by decide +kernel
private theorem swap_tables : ∀ n : Fin 2, ∀ j : Fin 9, ∀ a b : Fin (9+n.val),
    (plainRules (9+n.val)).swapsOK[j.val]![a.val]![b.val]! =
    swapTest (9+n.val) (10+j.val) a.val b.val := by decide +kernel

private theorem band_mem {d : Nat} (h : d∈bands) : 1≤d ∧ d≤4 := by
  simp only [bands,List.mem_cons,List.not_mem_nil,or_false] at h; omega

private theorem gate_band_iff {d g : Nat} (sd : d≤4) : g∈gateBand d ↔ 14-d≤g ∧ g≤14+d := by
  simp only [gateBand,List.mem_toFinset,List.mem_range'_1]; omega

theorem initial_label_bound {p : Drawing 28 ℝ} (gp : GeneralPosition p) {X : Finset V}
    (F : GroupFrame p X) {a : V} (ha : a∈X) : initialLabel F.q X a < X.card := by
  rw [←initial_local F.q X a]; exact local_bound (F.gp gp) F.horizontal ha 0

private theorem inside_normal {X : Finset V} {e : Pair} {a b : V} (key : endpoints a b=e) :
    Inside X e ↔ a∈X ∧ b∈X := by
  rw [←key]; rcases le_total a b with h|h
  · simp [Inside,endpoints,min_eq_left h,max_eq_right h]
  · simp [Inside,endpoints,min_eq_right h,max_eq_left h,and_comm]

theorem permitted_exit {p : Drawing 28 ℝ} (gp : GeneralPosition p) {X : Finset V}
    (F : GroupFrame p X) (rules : LocalRules F) (size : X.card=9 ∨ X.card=10)
    {t e a b} (ev : FullEvent F.q t e a b) (ax : a∈X) (bx : b∉X)
    {j : Nat} (hj : j<9) (gate : gateAt F.q Finset.univ e=10+j) :
    (plainRules X.card).exitsOK[j]![initialLabel F.q X a]! = true := by
  classical
  have ab : a≠b := fun h => ev.order.ne (h ▸ rfl)
  have ein : e∈pairs := ev.key ▸ endpoint_pair a b ab
  have ka := initial_label_bound gp F ax
  have bound (d : Nat) (hd : d∈bands) (g : 14-d≤10+j ∧ 10+j≤14+d)
      (z : Nat) (hz : z∈minimizingCuts X.card d) : z≤initialLabel F.q X a := by
    by_contra! lt
    have h := rules.cuts d (band_mem hd) z hz
    have pref : a∈firstLabels F.q X z := Finset.mem_filter.mpr ⟨ax,lt⟩
    have outside : b∈(Finset.univ \ X : Finset V) := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,bx⟩
    have mix : Between (firstLabels F.q X z) (Finset.univ \ X) e := by
      rw [←ev.key]
      rcases le_total a b with h|h
      · simpa [Between,endpoints,min_eq_left h,max_eq_right h] using Or.inl (b:=b∈firstLabels F.q X z ∧ a∈Finset.univ \ X) (And.intro pref outside)
      · simpa [Between,endpoints,min_eq_right h,max_eq_left h] using Or.inr (a:=b∈firstLabels F.q X z ∧ a∈Finset.univ \ X) (And.intro pref outside)
    apply h.outsidePairs e ein mix
    exact (band_at_gate gp F.horizontal F.areas ein (band_mem hd).2).mpr (gate ▸ (gate_band_iff (band_mem hd).2).mpr g)
  have test : exitTest X.card (10+j) (initialLabel F.q X a)=true := by
    apply List.all_eq_true.mpr
    intro d hd; split_ifs with hg
    · exact List.all_eq_true.mpr fun z hz => decide_eq_true (bound d hd hg z hz)
    · rfl
  rcases size with sm|sm
  · rw [sm] at test ka ⊢; exact (exit_tables 0 ⟨j,hj⟩ ⟨initialLabel F.q X a,ka⟩).trans test
  · rw [sm] at test ka ⊢; exact (exit_tables 1 ⟨j,hj⟩ ⟨initialLabel F.q X a,ka⟩).trans test

theorem permitted_swap {p : Drawing 28 ℝ} (gp : GeneralPosition p) {X : Finset V}
    (F : GroupFrame p X) (rules : LocalRules F) (size : X.card=9 ∨ X.card=10)
    {t e a b} (ev : FullEvent F.q t e a b) (ax : a∈X) (bx : b∈X)
    {j : Nat} (hj : j<9) (gate : gateAt F.q Finset.univ e=10+j) :
    (plainRules X.card).swapsOK[j]![initialLabel F.q X a]![initialLabel F.q X b]! = true := by
  classical
  have ab : a≠b := fun h => ev.order.ne (h ▸ rfl)
  have ein : e∈pairs := ev.key ▸ endpoint_pair a b ab
  have ka := initial_label_bound gp F ax
  have kb := initial_label_bound gp F bx
  have order : initialLabel F.q X a<initialLabel F.q X b := by
    simp only [←initial_local]
    apply (ranks_order F.horizontal (local_order (F.gp gp) F.horizontal X 0) ax bx).mpr
    simpa [Earlier,seenAt] using ev.order
  have bound (d : Nat) (hd : d∈bands) (g : ¬(14-d≤10+j ∧ 10+j≤14+d))
      (z : Nat) (hz : z∈minimizingCuts X.card d) : initialLabel F.q X a<z ∧ z≤initialLabel F.q X b := by
    have h := rules.cuts d (band_mem hd) z hz
    have outside : ¬ InBand p d e := fun inside => g ((gate_band_iff (band_mem hd).2).mp
      (gate ▸ (band_at_gate gp F.horizontal F.areas ein (band_mem hd).2).mp inside))
    constructor
    · by_contra! ge
      have x : a∈X \ firstLabels F.q X z := Finset.mem_sdiff.mpr ⟨ax,fun hh => (not_lt.mpr ge) (Finset.mem_filter.mp hh).2⟩
      have y : b∈X \ firstLabels F.q X z := Finset.mem_sdiff.mpr ⟨bx,fun hh => (not_lt.mpr (ge.trans order.le)) (Finset.mem_filter.mp hh).2⟩
      exact outside (h.suffixPairs e (ev.key ▸ in_edgeSet x y ab))
    · by_contra! lt
      have x : a∈firstLabels F.q X z := Finset.mem_filter.mpr ⟨ax,order.trans lt⟩
      have y : b∈firstLabels F.q X z := Finset.mem_filter.mpr ⟨bx,lt⟩
      exact outside (h.prefixPairs e (ev.key ▸ in_edgeSet x y ab))
  have test : swapTest X.card (10+j) (initialLabel F.q X a) (initialLabel F.q X b)=true := by
    apply Bool.and_eq_true_iff.mpr
    refine ⟨decide_eq_true order,List.all_eq_true.mpr ?_⟩
    intro d hd; split_ifs with hg
    · rfl
    · exact List.all_eq_true.mpr fun z hz => decide_eq_true (bound d hd hg z hz)
  rcases size with sm|sm
  · rw [sm] at test ka kb ⊢; exact (swap_tables 0 ⟨j,hj⟩ ⟨initialLabel F.q X a,ka⟩ ⟨initialLabel F.q X b,kb⟩).trans test
  · rw [sm] at test ka kb ⊢; exact (swap_tables 1 ⟨j,hj⟩ ⟨initialLabel F.q X a,ka⟩ ⟨initialLabel F.q X b,kb⟩).trans test

end K28.Projection
