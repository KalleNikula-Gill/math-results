import K28.LowArc

namespace K28.Low
open K28.Edges K28.Projection

noncomputable def frontSet (T : Finset V) (f : V → ℝ) (k : Nat) :=
  T.filter fun i => priorCount T f i<k
noncomputable def backSet (T : Finset V) (f : V → ℝ) (k : Nat) :=
  frontSet T (fun i => -f i) k

theorem ends_disjoint {T : Finset V} {f : V → ℝ} (inj : Set.InjOn f T) {k : Nat} (space : 2*k≤T.card) :
    Disjoint (frontSet T f k) (backSet T f k) := by
  classical
  apply Finset.disjoint_left.mpr
  intro a la ha
  obtain ⟨ma,low⟩ := Finset.mem_filter.mp la
  have high := (Finset.mem_filter.mp ha).2
  let L := T.filter fun i => f i<f a
  let H := T.filter fun i => -f i< -f a
  have d : Disjoint L H := Finset.disjoint_left.mpr (fun i hi hj =>
    (Finset.mem_filter.mp hi).2.not_gt (neg_lt_neg_iff.mp (Finset.mem_filter.mp hj).2))
  have union : L∪H=T.erase a := by
    ext i; simp only [L,H,Finset.mem_union,Finset.mem_filter,neg_lt_neg_iff,Finset.mem_erase]
    by_cases ti : i∈T
    · simp only [ti,true_and,and_true,←ne_iff_lt_or_gt]
      exact ⟨fun h eq => h (eq ▸ rfl),fun h eq => h (inj ti ma eq)⟩
    · simp [ti]
  have n := Finset.card_union_of_disjoint d
  rw [union,Finset.card_erase_of_mem ma] at n
  change L.card<k at low
  change H.card<k at high
  omega

/-- An oriented edge in this sector has its negative outward ray at z.
The common small-side cardinality is one less than the sweep gate. -/
noncomputable def sector (p : Drawing 28 ℝ) (T : Finset V) (g : Nat) (u v z : Vec) :=
  (T ×ˢ T).filter fun e => e.1≠e.2 ∧ side p T e+1=g ∧
    0<dot (normal p e) u ∧ 0<dot (normal p e) v ∧ dot (normal p e) z<0

theorem sector_mem {p : Drawing 28 ℝ} {T : Finset V} {g : Nat} {u v z : Vec} {a b : V} :
    (a,b)∈sector p T g u v z ↔ a∈T ∧ b∈T ∧ a≠b ∧ side p T (a,b)+1=g ∧
      0<dot (normal p (a,b)) u ∧ 0<dot (normal p (a,b)) v ∧ dot (normal p (a,b)) z<0 := by
  simp only [sector,Finset.mem_filter,Finset.mem_product]; tauto

theorem sector_event {p : Drawing 28 ℝ} {T : Finset V} {u v z : Vec}
    (uv : 0<cross u v) (vz : 0<cross v z) (zu : 0<cross z u)
    {a b : V} (ma : a∈T) (mb : b∈T) (xy : cross v (p a)<cross v (p b))
    (spos : 0<event (arcFrame p u v a) (arcFrame p u v b)) :
    (b,a)∈sector p T (gateAt (arcFrame p u v) T (a,b)) u v z := by
  classical
  let q := arcFrame p u v
  let t := event (q a) (q b)
  let dx := cross v (p b)-cross v (p a)
  let d := normal p (b,a)
  have xp : 0<dx := sub_pos.mpr xy
  have elapsed : t*dx=cross u (p b)-cross u (p a) := div_mul_cancel₀ _ xp.ne'
  have relation (x : Vec) : dx*(cross u x - t*cross v x)=cross u v*dot d x := by
    calc _ = dx*cross u x-(t*dx)*cross v x := by ring
         _ = _ := by rw [elapsed]; dsimp [dx,d,normal,perp,diff,dot,cross]; ring
  have positive (x : Vec) (h : 0<cross u x-t*cross v x) : 0<dot d x := by
    have m := mul_pos xp h; rw [relation] at m; exact (mul_pos_iff_of_pos_left uv).mp m
  have neg (x : Vec) (h : cross u x-t*cross v x<0) : dot d x<0 := by
    by_contra! bad
    have m := mul_neg_of_pos_of_neg xp h; rw [relation] at m
    exact m.not_ge (mul_nonneg uv.le bad)
  have below (i : V) : orient (p b) (p a) (p i)<0 ↔ value t (q i)<value t (q a) := by
    have rel := relation (diff (p i) (p a))
    have orient' : dot d (diff (p i) (p a))=orient (p b) (p a) (p i) := by
      dsimp [d,normal,diff,perp,dot,orient]; ring
    have level : cross u (diff (p i) (p a))-t*cross v (diff (p i) (p a)) =
        value t (q i)-value t (q a) := by dsimp [q,arcFrame,value,cross,diff]; ring
    rw [orient',level] at rel
    constructor
    · intro h; have m := mul_neg_of_pos_of_neg uv h; rw [←rel] at m
      by_contra! h'; exact m.not_ge (mul_nonneg xp.le (sub_nonneg.mpr h'))
    · intro h; have m := mul_neg_of_pos_of_neg xp (sub_neg.mpr h); rw [rel] at m
      by_contra! h'; exact m.not_ge (mul_nonneg uv.le h')
  have ba : b≠a := fun h => xy.ne (h ▸ rfl)
  apply sector_mem.mpr
  refine ⟨mb,ma,ba,?_,positive u ?_,positive v ?_,neg z ?_⟩
  · unfold gateAt side
    exact congrArg (fun s : Finset V => s.card+1) (Finset.filter_congr (fun i _ => below i))
  · rw [cross_self,cross_neg u]; change 0<t at spos
    linarith only [mul_pos spos uv]
  · simpa [cross_self] using uv
  · rw [cross_neg z]; change 0<t at spos
    linarith only [mul_pos spos vz,zu]

theorem sector_bound {p : Drawing 28 ℝ} (gp : GeneralPosition p) (T : Finset V) {u v z : Vec}
    (gu : Generic p u) (gv : Generic p v) (uv : 0<cross u v) (vz : 0<cross v z) (zu : 0<cross z u)
    (j : Nat) (space : j≤T.card) :
    j≤(sector p T j u v z).card+
      (frontSet T (fun i => cross u (p i)) j ∩ backSet T (fun i => cross v (p i)) j).card := by
  classical
  let A:=frontSet T (fun i => cross u (p i)) j
  let B:=backSet T (fun i => cross v (p i)) j
  have cover (i : V) : ∃ b : V, i∈A\B → (b,i)∈sector p T j u v z := by
    by_cases hi : i∈A\B
    · obtain ⟨a,nb⟩ := Finset.mem_sdiff.mp hi
      have ⟨mt,start⟩ := Finset.mem_filter.mp a
      have finish : j≤priorCount T (fun x => -cross v (p x)) i := by
        by_contra! bad; exact nb (Finset.mem_filter.mpr ⟨mt,bad⟩)
      obtain ⟨b,mb,xy,pos,g⟩ := exit_event (q:=arcFrame p u v) (arc_gp gp uv gv) gv gu mt start finish
      exact ⟨b,fun _ => g ▸ sector_event uv vz zu mt mb xy pos⟩
    · exact ⟨i,fun h => False.elim (hi h)⟩
  choose f includes using cover
  have mapped := Finset.card_le_card_of_injOn (fun i => (f i,i)) (fun i h => includes i h)
    (fun i _ h _ eq => congrArg Prod.snd eq)
  have card : A.card=j := prefix_card gu.injOn space
  have total := Finset.card_sdiff_add_card_inter A B
  change j≤_+(A∩B).card
  omega

end K28.Low
