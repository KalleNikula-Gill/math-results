import K28.LowDirections

namespace K28.Low
open K28.Edges K28.Projection

/-- In the new coordinate system the positive-time sweep has projection
cross(u,p) - t cross(v,p). Its starting and final orders are the two
orders needed for the angular sector bounded by u and v. -/
def arcFrame (p : Drawing 28 ℝ) (u v : Vec) : Drawing 28 ℝ := fun i => (cross v (p i),cross u (p i))
def arcNormal (u v : Vec) (s : ℝ) : Vec := (-u.2+s*v.2,u.1-s*v.1)

theorem arc_gp {p : Drawing 28 ℝ} (gp : GeneralPosition p) {u v : Vec} (uv : 0<cross u v)
    (gen : Generic p v) : GeneralPosition (arcFrame p u v) := by
  refine ⟨fun a b h => gen (congrArg Prod.fst h),?_⟩
  intro a b c ab ac bc
  have id : orient (arcFrame p u v a) (arcFrame p u v b) (arcFrame p u v c) =
      -(cross u v)*orient (p a) (p b) (p c) := by unfold arcFrame orient cross; dsimp; ring
  rw [id]; exact mul_ne_zero (neg_ne_zero.mpr uv.ne') (gp.2 a b c ab ac bc)

private theorem split_time {α : Type*} (f : α → ℝ) {L : List α}
    (ord : L.Pairwise (fun a b => f a≤f b)) (nz : ∀ a∈L, f a≠0) :
    ∃ P R, L=P++R ∧ (∀ a∈P, f a<0) ∧ ∀ a∈R, 0<f a := by
  induction L with
  | nil => exact ⟨[],[],rfl,by simp,by simp⟩
  | cons a L ih =>
    rcases lt_or_gt_of_ne (nz a List.mem_cons_self) with neg|pos
    · obtain ⟨P,R,split,before,after⟩ := ih (List.pairwise_cons.mp ord).2
        (fun i hi => nz i (List.mem_cons_of_mem _ hi))
      refine ⟨a::P,R,by simp [split],?_,after⟩
      intro i hi; rcases List.mem_cons.mp hi with rfl|mem
      · exact neg
      · exact before i mem
    · refine ⟨[],a::L,rfl,by simp,?_⟩
      intro i hi; rcases List.mem_cons.mp hi with rfl|mem
      · exact pos
      · exact pos.trans_le ((List.pairwise_cons.mp ord).1 i mem)

private theorem at_zero {q : Drawing 28 ℝ} (ix : Function.Injective (fun i => (q i).1))
    (iy : Function.Injective (fun i => (q i).2)) (T : Finset V) :
    ∃ m, m≤(schedule q T).length ∧
      (∀ i∈T, rankAt q T m i=priorCount T (fun j => (q j).2) i) ∧
      ∀ t, m≤t → ∀ hi : t<(schedule q T).length, 0<timeOf q ((schedule q T)[t]) := by
  classical
  let L := schedule q T
  have nz (e : Pair) (he : e∈L) : timeOf q e≠0 := by
    have lt := (normalized ((schedule_mem q T _).mp he)).2.2.1
    exact div_ne_zero (sub_ne_zero.mpr (iy.ne lt.ne.symm)) (sub_ne_zero.mpr (ix.ne lt.ne.symm))
  obtain ⟨P,R,split,neg,pos⟩ := split_time (timeOf q) (ordered_schedule q T) nz
  have front : Frontier q T P.toFinset 0 := by
    constructor
    · intro i hi j hj ne old
      have mem := (schedule_mem q T _).mpr (in_edgeSet hi hj ne)
      rw [split,List.mem_append] at mem
      rcases mem with h|h
      · exact List.mem_toFinset.mpr h
      · have later := pos _ h; rw [normalized_time] at later; linarith only [later,old]
    · intro i hi j hj ne late h
      have before := neg _ (List.mem_toFinset.mp h)
      rw [normalized_time] at before
      linarith only [before,late]
  have seen : seenAt q T P.length=P.toFinset := by simp [seenAt,split]
  refine ⟨P.length,by simp [split],?_,?_⟩
  · intro i hi
    unfold rankAt rank priorCount
    rw [seen]
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro j hj
    by_cases ji : j=i
    · subst j; simp [Earlier]
    have diff : value 0 (q j)≠value 0 (q i) := by simpa [value] using iy.ne ji
    simpa [value] using relative_order ix front hj hi diff
  · intro t lo hi
    have hR : t-P.length<R.length := by rw [split,List.length_append] at hi; omega
    apply pos
    rw [List.getElem_of_eq split, List.getElem_append_right lo]
    exact List.getElem_mem hR

private theorem crosses_rank (r : Nat → Nat) {m n k : Nat} (mn : m≤n) (lo : r m<k) (hi : k≤r n) :
    ∃ t, m≤t ∧ t<n ∧ r t<k ∧ k≤r (t+1) := by
  induction n with
  | zero => have h : m=0 := by omega
            subst m; omega
  | succ n ih =>
    by_cases eq : m=n+1
    · subst m; omega
    by_cases atN : k≤r n
    · obtain ⟨t,l,r',a,b⟩ := ih (by omega) atN
      exact ⟨t,l,by omega,a,b⟩
    · exact ⟨n,by omega,by omega,by omega,hi⟩

/-- Each point leaving a prefix in this angular sector is the right-moving
endpoint of a real positive-time event at the specified gate. -/
theorem exit_event {q : Drawing 28 ℝ} (gp : GeneralPosition q)
    (ix : Function.Injective (fun i => (q i).1)) (iy : Function.Injective (fun i => (q i).2))
    {T : Finset V} {a : V} (ha : a∈T) {k : Nat}
    (start : priorCount T (fun i => (q i).2) a<k)
    (finish : k≤priorCount T (fun i => -(q i).1) a) :
    ∃ b∈T, (q a).1<(q b).1 ∧ 0<event (q a) (q b) ∧ gateAt q T (a,b)=k := by
  classical
  obtain ⟨m,mn,atM,time⟩ := at_zero ix iy T
  have first : StartsFirst q T T := fun _ _ _ h n => False.elim (n h)
  have last := last_rank q (Finset.Subset.refl T) first ha
  simp only [Finset.sdiff_self,Finset.card_empty,zero_add] at last
  obtain ⟨t,lo,lt,l,h⟩ := crosses_rank (fun t => rankAt q T t a) mn (by change rankAt q T m a<k; rwa [atM a ha]) (by change k≤rankAt q T _ a; rw [last]; exact finish)
  obtain ⟨x,mx,y,my,key,xy,gate,adj,sx,sy,other⟩ := (geometric_sweep gp ix T t lt).swap
  have ax : a=x := by
    by_contra neq
    by_cases ay : a=y
    · subst a
      omega
    · have eq := other a neq ay
      omega
  subst x
  have ab : a≠y := fun z => xy.ne (z ▸ rfl)
  have when := time t lo lt
  rw [key,normalized_time] at when
  rw [key,normalized_gate ix T ab] at gate
  exact ⟨y,my,xy,when,by omega⟩

end K28.Low
