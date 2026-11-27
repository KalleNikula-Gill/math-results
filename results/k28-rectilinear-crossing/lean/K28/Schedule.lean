import K28.SweepEvents

namespace K28.Projection
open K28.Edges

def edgeSet (T : Finset V) := pairs.toFinset.filter (fun e => e.1∈T ∧ e.2∈T)
noncomputable def timeOf (q : Drawing 28 ℝ) (e : Pair) := event (q e.1) (q e.2)
noncomputable def schedule (q : Drawing 28 ℝ) (T : Finset V) :=
  (edgeSet T).toList.mergeSort (fun e f => decide (timeOf q e ≤ timeOf q f))

theorem normalized_time (q : Drawing 28 ℝ) (i j : V) :
    timeOf q (endpoints i j) = event (q i) (q j) := by
  rcases le_total i j with ij|ji
  · simp [timeOf,endpoints,min_eq_left ij,max_eq_right ij]
  · simpa [timeOf,endpoints,min_eq_right ji,max_eq_left ji] using event_symm (q j) (q i)

theorem in_edgeSet {T : Finset V} {i j : V} (hi : i∈T) (hj : j∈T) (ij : i≠j) :
    endpoints i j ∈ edgeSet T := by
  apply Finset.mem_filter.mpr
  refine ⟨List.mem_toFinset.mpr (endpoint_pair _ _ ij),?_⟩
  rcases le_total i j with h|h
  · simpa only [endpoints,min_eq_left h,max_eq_right h] using And.intro hi hj
  · simpa only [endpoints,min_eq_right h,max_eq_left h] using And.intro hj hi

theorem normalized {T : Finset V} {e : Pair} (he : e∈edgeSet T) :
    e.1∈T ∧ e.2∈T ∧ e.1 < e.2 ∧ endpoints e.1 e.2 = e := by
  have a := Finset.mem_filter.mp he
  have order : pairs.all (fun e => decide (e.1<e.2)) = true := by decide +kernel
  have lt : e.1<e.2 := of_decide_eq_true (List.all_eq_true.mp order _ (List.mem_toFinset.mp a.1))
  exact ⟨a.2.1,a.2.2,lt,by simp [endpoints,min_eq_left lt.le,max_eq_right lt.le]⟩

theorem schedule_mem (q : Drawing 28 ℝ) (T : Finset V) (e : Pair) : e∈schedule q T ↔ e∈edgeSet T := by
  simp [schedule]

theorem schedule_nodup (q : Drawing 28 ℝ) (T : Finset V) : (schedule q T).Nodup :=
  (List.mergeSort_perm _ _).nodup_iff.mpr (edgeSet T).nodup_toList

theorem ordered_schedule (q : Drawing 28 ℝ) (T : Finset V) :
    (schedule q T).Pairwise (fun a b => timeOf q a ≤ timeOf q b) := by
  let compareTime := fun (a b : Pair) => decide (timeOf q a ≤ timeOf q b)
  have trans : ∀ a b c, compareTime a b → compareTime b c → compareTime a c := by
    intro a b c h h'; exact decide_eq_true ((of_decide_eq_true h).trans (of_decide_eq_true h'))
  have total : ∀ a b, compareTime a b || compareTime b a := by
    intro a b; simp only [compareTime,Bool.or_eq_true,decide_eq_true_eq]; exact le_total _ _
  exact (List.sorted_mergeSort trans total (edgeSet T).toList).imp (fun h => of_decide_eq_true h)

theorem frontier_at_split {q : Drawing 28 ℝ} {T : Finset V} {P R : List Pair} {e : Pair}
    (split : schedule q T=P++e::R) :
    Frontier q T P.toFinset (timeOf q e) ∧ e ∉ P.toFinset ∧ e∈edgeSet T := by
  have ord := ordered_schedule q T
  have nd := schedule_nodup q T
  rw [split,List.pairwise_append] at ord
  rw [split,List.nodup_append] at nd
  have early {f} (h : f∈P) : timeOf q f ≤ timeOf q e := ord.2.2 f h e List.mem_cons_self
  have late {f} (h : f∈e::R) : timeOf q e ≤ timeOf q f := by
    rcases List.mem_cons.mp h with he|mem
    · subst f; rfl
    · exact List.rel_of_pairwise_cons ord.2.1 mem
  constructor
  · constructor
    · intro i hi j hj ij before
      have mem := (schedule_mem q T _).mpr (in_edgeSet hi hj ij)
      rw [split,List.mem_append] at mem
      rcases mem with p|r
      · exact List.mem_toFinset.mpr p
      · have op := late r; rw [normalized_time] at op; exact False.elim (before.not_ge op)
    · intro i _ j _ _ after h
      have op := early (List.mem_toFinset.mp h)
      rw [normalized_time] at op
      exact after.not_ge op
  · constructor
    · intro mem; exact nd.2.2 _ (List.mem_toFinset.mp mem) _ List.mem_cons_self rfl
    · apply (schedule_mem q T _).mp; rw [split]; exact List.mem_append_right _ List.mem_cons_self

noncomputable def seenAt (q : Drawing 28 ℝ) (T : Finset V) (t : Nat) := ((schedule q T).take t).toFinset
noncomputable def rankAt (q : Drawing 28 ℝ) (T : Finset V) (t : Nat) := rank q T (seenAt q T t)

noncomputable def gateAt (q : Drawing 28 ℝ) (T : Finset V) (e : Pair) :=
  (T.filter fun i => value (timeOf q e) (q i) < value (timeOf q e) (q e.1)).card + 1

theorem normalized_gate {q : Drawing 28 ℝ} (ix : Function.Injective (fun i => (q i).1))
    (T : Finset V) {i j : V} (ij : i≠j) : gateAt q T (endpoints i j) = gateAt q T (i,j) := by
  rcases le_total i j with h|h
  · simp [endpoints,min_eq_left h,max_eq_right h]
  · simp only [endpoints,min_eq_right h,max_eq_left h,gateAt,timeOf]
    simp only [event_symm (q j) (q i),tie (q i) (q j) (ix.ne ij)]

structure AdjacentEvent (q : Drawing 28 ℝ) (T : Finset V)
    (r s : V → Nat) (e : Pair) : Prop where
  swap : ∃ a ∈ T, ∃ b ∈ T, e=endpoints a b ∧ (q a).1<(q b).1 ∧
    r a+1=gateAt q T e ∧ r b=r a+1 ∧ s a=r b ∧ s b=r a ∧ ∀ i, i≠a → i≠b → s i=r i

/-- An actual half-rotation has a finite schedule containing every pair
of retained labels exactly once. Consecutive ranks interchange at
adjacent slots; a slope tie between disjoint pairs causes no omission. -/
theorem geometric_sweep {q : Drawing 28 ℝ} (gp : GeneralPosition q)
    (ix : Function.Injective (fun i => (q i).1)) (T : Finset V) (t : Nat)
    (ht : t<(schedule q T).length) :
    AdjacentEvent q T (rankAt q T t) (rankAt q T (t+1)) ((schedule q T)[t]) := by
  classical
  let L := schedule q T
  let e := L[t]'ht
  let D := (L.take t).toFinset
  have split : schedule q T = L.take t ++ e :: L.drop (t+1) := by
    rw [List.getElem_cons_drop_succ_eq_drop, List.take_append_drop]
  obtain ⟨front,pending,mem⟩ := frontier_at_split split
  obtain ⟨ha,hb,ab,norm⟩ := normalized mem
  have after : seenAt q T (t+1)=insert e D := by
    change (L.take (t+1)).toFinset = insert e (L.take t).toFinset
    rw [List.take_succ_eq_append_getElem ht]
    ext k
    simp only [List.mem_toFinset,List.mem_append,List.mem_singleton,Finset.mem_insert]
    exact or_comm
  have make {u v : V} (hu : u∈T) (hv : v∈T) (ord : (q u).1<(q v).1) (key : endpoints u v = e) :
      AdjacentEvent q T (rankAt q T t) (rankAt q T (t+1)) e := by
    have time : event (q u) (q v)=timeOf q e := by rw [←key,normalized_time]
    have pre : endpoints u v ∉ D := key ▸ pending
    obtain ⟨start,step1,step2,other⟩ := rank_step gp ix hu hv ord (time ▸ front) pre
    have uv : u≠v := fun h => ord.ne (h ▸ rfl)
    have gate : rankAt q T t u+1 = gateAt q T e := by
      have edge := (prior_at_event gp ix hu hv ord (time ▸ front) pre).1
      calc _ = gateAt q T (u,v) := congrArg (fun z : Finset V => z.card+1) edge
           _ = _ := (normalized_gate ix T uv).symm.trans (congrArg (gateAt q T) key)
    refine ⟨u,hu,v,hv,key.symm,ord,gate,start,?_,?_,?_⟩
    · unfold rankAt; rw [after,←key]; exact step1
    · unfold rankAt; rw [after,←key]; exact step2
    · intro i iu iv; unfold rankAt; rw [after,←key]; exact other _ iu iv
  rcases lt_or_gt_of_ne (ix.ne ab.ne) with lt|lt
  · exact make ha hb lt norm
  · exact make hb ha lt ((same_edge.mpr (Or.inr ⟨rfl,rfl⟩)).trans norm)

end K28.Projection
