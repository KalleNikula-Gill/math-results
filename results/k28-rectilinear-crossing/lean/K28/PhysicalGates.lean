import K28.SweepRanks

namespace K28.Projection
open K28.Edges

def Mixed (X : Finset V) (e : Pair) :=
  (e.1∈X ∧ e.2∉X) ∨ (e.2∈X ∧ e.1∉X)

instance (X : Finset V) (e : Pair) : Decidable (Mixed X e) := by unfold Mixed; infer_instance

noncomputable def charge (q : Drawing 28 ℝ) (T X : Finset V) (g : Nat) (e : Pair) : Nat :=
  if gateAt q T e=g ∧ Mixed X e then 1 else 0

theorem normal_mixed (X : Finset V) (a b : V) : Mixed X (endpoints a b) ↔ Mixed X (a,b) := by
  rcases le_total a b with h|h
  · simp [Mixed,endpoints,min_eq_left h,max_eq_right h]
  · simp [Mixed,endpoints,min_eq_right h,max_eq_left h,or_comm]

private theorem split_count (X : Finset V) (P : V → Prop) [DecidablePred P] (u v : V) (uv : u≠v) :
    (X.filter P).card = (((X.erase u).erase v).filter P).card +
      (if u∈X ∧ P u then 1 else 0) + (if v∈X ∧ P v then 1 else 0) := by
  classical
  have cut (F : Finset V) (a : V) : F.card = (F.erase a).card + if a∈F then 1 else 0 := by
    by_cases m : a∈F
    · rw [if_pos m]; exact (Finset.card_erase_add_one m).symm
    · simp [m,Finset.erase_eq_of_notMem m]
  have hu := cut (X.filter P) u
  have hv := cut ((X.filter P).erase u) v
  have same : ((X.filter P).erase u).erase v = ((X.erase u).erase v).filter P := by
    ext a; simp only [Finset.mem_erase,Finset.mem_filter]; tauto
  rw [same] at hv
  simp only [Finset.mem_filter] at hu
  have hmem : v∈(X.filter P).erase u ↔ v∈X ∧ P v :=
    ⟨fun h => Finset.mem_filter.mp (Finset.mem_erase.mp h).2,
     fun h => Finset.mem_erase.mpr ⟨Ne.symm uv,Finset.mem_filter.mpr h⟩⟩
  simp only [hmem] at hv
  omega

theorem mass_step {q : Drawing 28 ℝ} {T X : Finset V} {g : Nat} (first : StartsFirst q T X)
    {r s : V → Nat} {e : Pair} (step : AdjacentEvent q T r s e) :
    (X.filter (fun i => s i<g)).card + charge q T X g e = (X.filter (fun i => r i<g)).card := by
  classical
  obtain ⟨u,hu,v,hv,key,dx,gate,adj,us,vs,other⟩ := step.swap
  have uv : u≠v := fun h => dx.ne (h ▸ rfl)
  have right : v∈X → u∈X := by
    intro vx; by_contra ux; exact dx.not_gt (first v vx u hu ux)
  have src := split_count X (fun i => r i<g) u v uv
  have dst := split_count X (fun i => s i<g) u v uv
  have fixed : (((X.erase u).erase v).filter (fun i => s i<g)) =
      (((X.erase u).erase v).filter (fun i => r i<g)) := by
    apply Finset.filter_congr
    intro i hi
    rw [other i (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1 (Finset.mem_erase.mp hi).1]
  rw [fixed] at dst
  have mixed : Mixed X e ↔ Mixed X (u,v) := key ▸ normal_mixed X u v
  rw [dst,src]
  unfold charge
  rw [if_congr (and_congr_right (fun _ => mixed)) rfl rfl]
  simp only [Mixed,us,vs,adj,← gate]
  by_cases ux : u∈X <;> by_cases vx : v∈X
  · simp [ux,vx,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]
  · simp [ux,vx]; split_ifs <;> omega
  · exact False.elim (ux (right vx))
  · simp [ux,vx]

theorem physical_gate_count {q : Drawing 28 ℝ} (gp : GeneralPosition q)
    (ix : Function.Injective (fun i => (q i).1)) {T X : Finset V}
    (sub : X⊆T) (first : StartsFirst q T X) (g : Nat) :
    ls (schedule q T) (charge q T X g) = min X.card g - min X.card (g-(T \ X).card) := by
  let L := schedule q T
  have flux (t : Nat) (ht : t≤L.length) :
      ls (L.take t) (charge q T X g) + mass q T X t g = mass q T X 0 g := by
    induction t with
    | zero => simp [ls]
    | succ t ih =>
      have lt : t<L.length := by omega
      have before := ih (by omega)
      have move := mass_step (g:=g) first (geometric_sweep gp ix T t lt)
      change mass q T X (t+1) g + charge q T X g L[t] = mass q T X t g at move
      rw [List.take_succ_eq_append_getElem lt]
      change (List.map (charge q T X g) (L.take t ++ [L[t]])).sum + _ = _
      rw [List.map_append,List.sum_append]
      change ls (L.take t) (charge q T X g) + (charge q T X g L[t] + 0) + _ = _
      omega
  have full := flux L.length (le_refl _)
  rw [List.take_length] at full
  change ls (schedule q T) (charge q T X g) + mass q T X (schedule q T).length g = mass q T X 0 g at full
  rw [first_mass q ix sub first, last_mass q ix sub first] at full
  omega

end K28.Projection
