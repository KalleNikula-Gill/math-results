import K28.StateEvents

namespace K28.Projection
open K28.Edges K28.Finite

set_option maxHeartbeats 1200000
attribute [local irreducible] pairs

theorem FullEvent.adjacent {q : Drawing 28 ℝ} (gp : GeneralPosition q) (ix : Function.Injective (fun i => (q i).1))
    {t e a b} (ev : FullEvent q t e a b) :
    AdjacentEvent q Finset.univ (rankAt q Finset.univ t) (rankAt q Finset.univ (t+1)) e := by
  obtain ⟨adj,left,right,other⟩ := ev.ranks gp ix (Finset.mem_univ a) (Finset.mem_univ b)
  exact ⟨a,Finset.mem_univ _,b,Finset.mem_univ _,ev.key.symm,ev.order,ev.gate gp ix _,adj,left,right,other⟩

theorem FullEvent.occupancy {q : Drawing 28 ℝ} (gp : GeneralPosition q) (ix : Function.Injective (fun i => (q i).1))
    {t e a b} (ev : FullEvent q t e a b) {X : Finset V} (ax : a∈X) :
    let g := gateAt q Finset.univ e
    mass q Finset.univ X t (g-1)+1=mass q Finset.univ X t g ∧
      mass q Finset.univ X t g=localRank q X t a+1 ∧
      (b∈X → mass q Finset.univ X t (g+1)=mass q Finset.univ X t g+1) := by
  let g := gateAt q Finset.univ e
  have pos : rankAt q Finset.univ t a+1=g := ev.gate gp ix Finset.univ
  have rb : rankAt q Finset.univ t b=g := (ev.ranks gp ix (Finset.mem_univ a) (Finset.mem_univ b)).1.trans pos
  have gm : g-1=rankAt q Finset.univ t a := by omega
  have one := mass_increment gp ix X t (rankAt q Finset.univ t a)
  rw [if_pos ⟨a,ax,rfl⟩,pos,mass_rank gp ix X t a] at one
  refine ⟨?_,one,?_⟩
  · change mass q Finset.univ X t (g-1)+1=mass q Finset.univ X t g
    rw [gm,mass_rank gp ix X t a,one]
  · intro bx
    have inc := mass_increment gp ix X t g
    have hit : ∃ i∈X, rankAt q Finset.univ t i=g := ⟨b,bx,rb⟩
    rw [if_pos hit] at inc
    exact inc

private theorem perm_ext {q : Drawing 28 ℝ} (gp : GeneralPosition q) (ix : Function.Injective (fun i => (q i).1))
    {X : Finset V} (t : Nat) (p : List Nat) (len : p.length=X.card)
    (lookup : ∀ i∈X, p[localRank q X t i]! = initialLabel q X i) : (realState q X t).permutation=p := by
  apply List.ext_getElem (by simp [realState,len])
  intro k hl hr
  have kb : k<X.card := len ▸ hr
  obtain ⟨i,hi,eq⟩ := local_surjective gp ix t kb
  have v := (lookup_perm gp ix t hi).trans (lookup i hi).symm
  rw [eq,getElem!_pos (realState q X t).permutation k hl,getElem!_pos p k hr] at v
  exact v

theorem perm_unchanged {q : Drawing 28 ℝ} (gp : GeneralPosition q) (ix : Function.Injective (fun i => (q i).1))
    {t e a b} (ev : FullEvent q t e a b) {X : Finset V} (h : ¬(a∈X ∧ b∈X)) :
    (realState q X (t+1)).permutation=(realState q X t).permutation := by
  apply perm_ext gp ix (t+1) _ (by simp [realState])
  intro i hi
  rw [ev.other_ranks h hi]
  exact lookup_perm gp ix t hi

theorem perm_swapped {q : Drawing 28 ℝ} (gp : GeneralPosition q) (ix : Function.Injective (fun i => (q i).1))
    {t e a b} (ev : FullEvent q t e a b) {X : Finset V} (ax : a∈X) (bx : b∈X) :
    let r := localRank q X t a
    (realState q X (t+1)).permutation=(((realState q X t).permutation.set r (initialLabel q X b)).set (r+1) (initialLabel q X a)) := by
  let p := (realState q X t).permutation
  let k := localRank q X t a
  apply perm_ext gp ix (t+1) _ (by simp [realState])
  intro i hi
  let l := localRank q X (t+1) i
  have bounds : l<p.length := by simpa [l,p,realState] using local_bound gp ix hi (t+1)
  have key := ev.ranks gp ix ax bx
  change ((p.set k (initialLabel q X b)).set (k+1) (initialLabel q X a))[l]! = _
  rw [getElem!_pos ((p.set k _).set _ _) l (by simpa using bounds)]
  simp only [List.getElem_set]
  by_cases ia : i=a
  · subst i; have eq : l=k+1 := key.2.1.trans key.1
    simp [eq]
  by_cases ib : i=b
  · subst i; have eq : l=k := key.2.2.1
    simp [eq]
  have old : l=localRank q X t i := key.2.2.2 i ia ib
  have inj := rank_injective ix (local_order gp ix X t)
  have na : l≠k := fun h => ia (inj hi ax (old.symm.trans h))
  have nb : l≠k+1 := fun h => ib (inj hi bx ((old.symm.trans h).trans key.1.symm))
  simp only [if_neg na,if_neg nb,if_neg na.symm,if_neg nb.symm]
  have prev := lookup_perm gp ix t hi
  change p[localRank q X t i]! = _ at prev
  rw [←old,getElem!_pos p l bounds] at prev
  exact prev

private theorem pref_ext (q : Drawing 28 ℝ) (X : Finset V) (t : Nat) (p : List Nat) (len : p.length=9)
    (lookup : ∀ j : Nat, j<9 → p[j]! = mass q Finset.univ X t (10+j)) : (realState q X t).prefixes=p := by
  apply List.ext_getElem (by simp [realState,len]); intro j hj hp
  have h : j<9 := len ▸ hp
  have s := (lookup_count q X t j h).trans (lookup j h).symm
  rw [getElem!_pos (realState q X t).prefixes j hj,getElem!_pos p j hp] at s
  exact s

theorem count_update {p : Drawing 28 ℝ} (gp : GeneralPosition p) {X : Finset V} (F : GroupFrame p X)
    {t e a b} (ev : FullEvent F.q t e a b) (g : Nat) :
    mass F.q Finset.univ X (t+1) g+charge F.q Finset.univ X g e=mass F.q Finset.univ X t g :=
  mass_step F.first (ev.adjacent (F.gp gp) F.horizontal)

theorem pref_same {p : Drawing 28 ℝ} (gp : GeneralPosition p) {X : Finset V} (F : GroupFrame p X)
    {t e a b} (ev : FullEvent F.q t e a b)
    (silent : ¬Mixed X e ∨ ¬(10≤gateAt F.q Finset.univ e ∧ gateAt F.q Finset.univ e≤18)) :
    (realState F.q X (t+1)).prefixes=(realState F.q X t).prefixes := by
  apply pref_ext _ _ _ _ (by simp [realState]); intro j hj
  rw [lookup_count _ _ _ _ hj]
  have zero : ¬(gateAt F.q Finset.univ e=10+j ∧ Mixed X e) := by
    rintro ⟨g,m⟩; rcases silent with h|h; exact h m; apply h; omega
  simpa only [charge,if_neg zero,Nat.add_zero] using (count_update gp F ev (10+j)).symm

theorem pref_drops {p : Drawing 28 ℝ} (gp : GeneralPosition p) {X : Finset V} (F : GroupFrame p X)
    {t e a b} (ev : FullEvent F.q t e a b) (mixed : Mixed X e) {j : Nat} (hj : j<9) (g : gateAt F.q Finset.univ e=10+j) :
    (realState F.q X (t+1)).prefixes=(realState F.q X t).prefixes.set j (mass F.q Finset.univ X t (10+j)-1) := by
  apply pref_ext _ _ _ _ (by simp [realState])
  intro k hk
  let s := (realState F.q X t).prefixes
  have h := count_update gp F ev (10+k)
  have kb : k<s.length := by simpa [s,realState] using hk
  change (s.set j _)[k]! = _
  rw [getElem!_pos (s.set j _) k (by simpa using kb),List.getElem_set]
  by_cases kj : k=j
  · subst k; simp only [if_true]; simp only [charge,if_pos (And.intro g mixed)] at h; omega
  · have ne : gateAt F.q Finset.univ e≠10+k := by omega
    simp only [if_neg kj,if_neg (Ne.symm kj)]
    simp only [charge,ne,false_and,if_false,Nat.add_zero] at h
    have old := lookup_count F.q X t k hk
    change s[k]! = _ at old
    rw [getElem!_pos s k kb] at old
    exact old.trans h.symm

end K28.Projection
