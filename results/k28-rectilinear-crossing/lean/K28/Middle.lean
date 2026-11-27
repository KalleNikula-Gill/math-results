import K28.Realization

namespace K28.Projection
open K28.Edges

attribute [local irreducible] pairs

theorem unrestricted_frame {p : Drawing 28 ℝ} (gp : GeneralPosition p) :
    ∃ q : Drawing 28 ℝ, Function.Injective (fun i => (q i).1) ∧
      ∀ i j k, orient (q i) (q j) (q k)=orient (p i) (p j) (p k) := by
  classical
  obtain ⟨m,_,top⟩ := (Finset.univ : Finset V).exists_max_image (fun i => (p i).1) Finset.univ_nonempty
  let X := Finset.univ.filter (fun i => (p i).1=(p m).1)
  have existsOutside : ∃ i, i∉X := by
    by_contra! all
    have common (i : V) : (p i).1=(p m).1 := (Finset.mem_filter.mp (all i)).2
    apply gp.2 0 1 2 (by decide) (by decide) (by decide)
    simp only [orient,common 0,common 1,common 2,sub_self,zero_mul,mul_zero]
  have sep : StrictlySeparated p X := by
    refine ⟨1,0,?_⟩
    intro i hi j hj
    have n : (p j).1 ≠ (p m).1 := fun h => hj (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
    simpa [(Finset.mem_filter.mp hi).2] using (top j (Finset.mem_univ j)).lt_of_ne n
  obtain ⟨q,ix,_,area⟩ := starting_frame gp sep ⟨m,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩⟩ existsOutside
  exact ⟨q,ix,area⟩

noncomputable def middle (q : Drawing 28 ℝ) (t : Nat) : Finset V :=
  Finset.univ.filter fun i => rankAt q Finset.univ t i=13 ∨ rankAt q Finset.univ t i=14

theorem middle_closes {q : Drawing 28 ℝ} (ix : Function.Injective (fun i => (q i).1)) :
    middle q (schedule q Finset.univ).length=middle q 0 := by
  ext i
  have rev := reverse_local ix (Finset.mem_univ i)
  rw [←initial_local q Finset.univ i] at rev
  change rankAt q Finset.univ (schedule q Finset.univ).length i+rankAt q Finset.univ 0 i+1=28 at rev
  simp only [middle,Finset.mem_filter,Finset.mem_univ,true_and]
  omega

def unordered (e : Pair) : Finset V := {e.1,e.2}

theorem middle_at_center {q : Drawing 28 ℝ} (gp : GeneralPosition q) (ix : Function.Injective (fun i => (q i).1))
    {t e a b} (ev : FullEvent q t e a b) (central : gateAt q Finset.univ e=14) :
    middle q t=unordered e := by
  have g := ev.gate gp ix Finset.univ
  change rankAt q Finset.univ t a+1=gateAt q Finset.univ e at g
  have adj := (ev.ranks gp ix (Finset.mem_univ a) (Finset.mem_univ b)).1
  change rankAt q Finset.univ t b=rankAt q Finset.univ t a+1 at adj
  have ar : rankAt q Finset.univ t a=13 := by omega
  have br : rankAt q Finset.univ t b=14 := by omega
  have inj := rank_injective ix (order_at gp ix Finset.univ t)
  have s : middle q t={a,b} := by
    ext i
    simp only [middle,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert,Finset.mem_singleton]
    rw [←ar,←br]
    exact ⟨fun h => h.elim (fun v => Or.inl (inj (Finset.mem_univ _) (Finset.mem_univ _) v))
       (fun v => Or.inr (inj (Finset.mem_univ _) (Finset.mem_univ _) v)),
      fun h => h.elim (fun v => Or.inl (v ▸ rfl)) (fun v => Or.inr (v ▸ rfl))⟩
  rw [s,←ev.key]; rcases le_total a b with h|h
  · simp [unordered,endpoints,min_eq_left h,max_eq_right h]
  · simp [unordered,endpoints,min_eq_right h,max_eq_left h,Finset.pair_comm]

theorem middle_changes {q : Drawing 28 ℝ} (gp : GeneralPosition q) (ix : Function.Injective (fun i => (q i).1))
    {t e a b} (ev : FullEvent q t e a b) :
    middle q (t+1)≠middle q t ↔ gateAt q Finset.univ e=13 ∨ gateAt q Finset.univ e=15 := by
  have g := ev.gate gp ix Finset.univ
  have ⟨adj,ua,ub,other⟩ := ev.ranks gp ix (Finset.mem_univ a) (Finset.mem_univ b)
  change rankAt q Finset.univ t a+1=gateAt q Finset.univ e at g
  change rankAt q Finset.univ t b=rankAt q Finset.univ t a+1 at adj
  change rankAt q Finset.univ (t+1) a=rankAt q Finset.univ t b at ua
  change rankAt q Finset.univ (t+1) b=rankAt q Finset.univ t a at ub
  constructor
  · intro diff; by_contra! outside; apply diff
    ext i; simp only [middle,Finset.mem_filter,Finset.mem_univ,true_and]
    by_cases ia : i=a
    · subst i; omega
    by_cases ib : i=b
    · subst i; omega
    rw [show rankAt q Finset.univ (t+1) i=rankAt q Finset.univ t i from other i ia ib]
  · intro near same
    have mem := Finset.ext_iff.mp same a
    simp only [middle,Finset.mem_filter,Finset.mem_univ,true_and] at mem
    omega

/-- Every visited value of a nonconstant closed finite walk is an
arrival value of at least one change, including its initial value. -/
theorem visited_after_change {α : Type*} [DecidableEq α] (s : Nat → α) (n : Nat)
    (cycle : s n=s 0) (change : ∃ k<n, s (k+1)≠s k) :
    let jumps := (Finset.range n).filter fun k => s (k+1)≠s k
    ∀ t≤n, s t ∈ jumps.image (fun k => s (k+1)) := by
  classical
  let jumps := (Finset.range n).filter fun k => s (k+1)≠s k
  let arrivals := jumps.image (fun k => s (k+1))
  have arrive (k : Nat) (hk : k<n) (d : s (k+1)≠s k) : s (k+1)∈arrivals :=
    Finset.mem_image.mpr ⟨k,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk,d⟩,rfl⟩
  have extend (k : Nat) (m : s k∈arrivals) (d : Nat) (hd : k+d≤n) : s (k+d)∈arrivals := by
    induction d with
    | zero => simpa using m
    | succ d ih =>
      by_cases eq : s (k+d+1)=s (k+d)
      · exact eq ▸ ih (by omega)
      · exact arrive (k+d) (by omega) eq
  obtain ⟨k,hk,neq⟩ := change
  have all := extend (k+1) (arrive k hk neq) (n-(k+1)) (by omega)
  rw [show k+1+(n-(k+1))=n by omega,cycle] at all
  change ∀ t≤n, s t∈arrivals
  intro t ht
  simpa using extend 0 all t (by omega)

end K28.Projection
