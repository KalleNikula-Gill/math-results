import K28Arithmetic
import K28.Gates
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace K28.Flux

/-- Positions are numbered from zero. A swap of position k with k+1 uses
gate k+1 in the manuscript's one-based convention. -/
def swap {α : Type*} (f : Nat → α) (k j : Nat) :=
  if j=k then f (k+1) else if j=k+1 then f k else f j

def pref (f : Nat → ℤ) : Nat → ℤ
  | 0 => 0
  | g+1 => pref f g + f g

theorem swapped_prefix (f : Nat → ℤ) (k g : Nat) :
    pref (swap f k) g = pref f g + if g=k+1 then f (k+1)-f k else 0 := by
  induction g with
  | zero => simp [pref]
  | succ g ih =>
    by_cases hk : g=k
    · subst g
      simp [pref,swap,ih]
    by_cases hs : g=k+1
    · subst g
      simp [pref,swap] at ih ⊢
      omega
    · simp [pref,swap,ih,hk,hs]

def occupancy (b : Bool) : ℤ := if b then 1 else 0

/-- This projection of a finite sequence of real adjacent swaps retains
only membership in the selected set. Every swap of different statuses
moves the selected member to the right. -/
structure Rightward (n : Nat) where
  slots : Nat → Nat → Bool
  atSlot : Nat → Nat
  moves : ∀ t, t<n → slots (t+1) = swap (slots t) (atSlot t)
  right : ∀ t, t<n → slots t (atSlot t+1) = true → slots t (atSlot t) = true

def count (f : Nat → Bool) (g : Nat) := pref (fun i => occupancy (f i)) g

def exits (f : Nat → Bool) (k g : Nat) : ℤ :=
  if g=k+1 ∧ f k=true ∧ f (k+1)=false then 1 else 0

private theorem one_swap {n : Nat} (S : Rightward n) {t : Nat} (ht : t<n) (g : Nat) :
    count (S.slots (t+1)) g + exits (S.slots t) (S.atSlot t) g = count (S.slots t) g := by
  let f := S.slots t
  let k := S.atSlot t
  have real : (fun i => occupancy (S.slots (t+1) i)) = swap (fun i => occupancy (f i)) k := by
    funext i
    rw [S.moves t ht]
    dsimp only [f,k]; unfold swap; split_ifs <;> rfl
  have right : f (k+1)=true → f k=true := S.right t ht
  unfold count
  rw [real,swapped_prefix]
  change pref (fun i => occupancy (f i)) g + _ + exits f k g = _
  by_cases gate : g=k+1
  · cases h : f k <;> cases h' : f (k+1) <;> simp_all [exits,occupancy] <;> rfl
  · simp [gate,exits]; rfl

def accumulated {n : Nat} (S : Rightward n) (g : Nat) : Nat → ℤ
  | 0 => 0
  | t+1 => accumulated S g t + exits (S.slots t) (S.atSlot t) g

/-- Conservation across a single gate, including swaps internal to
either status class. -/
theorem gate_flux {n : Nat} (S : Rightward n) (g t : Nat) (ht : t≤n) :
    accumulated S g t = count (S.slots 0) g - count (S.slots t) g := by
  induction t with
  | zero => simp [accumulated]
  | succ t ih =>
    have one := one_swap S (by omega : t<n) g
    rw [accumulated,ih (by omega)]
    omega

private theorem left_block (x g : Nat) : count (fun i => decide (i<x)) g = (min g x : Nat) := by
  induction g with
  | zero => simp [count,pref]
  | succ g ih =>
    change count _ g + occupancy (decide (g<x)) = _
    rw [ih]; by_cases h : g<x <;> simp [h,occupancy,min_def] <;> split_ifs <;> omega

private theorem after_block (y g : Nat) : count (fun i => decide (y≤i)) g = (g-y : Nat) := by
  induction g with
  | zero => simp [count,pref]
  | succ g ih =>
    change count _ g + occupancy (decide (y≤g)) = _
    rw [ih]; by_cases h : y≤g <;> simp [h,occupancy] <;> omega

private theorem count_eq {f h : Nat → Bool} {g : Nat} (same : ∀ i, i<g → f i=h i) :
    count f g=count h g := by
  induction g with
  | zero => rfl
  | succ g ih =>
    change count f g + occupancy (f g) = count h g + occupancy (h g)
    rw [ih (fun i hi => same i (by omega)),same g (by omega)]

/-- The XY swap count on the projection restricted to X,Y. Only the
end block orders and the ordinary adjacent-transposition rules enter. -/
theorem two_group_gate_count {n : Nat} (S : Rightward n) (x y g : Nat)
    (start : ∀ i < g, S.slots 0 i = decide (i<x))
    (finish : ∀ i < g, S.slots n i = decide (y≤i)) :
    accumulated S g n = (min g x : Nat) - ((g-y : Nat) : ℤ) := by
  rw [gate_flux S g n (le_refl _),count_eq start,count_eq finish,left_block,after_block]

/-- For an original prefix of t group labels, the number of rightward
mixed swaps in a band is the number of gates times t when the prefix
starts entirely before each gate and finishes entirely after it. -/
theorem band_flux {n : Nat} (S : Rightward n) (G : Finset Nat) (t : Nat)
    (start : ∀ g ∈ G, count (S.slots 0) g = t)
    (finish : ∀ g ∈ G, count (S.slots n) g = 0) :
    (∑ g ∈ G, accumulated S g n) = (G.card : ℤ) * t := by
  calc _ = ∑ _g ∈ G, (t : ℤ) := Finset.sum_congr rfl (fun g hg => by rw [gate_flux S g n (le_refl _),
             start g hg,finish g hg,sub_zero])
       _ = _ := by simp

/-- The prefix--suffix and outside crossings exhaust the band flux.
Equality in the resulting bound forces all three slacks to vanish. -/
theorem tight_cut {pre suf mixed outside flux pcap scap : Nat}
    (net : mixed+outside=flux) (pmax : pre≤pcap) (smax : suf≤scap) :
    pre+suf+mixed ≤ pcap+scap+flux ∧
    (pre+suf+mixed=pcap+scap+flux ↔ pre=pcap ∧ suf=scap ∧ outside=0) := by omega

theorem count_falls {n : Nat} (S : Rightward n) (g a b : Nat) (ab : a≤b) (bn : b≤n) :
    count (S.slots b) g ≤ count (S.slots a) g := by
  induction b with
  | zero =>
    have ha : a=0 := by omega
    subst a
    rfl
  | succ b ih =>
    by_cases h : a=b+1
    · subst a; rfl
    · have past := ih (by omega) (by omega)
      have one := one_swap S (by omega : b<n) g
      have nn : 0 ≤ exits (S.slots b) (S.atSlot b) g := by unfold exits; split_ifs <;> decide
      omega

private theorem interval_moves {n : Nat} (S : Rightward n) (g lo hi : Nat)
    (high : hi≤n) (same : count (S.slots lo) (g+1) = count (S.slots hi) (g+1)) :
    ∀ i < hi-lo, K28.Gates.IntervalStep g (S.slots (lo+i)) (S.slots (lo+(i+1))) := by
  intro i hi'
  let t := lo+i
  have lt : t<n := by dsimp [t]; omega
  have ta : lo≤t := by dsimp [t]; omega
  have tb : t+1≤hi := by dsimp [t]; omega
  have one := one_swap S lt (g+1)
  have below := count_falls S (g+1) lo t ta (by omega)
  have above := count_falls S (g+1) (t+1) hi tb high
  have zero : exits (S.slots t) (S.atSlot t) (g+1) = 0 := by
    have nn : 0 ≤ exits (S.slots t) (S.atSlot t) (g+1) := by unfold exits; split_ifs <;> decide
    omega
  change K28.Gates.IntervalStep g (S.slots t) (S.slots (t+1))
  refine ⟨S.atSlot t,S.moves t lt,S.right t lt,?_⟩
  intro kg
  have right := S.right t lt
  cases x : S.slots t (S.atSlot t) <;> cases y : S.slots t (S.atSlot t+1)
  · rfl
  · exact x.symm.trans (right y)
  · rw [exits,if_pos ⟨by omega,x,y⟩] at zero
    contradiction
  · rfl

/-- In a full rightward trace, equal prefix counts locate one interval.
Two occupied gate slots and two vacant gate slots cannot both occur
there. No separate interval hypothesis is required. -/
theorem equal_count_incompatibility {n : Nat} (S : Rightward n) (g a b : Nat)
    (an : a≤n) (bn : b≤n) (eq : count (S.slots a) (g+1) = count (S.slots b) (g+1))
    (xx : S.slots a g = true ∧ S.slots a (g+1) = true)
    (yy : S.slots b g = false ∧ S.slots b (g+1) = false) : False := by
  let lo := min a b
  let hi := max a b
  have h : count (S.slots lo) (g+1) = count (S.slots hi) (g+1) := by
    rcases le_total a b with ab|ba
    · simpa only [lo,hi,min_eq_left ab,max_eq_right ab] using eq
    · simpa only [lo,hi,min_eq_right ba,max_eq_left ba] using eq.symm
  have ma : lo+(a-lo)=a := by dsimp [lo]; omega
  have mb : lo+(b-lo)=b := by dsimp [lo]; omega
  apply K28.Gates.interval_incompatibility (n:=hi-lo) (a:=a-lo) (b:=b-lo)
    (fun i => S.slots (lo+i)) (interval_moves S g lo hi (by dsimp [hi]; omega) h)
  · dsimp [lo,hi]; omega
  · dsimp [lo,hi]; omega
  · simpa only [ma] using xx
  · simpa only [mb] using yy

end K28.Flux
