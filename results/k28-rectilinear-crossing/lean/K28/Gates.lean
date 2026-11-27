import Lean

namespace K28.Gates

/-- True means that the label belongs to the group under consideration.
The index k is the left slot of an adjacent swap. -/
def swapAt (f : Nat → Bool) (k j : Nat) : Bool :=
  if j = k then f (k+1) else if j = k+1 then f k else f j

/-- During a fixed-count interval at gate g every outside swap moves a
group label right. A swap at g itself preserves group occupancy. -/
structure IntervalStep (g : Nat) (f h : Nat → Bool) : Prop where
  move : ∃ k, h = swapAt f k ∧ (f (k+1) = true → f k = true) ∧
    (k = g → f k = f (k+1))

theorem boundaries {g : Nat} {f h : Nat → Bool} (s : IntervalStep g f h) :
    (f g = true → h g = true) ∧ (h (g+1) = true → f (g+1) = true) := by
  obtain ⟨k,rfl,right,same⟩ := s.move
  constructor
  · intro hg
    by_cases e : g = k
    · subst k; simpa [swapAt, ← same rfl] using hg
    · by_cases h : g = k+1
      · subst g; simpa [swapAt] using right hg
      · simpa [swapAt,e,h] using hg
  · intro hg
    by_cases e : g+1 = k
    · subst k; apply right; simpa [swapAt] using hg
    · by_cases h : g = k
      · subst k; simpa [swapAt, ← same rfl] using hg
      · simpa [swapAt,e,h] using hg

private theorem persists {P : Nat → Prop} {b : Nat} (step : ∀ i, i<b → P i → P (i+1)) :
    ∀ a, a ≤ b → P a → P b := by
  induction b with
  | zero =>
    intro a h pa
    have eq : a = 0 := by omega
    simpa [eq] using pa
  | succ b ih =>
    intro a hab pa
    by_cases eq : a = b+1
    · simpa [eq] using pa
    · exact step b (by omega) (ih (fun i hi => step i (by omega)) a (by omega) pa)

/-- An XX swap and a YY swap at the same gate require, respectively, two
occupied and two vacant slots. They cannot coexist in this interval. -/
theorem interval_incompatibility {g n : Nat} (f : Nat → Nat → Bool)
    (moves : ∀ i, i < n → IntervalStep g (f i) (f (i+1))) {a b : Nat}
    (ha : a ≤ n) (hb : b ≤ n)
    (xx : f a g = true ∧ f a (g+1) = true)
    (yy : f b g = false ∧ f b (g+1) = false) : False := by
  by_cases ab : a ≤ b
  · have h := persists (P := fun i => f i g = true)
      (b:=b) (fun i hi => (boundaries (moves i (by omega))).1) a ab xx.1
    simp [h] at yy
  · have h := persists (P := fun i => f i (g+1) ≠ true)
      (b:=a) (fun i hi hn ht => hn ((boundaries (moves i (by omega))).2 ht))
      b (by omega) (by simp [yy.2])
    exact h xx.2

end K28.Gates
