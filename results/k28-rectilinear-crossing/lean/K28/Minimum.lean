import K28.LowRecurrence

namespace K28.Low
open K28.Edges K28.Projection

attribute [local irreducible] pairs

private theorem side_counts (p : Drawing 28 ℝ) (a b : V) :
    side p Finset.univ (a,b)=right p (a,b) ∧ side p Finset.univ (b,a)=left p (a,b) := by
  classical
  have labels_all : labels.toFinset=(Finset.univ : Finset V) := by ext; simp [labels]
  constructor
  · rw [right,ls_finset labels _ (show labels.Nodup from List.nodup_finRange 28),labels_all]
    exact (natBoole _ _).symm
  · rw [left,ls_finset labels _ (show labels.Nodup from List.nodup_finRange 28),labels_all]
    unfold plus flag
    rw [natBoole]
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro i _
    simp only [area_flip (p a) (p b),neg_lt_zero]

private theorem forget_orientation (p : Drawing 28 ℝ) (gp : GeneralPosition p) {k : Nat} (small : k<12) :
    (lowSet p Finset.univ (k+1)).card ≤ E (counts p) k := by
  classical
  let canonical := fun e : Pair => endpoints e.1 e.2
  rw [cumulative,ls_finset pairs _ (show pairs.Nodup from pairs_nodup),natBoole]
  apply Finset.card_le_card_of_injOn canonical
  · rintro ⟨a,b⟩ mem
    obtain ⟨_,_,ne,low⟩ := low_mem.mp mem
    apply Finset.mem_filter.mpr
    refine ⟨List.mem_toFinset.mpr (endpoint_pair a b ne),?_⟩
    change edgeType p (endpoints a b)≤k
    rcases le_total a b with h|h
    · simp only [endpoints,min_eq_left h,max_eq_right h,edgeType]
      have eq := (side_counts p a b).1
      exact (min_le_right _ _).trans (by omega)
    · simp only [endpoints,min_eq_right h,max_eq_left h,edgeType]
      have eq := (side_counts p b a).2
      exact (min_le_left _ _).trans (by omega)
  · rintro ⟨a,b⟩ h ⟨c,d⟩ j equ
    rcases same_edge.mp equ with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · rfl
    · obtain ⟨ma,mb,ne,l⟩ := low_mem.mp h
      have r := (low_mem.mp j).2.2.2
      change side p Finset.univ (a,b)<k+1 at l
      change side p Finset.univ (b,a)<k+1 at r
      have tot := side_sum gp ma mb ne
      change side p Finset.univ (a,b)+side p Finset.univ (b,a)+2=(Finset.univ : Finset V).card at tot
      have num : (Finset.univ : Finset V).card=28 := by decide +kernel
      omega

theorem bound_values : ∀ k : Fin 12, bound 28 (k.val+1)=publishedLow k.val := by decide +kernel

/-- The twelve geometric instances of Theorem 11 at n=28. The exposed
rays, the shallow sides and the sector changes are all constructed from p. -/
theorem cumulative_bound_28 (p : Drawing 28 ℝ) (gp : GeneralPosition p) (k : Nat) (small : k<12) :
    publishedLow k≤E (counts p) k := by
  have num : (Finset.univ : Finset V).card=28 := by decide +kernel
  have low := low_bound p gp (k+1) Finset.univ (by rw [num]; omega)
  rw [num,bound_values ⟨k,small⟩] at low
  exact low.trans (forget_orientation p gp small)

end K28.Low

namespace K28

/-- The minimum number of unordered interior crossing pairs over all
28 labeled real-plane points in general position is exactly 7,234. -/
theorem minimum_28 : MinimumIs 7234 :=
  Projection.minimum_using_theorem11 Low.cumulative_bound_28

end K28
