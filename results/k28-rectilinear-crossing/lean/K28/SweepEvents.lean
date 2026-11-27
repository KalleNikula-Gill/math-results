import K28.Frames

namespace K28.Projection
open K28.Edges

def Earlier (q : Drawing 28 ℝ) (seen : Finset Pair) (i j : V) : Prop :=
  if endpoints i j ∈ seen then (q j).1 < (q i).1 else (q i).1 < (q j).1

noncomputable instance earlierDec (q : Drawing 28 ℝ) (seen : Finset Pair) (i j : V) :
    Decidable (Earlier q seen i j) := Classical.propDecidable _

noncomputable def prior (q : Drawing 28 ℝ) (T : Finset V) (seen : Finset Pair) (i : V) :=
  T.filter (fun j => Earlier q seen j i)

noncomputable def rank (q : Drawing 28 ℝ) (T : Finset V) (seen : Finset Pair) (i : V) :=
  (prior q T seen i).card

/-- Applied events are a prefix of increasing slope order. Ties from
disjoint parallel pairs may be broken in any order. -/
structure Frontier (q : Drawing 28 ℝ) (T : Finset V) (seen : Finset Pair) (t : ℝ) : Prop where
  past : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → event (q i) (q j)<t → endpoints i j ∈ seen
  future : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → t<event (q i) (q j) → endpoints i j ∉ seen

theorem event_symm (a b : Point ℝ) : event a b = event b a := by
  unfold event
  rw [show b.2-a.2 = -(a.2-b.2) by ring,show b.1-a.1 = -(a.1-b.1) by ring,neg_div_neg_eq]

private theorem ends_comm (i j : V) : endpoints i j=endpoints j i := same_edge.mpr (Or.inr ⟨rfl,rfl⟩)

theorem relative_order {q : Drawing 28 ℝ} (ix : Function.Injective (fun i => (q i).1))
    {T seen t} (front : Frontier q T seen t) {i j : V} (hi : i ∈ T) (hj : j ∈ T)
    (different : value t (q i) ≠ value t (q j)) :
    Earlier q seen i j ↔ value t (q i) < value t (q j) := by
  have ij : i≠j := fun h => different (h ▸ rfl)
  have dx : (q i).1 ≠ (q j).1 := ix.ne ij
  have tm : t ≠ event (q i) (q j) := by intro eq; subst t; exact different (tie _ _ dx)
  unfold Earlier
  rcases lt_or_gt_of_ne tm with future|past
  · rw [if_neg (front.future i hi j hj ij future)]
    rcases lt_or_gt_of_ne dx with less|more
    · exact iff_of_true less ((passes_right t _ _ less).1.mpr future)
    · have f : t<event (q j) (q i) := by rwa [event_symm]
      exact iff_of_false more.not_gt (((passes_right t _ _ more).1.mpr f).not_gt)
  · rw [if_pos (front.past i hi j hj ij past)]
    rcases lt_or_gt_of_ne dx with less|more
    · exact iff_of_false less.not_gt (((passes_right t _ _ less).2.2.mpr past).not_gt)
    · have f : event (q j) (q i)<t := by rwa [event_symm]
      exact iff_of_true more ((passes_right t _ _ more).2.2.mpr f)

private theorem not_tied {q : Drawing 28 ℝ} (gp : GeneralPosition q)
    (ix : Function.Injective (fun i => (q i).1)) {a b k : V} (ab : a≠b) (ka : k≠a) (kb : k≠b) :
    value (event (q a) (q b)) (q k) ≠ value (event (q a) (q b)) (q a) := by
  intro eq
  have side := side_at_event (q a) (q b) (q k) (ix.ne ab)
  rw [eq,sub_self,mul_zero] at side
  exact gp.2 a b k ab ka.symm kb.symm side.symm

private theorem self_earlier (q : Drawing 28 ℝ) (seen : Finset Pair) (a : V) :
    ¬ Earlier q seen a a := by simp [Earlier]

/-- At a real event the only tied labels are its endpoints. The lower
endpoint in initial order has exactly the earlier projections below
the tied value, including when disjoint events share its time. -/
theorem prior_at_event {q : Drawing 28 ℝ} (gp : GeneralPosition q)
    (ix : Function.Injective (fun i => (q i).1)) {T seen} {a b : V}
    (ha : a∈T) (hb : b∈T) (dx : (q a).1 < (q b).1)
    (front : Frontier q T seen (event (q a) (q b))) (pending : endpoints a b ∉ seen) :
    let t := event (q a) (q b)
    prior q T seen a = T.filter (fun k => value t (q k)<value t (q a)) ∧
    prior q T seen b = insert a (prior q T seen a) := by
  classical
  let t := event (q a) (q b)
  have ab : a≠b := fun h => dx.ne (h ▸ rfl)
  have eqv : value t (q a)=value t (q b) := tie _ _ dx.ne
  have other {k : V} (hk : k∈T) (ka : k≠a) (kb : k≠b) :
      (Earlier q seen k a ↔ value t (q k)<value t (q a)) ∧
      (Earlier q seen k b ↔ value t (q k)<value t (q a)) := by
    have ne := not_tied gp ix ab ka kb
    have nb : value t (q k)≠value t (q b) := eqv ▸ ne
    exact ⟨relative_order ix front hk ha ne,eqv ▸ relative_order ix front hk hb nb⟩
  have l : Earlier q seen a b := by simpa [Earlier,pending] using dx
  have r : ¬ Earlier q seen b a := by simpa [Earlier,ends_comm b a,pending] using dx.not_gt
  constructor
  · ext k
    simp only [prior,Finset.mem_filter]
    apply and_congr_right
    intro hk
    by_cases ka : k=a
    · subst k; exact iff_of_false (self_earlier _ _ _) (lt_irrefl _)
    by_cases kb : k=b
    · subst k; exact iff_of_false r (by change ¬ value t (q b)<value t (q a); rw [eqv]; exact lt_irrefl _)
    exact (other hk ka kb).1
  · ext k
    simp only [prior,Finset.mem_filter,Finset.mem_insert]
    by_cases ka : k=a
    · subst k; simp [ha,l]
    by_cases kb : k=b
    · subst k; simp [hb,ab.symm,self_earlier,r]
    by_cases hk : k∈T
    · simp only [hk,true_and,ka,false_or]; exact (other hk ka kb).2.trans (other hk ka kb).1.symm
    · simp [ka,hk]

private theorem unchanged_comparison {q : Drawing 28 ℝ} {D : Finset Pair} {i j a b : V}
    (diff : endpoints i j ≠ endpoints a b) :
    Earlier q (insert (endpoints a b) D) i j ↔ Earlier q D i j := by
  simp [Earlier,diff]

/-- A full or restricted projection sweep takes an actual adjacent swap
at a pair's event. Its endpoints exchange their ranks and every other
surviving label keeps its rank. -/
theorem rank_step {q : Drawing 28 ℝ} (gp : GeneralPosition q)
    (ix : Function.Injective (fun i => (q i).1)) {T D} {a b : V}
    (ha : a∈T) (hb : b∈T) (dx : (q a).1 < (q b).1)
    (front : Frontier q T D (event (q a) (q b))) (pending : endpoints a b ∉ D) :
    let D' := insert (endpoints a b) D
    rank q T D b = rank q T D a + 1 ∧ rank q T D' a=rank q T D b ∧
      rank q T D' b=rank q T D a ∧ ∀ i, i≠a → i≠b → rank q T D' i=rank q T D i := by
  classical
  let D' := insert (endpoints a b) D
  have h := (prior_at_event gp ix ha hb dx front pending).2
  have na : a∉prior q T D a := by simp [prior,self_earlier]
  have ab : a≠b := fun h => dx.ne (h ▸ rfl)
  have nb : b∉prior q T D a := by simp [prior,Earlier,ends_comm b a,pending,dx.not_gt]
  have s₁ : prior q T D' a=insert b (prior q T D a) := by
    ext i
    simp only [prior,Finset.mem_filter,Finset.mem_insert]
    by_cases ib : i=b
    · subst i; simp [D',Earlier,ends_comm b a,dx,hb]
    by_cases mem : i∈T
    · simp only [mem,true_and,ib,false_or]
      apply unchanged_comparison
      intro e; rcases same_edge.mp e with ⟨_,h⟩|⟨h,_⟩ <;> contradiction
    · simp [mem,ib]
  have s₂ : prior q T D' b=prior q T D a := by
    have alt : prior q T D' b=(prior q T D b).erase a := by
      ext i
      simp only [prior,Finset.mem_filter,Finset.mem_erase]
      by_cases ia : i=a
      · subst i; simp [D',Earlier,dx.not_gt]
      by_cases mem : i∈T
      · simp [mem,ia]
        apply unchanged_comparison
        intro e; rcases same_edge.mp e with ⟨h,_⟩|⟨_,h⟩ <;> grind
      · simp [mem]
    rw [alt,h,Finset.erase_insert na]
  dsimp only
  refine ⟨?_,?_,?_,?_⟩
  · unfold rank; rw [h,Finset.card_insert_of_notMem na]
  · unfold rank; rw [s₁,h,Finset.card_insert_of_notMem na,Finset.card_insert_of_notMem nb]
  · exact congrArg Finset.card s₂
  · intro i ia ib
    apply congrArg Finset.card
    ext j
    simp only [prior,Finset.mem_filter]
    apply and_congr_right
    intro _
    apply unchanged_comparison
    intro e; rcases same_edge.mp e with ⟨_,h⟩|⟨_,h⟩ <;> contradiction

end K28.Projection
