import K28.CentralBound

namespace K28.Low
open K28.Edges

abbrev Vec := Point ℝ
def dot (u v : Vec) := u.1*v.1+u.2*v.2
def cross (u v : Vec) := u.1*v.2-u.2*v.1
def perp (u : Vec) : Vec := (-u.2,u.1)
def diff (u v : Vec) : Vec := (u.1-v.1,u.2-v.2)
def normal (p : Drawing 28 ℝ) (e : Pair) := perp (diff (p e.2) (p e.1))
def zeroV : Vec := (0,0)

theorem dot_diff (u x y : Vec) : dot u (diff x y)=dot u x-dot u y := by
  unfold dot diff; dsimp; ring
theorem dot_perp (u x : Vec) : dot (perp u) x=cross u x := by unfold dot perp cross; dsimp; ring
theorem area_dot (p : Drawing 28 ℝ) (a b c : V) :
    orient (p a) (p b) (p c)=dot (normal p (a,b)) (p c)-dot (normal p (a,b)) (p a) := by
  unfold orient dot normal perp diff; dsimp; ring
theorem area_flip (x y z : Vec) : orient y x z= -orient x y z := by unfold orient; ring
theorem area_start (x y : Vec) : orient x y x=0 := by simp [orient]
theorem area_end (x y : Vec) : orient x y y=0 := by unfold orient; ring
theorem square_pos {u : Vec} (h : u ≠ zeroV) : 0 < dot u u := by
  by_cases z : u.1=0
  · have nz : u.2≠0 := fun hz => h (Prod.ext z hz)
    simpa [dot,z] using mul_self_pos.mpr nz
  · exact add_pos_of_pos_of_nonneg (mul_self_pos.mpr z) (mul_self_nonneg _)

theorem perp_nonzero {u : Vec} (h : u≠zeroV) : perp u≠zeroV := by
  intro z; apply h; apply Prod.ext
  · exact congrArg Prod.snd z
  · simpa [perp,zeroV] using congrArg Prod.fst z

theorem cross_neg (u v : Vec) : cross v u= -cross u v := by unfold cross; ring
theorem cross_self (u : Vec) : cross u u=0 := by unfold cross; ring
theorem normal_nonzero {p : Drawing 28 ℝ} (gp : GeneralPosition p) {a b : V} (h : a≠b) :
    normal p (a,b)≠zeroV := by
  apply perp_nonzero
  intro z; apply h.symm; apply gp.1; apply Prod.ext
  · exact sub_eq_zero.mp (congrArg Prod.fst z)
  · exact sub_eq_zero.mp (congrArg Prod.snd z)

/-- A bounded open interval has a point outside an arbitrary finite list of exceptions. -/
theorem avoid {a b : ℝ} (ab : a<b) (B : Finset ℝ) : ∃ t, a<t ∧ t<b ∧ t∉B := by
  classical
  let C := B.filter (fun x => a<x)
  by_cases non : C.Nonempty
  · let c := C.min' non
    have ac := (Finset.mem_filter.mp (C.min'_mem non)).2
    have mn : a<min b c := lt_min ab ac
    obtain ⟨t,at',tb⟩ := exists_between mn
    refine ⟨t,at',tb.trans_le (min_le_left _ _),?_⟩
    intro ht
    exact (tb.trans_le (min_le_right _ _)).not_ge (C.min'_le _ (Finset.mem_filter.mpr ⟨ht,at'⟩))
  · obtain ⟨t,at',tb⟩ := exists_between ab
    exact ⟨t,at',tb,fun ht => non ⟨t,Finset.mem_filter.mpr ⟨ht,at'⟩⟩⟩

noncomputable def priorCount (S : Finset V) (f : V → ℝ) (a : V) :=
  (S.filter (fun b => f b<f a)).card

theorem order_rank {S : Finset V} {f : V → ℝ} {a b : V} (ha : a∈S) (ab : f a<f b) :
    priorCount S f a < priorCount S f b := by
  apply Finset.card_lt_card
  apply (Finset.ssubset_iff_of_subset _).mpr
  · exact ⟨a,Finset.mem_filter.mpr ⟨ha,ab⟩,by simp⟩
  · intro i hi; obtain ⟨mem,h⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨mem,h.trans ab⟩

theorem rank_range {S : Finset V} {f : V → ℝ} (inj : Set.InjOn f S) :
    S.image (priorCount S f) = Finset.range S.card := by
  classical
  apply Finset.eq_of_subset_of_card_le
  · intro r h; obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp h
    apply Finset.mem_range.mpr; apply Finset.card_lt_card
    exact (Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)).mpr ⟨a,ha,by simp⟩
  · have hi : Set.InjOn (priorCount S f) S := by
      intro a ha b hb eq
      rcases lt_trichotomy (f a) (f b) with h|h|h
      · exact False.elim ((order_rank ha h).ne eq)
      · exact inj ha hb h
      · exact False.elim ((order_rank hb h).ne eq.symm)
    rw [Finset.card_image_iff.mpr hi,Finset.card_range]

theorem prefix_card {S : Finset V} {f : V → ℝ} (inj : Set.InjOn f S) {k : Nat} (hk : k≤S.card) :
    (S.filter (fun a => priorCount S f a<k)).card=k := by
  classical
  have im := rank_range inj
  let T := S.filter fun a => priorCount S f a<k
  have eq : T.image (priorCount S f) = Finset.range k := by
    ext j
    constructor
    · rintro h; obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp h
      exact Finset.mem_range.mpr (Finset.mem_filter.mp ha).2
    · intro h
      have hj := Finset.mem_range.mp h
      obtain ⟨a,ha,eq⟩ := Finset.mem_image.mp (im ▸ Finset.mem_range.mpr (hj.trans_le hk) :
        j∈S.image (priorCount S f))
      exact Finset.mem_image.mpr ⟨a,Finset.mem_filter.mpr ⟨ha,eq ▸ hj⟩,eq⟩
  have hi := Finset.card_image_iff.mp (show (S.image (priorCount S f)).card=S.card by rw [im,Finset.card_range])
  change T.card=k
  rw [←Finset.card_image_iff.mpr (hi.mono (Finset.filter_subset _ _)),eq,Finset.card_range]

noncomputable def side (p : Drawing 28 ℝ) (S : Finset V) (e : Pair) :=
  (S.filter fun i => orient (p e.1) (p e.2) (p i)<0).card
noncomputable def lowSet (p : Drawing 28 ℝ) (S : Finset V) (w : Nat) :=
  (S ×ˢ S).filter fun e => e.1≠e.2 ∧ side p S e<w

theorem low_mem {p : Drawing 28 ℝ} {S : Finset V} {w : Nat} {a b : V} :
    (a,b)∈lowSet p S w ↔ a∈S ∧ b∈S ∧ a≠b ∧ side p S (a,b)<w := by
  simp only [lowSet,Finset.mem_filter,Finset.mem_product]; tauto

theorem side_sum {p : Drawing 28 ℝ} (gp : GeneralPosition p) {S : Finset V} {a b : V}
    (ha : a∈S) (hb : b∈S) (ab : a≠b) :
    side p S (a,b)+side p S (b,a)+2=S.card := by
  classical
  let U := S.filter (fun z => orient (p a) (p b) (p z)<0)
  let W := S.filter (fun z => orient (p b) (p a) (p z)<0)
  have dis : Disjoint U W := Finset.disjoint_left.mpr (fun x hx hy => by
    have l := (Finset.mem_filter.mp hx).2
    have r := (Finset.mem_filter.mp hy).2
    rw [area_flip (p b)] at l
    linarith)
  have eq : U∪W=(S.erase a).erase b := by
    ext x
    simp only [U,W,Finset.mem_union,Finset.mem_filter,Finset.mem_erase]
    by_cases xa : x=a
    · subst x; simp [area_start,area_end]
    by_cases xb : x=b
    · subst x; simp [area_start,area_end]
    have nz := gp.2 a b x ab (Ne.symm xa) (Ne.symm xb)
    rw [area_flip (p a)]
    rcases lt_or_gt_of_ne nz with h|h <;> simp [h,h.le,xa,xb]
  have card := Finset.card_union_of_disjoint dis
  rw [eq,Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨ab.symm,hb⟩),Finset.card_erase_of_mem ha] at card
  have h1 : 0<(S.erase a).card := Finset.card_pos.mpr ⟨b,Finset.mem_erase.mpr ⟨ab.symm,hb⟩⟩
  rw [Finset.card_erase_of_mem ha] at h1
  change U.card+W.card+2=S.card
  omega

end K28.Low
