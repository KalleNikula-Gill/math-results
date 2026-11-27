import K28.LowPlane

namespace K28.Low
open K28.Edges

/-- Use an inward horizontal axis at a strictly exposed point. -/
def Exposed (p : Drawing 28 ℝ) (S : Finset V) (a : V) :=
  ∃ u : Vec, u≠zeroV ∧ ∀ b∈S.erase a, 0<dot u (diff (p b) (p a))

noncomputable def slope (u : Vec) (p : Drawing 28 ℝ) (a b : V) :=
  cross u (diff (p b) (p a)) / dot u (diff (p b) (p a))

theorem slope_identity {p : Drawing 28 ℝ} {a b c : V} {u : Vec}
    (bx : 0<dot u (diff (p b) (p a))) (cx : 0<dot u (diff (p c) (p a))) :
    dot u u * orient (p a) (p b) (p c) =
      (dot u (diff (p b) (p a))*dot u (diff (p c) (p a)))*(slope u p a c-slope u p a b) := by
  unfold slope
  field_simp [bx.ne',cx.ne']
  unfold dot cross diff orient
  dsimp
  ring

theorem slopes_injective {p : Drawing 28 ℝ} (gp : GeneralPosition p) {a : V} {S : Finset V} {u : Vec}
    (nz : u≠zeroV) (pos : ∀ b∈S.erase a, 0<dot u (diff (p b) (p a))) :
    Set.InjOn (slope u p a) (S.erase a) := by
  intro b hb c hc eq
  by_contra bc
  have h := slope_identity (pos b hb) (pos c hc)
  rw [eq,sub_self,mul_zero] at h
  exact gp.2 a b c (Finset.ne_of_mem_erase hb).symm (Finset.ne_of_mem_erase hc).symm bc
    ((mul_eq_zero.mp h).resolve_left (square_pos nz).ne')

theorem median_gap {S : Finset V} {f : V → ℝ} (hs : 2≤S.card) (inj : Set.InjOn f S) :
    ∃ l r : ℝ, l<r ∧ ∀ t, l<t → t<r →
      S.card/2 ≤ (S.filter (fun i => f i<t)).card ∧
      S.card/2 ≤ (S.filter (fun i => t<f i)).card := by
  classical
  have rank := rank_range inj
  have get (k : Nat) (hk : k<S.card) : ∃ i∈S, priorCount S f i=k :=
    Finset.mem_image.mp (rank ▸ Finset.mem_range.mpr hk : k∈S.image (priorCount S f))
  obtain ⟨a,ha,ra⟩ := get (S.card/2-1) (by omega)
  obtain ⟨b,hb,rb⟩ := get (S.card/2) (by omega)
  have less : f a<f b := by
    rcases lt_trichotomy (f a) (f b) with h|h|h
    · exact h
    · have eq := inj ha hb h; subst b; omega
    · have bad := order_rank hb h; omega
  refine ⟨f a,f b,less,?_⟩
  intro t l r
  have left : insert a (S.filter (fun i => f i<f a)) ⊆ S.filter (fun i => f i<t) := by
    intro i h
    rcases Finset.mem_insert.mp h with eq|mem
    · subst i; exact Finset.mem_filter.mpr ⟨ha,l⟩
    · obtain ⟨hs,small⟩ := Finset.mem_filter.mp mem
      exact Finset.mem_filter.mpr ⟨hs,small.trans l⟩
  have n := Finset.card_le_card left
  rw [Finset.card_insert_of_notMem (by simp)] at n
  change priorCount S f a + 1 ≤ _ at n
  have right : S.filter (fun i => ¬f i<f b) ⊆ S.filter (fun i => t<f i) := by
    intro i hi; obtain ⟨mem,h⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨mem,r.trans_le (le_of_not_gt h)⟩
  have m := Finset.card_le_card right
  have tot := Finset.filter_card_add_filter_neg_card_eq_card (s:=S) (fun i => f i<f b)
  change priorCount S f b + _ = _ at tot
  omega

/-- If the ideal outward direction points out of a half-plane containing a,
at least half the other points lie no farther out than a. -/
structure SafeRay (p : Drawing 28 ℝ) (S : Finset V) (a : V) (v : Vec) : Prop where
  exposed : Exposed p S a
  safe : ∀ d : Vec, 0≤dot d v →
    (S.erase a).card/2 ≤ ((S.erase a).filter fun b => dot d (p b)≤dot d (p a)).card

theorem ray_exists {p : Drawing 28 ℝ} (gp : GeneralPosition p) {S : Finset V} {a : V}
    (size : 2≤(S.erase a).card) (ex : Exposed p S a) (bad : Finset Vec) :
    ∃ v : Vec, SafeRay p S a v ∧ ∀ z∈bad, z≠zeroV → cross v z≠0 := by
  classical
  obtain ⟨u,nz,pos⟩ := ex
  let F := slope u p a
  obtain ⟨l,r,lt,gap⟩ := median_gap size (slopes_injective gp nz pos)
  let roots := bad.image (fun z => cross u z / dot u z)
  obtain ⟨t,tl,tr,out⟩ := avoid lt roots
  let v : Vec := (-u.1+t*u.2,-u.2-t*u.1)
  refine ⟨v,⟨⟨u,nz,pos⟩,?_⟩,?_⟩
  · intro d dv
    obtain ⟨low,high⟩ := gap t tl tr
    have sgn : dot u d + t*cross u d ≤ 0 := by
      change 0≤dot d v at dv
      dsimp [dot,cross,v] at dv ⊢
      linarith only [dv]
    have project {b : V} (hb : b∈S.erase a) (h : dot u d+cross u d*F b≤0) :
        dot d (p b)≤dot d (p a) := by
      have bx := pos b hb
      have eq : dot u u*(dot d (p b)-dot d (p a)) =
          dot u (diff (p b) (p a))*(dot u d+cross u d*F b) := by
        dsimp only [F,slope]; field_simp [bx.ne']; unfold dot cross diff; dsimp; ring
      by_contra! fail
      have positive := mul_pos (square_pos nz) (sub_pos.mpr fail)
      rw [eq] at positive
      exact positive.not_ge (mul_nonpos_of_nonneg_of_nonpos bx.le h)
    rcases le_total 0 (cross u d) with s|s
    · apply low.trans; apply Finset.card_le_card; intro i mem
      obtain ⟨hi,h⟩ := Finset.mem_filter.mp mem
      exact Finset.mem_filter.mpr ⟨hi,project hi (by
        have m := mul_le_mul_of_nonneg_left h.le s
        change cross u d*F i ≤ _ at m
        linarith only [m,sgn])⟩
    · apply high.trans; apply Finset.card_le_card; intro i mem
      obtain ⟨hi,h⟩ := Finset.mem_filter.mp mem
      exact Finset.mem_filter.mpr ⟨hi,project hi (by
        have m := mul_le_mul_of_nonpos_left h.le s
        change cross u d*F i ≤ _ at m
        linarith only [m,sgn])⟩
  · intro z hz zn zero
    have rel : cross u z=t*dot u z := by dsimp [v,cross,dot] at zero ⊢; linarith only [zero]
    by_cases den : dot u z=0
    · have cr : cross u z=0 := by rw [rel,den,mul_zero]
      have norm : dot u u*dot z z=dot u z^2+cross u z^2 := by unfold dot cross; ring
      rw [cr,den] at norm
      have pos' := mul_pos (square_pos nz) (square_pos zn)
      linarith only [norm,pos']
    · exact out (Finset.mem_image.mpr ⟨z,hz,(div_eq_iff den).mpr rel⟩)

end K28.Low
