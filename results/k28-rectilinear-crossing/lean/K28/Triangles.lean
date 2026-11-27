import K28.Hull
import K28.Peeling

namespace K28.Edges

private def along (a b u : Point ℝ) :=
  (a.1-b.1)*(u.1-b.1) + (a.2-b.2)*(u.2-b.2)

private theorem length_pos {a b : Point ℝ} (ne : a ≠ b) : 0 < along a b a := by
  rcases eq_or_ne a.1 b.1 with ex | ex
  · have ey : a.2 ≠ b.2 := fun h => ne (Prod.ext ex h)
    unfold along; rw [ex, sub_self,zero_mul,zero_add]
    exact mul_self_pos.mpr (sub_ne_zero.mpr ey)
  · unfold along; exact add_pos_of_pos_of_nonneg (mul_self_pos.mpr (sub_ne_zero.mpr ex)) (mul_self_nonneg _)

private theorem ratio_area (a b u v : Point ℝ) (hu : orient b a u ≠ 0) (hv : orient b a v ≠ 0) :
    along a b a * orient b u v =
      (orient b a u * orient b a v) * (along a b u/orient b a u - along a b v/orient b a v) := by
  field_simp [hu,hv]; unfold orient along; ring

/-- Starting with a supporting edge ab, gift wrapping at b finds a
different supporting edge bc; general position makes each comparison strict. -/
theorem next_support (p : Drawing 28 ℝ) (gp : GeneralPosition p) (S : Finset V)
    (hs : 3 ≤ S.card) {a b : V} (ha : a ∈ S) (hb : b ∈ S) (ab : a ≠ b)
    (supp : Supports p S a b) : ∃ c ∈ S, c ≠ a ∧ c ≠ b ∧ Supports p S b c := by
  classical
  let T := (S.erase a).erase b
  have bc : b ∈ S.erase a := Finset.mem_erase.mpr ⟨ab.symm,hb⟩
  have ne : T.Nonempty := Finset.card_pos.mp (by dsimp [T]; rw [Finset.card_erase_of_mem bc,Finset.card_erase_of_mem ha]; omega)
  have dd {k : V} (h : k ∈ T) : k ≠ a ∧ k ≠ b ∧ k ∈ S :=
    ⟨(Finset.mem_erase.mp (Finset.mem_erase.mp h).2).1,(Finset.mem_erase.mp h).1,
      (Finset.mem_erase.mp (Finset.mem_erase.mp h).2).2⟩
  let H := fun k => orient (p b) (p a) (p k)
  let F := fun k => along (p a) (p b) (p k) / H k
  have nonzero {k : V} (hk : k ∈ T) : H k ≠ 0 :=
    gp.2 b a k ab.symm (dd hk).2.1.symm (dd hk).1.symm
  have hlen := length_pos (gp.1.ne ab)
  have atA (k : V) : orient (p b) (p k) (p a) = -H k := by unfold H orient; ring
  have atB (k : V) : orient (p b) (p k) (p b) = 0 := by simp [orient]
  have relation {k l : V} (hk : k ∈ T) (hl : l ∈ T) :
      along (p a) (p b) (p a) * orient (p b) (p k) (p l) = (H k*H l)*(F k-F l) :=
    ratio_area _ _ _ _ (nonzero hk) (nonzero hl)
  rcases flip_support supp with pos|neg
  · obtain ⟨c,hc,lo⟩ := T.exists_min_image F ne
    refine ⟨c,(dd hc).2.2,(dd hc).1,(dd hc).2.1,Or.inr ?_⟩
    intro k hk
    by_cases ka : k=a
    · subst k; rw [atA]; exact neg_nonpos.mpr (pos c (dd hc).2.2)
    by_cases kb : k=b
    · subst k; rw [atB]
    have mem : k ∈ T := Finset.mem_erase.mpr ⟨kb,Finset.mem_erase.mpr ⟨ka,hk⟩⟩
    have hrel := relation hc mem
    have h := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (pos c (dd hc).2.2) (pos k hk)) (sub_nonpos.mpr (lo k mem))
    exact nonpos_of_mul_nonpos_right (hrel ▸ h) hlen
  · obtain ⟨c,hc,hi⟩ := T.exists_max_image F ne
    refine ⟨c,(dd hc).2.2,(dd hc).1,(dd hc).2.1,Or.inl ?_⟩
    intro k hk
    by_cases ka : k=a
    · subst k; rw [atA]; exact neg_nonneg.mpr (neg c (dd hc).2.2)
    by_cases kb : k=b
    · subst k; rw [atB]
    have mem : k ∈ T := Finset.mem_erase.mpr ⟨kb,Finset.mem_erase.mpr ⟨ka,hk⟩⟩
    have hrel := relation hc mem
    have h := mul_nonneg (mul_nonneg_of_nonpos_of_nonpos (neg c (dd hc).2.2) (neg k hk)) (sub_nonneg.mpr (hi k mem))
    exact nonneg_of_mul_nonneg_right (hrel ▸ h) hlen

private theorem product_support {p : Drawing 28 ℝ} {S : Finset V} {i j k l : V}
    (s : Supports p S i j) (hk : k ∈ S) (hl : l ∈ S) :
    0 ≤ orient (p i) (p j) (p k)*orient (p i) (p j) (p l) := by
  rcases s with h|h
  · exact mul_nonneg (h _ hk) (h _ hl)
  · exact mul_nonneg_of_nonpos_of_nonpos (h _ hk) (h _ hl)

/-- Three mutually supporting edges enclose every survivor in their
closed triangle, witnessed by explicit affine coordinates. -/
theorem triangle_of_supports (p : Drawing 28 ℝ) (gp : GeneralPosition p) {S : Finset V}
    {a b c : V} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c)
    (s₁ : Supports p S b c) (s₂ : Supports p S c a) (s₃ : Supports p S a b) :
    ∀ k ∈ S, InTriangle (p a) (p b) (p c) (p k) := by
  intro k hk
  let d := orient (p a) (p b) (p c)
  have nz : d ≠ 0 := gp.2 a b c ab ac bc
  have cyc (x y z : Point ℝ) : orient y z x = orient x y z := by unfold orient; ring
  have t₁ := product_support s₁ hk ha
  have t₂ := product_support s₂ hk hb
  have t₃ := product_support s₃ hk hc
  rw [cyc (p a) (p b) (p c)] at t₁
  rw [←cyc (p c) (p a) (p b)] at t₂
  have divNN {n : ℝ} (h : 0 ≤ n*d) : 0 ≤ n/d := by
    rcases le_or_gt 0 d with hd|hd
    · exact div_nonneg (nonneg_of_mul_nonneg_left h (hd.lt_of_ne nz.symm)) hd
    · exact div_nonneg_of_nonpos (nonpos_of_mul_nonneg_left h hd) hd.le
  let u := orient (p c) (p a) (p k)/d
  let v := orient (p a) (p b) (p k)/d
  have bary : orient (p b) (p c) (p k)/d + u + v = 1 := by
    dsimp only [u,v]; field_simp [nz]; unfold d orient; ring
  refine ⟨u,v,divNN t₂,divNN t₃,by linarith only [bary,divNN t₁],?_⟩
  apply Prod.ext <;> dsimp only [trianglePoint,u,v] <;> field_simp [nz] <;> unfold d orient <;> ring

noncomputable def supportSet (p : Drawing 28 ℝ) (D : Finset V) :=
  pairs.toFinset.filter (fun e => OnHull p D e)

theorem hull_count (p : Drawing 28 ℝ) (D : Finset V) : hullEdges p D = (supportSet p D).card := by
  classical
  have nd : pairs.Nodup := pairs_nodup
  rw [hullEdges,ls_finset pairs _ nd,natBoole]
  rfl

private theorem no_four {H : Finset Pair} (hc : H.card=3) {a b c d : Pair}
    (ha : a ∈ H) (hb : b ∈ H) (hc' : c ∈ H) (hd : d ∈ H)
    (ab : a ≠ b) (ac : a ≠ c) (ad : a ≠ d) (bc : b ≠ c) (bd : b ≠ d) (cd : c ≠ d) : False := by
  have sub : ({a,b,c,d} : Finset Pair) ⊆ H := by
    intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl|rfl|rfl|rfl <;> assumption
  have h := Finset.card_le_card sub
  simp [ab,ac,ad,bc,bd,cd,hc] at h

/-- Three supporting edges force a genuine triangular hull, with any
specified surviving support edge as its base. -/
theorem triangle_on_base (p : Drawing 28 ℝ) (gp : GeneralPosition p) (D : Finset V)
    (three : hullEdges p D = 3) (many : 3 ≤ (Finset.univ \ D).card) {b c : V}
    (hb : b ∉ D) (hc : c ∉ D) (bc : b ≠ c) (base : Supports p (Finset.univ \ D) b c) :
    ∃ x, x ∉ D ∧ x ≠ b ∧ x ≠ c ∧ Supports p (Finset.univ \ D) b x ∧
      Supports p (Finset.univ \ D) c x ∧ ∀ k, k ∉ D → InTriangle (p x) (p b) (p c) (p k) := by
  classical
  let S := Finset.univ \ D
  have mb : b ∈ S := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hb⟩
  have mc : c ∈ S := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hc⟩
  obtain ⟨x,mx,xc,xb,bx⟩ := next_support p gp S many mc mb bc.symm (flip_support base)
  obtain ⟨y,my,yb,yc,cy⟩ := next_support p gp S many mb mc bc base
  have nx := (Finset.mem_sdiff.mp mx).2
  have ny := (Finset.mem_sdiff.mp my).2
  have eq : x=y := by
    by_contra hxy
    obtain ⟨w,mw,wb,wx,xw⟩ := next_support p gp S many mb mx xb.symm bx
    have nw := (Finset.mem_sdiff.mp mw).2
    rw [hull_count] at three
    apply no_four three (supporting_mem hb hc bc base) (supporting_mem hb nx xb.symm bx)
      (supporting_mem hc ny yc.symm cy) (supporting_mem nx nw wx.symm xw)
    all_goals intro h; rcases same_edge.mp h with ⟨h₁,h₂⟩|⟨h₁,h₂⟩ <;> grind
  subst y
  refine ⟨x,nx,xb,xc,bx,cy,fun k hk => ?_⟩
  exact triangle_of_supports p gp mx mb mc xb xc bc base cy (flip_support bx) k
    (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hk⟩)

theorem exists_base (p : Drawing 28 ℝ) (gp : GeneralPosition p) :
    ∃ b c : V, b ≠ c ∧ Supports p Finset.univ b c := by
  classical
  have h := three_hull_edges p gp ∅ (by simp)
  rw [hull_count] at h
  obtain ⟨e,he⟩ := Finset.card_pos.mp (show 0 < (supportSet p ∅).card by omega)
  obtain ⟨mem,_,_,lr⟩ := Finset.mem_filter.mp he
  have distinct : pairs.all (fun a => a.1 != a.2) = true := by decide +kernel
  have ne : e.1 ≠ e.2 := by simpa using List.all_eq_true.mp distinct e (List.mem_toFinset.mp mem)
  refine ⟨e.1,e.2,ne,?_⟩
  rcases lr with l|r
  · right; intro i _
    by_contra! pos
    exact Finset.notMem_empty i (l (Finset.mem_filter.mpr ⟨Finset.mem_univ _,pos⟩))
  · left; intro i _
    by_contra! neg
    exact Finset.notMem_empty i (r (Finset.mem_filter.mpr ⟨Finset.mem_univ _,neg⟩))

theorem strict_of_triangle (p : Drawing 28 ℝ) (gp : GeneralPosition p) {a b c k : V}
    (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c) (ak : a ≠ k) (bk : b ≠ k) (ck : c ≠ k)
    (inside : InTriangle (p a) (p b) (p c) (p k)) : StrictlyInside (p a) (p b) (p c) (p k) := by
  obtain ⟨u,v,hu,hv,hs,hk⟩ := inside
  have nzU := gp.2 c a k ac.symm ck ak
  have nzV := gp.2 a b k ab ak bk
  have nzS := gp.2 b c k bc bk ck
  rw [hk] at nzU nzV nzS
  have posU : u ≠ 0 := by
    intro eq; subst u; apply nzU; unfold orient trianglePoint; dsimp; ring
  have posV : v ≠ 0 := by
    intro eq; subst v; apply nzV; unfold orient trianglePoint; dsimp; ring
  have small : u+v ≠ 1 := by
    intro eq; apply nzS
    have h : v=1-u := by linarith
    rw [h]; unfold orient trianglePoint; dsimp; ring
  exact ⟨u,v,hu.lt_of_ne posU.symm,hv.lt_of_ne posV.symm,hs.lt_of_ne small,hk⟩

end K28.Edges
