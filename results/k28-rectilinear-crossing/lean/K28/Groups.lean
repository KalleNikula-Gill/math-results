import K28.Triangles

namespace K28.Edges

set_option maxRecDepth 4096

/-- Each chosen label was the exposed apex after removing a prefix
drawn from this chain. The two fixed hull vertices always survive. -/
structure Chain (p : Drawing 28 ℝ) (b c : V) (A : Finset V) : Prop where
  fixedB : b ∉ A
  fixedC : c ∉ A
  exposed : ∀ x ∈ A, ∃ D : Finset V, D ⊆ A ∧ D.card ≤ 9 ∧ x ∉ D ∧
    ∀ k, k ∉ D → InTriangle (p x) (p b) (p c) (p k)

private theorem restrict_support {p : Drawing 28 ℝ} {S T : Finset V} {b c : V}
    (s : Supports p S b c) (sub : T ⊆ S) : Supports p T b c := by
  rcases s with h|h
  · exact Or.inl (fun i hi => h _ (sub hi))
  · exact Or.inr (fun i hi => h _ (sub hi))

private theorem extend_chain {p : Drawing 28 ℝ} (gp : GeneralPosition p) {b c : V}
    (bc : b ≠ c) (base : Supports p Finset.univ b c) {A : Finset V}
    (chain : Chain p b c A) (ht : hullEdges p A = 3) (hn : A.card ≤ 9) :
    ∃ W, A ⊆ W ∧ W.card=A.card+1 ∧ Chain p b c W := by
  obtain ⟨x,hx,xb,xc,_,_,encloses⟩ := triangle_on_base p gp A ht
    (by rw [survivor_card]; omega) chain.fixedB chain.fixedC bc (restrict_support base (Finset.subset_univ _))
  have sub : A ⊆ insert x A := Finset.subset_insert _ _
  refine ⟨insert x A,sub,Finset.card_insert_of_notMem hx,?_,?_,?_⟩
  · simpa [xb.symm] using chain.fixedB
  · simpa [xc.symm] using chain.fixedC
  · intro k hk
    rcases Finset.mem_insert.mp hk with eq|mem
    · subst k; exact ⟨A,sub,hn,hx,encloses⟩
    · obtain ⟨D,hd,n,avoid,h⟩ := chain.exposed k mem
      exact ⟨D,hd.trans sub,n,avoid,h⟩

private theorem first_nine {p : Drawing 28 ℝ} (gp : GeneralPosition p)
    (ep : ∀ k : Nat, k < 10 → counts p k = profile[k]!) {b c : V}
    (bc : b ≠ c) (base : Supports p Finset.univ b c) (n : Nat) (hn : n ≤ 9) :
    ∃ A, A.card=n ∧ Chain p b c A := by
  induction n with
  | zero => exact ⟨∅,rfl,by simp,by simp,by simp⟩
  | succ n ih =>
    obtain ⟨A,hc,hA⟩ := ih (by omega)
    obtain ⟨W,_,hw,hW⟩ := extend_chain gp bc base hA (three_after_eight p gp ep A (by omega)) (by omega)
    exact ⟨W,by omega,hW⟩

private theorem make_branch {p : Drawing 28 ℝ} (gp : GeneralPosition p)
    (ep : ∀ k : Nat, k < 10 → counts p k = profile[k]!) {b c : V}
    (bc : b ≠ c) (base : Supports p Finset.univ b c) : ∃ removed members : Finset V,
      removed.card=9 ∧ removed ⊆ members ∧ Chain p b c members ∧
      members.card = (if hullEdges p removed=3 then 10 else 9) := by
  classical
  obtain ⟨A,n,ch⟩ := first_nine gp ep bc base 9 (by decide)
  by_cases h : hullEdges p A=3
  · obtain ⟨W,sub,hw,chw⟩ := extend_chain gp bc base ch h n.le
    exact ⟨A,W,n,sub,chw,by simp [h,hw,n]⟩
  · exact ⟨A,A,n,Finset.Subset.rfl,ch,by simp [h,n]⟩

private theorem rotate_triangle {a b c z : Point ℝ} (h : InTriangle a b c z) : InTriangle c a b z := by
  obtain ⟨u,v,hu,hv,hs,hz⟩ := h
  refine ⟨1-u-v,u,by linarith,hu,by linarith,?_⟩
  rw [hz]; apply Prod.ext <;> dsimp [trianglePoint] <;> ring

private theorem reverse_base {a b c z : Point ℝ} (h : InTriangle a b c z) : InTriangle a c b z := by
  obtain ⟨u,v,hu,hv,hs,hz⟩ := h
  refine ⟨v,u,hv,hu,by linarith,?_⟩
  rw [hz]; apply Prod.ext <;> dsimp [trianglePoint] <;> ring

private theorem common_survivor (D E : Finset V) (x c : V) (hd : D.card ≤ 9) (he : E.card ≤ 9) :
    ∃ k : V, k ∉ D ∧ k ∉ E ∧ k ≠ x ∧ k ≠ c := by
  classical
  let F := D ∪ E ∪ {x,c}
  have h₁ := Finset.card_union_le D E
  have h₂ := Finset.card_union_le (D ∪ E) ({x,c} : Finset V)
  have h₃ := Finset.card_le_two (a:=x) (b:=c)
  by_contra! fail
  have sub : (Finset.univ : Finset V) ⊆ F := by
    intro y _
    by_contra hm
    simp only [F,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,not_or] at hm
    exact hm.2.2 (fail y hm.1.1 hm.1.2 hm.2.1)
  have h := Finset.card_le_card sub
  change (Finset.univ : Finset V).card ≤ (D ∪ E ∪ {x,c}).card at h
  rw [Finset.card_univ,Fintype.card_fin] at h
  omega

theorem disjoint_chains {p : Drawing 28 ℝ} (gp : GeneralPosition p) {a b c : V}
    (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c)
    (inside : ∀ k, InTriangle (p a) (p b) (p c) (p k))
    {A B : Finset V} (ca : Chain p b c A) (cb : Chain p c a B) : Disjoint A B := by
  apply Finset.disjoint_left.mpr
  intro x ax bx
  have xa : x ≠ a := fun e => cb.fixedC (e ▸ bx)
  have xb : x ≠ b := fun e => ca.fixedB (e ▸ ax)
  have xc : x ≠ c := fun e => ca.fixedC (e ▸ ax)
  have strict := strict_of_triangle p gp ab ac bc xa.symm xb.symm xc.symm (inside x)
  obtain ⟨D,_,hd,_,left⟩ := ca.exposed x ax
  obtain ⟨E,_,he,_,right⟩ := cb.exposed x bx
  obtain ⟨k,kd,ke,kx,kc⟩ := common_survivor D E x c hd he
  exact gp.2 x c k xc kx.symm kc.symm (shared_apex_line (gp.2 a b c ab ac bc) strict
    (left k kd) (rotate_triangle (right k ke)))

/-- There is an affine functional that is strictly larger on every group
member than on every label outside the group. -/
def StrictlySeparated (p : Drawing 28 ℝ) (A : Finset V) :=
  ∃ u v : ℝ, ∀ x ∈ A, ∀ y ∉ A, u*(p y).1+v*(p y).2 < u*(p x).1+v*(p x).2

theorem separated_chain {p : Drawing 28 ℝ} (gp : GeneralPosition p) {b c : V}
    (bc : b ≠ c) (s : Supports p Finset.univ b c) {A : Finset V}
    (ch : Chain p b c A) : StrictlySeparated p A := by
  have coeff (i j k : V) : orient (p i) (p j) (p k) =
      ((p i).2-(p j).2)*(p k).1 + ((p j).1-(p i).1)*(p k).2 +
        ((p i).1*(p j).2-(p j).1*(p i).2) := by unfold orient; ring
  rcases s with pos|neg
  · refine ⟨(p b).2-(p c).2,(p c).1-(p b).1,?_⟩
    intro x hx y hy
    have xb : b ≠ x := fun e => ch.fixedB (e ▸ hx)
    have xc : c ≠ x := fun e => ch.fixedC (e ▸ hx)
    obtain ⟨D,sub,_,_,h⟩ := ch.exposed x hx
    have dif : p y ≠ p x := gp.1.ne (fun e => hy (e ▸ hx))
    have high := apex_height ((pos x (Finset.mem_univ _)).lt_of_ne (gp.2 b c x bc xb xc).symm)
      (h y (fun hd => hy (sub hd))) dif
    rw [coeff,coeff] at high; linarith only [high]
  · refine ⟨(p c).2-(p b).2,(p b).1-(p c).1,?_⟩
    intro x hx y hy
    have xb : b ≠ x := fun e => ch.fixedB (e ▸ hx)
    have xc : c ≠ x := fun e => ch.fixedC (e ▸ hx)
    obtain ⟨D,sub,_,_,h⟩ := ch.exposed x hx
    have dif : p y ≠ p x := gp.1.ne (fun e => hy (e ▸ hx))
    have pos : 0 < orient (p c) (p b) (p x) := by
      have hh := (neg x (Finset.mem_univ _)).lt_of_ne (gp.2 b c x bc xb xc)
      have rev : orient (p c) (p b) (p x) = -orient (p b) (p c) (p x) := by unfold orient; ring
      rw [rev]; exact neg_pos.mpr hh
    have high := apex_height pos (reverse_base (h y (fun hd => hy (sub hd)))) dif
    rw [coeff,coeff] at high; linarith only [high]

/-- A partition of an actual drawing by three strictly separated finite
sets of labels, with the largest group named first. -/
structure ThreeGroups (p : Drawing 28 ℝ) where
  A : Finset V
  B : Finset V
  C : Finset V
  sizeA : A.card=10
  sizeB : B.card=9
  sizeC : C.card=9
  disAB : Disjoint A B
  disBC : Disjoint B C
  disCA : Disjoint C A
  exhaust : A ∪ B ∪ C = Finset.univ
  sepA : StrictlySeparated p A
  sepB : StrictlySeparated p B
  sepC : StrictlySeparated p C

private theorem full_union {A B C : Finset V} (ab : Disjoint A B) (bc : Disjoint B C)
    (ca : Disjoint C A) (tot : A.card+B.card+C.card=28) : A ∪ B ∪ C = Finset.univ := by
  apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
  rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨ca.symm,bc⟩),
    Finset.card_union_of_disjoint ab,tot]
  simp

private theorem unequal_prefix {I J X Y : Finset V} (n : I.card=9)
    (s : I ⊆ X) (t : J ⊆ Y) (dis : Disjoint X Y) : I ≠ J := by
  intro eq
  obtain ⟨i,hi⟩ := Finset.card_pos.mp (show 0<I.card by omega)
  exact Finset.disjoint_left.mp dis (s hi) (t (eq ▸ hi))

theorem groups_of_profile (p : Drawing 28 ℝ) (gp : GeneralPosition p)
    (ep : ∀ k : Nat, k < 10 → counts p k = profile[k]!) : Nonempty (ThreeGroups p) := by
  classical
  obtain ⟨b,c,bc,base⟩ := exists_base p gp
  obtain ⟨a,_,ab,ac,sba,sca,enc⟩ := triangle_on_base p gp ∅
    (three_after_eight p gp ep _ (by simp)) (by simp) (Finset.notMem_empty _) (Finset.notMem_empty _)
    bc (by simpa using base)
  have inside : ∀ i, InTriangle (p a) (p b) (p c) (p i) := fun i => enc i (Finset.notMem_empty _)
  have sb : Supports p Finset.univ c a := by simpa using sca
  have sc : Supports p Finset.univ a b := flip_support (by simpa using sba)
  obtain ⟨DX,X,nX,subX,chX,sx⟩ := make_branch gp ep bc base
  obtain ⟨DY,Y,nY,subY,chY,sy⟩ := make_branch gp ep ac.symm sb
  obtain ⟨DZ,Z,nZ,subZ,chZ,sz⟩ := make_branch gp ep ab sc
  have xy := disjoint_chains gp ab ac bc inside chX chY
  have yz := disjoint_chains gp bc ab.symm ac.symm (fun i => rotate_triangle (rotate_triangle (inside i))) chY chZ
  have zx := disjoint_chains gp ac.symm bc.symm ab (fun i => rotate_triangle (inside i)) chZ chX
  have upper := Finset.card_le_card (Finset.subset_univ (X ∪ Y ∪ Z))
  rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨zx.symm,yz⟩),
    Finset.card_union_of_disjoint xy,Finset.card_univ,Fintype.card_fin] at upper
  let bad := ((Finset.univ : Finset V).powersetCard 9).filter (fun D => 3 < hullEdges p D)
  have badmem {D : Finset V} (n : D.card=9) (h : hullEdges p D ≠ 3) : D ∈ bad := by
    have low := three_hull_edges p gp D (by rw [survivor_card,n]; decide)
    exact Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,n⟩,by omega⟩
  have one : hullEdges p DX=3 ∨ hullEdges p DY=3 ∨ hullEdges p DZ=3 := by
    by_contra! none
    have h : 2 < bad.card := Finset.two_lt_card_iff.mpr
      ⟨_,_,_,badmem nX none.1,badmem nY none.2.1,badmem nZ none.2.2,
        unequal_prefix nX subX subY xy,(unequal_prefix nZ subZ subX zx).symm,unequal_prefix nY subY subZ yz⟩
    exact (not_lt_of_ge (at_most_two_ninth_exceptions p gp ep)) h
  have ax := separated_chain gp bc base chX
  have ay := separated_chain gp ac.symm sb chY
  have az := separated_chain gp ab sc chZ
  rcases one with h|h|h
  · rw [if_pos h] at sx
    split_ifs at sy sz <;> first | omega | exact ⟨⟨_,_,_,sx,sy,sz,xy,yz,zx,
      full_union xy yz zx (by omega),ax,ay,az⟩⟩
  · rw [if_pos h] at sy
    split_ifs at sx sz <;> first | omega | exact ⟨⟨_,_,_,sy,sz,sx,yz,zx,xy,
      full_union yz zx xy (by omega),ay,az,ax⟩⟩
  · rw [if_pos h] at sz
    split_ifs at sx sy <;> first | omega | exact ⟨⟨_,_,_,sz,sx,sy,zx,xy,yz,
      full_union zx xy yz (by omega),az,ax,ay⟩⟩

/-- Only the two published edge estimates are supplied as geometric
hypotheses. All hull counting and group extraction are derived. -/
theorem groups_of_7233 (p : Drawing 28 ℝ) (gp : GeneralPosition p)
    (low : ∀ k : Nat, k < 12 → lower[k]! ≤ E (counts p) k)
    (central : counts p 13 ≤ counts p 12) (eq : crossings p = 7233) : Nonempty (ThreeGroups p) :=
  groups_of_profile p gp (fun k hk => drawing_profile p gp low central eq k (by omega))

end K28.Edges
