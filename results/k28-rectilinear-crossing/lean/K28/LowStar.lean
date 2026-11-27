import K28.LowDirections

namespace K28.Low
open K28.Edges

noncomputable def star (p : Drawing 28 ℝ) (S : Finset V) (w : Nat) (a : V) :=
  (lowSet p S w).filter fun e => e.1=a ∨ e.2=a

theorem radial_sides {p : Drawing 28 ℝ} {S : Finset V} {a b : V} {u : Vec}
    (nz : u≠zeroV) (pos : ∀ j∈S.erase a, 0<dot u (diff (p j) (p a))) (hb : b∈S.erase a) :
    side p S (a,b)=priorCount (S.erase a) (slope u p a) b ∧
    side p S (b,a)=priorCount (S.erase a) (fun x => -slope u p a x) b := by
  have both (c : V) (hc : c∈S.erase a) :
      (orient (p a) (p b) (p c)<0 ↔ slope u p a c<slope u p a b) ∧
      (0<orient (p a) (p b) (p c) ↔ slope u p a b<slope u p a c) := by
    have id := slope_identity (pos b hb) (pos c hc)
    have len := square_pos nz
    have sc := mul_pos (pos b hb) (pos c hc)
    have eq : orient (p a) (p b) (p c) =
        (dot u (diff (p b) (p a))*dot u (diff (p c) (p a))*(slope u p a c-slope u p a b))/dot u u :=
      (eq_div_iff len.ne').mpr (by rw [mul_comm]; exact id)
    rw [eq,div_neg_iff,div_pos_iff,mul_neg_iff,mul_pos_iff]
    simp [len,sc,not_lt_of_ge len.le,not_lt_of_ge sc.le,sub_neg,sub_pos]
  constructor <;> apply congrArg Finset.card <;> ext c
  · by_cases ca : c=a
    · subst c; simp [area_start]
    by_cases mem : c∈S
    · have hc := Finset.mem_erase.mpr ⟨ca,mem⟩
      simp only [Finset.mem_filter,mem,hc,true_and]; exact (both c hc).1
    · simp [mem]
  · by_cases ca : c=a
    · subst c; simp [area_end]
    by_cases mem : c∈S
    · have hc := Finset.mem_erase.mpr ⟨ca,mem⟩
      simp only [Finset.mem_filter,mem,hc,true_and,neg_lt_neg_iff,area_flip (p a) (p b),neg_lt_zero]
      exact (both c hc).2
    · simp [mem]

theorem star_size {p : Drawing 28 ℝ} (gp : GeneralPosition p) {S : Finset V} {a : V} (ha : a∈S)
    (ex : Exposed p S a) (w : Nat) (hw : w<S.card) : 2*w≤(star p S w a).card := by
  classical
  obtain ⟨u,nz,pos⟩ := ex
  let F := slope u p a
  let X := S.erase a
  let L := X.filter fun i => priorCount X F i<w
  let H := X.filter fun i => priorCount X (fun j => -F j) i<w
  let A := L.image (fun i => (a,i))
  let B := H.image (fun i => (i,a))
  have hX : w≤X.card := by dsimp [X]; rw [Finset.card_erase_of_mem ha]; omega
  have inj := slopes_injective gp nz pos
  have ca : A.card=w := by
    rw [show A.card=L.card from Finset.card_image_iff.mpr (fun _ _ _ _ e => congrArg Prod.snd e)]
    exact prefix_card inj hX
  have cb : B.card=w := by
    rw [show B.card=H.card from Finset.card_image_iff.mpr (fun _ _ _ _ e => congrArg Prod.fst e)]
    exact prefix_card (fun i hi j hj e => inj hi hj (neg_inj.mp e)) hX
  have dis : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro e h k
    obtain ⟨i,mi,rfl⟩ := Finset.mem_image.mp h
    obtain ⟨j,_,eq⟩ := Finset.mem_image.mp k
    exact Finset.ne_of_mem_erase (Finset.mem_filter.mp mi).1 (congrArg Prod.snd eq).symm
  have sub : A∪B⊆star p S w a := by
    intro e he
    rcases Finset.mem_union.mp he with h|h
    · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp h
      obtain ⟨m,t⟩ := Finset.mem_filter.mp hi
      have count := (radial_sides nz pos m).1
      exact Finset.mem_filter.mpr ⟨low_mem.mpr ⟨ha,Finset.mem_of_mem_erase m,(Finset.ne_of_mem_erase m).symm,
        count ▸ t⟩,Or.inl rfl⟩
    · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp h
      obtain ⟨m,t⟩ := Finset.mem_filter.mp hi
      have count := (radial_sides nz pos m).2
      exact Finset.mem_filter.mpr ⟨low_mem.mpr ⟨Finset.mem_of_mem_erase m,ha,Finset.ne_of_mem_erase m,
        count ▸ t⟩,Or.inr rfl⟩
  have b := Finset.card_le_card sub; rw [Finset.card_union_of_disjoint dis,ca,cb] at b; omega

theorem star_overlap {p : Drawing 28 ℝ} (gp : GeneralPosition p) {S : Finset V} {a b : V}
    (ab : a≠b) {w : Nat} (space : 2*w<S.card) :
    ((star p S w a)∩(star p S w b)).card≤1 := by
  classical
  have shape {e : Pair} (h : e∈star p S w a∩star p S w b) :
      e=(a,b) ∨ e=(b,a) := by
    have i := Finset.mem_inter.mp h
    obtain x|x := (Finset.mem_filter.mp i.1).2 <;> obtain y|y := (Finset.mem_filter.mp i.2).2
    · exact False.elim (ab (x.symm.trans y))
    · exact Or.inl (Prod.ext x y)
    · exact Or.inr (Prod.ext y x)
    · exact False.elim (ab (x.symm.trans y))
  have exclusive (h : (a,b)∈star p S w a∩star p S w b) (j : (b,a)∈star p S w a∩star p S w b) : False := by
    have x := low_mem.mp (Finset.mem_filter.mp (Finset.mem_inter.mp h).1).1
    have y := low_mem.mp (Finset.mem_filter.mp (Finset.mem_inter.mp j).1).1
    have total := side_sum gp x.1 x.2.1 ab
    omega
  apply Finset.card_le_one.mpr
  intro e he f hf
  rcases shape he with h|h <;> rcases shape hf with k|k <;> subst e <;> subst f
  · rfl
  · exact False.elim (exclusive he hf)
  · exact False.elim (exclusive hf he)
  · rfl

theorem three_stars {p : Drawing 28 ℝ} (gp : GeneralPosition p) {S : Finset V} {a b c : V} {u v z : Vec}
    (aR : Ray p S a u) (bR : Ray p S b v) (cR : Ray p S c z)
    (ab : a≠b) (bc : b≠c) (ac : a≠c) {w : Nat} (space : 2*w<S.card) :
    6*w ≤ ((star p S w a∪star p S w b)∪star p S w c).card+3 := by
  let A:=star p S w a; let B:=star p S w b; let C:=star p S w c
  have aa := star_size gp aR.mem aR.exposed w (by omega)
  have bb := star_size gp bR.mem bR.exposed w (by omega)
  have cc := star_size gp cR.mem cR.exposed w (by omega)
  have xy := star_overlap gp ab space
  have yz := star_overlap gp bc space
  have xz := star_overlap gp ac space
  have s := Finset.card_union_add_card_inter A B
  have t := Finset.card_union_add_card_inter (A∪B) C
  rw [Finset.union_inter_distrib_right] at t
  have h := Finset.card_union_le (A∩C) (B∩C)
  dsimp only [A,B,C] at s t h
  omega

end K28.Low
