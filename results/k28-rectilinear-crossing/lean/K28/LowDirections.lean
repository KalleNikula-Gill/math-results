import K28.LowRay

namespace K28.Low
open K28.Edges

theorem frame_det (d u v : Vec) :
    dot d u * cross d v - cross d u * dot d v = dot d d * cross u v := by
  unfold dot cross; ring

theorem tie_collinear {p : Drawing 28 ℝ} {a b c : V} {d : Vec} (nz : d≠zeroV)
    (hb : dot d (p b)=dot d (p a)) (hc : dot d (p c)=dot d (p a)) :
    orient (p a) (p b) (p c)=0 := by
  have id := frame_det d (diff (p b) (p a)) (diff (p c) (p a))
  rw [dot_diff,dot_diff,hb,hc,sub_self,zero_mul,mul_zero,sub_zero] at id
  exact (mul_eq_zero.mp id.symm).resolve_left (square_pos nz).ne'

theorem tie_capacity {p : Drawing 28 ℝ} (gp : GeneralPosition p) {S : Finset V} (a : V)
    {d : Vec} (nz : d≠zeroV) :
    ((S.erase a).filter (fun b => dot d (p b)=dot d (p a))).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro b hb c hc
  obtain ⟨mb,eb⟩ := Finset.mem_filter.mp hb
  obtain ⟨mc,ec⟩ := Finset.mem_filter.mp hc
  by_contra ne
  exact gp.2 a b c (Finset.ne_of_mem_erase mb).symm (Finset.ne_of_mem_erase mc).symm ne (tie_collinear nz eb ec)

/-- Lexicographic tie breaking among finitely many projections is a single
linear functional. The strict inequalities of the first component survive. -/
theorem refine_axis {p : Drawing 28 ℝ} (gp : GeneralPosition p) {d : Vec} (nz : d≠zeroV) :
    ∃ u : Vec, Function.Injective (fun a => dot u (p a)) ∧
      ∀ a b, dot d (p a)<dot d (p b) → dot u (p a)<dot u (p b) := by
  classical
  let f := fun i => dot d (p i)
  let g := fun i => cross d (p i)
  let ratio := fun (i j : V) => (g i-g j)/(f j-f i)
  let B := (Finset.univ : Finset V).biUnion fun i => Finset.univ.image (ratio i)
  have mem (i j : V) : ratio i j∈B :=
    Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩⟩
  let t := B.max' ⟨_,mem 0 0⟩+1
  let u : Vec := (t*d.1-d.2,t*d.2+d.1)
  have val (i : V) : dot u (p i)=t*f i+g i := by dsimp [u,f,g,dot,cross]; ring
  have mono {i j} (h : f i<f j) : dot u (p i)<dot u (p j) := by
    have big : ratio i j<t := (B.le_max' _ (mem i j)).trans_lt (lt_add_one _)
    have b := (div_lt_iff₀ (sub_pos.mpr h)).mp big
    rw [val,val]; linarith only [b]
  refine ⟨u,?_,fun _ _ => mono⟩
  intro i j eq
  change dot u (p i)=dot u (p j) at eq
  rcases lt_trichotomy (f i) (f j) with h|h|h
  · exact False.elim ((mono h).ne eq)
  · have gg : g i=g j := by rw [val,val,h] at eq; linarith only [eq]
    let v := diff (p i) (p j)
    have d0 : dot d v=0 := (dot_diff _ _ _).trans (sub_eq_zero.mpr h)
    have c0 : cross d v=0 := by
      change cross d (diff (p i) (p j))=0
      calc _ = g i-g j := by dsimp [g,cross,diff]; ring
           _ = 0 := sub_eq_zero.mpr gg
    by_contra ne
    have vt : v≠zeroV := by
      intro z; apply ne; apply gp.1
      exact Prod.ext (sub_eq_zero.mp (congrArg Prod.fst z)) (sub_eq_zero.mp (congrArg Prod.snd z))
    have id : dot d d*dot v v=dot d v^2+cross d v^2 := by unfold dot cross; ring
    rw [d0,c0] at id
    linarith only [id,mul_pos (square_pos nz) (square_pos vt)]
  · exact False.elim ((mono h).ne eq.symm)

theorem exposed_max {p : Drawing 28 ℝ} (gp : GeneralPosition p) {S : Finset V} (ns : S.Nonempty)
    {d : Vec} (nz : d≠zeroV) :
    ∃ a∈S, Exposed p S a ∧ ∀ b∈S, dot d (p b)≤dot d (p a) := by
  obtain ⟨u,inj,mono⟩ := refine_axis gp nz
  obtain ⟨a,ha,highest⟩ := S.exists_max_image (fun i => dot u (p i)) ns
  have un : u≠zeroV := by
    intro z; subst u
    have bad := inj (show dot zeroV (p 0)=dot zeroV (p 1) by simp [dot,zeroV])
    exact (by decide : (0:V)≠1) bad
  refine ⟨a,ha,⟨(-u.1,-u.2),fun z => un (Prod.ext (by simpa [zeroV] using congrArg Prod.fst z)
    (by simpa [zeroV] using congrArg Prod.snd z)),?_⟩,?_⟩
  · intro b hb
    have lt := (highest b (Finset.mem_of_mem_erase hb)).lt_of_ne ((inj.ne (Finset.ne_of_mem_erase hb)))
    dsimp [dot,diff] at lt ⊢; linarith only [lt]
  · intro b hb; by_contra! h
    exact (highest b hb).not_gt (mono a b h)

def Generic (p : Drawing 28 ℝ) (v : Vec) := Function.Injective (fun i => cross v (p i))
structure Ray (p : Drawing 28 ℝ) (S : Finset V) (a : V) (v : Vec) : Prop extends SafeRay p S a v where
  mem : a∈S
  generic : Generic p v

theorem ray_nonzero {p : Drawing 28 ℝ} {v : Vec} (h : Generic p v) : v≠zeroV := by
  intro eq; subst v
  exact (by decide : (0:V)≠1) (h (show cross zeroV (p 0)=cross zeroV (p 1) by simp [zeroV,cross]))

theorem generic_ray {p : Drawing 28 ℝ} (gp : GeneralPosition p) {S : Finset V} (size : 3≤S.card)
    {a : V} (ha : a∈S) (ex : Exposed p S a) (z : Vec) :
    ∃ v, Ray p S a v ∧ (z≠zeroV → cross v z≠0) := by
  classical
  let B := ((Finset.univ : Finset V) ×ˢ (Finset.univ : Finset V)).image (fun e => diff (p e.1) (p e.2))
  obtain ⟨v,h,gen⟩ := ray_exists gp (by rw [Finset.card_erase_of_mem ha]; omega) ex (insert z B)
  refine ⟨v,⟨h,ha,?_⟩,gen z (Finset.mem_insert_self _ _)⟩
  intro i j eq
  by_contra ne
  let d := diff (p i) (p j)
  have dn : d≠zeroV := by
    intro zz; apply ne; apply gp.1
    exact Prod.ext (sub_eq_zero.mp (congrArg Prod.fst zz)) (sub_eq_zero.mp (congrArg Prod.snd zz))
  apply gen d (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨(i,j),Finset.mem_product.mpr ⟨Finset.mem_univ _,Finset.mem_univ _⟩,rfl⟩)) dn
  dsimp [d,diff,cross] at eq ⊢
  linarith only [eq]

theorem covers {p : Drawing 28 ℝ} (gp : GeneralPosition p) {S : Finset V} (size : 5≤S.card)
    {r : V → Vec} (rays : ∀ a∈S, Exposed p S a → SafeRay p S a (r a))
    {d : Vec} (nz : d≠zeroV) : ∃ a∈S, Exposed p S a ∧ 0<dot d (r a) := by
  classical
  obtain ⟨a,ha,ex,top⟩ := exposed_max (S:=S) gp (Finset.card_pos.mp (by omega)) nz
  refine ⟨a,ha,ex,?_⟩
  by_contra! bad
  let neg : Vec := (-d.1,-d.2)
  have opp : ∀ x, dot neg x= -dot d x := by intro x; dsimp [neg,dot]; ring
  have count := (rays a ha ex).safe neg (by rw [opp]; linarith only [bad])
  have sub : ((S.erase a).filter fun i => dot neg (p i)≤dot neg (p a)) ⊆
      (S.erase a).filter (fun i => dot d (p i)=dot d (p a)) := by
    intro i hi
    obtain ⟨m,h⟩ := Finset.mem_filter.mp hi
    rw [opp,opp,neg_le_neg_iff] at h
    exact Finset.mem_filter.mpr ⟨m,le_antisymm (top i (Finset.mem_of_mem_erase m)) h⟩
  have lim := tie_capacity (S:=S) gp a nz
  have bound := Finset.card_le_card sub
  rw [Finset.card_erase_of_mem ha] at count
  omega

/-- Three exposed rays surround the origin. All their normal projections
are generic for the full input, even when S is a proper subset. -/
theorem three_rays {p : Drawing 28 ℝ} (gp : GeneralPosition p) {S : Finset V} (size : 5≤S.card) :
    ∃ a b c : V, ∃ u v w : Vec, Ray p S a u ∧ Ray p S b v ∧ Ray p S c w ∧
      a≠b ∧ b≠c ∧ a≠c ∧ 0<cross u v ∧ 0<cross v w ∧ 0<cross w u := by
  classical
  obtain ⟨a,ma,ex,_⟩ := exposed_max (S:=S) gp (Finset.card_pos.mp (by omega))
    (show (1,0)≠zeroV by simp [zeroV])
  obtain ⟨u,ru,_⟩ := generic_ray gp (by omega) ma ex zeroV
  have un := ray_nonzero ru.generic
  have chooseRay (i : V) : ∃ z, i∈S → Exposed p S i → Ray p S i z ∧
      (i=a → z=u) ∧ (i≠a → cross u z≠0) := by
    by_cases ia : i=a
    · subst i; exact ⟨u,fun _ _ => ⟨ru,fun _ => rfl,fun h => False.elim (h rfl)⟩⟩
    by_cases cond : i∈S ∧ Exposed p S i
    · obtain ⟨z,rz,av⟩ := generic_ray gp (by omega) cond.1 cond.2 u
      exact ⟨z,fun _ _ => ⟨rz,fun eq => False.elim (ia eq),fun _ => by rw [cross_neg z]; exact neg_ne_zero.mpr (av un)⟩⟩
    · exact ⟨zeroV,fun m e => False.elim (cond ⟨m,e⟩)⟩
  choose r spec using chooseRay
  have ra := (spec a ma ex).2.1 rfl
  have all := fun i hi h => (spec i hi h).1.toSafeRay
  let H := S.filter (fun i => Exposed p S i ∧ 0<cross u (r i))
  obtain ⟨b0,m0,e0,p0⟩ := covers gp size all (perp_nonzero un)
  rw [dot_perp] at p0
  have nh : H.Nonempty := ⟨b0,Finset.mem_filter.mpr ⟨m0,e0,p0⟩⟩
  let ratio := fun i => dot u (r i)/cross u (r i)
  obtain ⟨b,mb,minimal⟩ := H.exists_min_image ratio nh
  obtain ⟨bs,be,uv⟩ := Finset.mem_filter.mp mb
  obtain ⟨c,cs,ce,vw⟩ := covers gp size all (perp_nonzero (ray_nonzero (spec b bs be).1.generic))
  rw [dot_perp] at vw
  have uw : cross u (r c)<0 := by
    by_contra! non
    have ca : c≠a := by intro h; subst c; rw [ra,cross_neg u] at vw; linarith
    have pos := non.lt_of_ne ((spec c cs ce).2.2 ca).symm
    have mr := minimal c (Finset.mem_filter.mpr ⟨cs,ce,pos⟩)
    have ineq := (div_le_div_iff₀ uv pos).mp mr
    have id := frame_det u (r b) (r c)
    linarith only [ineq,id,mul_pos (square_pos un) vw]
  refine ⟨a,b,c,u,r b,r c,ru,(spec b bs be).1,(spec c cs ce).1,?_,?_,?_,uv,vw,?_⟩
  · intro eq; subst b; rw [ra,cross_self] at uv; exact lt_irrefl _ uv
  · intro eq; subst c; rw [cross_self] at vw; exact lt_irrefl _ vw
  · intro eq; subst c; rw [ra,cross_self] at uw; exact lt_irrefl _ uw
  · rw [cross_neg u]; linarith

end K28.Low
