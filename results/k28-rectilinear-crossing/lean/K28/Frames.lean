import K28.Transversals

namespace K28.Projection
open K28.Edges

/-- A determinant-preserving coordinate system that starts a half-turn
with any given strictly separated group first. Distinct initial
projections are obtained by avoiding finitely many slope ratios. -/
theorem starting_frame {p : Drawing 28 ℝ} (gp : GeneralPosition p) {A : Finset V}
    (sep : StrictlySeparated p A) (members : A.Nonempty) (outside : ∃ b : V, b ∉ A) :
    ∃ q : Drawing 28 ℝ, Function.Injective (fun i => (q i).1) ∧
      (∀ a ∈ A, ∀ b ∉ A, (q a).1 < (q b).1) ∧
      ∀ i j k, orient (q i) (q j) (q k) = orient (p i) (p j) (p k) := by
  classical
  obtain ⟨u,v,strict⟩ := sep
  let f := fun i => -(u*(p i).1+v*(p i).2)
  let g := fun i => v*(p i).1-u*(p i).2
  let L := u*u+v*v
  have len : 0<L := by
    obtain ⟨a,ha⟩ := members
    obtain ⟨b,hb⟩ := outside
    have hs := strict a ha b hb
    by_cases hu : u=0
    · have hv : v≠0 := by intro h; simp [h,hu] at hs
      dsimp [L]; rw [hu,zero_mul,zero_add]; exact mul_self_pos.mpr hv
    · exact add_pos_of_pos_of_nonneg (mul_self_pos.mpr hu) (mul_self_nonneg v)
  let ratio := fun (a b : V) => (g a-g b)/(f b-f a)
  let B := (Finset.univ : Finset V).biUnion fun a => (Finset.univ : Finset V).image (ratio a)
  have mem (a b : V) : ratio a b ∈ B := Finset.mem_biUnion.mpr
    ⟨a,Finset.mem_univ _,Finset.mem_image.mpr ⟨b,Finset.mem_univ _,rfl⟩⟩
  obtain ⟨m,_,maximal⟩ := B.exists_max_image id ⟨_,mem 0 0⟩
  let t := m+1
  let q : Drawing 28 ℝ := fun i => (t*f i+g i,-f i/L)
  have mono {i j : V} (hh : f i<f j) : (q i).1 < (q j).1 := by
    have h := maximal (ratio i j) (mem i j)
    change ratio i j ≤ m at h
    have bound : ratio i j < t := h.trans_lt (lt_add_one _)
    have prod := (div_lt_iff₀ (sub_pos.mpr hh)).mp bound
    dsimp only [q]; linarith only [prod]
  refine ⟨q,?_,?_,?_⟩
  · intro i j eq
    rcases lt_trichotomy (f i) (f j) with h|h|h
    · exact False.elim ((mono h).ne eq)
    · have gg : g i=g j := by change t*f i+g i=t*f j+g j at eq; rw [h] at eq; linarith
      have hx : L*((p i).1-(p j).1) = (-u)*(f i-f j)+v*(g i-g j) := by dsimp [L,f,g]; ring
      have hy : L*((p i).2-(p j).2) = (-v)*(f i-f j)-u*(g i-g j) := by dsimp [L,f,g]; ring
      rw [h,gg,sub_self,sub_self,mul_zero,mul_zero,add_zero] at hx
      rw [h,gg,sub_self,sub_self,mul_zero,mul_zero,sub_zero] at hy
      exact gp.1 (Prod.ext (sub_eq_zero.mp ((mul_eq_zero.mp hx).resolve_left len.ne'))
        (sub_eq_zero.mp ((mul_eq_zero.mp hy).resolve_left len.ne')))
    · exact False.elim ((mono h).ne eq.symm)
  · intro i hi j hj; exact mono (neg_lt_neg (strict i hi j hj))
  · intro i j k
    change (t*f j+g j-(t*f i+g i))*(-f k/L-(-f i/L))-
        (-f j/L-(-f i/L))*(t*f k+g k-(t*f i+g i))=_
    field_simp [len.ne']; dsimp only [f,g,L,orient]; ring

noncomputable def below (q : Drawing 28 ℝ) (e : Pair) :=
  let t := event (q e.1) (q e.2)
  ls labels (fun k => flag (value t (q k) < value t (q e.1)))
noncomputable def above (q : Drawing 28 ℝ) (e : Pair) :=
  let t := event (q e.1) (q e.2)
  ls labels (fun k => flag (value t (q e.1) < value t (q k)))

theorem counts_at_event {p q : Drawing 28 ℝ} (ix : Function.Injective (fun i => (q i).1))
    (area : ∀ i j k, orient (q i) (q j) (q k) = orient (p i) (p j) (p k))
    {a b : V} (ab : a≠b) :
    (below q (a,b)=left p (a,b) ∧ above q (a,b)=right p (a,b)) ∨
    (below q (a,b)=right p (a,b) ∧ above q (a,b)=left p (a,b)) := by
  let t := event (q a) (q b)
  have s (k : V) : ((q b).1-(q a).1)*(value t (q k)-value t (q a)) = orient (p a) (p b) (p k) :=
    (side_at_event (q a) (q b) (q k) (ix.ne ab)).trans (area a b k)
  have dx := ix.ne ab
  change (q a).1 ≠ (q b).1 at dx
  rcases lt_or_gt_of_ne dx with h|h
  · right
    have pos := sub_pos.mpr h
    constructor <;> apply congr_summands <;> intro k _
    · change flag (value t (q k)<value t (q a)) = flag (orient (p a) (p b) (p k)<0)
      rw [←s]; simp [mul_neg_iff,pos,pos.not_gt]
    · change flag (value t (q a)<value t (q k)) = flag (0<orient (p a) (p b) (p k))
      rw [←s]; simp [pos]
  · left
    have neg := sub_neg.mpr h
    constructor <;> apply congr_summands <;> intro k _
    · change flag (value t (q k)<value t (q a)) = flag (0<orient (p a) (p b) (p k))
      rw [←s]; simp [mul_pos_iff,neg,neg.not_gt]
    · change flag (value t (q a)<value t (q k)) = flag (orient (p a) (p b) (p k)<0)
      rw [←s]; simp [mul_neg_iff,neg,neg.not_gt]

/-- The one-based swap gate is one more than the number of projections
strictly below its tied value. The reflected gates give the actual edge type. -/
theorem gate_type {p q : Drawing 28 ℝ} (gp : GeneralPosition p)
    (ix : Function.Injective (fun i => (q i).1))
    (area : ∀ i j k, orient (q i) (q j) (q k) = orient (p i) (p j) (p k))
    {a b : V} (ab : a≠b) (edge : (a,b) ∈ pairs) :
    let gate := below q (a,b)+1
    edgeType p (a,b) = min (gate-1) (27-gate) := by
  have sum := sides p gp (a,b) edge
  rcases counts_at_event ix area ab with h|h <;>
    dsimp only <;> unfold edgeType <;> rw [h.1] <;> omega

end K28.Projection
