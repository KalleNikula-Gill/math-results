import K28.Deletions
import K28.Projection
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace K28.Edges
open K28.Projection

/-- A shear giving all coordinates distinct first components preserves
every determinant, including its sign and zero set. -/
private theorem generic_axis (p : Drawing 28 ℝ) (gp : GeneralPosition p) :
    ∃ q : Drawing 28 ℝ, Function.Injective (fun a => (q a).1) ∧
      ∀ a b c, orient (q a) (q b) (q c) = orient (p a) (p b) (p c) := by
  classical
  let bad := fun (a b : V) => ((p b).1-(p a).1)/((p a).2-(p b).2)
  let B := (Finset.univ : Finset V).biUnion fun a => (Finset.univ : Finset V).image (bad a)
  have outside : ∃ t : ℝ, t ∉ B := by
    by_cases non : B.Nonempty
    · obtain ⟨m,_,mx⟩ := B.exists_max_image id non
      refine ⟨m+1,fun mem => ?_⟩
      have h := mx (m+1) mem
      change m+1 ≤ m at h
      linarith
    · exact ⟨0,fun h => non ⟨_,h⟩⟩
  obtain ⟨t,ht⟩ := outside
  let q : Drawing 28 ℝ := fun a => ((p a).1 + t*(p a).2,(p a).2)
  refine ⟨q,?_,?_⟩
  · intro a b ab
    change (p a).1+t*(p a).2 = (p b).1+t*(p b).2 at ab
    by_cases hy : (p a).2=(p b).2
    · exact gp.1 (Prod.ext (by linarith only [ab,congrArg (fun v => t*v) hy]) hy)
    · have eq : t = bad a b := (eq_div_iff (sub_ne_zero.mpr hy)).mpr (by linarith only [ab])
      exact False.elim (ht (eq ▸ Finset.mem_biUnion.mpr
        ⟨a,Finset.mem_univ _,Finset.mem_image.mpr ⟨b,Finset.mem_univ _,rfl⟩⟩))
  · intro a b c; unfold orient; dsimp [q]; ring

def endpoints (a b : V) : Pair := (min a b,max a b)

theorem endpoint_pair (a b : V) (ab : a ≠ b) : endpoints a b ∈ pairs := by
  have ordered (a b : V) (ab : a < b) : (a,b) ∈ pairs := by
    apply List.mem_flatMap.mpr
    exact ⟨b,List.mem_finRange _,List.mem_map.mpr ⟨⟨a.val,ab⟩,List.mem_finRange _,rfl⟩⟩
  rcases lt_or_gt_of_ne ab with h | h
  · simpa only [endpoints,min_eq_left h.le,max_eq_right h.le] using ordered a b h
  · simpa only [endpoints,min_eq_right h.le,max_eq_left h.le] using ordered b a h

theorem same_edge {a b c d : V} : endpoints a b = endpoints c d ↔
    (a=c ∧ b=d) ∨ (a=d ∧ b=c) := by
  simp only [endpoints,min_def,max_def]
  split_ifs <;> simp only [Prod.mk.injEq] <;> grind

private theorem sign_swap (a b c : Point ℝ) : orient b a c = -orient a b c := by unfold orient; ring

/-- A support edge is an unordered, surviving pair whose line has all
survivors in one closed half-plane. -/
def Supports (p : Drawing 28 ℝ) (S : Finset V) (a b : V) :=
  (∀ c ∈ S, 0 ≤ orient (p a) (p b) (p c)) ∨ (∀ c ∈ S, orient (p a) (p b) (p c) ≤ 0)

theorem flip_support {p : Drawing 28 ℝ} {S : Finset V} {a b : V}
    (h : Supports p S a b) : Supports p S b a := by
  rcases h with h|h
  · right; intro c hc; rw [sign_swap]; exact neg_nonpos.mpr (h c hc)
  · left; intro c hc; rw [sign_swap]; exact neg_nonneg.mpr (h c hc)

theorem supporting_mem {p : Drawing 28 ℝ} {D : Finset V} {a b : V}
    (ha : a ∉ D) (hb : b ∉ D) (ab : a ≠ b) (s : Supports p (Finset.univ \ D) a b) :
    endpoints a b ∈ pairs.toFinset.filter (fun e => OnHull p D e) := by
  classical
  have both {x y : V} (hx : x ∉ D) (hy : y ∉ D) (ss : Supports p (Finset.univ \ D) x y) :
      OnHull p D (x,y) := by
    refine ⟨hx,hy,?_⟩
    rcases ss with s|s
    · right; intro c hc
      by_contra h
      exact (not_lt_of_ge (s c (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,h⟩)))
        ((Finset.mem_filter.mp hc).2)
    · left; intro c hc
      by_contra h
      exact (not_lt_of_ge (s c (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,h⟩)))
        ((Finset.mem_filter.mp hc).2)
  refine Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr (endpoint_pair a b ab),?_⟩
  rcases le_total a b with h|h
  · simpa [endpoints,min_eq_left h,max_eq_right h] using both ha hb s
  · simpa [endpoints,min_eq_right h,max_eq_left h] using both hb ha (flip_support s)

private theorem det_slope (a b c : Point ℝ) (hb : b.1 ≠ a.1) (hc : c.1 ≠ a.1) :
    orient a b c = ((b.1-a.1)*(c.1-a.1))*(event a c - event a b) := by
  unfold orient event
  field_simp [sub_ne_zero.mpr hb,sub_ne_zero.mpr hc]

/-- At an extreme of a generic linear coordinate, the two extreme
slopes to other points yield two distinct supporting edges. -/
private theorem two_supports (p q : Drawing 28 ℝ) (gp : GeneralPosition p)
    (ix : Function.Injective (fun a => (q a).1))
    (eq : ∀ a b c, orient (q a) (q b) (q c) = orient (p a) (p b) (p c))
    (S : Finset V) (hs : 3 ≤ S.card) (a : V) (ha : a ∈ S)
    (extreme : (∀ i ∈ S, (q a).1 ≤ (q i).1) ∨ (∀ i ∈ S, (q i).1 ≤ (q a).1)) :
    ∃ b ∈ S, ∃ c ∈ S, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ Supports p S a b ∧ Supports p S a c := by
  classical
  let T := S.erase a
  have sz : 1 < T.card := by dsimp [T]; rw [Finset.card_erase_of_mem ha]; omega
  obtain ⟨b,hb,small⟩ := T.exists_min_image (fun i => event (q a) (q i)) (Finset.card_pos.mp (by omega))
  obtain ⟨c,hc,large⟩ := T.exists_max_image (fun i => event (q a) (q i)) (Finset.card_pos.mp (by omega))
  have ab : a ≠ b := (Finset.mem_erase.mp hb).1.symm
  have ac : a ≠ c := (Finset.mem_erase.mp hc).1.symm
  have sign {i j : V} (hi : i ∈ T) (hj : j ∈ T) :
      0 < ((q i).1-(q a).1)*((q j).1-(q a).1) := by
    obtain ⟨di,si⟩ := Finset.mem_erase.mp hi
    obtain ⟨dj,sj⟩ := Finset.mem_erase.mp hj
    have ni := ix.ne di
    have nj := ix.ne dj
    rcases extreme with ex|ex
    · exact mul_pos (sub_pos.mpr ((ex i si).lt_of_ne ni.symm)) (sub_pos.mpr ((ex j sj).lt_of_ne nj.symm))
    · exact mul_pos_of_neg_of_neg (sub_neg.mpr ((ex i si).lt_of_ne ni)) (sub_neg.mpr ((ex j sj).lt_of_ne nj))
  have area {i j : V} (hi : i ∈ T) (hj : j ∈ T) :
      orient (p a) (p i) (p j) =
      ((q i).1-(q a).1)*((q j).1-(q a).1)*(event (q a) (q j)-event (q a) (q i)) :=
    (eq _ _ _).symm.trans (det_slope _ _ _ (ix.ne (Finset.mem_erase.mp hi).1) (ix.ne (Finset.mem_erase.mp hj).1))
  have distinct : b ≠ c := by
    intro bc
    obtain ⟨k,hk,kb⟩ := Finset.exists_mem_ne sz b
    have same := le_antisymm ((bc ▸ large) k hk) (small k hk)
    have nz := gp.2 a b k ab (Finset.mem_erase.mp hk).1.symm kb.symm
    rw [area hb hk,same,sub_self,mul_zero] at nz
    exact nz rfl
  refine ⟨b,(Finset.mem_erase.mp hb).2,c,(Finset.mem_erase.mp hc).2,ab,ac,distinct,Or.inl ?_,Or.inr ?_⟩
  · intro k hk
    by_cases h : k=a
    · subst k; simp [orient]
    · have mem := Finset.mem_erase.mpr ⟨h,hk⟩
      rw [area hb mem]; exact mul_nonneg (sign hb mem).le (sub_nonneg.mpr (small k mem))
  · intro k hk
    by_cases h : k=a
    · subst k; simp [orient]
    · have mem := Finset.mem_erase.mpr ⟨h,hk⟩
      rw [area hc mem]; exact mul_nonpos_of_nonneg_of_nonpos (sign hc mem).le (sub_nonpos.mpr (large k mem))

private theorem three_distinct {H : Finset Pair} {a z b c u v : V} (az : a ≠ z)
    (bc : b ≠ c) (uv : u ≠ v) (h₁ : endpoints a b ∈ H) (h₂ : endpoints a c ∈ H)
    (h₃ : endpoints z u ∈ H) (h₄ : endpoints z v ∈ H) : 2 < H.card := by
  have diff : endpoints a b ≠ endpoints a c := by intro h; rcases same_edge.mp h with ⟨_,h₂⟩|⟨h₁,h₂⟩ <;> grind
  by_cases bu : endpoints z u = endpoints a b ∨ endpoints z u = endpoints a c
  · by_cases bv : endpoints z v = endpoints a b ∨ endpoints z v = endpoints a c
    · rcases bu with hu|hu <;> rcases bv with hv|hv <;> rcases same_edge.mp hu with ⟨u₁,u₂⟩|⟨u₁,u₂⟩ <;>
        rcases same_edge.mp hv with ⟨v₁,v₂⟩|⟨v₁,v₂⟩ <;> grind
    · exact Finset.two_lt_card_iff.mpr ⟨_,_,_,h₁,h₂,h₄,diff,(fun h => bv (Or.inl h.symm)),(fun h => bv (Or.inr h.symm))⟩
  · exact Finset.two_lt_card_iff.mpr ⟨_,_,_,h₁,h₂,h₃,diff,(fun h => bu (Or.inl h.symm)),(fun h => bu (Or.inr h.symm))⟩

/-- Every retained set of at least three general-position points has at
least three supporting edges, counted with the original sorted pair indices. -/
theorem three_hull_edges (p : Drawing 28 ℝ) (gp : GeneralPosition p) (D : Finset V)
    (hs : 3 ≤ (Finset.univ \ D).card) : 3 ≤ hullEdges p D := by
  classical
  let S := Finset.univ \ D
  change 3 ≤ S.card at hs
  have sn : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨q,ix,eq⟩ := generic_axis p gp
  obtain ⟨a,ha,lo⟩ := S.exists_min_image (fun i => (q i).1) sn
  obtain ⟨z,hz,hi⟩ := S.exists_max_image (fun i => (q i).1) sn
  have az : a ≠ z := by
    intro h
    obtain ⟨k,hk,kn⟩ := Finset.exists_mem_ne (s:=S) (by omega) a
    exact kn (ix (le_antisymm ((h ▸ hi) k hk) (lo k hk)))
  obtain ⟨b,hb,c,hc,ab,ac,bc,se₁,se₂⟩ := two_supports p q gp ix eq S hs a ha (Or.inl lo)
  obtain ⟨u,hu,v,hv,zu,zv,uv,se₃,se₄⟩ := two_supports p q gp ix eq S hs z hz (Or.inr hi)
  have nd : pairs.Nodup := pairs_nodup
  rw [hullEdges,ls_finset pairs _ nd,natBoole]
  exact three_distinct az bc uv
    (supporting_mem (Finset.mem_sdiff.mp ha).2 (Finset.mem_sdiff.mp hb).2 ab se₁)
    (supporting_mem (Finset.mem_sdiff.mp ha).2 (Finset.mem_sdiff.mp hc).2 ac se₂)
    (supporting_mem (Finset.mem_sdiff.mp hz).2 (Finset.mem_sdiff.mp hu).2 zu se₃)
    (supporting_mem (Finset.mem_sdiff.mp hz).2 (Finset.mem_sdiff.mp hv).2 zv se₄)

theorem survivor_card (D : Finset V) : (Finset.univ \ D).card = 28 - D.card := by
  simp [Finset.card_sdiff_of_subset]

theorem deletion_excess (p : Drawing 28 ℝ) (gp : GeneralPosition p)
    (ep : ∀ k : Nat, k < 10 → counts p k = profile[k]!)
    (d : Nat) (hd : d ≤ 9) :
    (∑ D ∈ (Finset.univ : Finset V).powersetCard d, (hullEdges p D - 3)) =
      if d=9 then 2 else 0 := by
  have hsum := mass_of_profile p gp ep d hd
  have eq : (∑ D ∈ (Finset.univ : Finset V).powersetCard d, hullEdges p D) =
      ∑ D ∈ (Finset.univ : Finset V).powersetCard d, (3 + (hullEdges p D - 3)) := by
    apply Finset.sum_congr rfl
    intro D hD
    have hc := (Finset.mem_powersetCard.mp hD).2
    have h := three_hull_edges p gp D (by rw [survivor_card,hc]; omega)
    omega
  rw [eq,Finset.sum_add_distrib] at hsum
  simp only [Finset.sum_const,Finset.card_powersetCard,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_id] at hsum
  omega

theorem three_after_eight (p : Drawing 28 ℝ) (gp : GeneralPosition p)
    (ep : ∀ k : Nat, k < 10 → counts p k = profile[k]!)
    (D : Finset V) (small : D.card ≤ 8) : hullEdges p D = 3 := by
  have h := deletion_excess p gp ep D.card (by omega)
  rw [if_neg (by omega)] at h
  have mem : D ∈ (Finset.univ : Finset V).powersetCard D.card :=
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,rfl⟩
  have le := Finset.single_le_sum (f:= fun E => hullEdges p E - 3) (fun _ _ => Nat.zero_le _) mem
  have lower := three_hull_edges p gp D (by rw [survivor_card]; omega)
  have zero : hullEdges p D - 3 ≤ 0 := le.trans h.le
  omega

theorem at_most_two_ninth_exceptions (p : Drawing 28 ℝ) (gp : GeneralPosition p)
    (ep : ∀ k : Nat, k < 10 → counts p k = profile[k]!) :
    (((Finset.univ : Finset V).powersetCard 9).filter (fun D => 3 < hullEdges p D)).card ≤ 2 := by
  classical
  rw [←natBoole]
  have h := deletion_excess p gp ep 9 (by decide)
  rw [if_pos rfl] at h
  rw [← h]
  exact Finset.sum_le_sum fun D _ => by split_ifs <;> omega

end K28.Edges
