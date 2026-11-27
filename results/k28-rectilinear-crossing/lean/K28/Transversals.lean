import K28.Groups

namespace K28.Edges

private def lin (u v : ℝ) (a : Point ℝ) := u*a.1 + v*a.2
private theorem lin_interp (u v : ℝ) (a b : Point ℝ) (s : ℝ) :
    lin u v (interpolate a b s) = (1-s)*lin u v a+s*lin u v b := by
  unfold lin interpolate; dsimp; ring
private theorem mix_gt {v a b s : ℝ} (s0 : 0 ≤ s) (s1 : s ≤ 1) (aa : v<a) (bb : v<b) :
    v < (1-s)*a+s*b := by
  by_cases h : s=0
  · simpa [h] using aa
  · nlinarith only [mul_nonneg (sub_nonneg.mpr s1) (sub_nonneg.mpr aa.le),
                    mul_pos (s0.lt_of_ne (Ne.symm h)) (sub_pos.mpr bb)]
private theorem mix_lt {v a b s : ℝ} (s0 : 0 ≤ s) (s1 : s ≤ 1) (aa : a<v) (bb : b<v) :
    (1-s)*a+s*b < v := by
  have h := mix_gt s0 s1 (neg_lt_neg aa) (neg_lt_neg bb)
  linarith

private theorem collinear_param {b c z : Point ℝ} (ne : b ≠ c) (col : orient b c z=0) :
    ∃ t : ℝ, z=interpolate b c t := by
  by_cases dx : c.1=b.1
  · have dy : c.2≠b.2 := fun h => ne (Prod.ext dx.symm h.symm)
    refine ⟨(z.2-b.2)/(c.2-b.2),?_⟩
    apply Prod.ext
    · dsimp [interpolate]; rw [dx]; simp
      unfold orient at col
      rw [dx,sub_self,zero_mul,zero_sub] at col
      rcases mul_eq_zero.mp (neg_eq_zero.mp col) with h|h
      · exact False.elim ((sub_ne_zero.mpr dy) h)
      · exact sub_eq_zero.mp h
    · dsimp [interpolate]; field_simp [sub_ne_zero.mpr dy]; ring
  · refine ⟨(z.1-b.1)/(c.1-b.1),?_⟩
    apply Prod.ext <;> dsimp [interpolate] <;> field_simp [sub_ne_zero.mpr dx] <;> unfold orient at col <;>
      linarith only [col]

private theorem line_obstruction {a a' b c : Point ℝ} {s t : ℝ} (s0 : 0 ≤ s) (s1 : s ≤ 1)
    (eq : interpolate a a' s = interpolate b c t)
    (al : ∃ u v, lin u v b < lin u v a ∧ lin u v c < lin u v a ∧
                 lin u v b < lin u v a' ∧ lin u v c < lin u v a')
    (be : ∃ u v, lin u v a < lin u v b ∧ lin u v a' < lin u v b ∧ lin u v c < lin u v b)
    (ce : ∃ u v, lin u v a < lin u v c ∧ lin u v a' < lin u v c ∧ lin u v b < lin u v c) : False := by
  by_cases ht : t<0
  · obtain ⟨u,v,ha,ha',hc⟩ := be
    have h := mix_lt s0 s1 ha ha'
    have e := congrArg (lin u v) eq
    rw [lin_interp,lin_interp] at e
    nlinarith only [h,e,mul_pos_of_neg_of_neg ht (sub_neg.mpr hc)]
  by_cases th : 1<t
  · obtain ⟨u,v,ha,ha',hb⟩ := ce
    have h := mix_lt s0 s1 ha ha'
    have e := congrArg (lin u v) eq
    rw [lin_interp,lin_interp] at e
    nlinarith only [h,e,mul_pos_of_neg_of_neg (sub_neg.mpr th) (sub_neg.mpr hb)]
  obtain ⟨u,v,ab,ac,ab',ac'⟩ := al
  let z := lin u v (interpolate a a' s)
  have zb : lin u v b < z := by dsimp only [z]; rw [lin_interp]; exact mix_gt s0 s1 ab ab'
  have zc : lin u v c < z := by dsimp only [z]; rw [lin_interp]; exact mix_gt s0 s1 ac ac'
  have impossible := mix_lt (le_of_not_gt ht) (le_of_not_gt th) zb zc
  have e : z = (1-t)*lin u v b+t*lin u v c := by dsimp only [z]; rw [eq,lin_interp]
  linarith only [e,impossible]

/-- Changing the representative of one separated group preserves the
sign of the oriented area with fixed representatives of the other two. -/
theorem keep_sign {p : Drawing 28 ℝ} (gp : GeneralPosition p) {A B C : Finset V}
    (ab : Disjoint A B) (bc : Disjoint B C) (ca : Disjoint C A)
    (sa : StrictlySeparated p A) (sb : StrictlySeparated p B) (sc : StrictlySeparated p C)
    {i j k l : V} (hi : i ∈ A) (hj : j ∈ A) (hk : k ∈ B) (hl : l ∈ C) :
    0 < orient (p k) (p l) (p i) * orient (p k) (p l) (p j) := by
  let x := orient (p k) (p l) (p i)
  let y := orient (p k) (p l) (p j)
  have kl : k ≠ l := fun h => Finset.disjoint_left.mp bc hk (h ▸ hl)
  have nka : k ∉ A := fun h => Finset.disjoint_left.mp ab h hk
  have nla : l ∉ A := Finset.disjoint_left.mp ca hl
  have nib : i ∉ B := Finset.disjoint_left.mp ab hi
  have njb : j ∉ B := Finset.disjoint_left.mp ab hj
  have nlb : l ∉ B := fun h => Finset.disjoint_left.mp bc h hl
  have nic : i ∉ C := fun h => Finset.disjoint_left.mp ca h hi
  have njc : j ∉ C := fun h => Finset.disjoint_left.mp ca h hj
  have nkc : k ∉ C := Finset.disjoint_left.mp bc hk
  have nx : x ≠ 0 := gp.2 _ _ _ kl (fun h => nka (h ▸ hi)) (fun h => nla (h ▸ hi))
  have ny : y ≠ 0 := gp.2 _ _ _ kl (fun h => nka (h ▸ hj)) (fun h => nla (h ▸ hj))
  by_contra! bad
  have neg : x*y<0 := bad.lt_of_ne (mul_ne_zero nx ny)
  let s := x/(x-y)
  have hxy : x-y≠0 := by
    intro h; have h' := sub_eq_zero.mp h; rw [h'] at neg; exact (not_lt_of_ge (mul_self_nonneg _)) neg
  have inter : 0 ≤ s ∧ s ≤ 1 := by
    rcases mul_neg_iff.mp neg with ⟨px,ny'⟩|⟨nx',py⟩
    · have hd : 0 < x-y := by linarith
      exact ⟨div_nonneg px.le hd.le,(div_le_one hd).mpr (by linarith)⟩
    · have hd : x-y<0 := by linarith
      exact ⟨div_nonneg_of_nonpos nx'.le hd.le,(div_le_one_of_neg hd).mpr (by linarith)⟩
  have col : orient (p k) (p l) (interpolate (p i) (p j) s) = 0 := by
    calc _ = (1-s)*x+s*y := by unfold x y orient interpolate; dsimp; ring
         _ = 0 := by dsimp only [s]; field_simp [hxy]; ring
  obtain ⟨t,eq⟩ := collinear_param (gp.1.ne kl) col
  obtain ⟨ua,va,fa⟩ := sa
  obtain ⟨ub,vb,fb⟩ := sb
  obtain ⟨uc,vc,fc⟩ := sc
  exact line_obstruction inter.1 inter.2 eq
    ⟨ua,va,fa i hi k nka,fa i hi l nla,fa j hj k nka,fa j hj l nla⟩
    ⟨ub,vb,fb k hk i nib,fb k hk j njb,fb k hk l nlb⟩
    ⟨uc,vc,fc l hl i nic,fc l hl j njc,fc l hl k nkc⟩

private theorem same_positive_product {x y z : ℝ} (h : 0 < x*y) (i : 0 < y*z) : 0 < x*z := by
  rcases mul_pos_iff.mp h with h|h <;> rcases mul_pos_iff.mp i with i|i <;>
    first | exact mul_pos h.1 i.2 | exact mul_pos_of_neg_of_neg h.1 i.2 | linarith [h.2,i.1]

theorem transversal_sign {p : Drawing 28 ℝ} (gp : GeneralPosition p) (G : ThreeGroups p)
    {i j k i' j' k' : V} (hi : i ∈ G.A) (hj : j ∈ G.B) (hk : k ∈ G.C)
    (hi' : i' ∈ G.A) (hj' : j' ∈ G.B) (hk' : k' ∈ G.C) :
    0 < orient (p i) (p j) (p k)*orient (p i') (p j') (p k') := by
  have cyc (a b c : Point ℝ) : orient a b c = orient b c a := by unfold orient; ring
  have a := keep_sign gp G.disAB G.disBC G.disCA G.sepA G.sepB G.sepC hi hi' hj hk
  have b := keep_sign gp G.disBC G.disCA G.disAB G.sepB G.sepC G.sepA hj hj' hk hi'
  have c := keep_sign gp G.disCA G.disAB G.disBC G.sepC G.sepA G.sepB hk hk' hi' hj'
  rw [←cyc (p i) (p j) (p k),←cyc (p i') (p j) (p k)] at a
  rw [cyc (p k) (p i') (p j),cyc (p k) (p i') (p j')] at b
  exact same_positive_product (same_positive_product a b) c

theorem oriented_groups_of_7233 (p : Drawing 28 ℝ) (gp : GeneralPosition p)
    (low : ∀ k : Nat, k < 12 → lower[k]! ≤ E (counts p) k)
    (central : counts p 13 ≤ counts p 12) (eq : crossings p = 7233) :
    ∃ G : ThreeGroups p, ∀ i ∈ G.A, ∀ j ∈ G.B, ∀ k ∈ G.C, 0 < orient (p i) (p j) (p k) := by
  classical
  obtain ⟨G⟩ := groups_of_7233 p gp low central eq
  obtain ⟨i,hi⟩ := Finset.card_pos.mp (show 0<G.A.card by rw [G.sizeA]; decide)
  obtain ⟨j,hj⟩ := Finset.card_pos.mp (show 0<G.B.card by rw [G.sizeB]; decide)
  obtain ⟨k,hk⟩ := Finset.card_pos.mp (show 0<G.C.card by rw [G.sizeC]; decide)
  by_cases pos : 0 < orient (p i) (p j) (p k)
  · exact ⟨G,fun _ a _ b _ c => pos_of_mul_pos_right (transversal_sign gp G hi hj hk a b c) pos.le⟩
  · let swap : ThreeGroups p := ⟨G.A,G.C,G.B,G.sizeA,G.sizeC,G.sizeB,G.disCA.symm,G.disBC.symm,
        G.disAB.symm,by rw [Finset.union_right_comm,G.exhaust],G.sepA,G.sepC,G.sepB⟩
    refine ⟨swap,?_⟩
    intro a ha c hc b hb
    have prod := transversal_sign gp G hi hj hk ha hb hc
    have neg : orient (p a) (p b) (p c)<0 := by
      rcases mul_pos_iff.mp prod with hs|hs
      · exact False.elim (pos hs.1)
      · exact hs.2
    have rev : orient (p a) (p c) (p b) = -orient (p a) (p b) (p c) := by unfold orient; ring
    rw [rev]; exact neg_pos.mpr neg

end K28.Edges
