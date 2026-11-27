import K28.LowStar

namespace K28.Low
open K28.Edges

structure Triple (p : Drawing 28 ℝ) (S : Finset V) where
  a : V
  b : V
  c : V
  u : Vec
  v : Vec
  z : Vec
  first : Ray p S a u
  second : Ray p S b v
  third : Ray p S c z
  ab : a≠b
  bc : b≠c
  ac : a≠c
  uv : 0<cross u v
  vz : 0<cross v z
  zu : 0<cross z u

theorem triple_exists {p : Drawing 28 ℝ} (gp : GeneralPosition p) {S : Finset V} (ns : 5≤S.card) :
    Nonempty (Triple p S) := by
  obtain ⟨a,b,c,u,v,z,ha,hb,hc,ab,bc,ac,uv,vz,zu⟩ := three_rays gp ns
  exact ⟨⟨a,b,c,u,v,z,ha,hb,hc,ab,bc,ac,uv,vz,zu⟩⟩

namespace Triple
variable {p : Drawing 28 ℝ} {S : Finset V} (G : Triple p S)
def vertices : Finset V := {G.a,G.b,G.c}
def rest := S \ G.vertices
theorem three : G.vertices.card=3 := by simp [vertices,G.ab,G.bc,G.ac]
theorem subset : G.vertices⊆S := by
  intro i hi; simp only [vertices,Finset.mem_insert,Finset.mem_singleton] at hi
  rcases hi with rfl|rfl|rfl
  · exact G.first.mem
  · exact G.second.mem
  · exact G.third.mem
theorem rest_size : G.rest.card=S.card-3 := by rw [rest,Finset.card_sdiff_of_subset G.subset,G.three]
theorem reconstruct : insert G.a (insert G.b (insert G.c G.rest))=S := by
  ext i
  simp only [rest,vertices,Finset.mem_insert,Finset.mem_sdiff,Finset.mem_singleton]
  have ma:=G.first.mem; have mb:=G.second.mem; have mc:=G.third.mem
  by_cases a : i=G.a <;> by_cases b : i=G.b <;> by_cases c : i=G.c <;> simp_all

noncomputable def cost (G : Triple p S) (d : Vec) : Nat := by
  classical exact (if dot d G.u<0 then 1 else 0)+(if dot d G.v<0 then 1 else 0)+(if dot d G.z<0 then 1 else 0)
theorem cost_le (d : Vec) : G.cost d≤2 := by
  have relation : cross G.v G.z * dot d G.u + cross G.z G.u * dot d G.v +
      cross G.u G.v * dot d G.z=0 := by unfold cross dot; ring
  have h : ¬(dot d G.u<0 ∧ dot d G.v<0 ∧ dot d G.z<0) := by
    rintro ⟨a,b,c⟩
    linarith only [relation,mul_neg_of_pos_of_neg G.vz a,mul_neg_of_pos_of_neg G.zu b,
      mul_neg_of_pos_of_neg G.uv c]
  unfold cost
  split_ifs <;> first | decide | exact False.elim (h ⟨by assumption,by assumption,by assumption⟩)

private theorem ray_outside {i : V} {v : Vec} (ray : Ray p S i v) (inG : i∈G.vertices) {e : Pair}
    (small : side p G.rest e + 2 < (S.card-1)/2) (miss : 0≤dot (normal p e) v) :
    ¬orient (p e.1) (p e.2) (p i)<0 := by
  classical
  let d := normal p e
  intro below
  have safe := ray.safe d miss
  let B := G.rest.filter fun j => orient (p e.1) (p e.2) (p j)<0
  have sub : ((S.erase i).filter fun j => dot d (p j)≤dot d (p i)) ⊆ B∪(G.vertices.erase i) := by
    intro j mem
    obtain ⟨m,h⟩ := Finset.mem_filter.mp mem
    by_cases g : j∈G.vertices
    · exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨Finset.ne_of_mem_erase m,g⟩)
    · apply Finset.mem_union_left _
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_of_mem_erase m,g⟩,?_⟩
      rw [area_dot] at below ⊢
      change dot d (p i)-dot d (p e.1)<0 at below
      change dot d (p j)-dot d (p e.1)<0
      linarith only [below,h]
  have m := (Finset.card_le_card sub).trans (Finset.card_union_le _ _)
  rw [Finset.card_erase_of_mem inG,G.three] at m
  rw [Finset.card_erase_of_mem ray.mem] at safe
  change B.card + 2 < _ at small
  omega

private theorem add_point {X : Finset V} {i : V} (e : Pair) (hi : i∉X) :
    side p (insert i X) e = side p X e + if orient (p e.1) (p e.2) (p i)<0 then 1 else 0 := by
  classical
  by_cases small : orient (p e.1) (p e.2) (p i)<0 <;>
    simp [side,Finset.filter_insert,small,hi]

theorem compare (e : Pair) (small : side p G.rest e+2<(S.card-1)/2) :
    side p S e ≤ side p G.rest e + G.cost (normal p e) := by
  classical
  have inc {i : V} {v : Vec} (ray : Ray p S i v) (inG : i∈G.vertices) :
      (if orient (p e.1) (p e.2) (p i)<0 then 1 else 0 : Nat) ≤
      if dot (normal p e) v<0 then 1 else 0 := by
    by_cases he : dot (normal p e) v<0
    · simp [he]; split <;> decide
    · rw [if_neg he,if_neg (G.ray_outside ray inG small (le_of_not_gt he))]
  have a := inc G.first (by simp [vertices])
  have b := inc G.second (by simp [vertices])
  have c := inc G.third (by simp [vertices])
  let R := G.rest
  have na : G.a∉insert G.b (insert G.c R) := by simp [R,rest,vertices,G.ab,G.ac]
  have nb : G.b∉insert G.c R := by simp [R,rest,vertices,G.bc]
  have nc : G.c∉R := by simp [R,rest,vertices]
  calc side p S e = side p (insert G.a (insert G.b (insert G.c R))) e :=
         congrArg (fun X => side p X e) G.reconstruct.symm
       _ ≤ _ := by
         rw [add_point e na,add_point e nb,add_point e nc]
         unfold cost; dsimp only [R]; omega

theorem lift_base {w : Nat} (space : 2*w+4≤S.card) :
    lowSet p G.rest (w-2)⊆lowSet p S w := by
  intro e he
  obtain ⟨a,b⟩ := e
  obtain ⟨ma,mb,ne,h⟩ := low_mem.mp he
  have hc := G.compare (a,b) (by omega)
  have cc := G.cost_le (normal p (a,b))
  exact low_mem.mpr ⟨(Finset.mem_sdiff.mp ma).1,(Finset.mem_sdiff.mp mb).1,ne,by omega⟩

end Triple
end K28.Low
