import K28.LowDelete
import K28.LowSector

namespace K28.Low
open K28.Edges

private theorem sector_disjoint (p : Drawing 28 ℝ) (T : Finset V) (g : Nat) (u v z : Vec) :
    Disjoint (sector p T g u v z) (sector p T g v z u) := by
  apply Finset.disjoint_left.mpr
  intro e he hf
  have a := (Finset.mem_filter.mp he).2.2.2.1
  have b := (Finset.mem_filter.mp hf).2.2.2.2.2
  exact a.asymm b

private theorem intersection_disjoint {T : Finset V} {f g h : V → ℝ}
    (gg : Set.InjOn g T) {k : Nat} (space : 2*k≤T.card) :
    Disjoint (frontSet T f k ∩ backSet T g k) (frontSet T g k ∩ backSet T h k) :=
  Finset.disjoint_left.mpr fun _ hi hj => Finset.disjoint_left.mp (ends_disjoint gg space)
    (Finset.mem_inter.mp hj).1 (Finset.mem_inter.mp hi).2

private theorem card_three {α : Type*} [DecidableEq α] {A B C : Finset α}
    (ab : Disjoint A B) (bc : Disjoint B C) (ca : Disjoint C A) :
    ((A∪B)∪C).card=A.card+B.card+C.card := by
  rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨ca.symm,bc⟩),
    Finset.card_union_of_disjoint ab]

namespace Triple
variable {p : Drawing 28 ℝ} {S : Finset V} (G : Triple p S)
noncomputable def extra (g : Nat) :=
    (sector p G.rest g G.u G.v G.z∪sector p G.rest g G.v G.z G.u)∪sector p G.rest g G.z G.u G.v
noncomputable def incident (w : Nat) := (star p S w G.a ∪ star p S w G.b) ∪ star p S w G.c

theorem extra_bound (gp : GeneralPosition p) (g : Nat) (room : 2*g≤G.rest.card) :
    3*g ≤ (G.extra g).card+G.rest.card := by
  classical
  let T:=G.rest
  let u:=fun i => cross G.u (p i)
  let v:=fun i => cross G.v (p i)
  let z:=fun i => cross G.z (p i)
  let A:=frontSet T u g∩backSet T v g
  let B:=frontSet T v g∩backSet T z g
  let C:=frontSet T z g∩backSet T u g
  have space : g≤T.card := by dsimp [T]; omega
  have x := sector_bound gp T G.first.generic G.second.generic G.uv G.vz G.zu g space
  have y := sector_bound gp T G.second.generic G.third.generic G.vz G.zu G.uv g space
  have z' := sector_bound gp T G.third.generic G.first.generic G.zu G.uv G.vz g space
  have ij : Disjoint A B := intersection_disjoint G.second.generic.injOn room
  have jk : Disjoint B C := intersection_disjoint G.third.generic.injOn room
  have ki : Disjoint C A := intersection_disjoint G.first.generic.injOn room
  have contain : (A∪B)∪C⊆T := by
    intro i h
    simp only [Finset.mem_union] at h
    rcases h with (h|h)|h <;> exact (Finset.mem_filter.mp (Finset.mem_inter.mp h).1).1
  have size := Finset.card_le_card contain
  rw [card_three ij jk ki] at size
  unfold extra
  rw [card_three (sector_disjoint ..) (sector_disjoint ..) (sector_disjoint ..)]
  change g≤(sector p G.rest g G.u G.v G.z).card+A.card at x
  change g≤(sector p G.rest g G.v G.z G.u).card+B.card at y
  change g≤(sector p G.rest g G.z G.u G.v).card+C.card at z'
  change A.card+B.card+C.card≤G.rest.card at size
  omega

theorem extra_info {g : Nat} {a b : V} (mem : (a,b)∈G.extra g) :
    a∈G.rest ∧ b∈G.rest ∧ a≠b ∧ side p G.rest (a,b)+1=g ∧ G.cost (normal p (a,b))=1 := by
  unfold extra at mem; simp only [Finset.mem_union] at mem
  rcases mem with (m|m)|m
  all_goals
    obtain ⟨ma,mb,ne,s,x,y,z⟩ := sector_mem.mp m
    exact ⟨ma,mb,ne,s,by simp only [cost,if_neg (not_lt_of_gt x),if_neg (not_lt_of_gt y),if_pos z]⟩

theorem incident_info {w : Nat} {e : Pair} (he : e∈G.incident w) :
    e∈lowSet p S w ∧ (e.1∈G.vertices ∨ e.2∈G.vertices) := by
  unfold incident at he; simp only [Finset.mem_union] at he
  rcases he with (h|h)|h
  all_goals
    obtain ⟨mem,l|r⟩ := Finset.mem_filter.mp h
    · exact ⟨mem,Or.inl (by simp [l,vertices])⟩
    · exact ⟨mem,Or.inr (by simp [r,vertices])⟩

theorem incident_count (gp : GeneralPosition p) (w : Nat) (room : 2*w<S.card) :
    6*w≤(G.incident w).card+3 :=
  three_stars gp G.first G.second G.third G.ab G.bc G.ac room

/-- The full recurrence step. Its three classes are edges incident to an
exposed point, surviving low edges, and surviving edges in the three sectors. -/
theorem recursion_step (gp : GeneralPosition p) (w : Nat) (room : 2*(w+2)+4≤S.card) :
    (lowSet p G.rest w).card+(6*(w+2)-3)+(3*(w+2)-S.card) ≤ (lowSet p S (w+2)).card := by
  classical
  let I:=G.incident (w+2)
  let B:=lowSet p G.rest w
  let C:=G.extra (w+1)
  have ib : Disjoint I B := by
    apply Finset.disjoint_left.mpr
    intro ⟨a,b⟩ hi mem
    have x:=G.incident_info hi
    obtain ⟨ma,mb,_,_⟩ := low_mem.mp mem
    exact x.2.elim (Finset.mem_sdiff.mp ma).2 (Finset.mem_sdiff.mp mb).2
  have ci : Disjoint C I := by
    apply Finset.disjoint_left.mpr
    intro ⟨a,b⟩ mem hi
    have x:=G.incident_info hi
    obtain ⟨ma,mb,_,_,_⟩ := G.extra_info mem
    exact x.2.elim (Finset.mem_sdiff.mp ma).2 (Finset.mem_sdiff.mp mb).2
  have bc : Disjoint B C := by
    apply Finset.disjoint_left.mpr
    intro ⟨a,b⟩ h j
    have low := (low_mem.mp h).2.2.2
    have high := (G.extra_info j).2.2.2.1
    omega
  have inside : (I∪B)∪C⊆lowSet p S (w+2) := by
    intro e mem
    rcases Finset.mem_union.mp mem with m|m
    · rcases Finset.mem_union.mp m with hi|hb
      · exact (G.incident_info hi).1
      · exact G.lift_base room hb
    · obtain ⟨a,b⟩ := e
      have ⟨ma,mb,ne,s,k⟩ := G.extra_info m
      have v := G.compare (a,b) (by omega)
      exact low_mem.mpr ⟨(Finset.mem_sdiff.mp ma).1,(Finset.mem_sdiff.mp mb).1,ne,by omega⟩
  have total := Finset.card_le_card inside
  rw [card_three ib bc ci] at total
  have many := G.incident_count gp (w+2) (by omega)
  have rem := G.rest_size
  have more := G.extra_bound gp (w+1) (by omega)
  dsimp only [I,B,C] at total
  omega

end Triple

def bound (n : Nat) (w : Nat) : Nat :=
  match w with
  | 0 => 0
  | 1 => 3
  | j+2 => bound (n-3) j+(6*(j+2)-3)+(3*(j+2)-n)
termination_by structural w

/-- A specialized range with enough room for the outward median rays.
The induction performs only the deletions required by the 28-point target. -/
theorem low_bound (p : Drawing 28 ℝ) (gp : GeneralPosition p) (w : Nat) (S : Finset V)
    (room : 2*w+4≤S.card) : bound S.card w≤(lowSet p S w).card := by
  match w with
  | 0 => simp [bound]
  | 1 =>
    obtain ⟨G⟩ := triple_exists gp (S:=S) (by omega)
    have inc := G.incident_count gp 1 (by omega)
    have sub : G.incident 1 ⊆ lowSet p S 1 := fun _ h => (G.incident_info h).1
    have cc := Finset.card_le_card sub
    rw [bound]; omega
  | j+2 =>
    obtain ⟨G⟩ := triple_exists gp (S:=S) (by omega)
    have rem := G.rest_size
    have ih := low_bound p gp j G.rest (by omega)
    have step := G.recursion_step gp j room
    rw [bound,←rem]; omega
termination_by w

end K28.Low
