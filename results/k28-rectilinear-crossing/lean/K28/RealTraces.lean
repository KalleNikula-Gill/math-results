import K28.RecordConflict
import K28.Saturation
import SweepCore.CaseAudit

namespace K28.Projection
open K28.Edges K28.Finite

set_option maxHeartbeats 1600000
attribute [local irreducible] pairs

structure GroupFrame (p : Drawing 28 ℝ) (X : Finset V) where
  q : Drawing 28 ℝ
  horizontal : Function.Injective (fun i => (q i).1)
  first : StartsFirst q Finset.univ X
  areas : ∀ i j k, orient (q i) (q j) (q k)=orient (p i) (p j) (p k)

theorem GroupFrame.gp {p : Drawing 28 ℝ} (gp : GeneralPosition p) {X : Finset V}
    (F : GroupFrame p X) : GeneralPosition F.q :=
  ⟨fun i j h => F.horizontal (congrArg Prod.fst h),fun i j k a b c => (F.areas i j k) ▸ gp.2 i j k a b c⟩

theorem exists_frame {p : Drawing 28 ℝ} (gp : GeneralPosition p) {X : Finset V}
    (sep : StrictlySeparated p X) (size : X.card=9 ∨ X.card=10) : Nonempty (GroupFrame p X) := by
  have nx : X.Nonempty := Finset.card_pos.mp (by omega)
  have outside : ∃ j : V, j∉X := by
    by_contra! all
    have h := Finset.eq_univ_of_forall all
    have count : X.card=28 := h ▸ rfl
    omega
  obtain ⟨q,ix,f,a⟩ := starting_frame gp sep nx outside
  exact ⟨⟨q,ix,fun i hi j _ hj => f i hi j hj,a⟩⟩

noncomputable def mark (q : Drawing 28 ℝ) (X : Finset V) (e : Pair) : Option Nat := by
  classical
  let g := gateAt q Finset.univ e
  exact if 10≤g ∧ g≤18 then
    if Inside X e then some (tag g (gateAt q X e)) else if Mixed X e then some 0 else none
    else none

noncomputable def realTrace (q : Drawing 28 ℝ) (X : Finset V) :=
  (schedule q Finset.univ).filterMap (mark q X)

theorem rank_bounds {q : Drawing 28 ℝ} (gp : GeneralPosition q) (ix : Function.Injective (fun i => (q i).1))
    {X : Finset V} {e : Pair} (he : e∈edgeSet X) : 0<gateAt q X e ∧ gateAt q X e<X.card := by
  obtain ⟨a,b,lt,_⟩ := normalized he
  have cap : (closedSide q X e).card≤X.card := Finset.card_le_card (Finset.filter_subset _ _)
  rw [closed_inside gp ix lt.ne a b] at cap
  change 0<(openSide q X e).card+1 ∧ (openSide q X e).card+1<X.card
  omega

theorem recorded_tag {q : Drawing 28 ℝ} (gp : GeneralPosition q) (ix : Function.Injective (fun i => (q i).1))
    {X : Finset V} (size : X.card≤10) {g r : Nat} (range : 10≤g ∧ g≤18) (rank : 0<r ∧ r<10)
    (used : tag g r∈realTrace q X) : physicalRecord q X g r := by
  classical
  obtain ⟨e,inL,m⟩ := List.mem_filterMap.mp used
  have edge := (schedule_mem q Finset.univ e).mp inL
  have shape := Finset.mem_filter.mp edge
  dsimp only [mark] at m
  split_ifs at m with ghere inner mixed
  · have ein : e∈edgeSet X := Finset.mem_filter.mpr ⟨shape.1,inner⟩
    have ⟨lo,hi⟩ := rank_bounds gp ix ein
    have eq := Option.some.inj m
    unfold tag at eq
    exact ⟨e,ein,by omega,by omega⟩
  · have eq := Option.some.inj m
    unfold tag at eq; omega
  all_goals contradiction

private def optionWeight (s : Option Nat) := match s with | none => 0 | some r => weight r

private theorem scored {α : Type*} (L : List α) (f : α → Option Nat) :
    score (L.filterMap f)=ls L (fun e => optionWeight (f e)) := by
  induction L with
  | nil => rfl
  | cons e tail ih => cases eq : f e <;> simp [eq,score,ls,optionWeight,List.filterMap_cons,score,ls] at ih ⊢ <;> omega

noncomputable def typeInside (p : Drawing 28 ℝ) (X : Finset V) (k : Nat) :=
  number (fun e => edgeType p e=k ∧ Inside X e)

theorem real_score {p : Drawing 28 ℝ} (gp : GeneralPosition p) {X : Finset V}
    (F : GroupFrame p X) (size : X.card≤10) : score (realTrace F.q X)=typeInside p X 13 := by
  classical
  have whole : (schedule F.q Finset.univ).toFinset=pairs.toFinset := by ext e; simp [schedule_mem,edgeSet]
  rw [realTrace,scored,ls_finset _ _ (schedule_nodup _ _),whole,typeInside,number_sum]
  apply Finset.sum_congr rfl
  intro e he
  have ⟨glo,ghi,ty⟩ := gate_center_view gp F.horizontal F.areas (List.mem_toFinset.mp he)
  have center : edgeType p e=13 ↔ gateAt F.q Finset.univ e=14 := by omega
  by_cases inX : Inside X e
  · have rb := rank_bounds (F.gp gp) F.horizontal (show e∈edgeSet X from Finset.mem_filter.mpr ⟨he,inX⟩)
    by_cases gc : gateAt F.q Finset.univ e=14
    · have rg : 10≤gateAt F.q Finset.univ e ∧ gateAt F.q Finset.univ e≤18 := by omega
      have wt : 41≤tag (gateAt F.q Finset.univ e) (gateAt F.q X e) ∧ tag (gateAt F.q Finset.univ e) (gateAt F.q X e)≤50 := by unfold tag; omega
      simp [mark,rg,inX,optionWeight,weight,wt,flag,center.mpr gc]
    · have wt : ¬(41≤tag (gateAt F.q Finset.univ e) (gateAt F.q X e) ∧ tag (gateAt F.q Finset.univ e) (gateAt F.q X e)≤50) := by unfold tag; omega
      by_cases rg : 10≤gateAt F.q Finset.univ e ∧ gateAt F.q Finset.univ e≤18 <;> simp [mark,rg,inX,optionWeight,weight,wt,flag,center,gc]
  · by_cases rg : 10≤gateAt F.q Finset.univ e ∧ gateAt F.q Finset.univ e≤18 <;>
      by_cases mix : Mixed X e <;> simp [mark,rg,inX,mix,optionWeight,weight,flag]

end K28.Projection
