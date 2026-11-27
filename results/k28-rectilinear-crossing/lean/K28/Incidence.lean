import K28.Quartet
import K28Arithmetic

namespace K28.Edges

set_option maxHeartbeats 1600000

abbrev V := Fin 28
abbrev Pair := V × V
abbrev Key := V × V × V × V
def labels := List.finRange 28
def pairs : List Pair := labels.flatMap fun b =>
  (List.finRange b.val).map fun a => (⟨a.val,by omega⟩, b)
theorem pairs_nodup : pairs.Nodup := by
  unfold pairs
  apply List.nodup_flatMap.mpr
  constructor
  · intro b _
    apply (List.nodup_finRange b.val).map
    intro i j h
    exact Fin.ext (congrArg (fun e : Pair => e.1.val) h)
  · apply (List.nodup_finRange 28).imp
    intro b c ne e h k
    obtain ⟨a,_,ha⟩ := List.mem_map.mp h
    obtain ⟨d,_,hd⟩ := List.mem_map.mp k
    exact ne (congrArg Prod.snd (ha.trans hd.symm))

def quads : List Key := labels.flatMap fun l => (List.finRange l.val).flatMap fun k =>
  (List.finRange k.val).flatMap fun j => (List.finRange j.val).map fun i =>
    (⟨i.val,by omega⟩,⟨j.val,by omega⟩,⟨k.val,by omega⟩,l)

def ls {α : Type*} (xs : List α) (f : α → Nat) := (xs.map f).sum

private theorem cat {α : Type*} (s t : List α) (f : α → Nat) :
    ls (s++t) f = ls s f + ls t f := by simp [ls]
private theorem bind {α β : Type*} (s : List α) (f : α → List β) (v : β → Nat) :
    ls (s.flatMap f) v = ls s (fun x => ls (f x) v) := by
  induction s with
  | nil => rfl
  | cons a tail ih =>
    rw [List.flatMap_cons,cat,ih]
    rfl
private theorem mapped {α β : Type*} (s : List α) (f : α → β) (v : β → Nat) :
    ls (s.map f) v = ls s (fun x => v (f x)) := by simp [ls, List.map_map, Function.comp_def]
theorem congr_summands {α : Type*} {s : List α} {f h : α → Nat}
    (eq : ∀ x ∈ s, f x = h x) : ls s f = ls s h :=
  congrArg List.sum (List.map_congr_left eq)
private theorem add {α : Type*} (s : List α) (f h : α → Nat) :
    ls s (fun x => f x + h x) = ls s f + ls s h := by
  induction s with
  | nil => rfl
  | cons a t ih =>
    change f a+h a+ls t _ = f a+ls t f + (h a+ls t h)
    rw [ih]; omega
private theorem mulL {α : Type*} (s : List α) (w : Nat) (f : α → Nat) :
    ls s (fun x => w*f x) = w * ls s f := by
  induction s with
  | nil => simp [ls]
  | cons a t ih => change w*f a + ls t _ = w*(f a + ls t f); rw [ih,Nat.mul_add]
theorem mulR {α : Type*} (s : List α) (w : Nat) (f : α → Nat) :
    ls s (fun x => f x*w) = ls s f * w := by simpa only [Nat.mul_comm w] using mulL s w f
private theorem flip {α β : Type*} (s : List α) (t : List β) (f : α → β → Nat) :
    ls s (fun a => ls t (f a)) = ls t (fun b => ls s (fun a => f a b)) := by
  induction s with
  | nil => simp [ls]
  | cons a s ih =>
    change ls t (f a) + ls s _ = ls t (fun b => f a b + ls s (fun a => f a b))
    rw [add, ih]
private theorem constant {α : Type*} (s : List α) (k : Nat) : ls s (fun _ => k) = s.length*k := by
  induction s with
  | nil => simp [ls]
  | cons a s ih => change k+ls s _ = (s.length+1)*k; rw [ih,Nat.add_mul]; omega

def valid (t : Key) : Bool :=
  let (a,b,c,d) := t
  a != c && a != d && b != c && b != d && c != d

def allKeys := pairs.flatMap fun (a,b) => labels.flatMap fun c => labels.map fun d => (a,b,c,d)
def both (a b c d : V) : List Key := [(a,b,c,d),(a,b,d,c)]
def expand (q : Key) : List Key :=
  let (a,b,c,d) := q
  both a b c d ++ both c d a b ++ both a c b d ++ both b d a c ++ both a d b c ++ both b c a d

/-- This fixed-index permutation compares two enumerations, independently
of any coordinates or signs. -/
private def keyOrd (t : Key) : Nat := ((t.1.val*28+t.2.1.val)*28+t.2.2.1.val)*28+t.2.2.2.val
private def precedes (x y : Key) : Bool := keyOrd x ≤ keyOrd y

private theorem sorted_keys :
    ((allKeys.filter valid).mergeSort precedes) =
      ((quads.flatMap expand).mergeSort precedes) := by native_decide

private theorem perm_keys : (allKeys.filter valid).Perm (quads.flatMap expand) := by
  exact (List.mergeSort_perm _ precedes).symm.trans
    (sorted_keys ▸ (List.mergeSort_perm (quads.flatMap expand) precedes))

noncomputable def flag (h : Prop) : Nat := by classical exact if h then 1 else 0
noncomputable def plus (p : Drawing 28 ℝ) (a b c : V) := flag (0 < orient (p a) (p b) (p c))
noncomputable def minus (p : Drawing 28 ℝ) (a b c : V) := flag (orient (p a) (p b) (p c) < 0)
noncomputable def val (p : Drawing 28 ℝ) (t : Key) : Nat :=
  let (a,b,c,d) := t
  plus p a b c * minus p a b d

private theorem both_sep (p : Drawing 28 ℝ) (a b c d : V) :
    ls (both a b c d) (val p) = sep (p a) (p b) (p c) (p d) := by
  simp only [ls,both,List.map_cons,List.sum_cons,List.map_nil,List.sum_nil,Nat.add_zero,val,
    plus,minus,flag,sep,mul_neg_iff]
  split_ifs <;> first | rfl | omega | tauto | linarith

private theorem vanish (p : Drawing 28 ℝ) (t : Key) (h : valid t = false) : val p t = 0 := by
  obtain ⟨a,b,c,d⟩ := t
  have lft (x y : Point ℝ) : orient x y x = 0 := by simp [orient]
  have rgt (x y : Point ℝ) : orient x y y = 0 := by unfold orient; ring
  by_cases ac : a = c
  · subst c; simp [val,plus,flag,lft]
  by_cases ad : a = d
  · subst d; simp [val,minus,flag,lft]
  by_cases bc : b = c
  · subst c; simp [val,plus,flag,rgt]
  by_cases bd : b = d
  · subst d; simp [val,minus,flag,rgt]
  by_cases cd : c = d
  · subst d
    simp only [val,plus,minus,flag]
    split_ifs <;> first | rfl | linarith
  simp [valid,ac,ad,bc,bd,cd] at h

private theorem filter_zero {α : Type*} (s : List α) (q : α → Bool) (f : α → Nat)
    (zero : ∀ x, q x = false → f x = 0) : ls (s.filter q) f = ls s f := by
  induction s with
  | nil => rfl
  | cons a s ih => cases e : q a <;> simp_all [ls]

noncomputable def left (p : Drawing 28 ℝ) (e : Pair) := ls labels (plus p e.1 e.2)
noncomputable def right (p : Drawing 28 ℝ) (e : Pair) := ls labels (minus p e.1 e.2)
noncomputable def edgeType (p : Drawing 28 ℝ) (e : Pair) := min (left p e) (right p e)
noncomputable def counts (p : Drawing 28 ℝ) (k : Nat) :=
  ls pairs (fun e => if edgeType p e = k then 1 else 0)

private theorem all_lines (p : Drawing 28 ℝ) :
    ls allKeys (val p) = ls pairs (fun e => left p e * right p e) := by
  rw [allKeys, bind]
  apply congr_summands
  rintro ⟨a,b⟩ _
  rw [bind]
  change ls labels (fun c => ls (labels.map (fun d => (a,b,c,d))) (val p)) = _
  simp only [mapped, val, mulL, mulR, left, right]

private def inc (q : Key) := q.1 < q.2.1 ∧ q.2.1 < q.2.2.1 ∧ q.2.2.1 < q.2.2.2
private instance (q : Key) : Decidable (inc q) := by unfold inc; infer_instance
private theorem increasing : quads.all (fun q => decide (inc q)) = true := by native_decide
private theorem nquads : quads.length = 20475 := by native_decide
private theorem npairs : pairs.length = 378 := by decide +kernel

private noncomputable def quadCost (p : Drawing 28 ℝ) (q : Key) :=
  let (a,b,c,d) := q
  threeMatchings meetCost (p a) (p b) (p c) (p d)

private theorem fromQuads (p : Drawing 28 ℝ) : crossings p = ls quads (quadCost p) := by
  unfold quads
  simp only [bind,mapped]
  rfl

theorem incidence (p : Drawing 28 ℝ) (gp : GeneralPosition p) :
    crossings p + ls pairs (fun e => left p e * right p e) = 61425 := by
  rw [←all_lines, ←filter_zero allKeys valid _ (vanish p), fromQuads]
  have perm := perm_keys.map (val p)
  change ls quads (quadCost p) + (List.map (val p) (List.filter valid allKeys)).sum = _
  rw [perm.sum_eq]
  change ls quads (quadCost p) + ls (quads.flatMap expand) (val p) = _
  rw [bind, ←add]
  calc ls quads _ = ls quads (fun _ => 3) := by
        apply congr_summands
        rintro ⟨a,b,c,d⟩ h
        have hi : inc (a,b,c,d) := of_decide_eq_true (List.all_eq_true.mp increasing _ h)
        obtain ⟨ab,bc,cd⟩ := hi
        change a < b at ab
        change b < c at bc
        change c < d at cd
        have ac := ab.trans bc
        have bd := bc.trans cd
        have ad := ac.trans cd
        simp only [quadCost,expand,cat,both_sep]
        exact quartet_identity _ _ _ _ (gp.2 a b c ab.ne ac.ne bc.ne)
          (gp.2 a b d ab.ne ad.ne bd.ne) (gp.2 a c d ac.ne ad.ne cd.ne)
          (gp.2 b c d bc.ne bd.ne cd.ne)
       _ = 61425 := by rw [constant,nquads]

private def other (a b c : V) : Nat := if a ≠ c ∧ b ≠ c then 1 else 0
private def pairData (e : Pair) : Bool := decide (e.1 < e.2 ∧ ls labels (other e.1 e.2) = 26)
private theorem pairData_ok : pairs.all pairData = true := by native_decide

theorem sides (p : Drawing 28 ℝ) (gp : GeneralPosition p) (e : Pair) (he : e ∈ pairs) :
    left p e + right p e = 26 := by
  obtain ⟨a,b⟩ := e
  have good : a < b ∧ ls labels (other a b) = 26 :=
    of_decide_eq_true (List.all_eq_true.mp pairData_ok _ he)
  rw [←good.2, left,right,←add]
  apply congr_summands
  intro c _
  change plus p a b c + minus p a b c = other a b c
  by_cases ac : a = c
  · subst c; simp [plus,minus,flag,other,orient]
  by_cases bc : b = c
  · subst c
    have hz : orient (p a) (p b) (p b) = 0 := by unfold orient; ring
    simp [plus,minus,flag,other,hz]
  have nz := gp.2 a b c good.1.ne ac bc
  rcases lt_or_gt_of_ne nz with h | h <;> simp [plus,minus,flag,other,ac,bc,h,h.not_gt]

private theorem indicator (k : Nat) (t : Nat) :
    ls (List.range (k+1)) (fun j => if t = j then 1 else 0) = (if t ≤ k then 1 else 0) := by
  induction k with
  | zero =>
    by_cases h : t = 0 <;> simp [h,ls]
  | succ k ih =>
    rw [List.range_succ, cat, ih]
    change (if t ≤ k then 1 else 0) + ((if t = k+1 then 1 else 0) + 0) = _
    split_ifs <;> omega

theorem cumulative (p : Drawing 28 ℝ) (k : Nat) :
    E (counts p) k = ls pairs (fun e => if edgeType p e ≤ k then 1 else 0) := by
  change ls (List.range (k+1)) (fun j => ls pairs (fun e => if edgeType p e = j then 1 else 0)) = _
  rw [flip]
  apply congr_summands
  exact fun e _ => indicator k (edgeType p e)

private theorem type_le {p : Drawing 28 ℝ} (gp : GeneralPosition p) {e : Pair} (he : e ∈ pairs) :
    edgeType p e ≤ 13 := by
  have h := sides p gp e he
  unfold edgeType; omega

theorem edgeTotal (p : Drawing 28 ℝ) (gp : GeneralPosition p) : E (counts p) 13 = 378 := by
  rw [cumulative]
  calc ls pairs _ = ls pairs (fun _ => 1) := congr_summands (fun e h => if_pos (type_le gp h))
       _ = 378 := by rw [constant,npairs]

def contribution (j : Nat) : Nat :=
  ls (List.range 13) (fun k => (25-2*k) * (if j ≤ k then 1 else 0))

private theorem pair_coeff : ∀ i : Fin 27, contribution (min i.val (26-i.val)) + i.val*(26-i.val) = 169 := by
  decide +kernel

private theorem balance {a b c : Nat} (h : a+b=63882) (i : c+b=61425) : a=c+2457 := by omega

theorem weighted_identity (p : Drawing 28 ℝ) (gp : GeneralPosition p) :
    weighted (counts p) = crossings p + 2457 := by
  have weight : weighted (counts p) = ls pairs (fun e => contribution (edgeType p e)) := by
    change ls (List.range 13) (fun k => (25-2*k) * E (counts p) k) = _
    trans ls (List.range 13) (fun k => ls pairs (fun e => (25-2*k) * (if edgeType p e ≤ k then 1 else 0)))
    · apply congr_summands
      intro k _
      rw [cumulative]
      exact (mulL pairs _ _).symm
    · exact flip (List.range 13) pairs (fun k e => (25-2*k) * (if edgeType p e ≤ k then 1 else 0))
  have total : ls pairs (fun e => contribution (edgeType p e)) +
      ls pairs (fun e => left p e * right p e) = 63882 := by
    rw [←add]
    calc ls pairs _ = ls pairs (fun _ => 169) := by
          apply congr_summands
          intro e he
          have s := sides p gp e he
          have hr : right p e = 26-left p e := by omega
          change contribution (min (left p e) (right p e)) + left p e * right p e = 169
          rw [hr]
          exact pair_coeff ⟨left p e,by omega⟩
         _ = 63882 := by rw [constant,npairs]
  exact weight.trans (balance total (incidence p gp))

theorem drawing_profile (p : Drawing 28 ℝ) (gp : GeneralPosition p)
    (low : ∀ k : Nat, k < 12 → lower[k]! ≤ E (counts p) k)
    (central : counts p 13 ≤ counts p 12) (eq : crossings p = 7233) :
    ∀ k : Nat, k < 14 → counts p k = profile[k]! := by
  apply profile_of_7233 _ low (edgeTotal p gp) central
  rw [weighted_identity p gp,eq]

private theorem mono_sum {α : Type*} {l : List α} {f h : α → Nat}
    (bound : ∀ i ∈ l, f i ≤ h i) : ls l f ≤ ls l h := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    exact Nat.add_le_add (bound a List.mem_cons_self) (ih fun x hx => bound x (List.mem_cons_of_mem _ hx))

theorem drawing_lower (p : Drawing 28 ℝ) (gp : GeneralPosition p)
    (low : ∀ k : Nat, k < 12 → lower[k]! ≤ E (counts p) k)
    (central : counts p 13 ≤ counts p 12) : 7233 ≤ crossings p := by
  have all : ∀ k < 13, lower[k]! ≤ E (counts p) k := by
    intro k hk
    by_cases h : k < 12
    · exact low k h
    · have eq : k = 12 := by omega
      subst k
      exact central_lower _ (edgeTotal p gp) (low 11 (by decide)) central
  have baseline : ls (List.range 13) (fun k => (25-2*k)*lower[k]!) = 9690 := by decide +kernel
  have bound : 9690 ≤ weighted (counts p) := by
    rw [←baseline]
    exact mono_sum fun k hk => Nat.mul_le_mul_left _ (all k (List.mem_range.mp hk))
  rw [weighted_identity p gp] at bound
  omega

end K28.Edges
