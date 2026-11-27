import Lean
import Std.Data.DHashMap

namespace K28.Finite

abbrev Graph := Array (List Nat)

/-- Encoded edges use 128 times the child index plus a record code.
Code zero denotes an outside swap. -/
def outgoing (g : Graph) (v : Nat) : List Nat := g[v]?.getD []
def child (e : Nat) := e / 128
def record (e : Nat) := e % 128
def weight (t : Nat) : Nat := if 41 ≤ t ∧ t ≤ 50 then 1 else 0
def score (ts : List Nat) : Nat := (ts.map weight).sum
def permits (b : Nat) (ts : List Nat) : Prop := ∀ t ∈ ts, b.testBit t = false

/-- Silent stuttering permits the certificate to contract a node with a
single unrecorded transition. -/
inductive GraphPath (g : Graph) : Nat → List Nat → Prop
  | done : GraphPath g 0 []
  | skip {v ts} : GraphPath g v ts → GraphPath g v (0 :: ts)
  | step {v e ts} : e ∈ outgoing g v → GraphPath g (child e) ts →
      GraphPath g v (record e :: ts)

def atScore (xs : Array Nat) (v : Nat) := xs[v]?.getD 0

/-- Zero is infeasible. A positive value is an upper bound on one plus the
score of any feasible continuation. -/
def arcBound (xs : Array Nat) (ban e : Nat) : Nat :=
  let v := atScore xs (child e)
  if ban.testBit (record e) || v == 0 then 0 else v + weight (record e)

def propose (g : Graph) (ban : Nat) : Array Nat := Id.run do
  let mut xs : Array Nat := Array.emptyWithCapacity g.size
  for es in g do
    let mut cap := if xs.size == 0 then 1 else 0
    for e in es do
      cap := max cap (arcBound xs ban e)
    xs := xs.push cap
  return xs

def validCaps (g : Graph) (ban : Nat) (xs : Array Nat) : Bool :=
  0 < atScore xs 0 && (List.range g.size).all fun v =>
    (outgoing g v).all fun e => decide (arcBound xs ban e ≤ atScore xs v)

theorem path_bound {g : Graph} {ban : Nat} {xs : Array Nat}
    (good : validCaps g ban xs = true) {v ts} (p : GraphPath g v ts)
    (safe : permits ban ts) : score ts + 1 ≤ atScore xs v := by
  obtain ⟨hEnd, hArcs⟩ := Bool.and_eq_true_iff.mp good
  have endOK : 0 < atScore xs 0 := of_decide_eq_true hEnd
  induction p with
  | done => simpa [score] using endOK
  | skip _ ih =>
    simpa [score, weight] using ih (fun t ht => safe t (List.mem_cons_of_mem _ ht))
  | @step v e ts edge _ ih =>
    have sub := ih (fun t ht => safe t (List.mem_cons_of_mem _ ht))
    have hs : v < g.size := by
      by_cases h : v < g.size
      · exact h
      · have hn : g[v]? = none := Array.getElem?_eq_none (by omega)
        simp [outgoing, hn] at edge
    have hv := List.all_eq_true.mp hArcs v (List.mem_range.mpr hs)
    have he : arcBound xs ban e ≤ atScore xs v :=
      of_decide_eq_true (List.all_eq_true.mp hv e edge)
    have hb := safe (record e) List.mem_cons_self
    have hn : atScore xs (child e) ≠ 0 := by omega
    simp [arcBound, hb, hn] at he
    simp only [score, List.map_cons, List.sum_cons] at sub ⊢
    omega

structure Bound (g : Graph) (root ban : Nat) where
  value : Nat
  sound : ∀ ts, GraphPath g root ts → permits ban ts → score ts + 1 ≤ value

def certify (g : Graph) (root ban : Nat) : Option (Bound g root ban) :=
  let xs := propose g ban
  if h : validCaps g ban xs = true then
    some ⟨atScore xs root, fun _ p safe => path_bound h p safe⟩
  else none

abbrev Bounds (g : Graph) (root : Nat) := Std.DHashMap Nat (Bound g root)

def makeBounds (g : Graph) (root : Nat) (queries : List Nat) : Bounds g root := Id.run do
  let mut tbl : Bounds g root := ∅
  for b in queries do
    if !tbl.contains b then
      if let some cap := certify g root b then tbl := tbl.insert b cap
  return tbl

#print axioms path_bound
end K28.Finite
