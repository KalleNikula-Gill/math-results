import SweepCore.SweepPaths

namespace K28.Finite

/-- Ordinary projection state. Labels are zero based. The j-th prefix
count belongs to one-based gate 10+j. -/
structure PlainState where
  permutation : List Nat
  prefixes : List Nat
deriving DecidableEq, Inhabited, Repr

def plainStart (m : Nat) : PlainState := ⟨List.range m,List.replicate 9 m⟩
def plainEnd (m : Nat) : PlainState := ⟨(List.range m).reverse,List.replicate 9 0⟩

def validCounts (m : Nat) (u : List Nat) : Bool :=
  u.length == 9 && u.all (fun n => decide (n ≤ m)) &&
    (u.zip u.tail).all (fun (a,b) => decide (a ≤ b ∧ b ≤ a+1))

def bands : List Nat := [1,2,3,4]

/-- For each gate, list the maximizing restrictions applicable at that
gate, as the forbidden labels or forbidden pairs of labels. -/
structure PlainRules where
  exitsOK : Array (Array Bool)
  swapsOK : Array (Array (Array Bool))

def plainRules (m : Nat) : PlainRules :=
  let cuts := bands.map fun d => (d,K28.minimizingCuts m d)
  let gates := List.range' 10 9
  let labels := List.range m
  let exits := gates.map fun g => (labels.map fun a => cuts.all fun (d,ts) =>
    if 14-d ≤ g ∧ g ≤ 14+d then ts.all (fun t => decide (t≤a)) else true).toArray
  let swaps := gates.map fun g => (labels.map fun a => (labels.map fun b => decide (a<b) &&
    cuts.all fun (d,ts) => if 14-d ≤ g ∧ g ≤ 14+d then true else
      ts.all (fun t => decide (a<t ∧ t≤b))).toArray).toArray
  ⟨exits.toArray,swaps.toArray⟩

/-- The two move rules on ordinary lists of labels and prefix counts.
The reduced counts are tested against the full shape constraints. -/
def plainMoves (m : Nat) (rules : PlainRules) (s : PlainState) : List (PlainState × Nat) :=
  (List.range 9).flatMap fun j =>
    let r := s.prefixes[j]!
    if r=0 then [] else
    let a := s.permutation[r-1]!
    let counts := s.prefixes.set j (r-1)
    let outside := if validCounts m counts && rules.exitsOK[j]![a]! then
        [(⟨s.permutation,counts⟩,0)] else []
    let occupied := (j=0 || s.prefixes[j-1]!+1 == r) &&
      (j=8 || s.prefixes[j+1]! == r+1)
    let inside := if occupied && r<m then
      let b := s.permutation[r]!
      if rules.swapsOK[j]![a]![b]! then
        [(⟨(s.permutation.set (r-1) b).set r a,s.prefixes⟩,tag (10+j) r)] else []
      else []
    outside ++ inside

inductive PlainPath (m : Nat) : PlainState → List Nat → Prop
  | done : PlainPath m (plainEnd m) []
  | step {s t r ts} : (t,r) ∈ plainMoves m (plainRules m) s → PlainPath m t ts →
      PlainPath m s (r::ts)

def decode (m raw : Nat) : PlainState :=
  let bits := raw % orderBase
  let shape := raw / orderBase
  ⟨(List.range m).map (label bits),(List.range 9).map (prefixCount shape)⟩

/-- All ordinary moves must be images of actual packed successors. The
terminal check prevents accepting a packed state with hidden extra digits. -/
def localPlain (m : Nat) (rules : PlainRules) (dest : PlainState) (finalRaw : Nat) (raw : Nat)
    (es : List Nat) : Bool :=
  let s := decode m raw
  let actual := es.map fun e => (decode m (child e),record e)
  (!decide (s=dest) || raw==finalRaw) &&
    (plainMoves m rules s).all (fun step => actual.any (fun item => decide (item=step)))

theorem encode_path {m : Nat} {s : PlainState} {ts : List Nat} (p : PlainPath m s ts) :
    ∀ raw, decode m raw=s →
    Closed (successors (tabs m)) (localPlain m (plainRules m) (plainEnd m) (terminal m)) raw →
    SweepPath (tabs m) (terminal m) raw ts := by
  induction p with
  | done =>
    intro raw eq closed
    obtain ⟨localH,_⟩ := closed
    have one := (Bool.and_eq_true_iff.mp localH).1
    have done : raw=terminal m := by simpa [eq] using one
    subst raw; exact .done
  | @step s t r ts hmove _ ih =>
    intro raw eq closed
    obtain ⟨localH,children⟩ := closed
    have mem := List.all_eq_true.mp (Bool.and_eq_true_iff.mp localH).2 (t,r) (eq ▸ hmove)
    have existsEdge : (t,r) ∈ (successors (tabs m) raw).map
        (fun e => (decode m (child e),record e)) := by simpa using mem
    obtain ⟨e,he,h⟩ := List.mem_map.mp existsEdge
    have ht := congrArg Prod.fst h
    have hr := congrArg Prod.snd h
    change record e = r at hr
    subst r
    exact .step he (ih _ ht (children _ he))

def plainCoverage (m : Nat) :=
  let next := successors (tabs m)
  let test := localPlain m (plainRules m) (plainEnd m) (terminal m)
  (visit next test 150 (initial m)).run' ∅

end K28.Finite
