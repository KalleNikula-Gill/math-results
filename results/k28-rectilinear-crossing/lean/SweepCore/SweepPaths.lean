import SweepCore.CaseAudit
import K28Arithmetic

namespace K28.Finite

/-- Nine prefix counts are encoded by their leftmost value (high bits) and
their eight successive differences (one bit each). Four bits encode each
label of the projected permutation, least significant label first. -/
def orderBase : Nat := 2^40
def pack (shape order : Nat) := shape * orderBase + order
def label (key pos : Nat) := (key >>> (4*pos)) &&& 15

def initial (m : Nat) : Nat :=
  pack (256*m) (((List.range m).map fun i => i <<< (4*i)).sum)
def terminal (m : Nat) : Nat := ((List.range m).map fun i => (m-1-i) <<< (4*i)).sum

def prefixCount (shape j : Nat) := shape/256 + ((List.range j).filter shape.testBit).length

structure Move where
  gate : Nat
  rank : Nat
  outside : Bool
  newShape : Nat
deriving Inhabited

def shapeMoves (m code : Nat) : List Move :=
  (List.range 9).flatMap fun j =>
    let r := prefixCount code j
    let g := 10+j
    if r = 0 || (j != 0 && prefixCount code (j-1) == r) then [] else
    let drop := if j = 8 || prefixCount code (j+1) == r then
        let code' := (if j=0 then code-256 else code-2^(j-1)) + (if j<8 then 2^j else 0)
        [⟨g,r,true,code'⟩] else []
    let inside := if r<m && (j = 8 || r < prefixCount code (j+1)) then
        [⟨g,r,false,code⟩] else []
    inside ++ drop

def distance (g : Nat) := (g-14)+(14-g)
def admissibleOutside (m g a : Nat) : Bool :=
  ([1,2,3,4] : List Nat).all fun d => decide (d < distance g) ||
    (K28.minimizingCuts m d).all fun t => decide (t ≤ a)
def admissibleInside (m g a b : Nat) : Bool :=
  decide (a < b) && ([1,2,3,4] : List Nat).all fun d => decide (distance g ≤ d) ||
    (K28.minimizingCuts m d).all fun t => (decide (a < t) != decide (b < t))

structure Tables where
  shapes : Array (List Move)
  outside : Array Bool
  inside : Array Bool

def tabs (m : Nat) : Tables :=
  ⟨((List.range ((m+1)*256)).map (shapeMoves m)).toArray,
    ((List.range 90).map fun i => admissibleOutside m (10+i/10) (i%10)).toArray,
    ((List.range 900).map fun i => admissibleInside m (10+i/100) ((i/10)%10) (i%10)).toArray⟩

/-- Each outgoing edge encodes 128 times the successor state plus its record. -/
def successors (T : Tables) (s : Nat) : List Nat :=
  let shape := s / orderBase
  let order := s % orderBase
  (T.shapes[shape]?.getD []).filterMap fun move =>
    let k := move.rank-1
    let a := label order k
    let i := (move.gate-10)*10+a
    if move.outside then
      if T.outside[i]?.getD false then some (128*pack move.newShape order) else none
    else
      let b := label order move.rank
      if T.inside[i*10+b]?.getD false then
        let bits := a ^^^ b
        let s' := (s ^^^ (bits <<< (4*k))) ^^^ (bits <<< (4*move.rank))
        some (128*s' + tag move.gate move.rank)
      else none

/-- A path is accepted only by ending in the reversed order with nine zero
prefix counts. Every other constructor makes an explicitly generated move. -/
inductive SweepPath (T : Tables) (endState : Nat) : Nat → List Nat → Prop
  | done : SweepPath T endState endState []
  | step {s e ts} : e ∈ successors T s → SweepPath T endState (child e) ts →
      SweepPath T endState s (record e :: ts)

abbrev Index := Std.HashMap Nat Nat

def readIndex (text : String) : Index := Id.run do
  let mut ids : Index := ∅
  for row in text.splitOn "\n" do
    match row.splitOn " " with
    | [key, val] => ids := ids.insert (key.toNat?.getD 0) (val.toNat?.getD 0)
    | _ => pure ()
  return ids

def index10 := readIndex (include_str "Certificates/states10.txt")
def index9 := readIndex (include_str "Certificates/states9.txt")
def imageId (ids : Index) (s : Nat) : Nat := ids.getD s 0

/-- A zero image may only have successors with zero image. Positive images
must simulate every edge that leads to a positive image. -/
def representsEdge (g : Graph) (u v t : Nat) : Bool :=
  v == 0 || (u != 0 && ((u == v && t == 0) ||
    (outgoing g (u-1)).contains ((v-1)*128+t)))

def localOK (g : Graph) (ids : Index) (endState s : Nat) (es : List Nat) : Bool :=
  let u := imageId ids s
  (s != endState || u == 1) &&
    es.all fun e => representsEdge g u (imageId ids (child e)) (record e)

inductive Closed (next : Nat → List Nat) (test : Nat → List Nat → Bool) : Nat → Prop
  | intro {s} : test s (next s) = true →
      (∀ e ∈ next s, Closed next test (child e)) → Closed next test s

private def collect {M : Type → Type} [Monad M] {p : Nat → Prop}
    (visit : (e : Nat) → M (Checked (p e))) :
    (es : List Nat) → M (Checked (∀ e ∈ es, p e))
  | [] => pure ⟨true, by simp⟩
  | e::es => do
    let a ← visit e
    if !a.ok then return failed
    let b ← collect visit es
    return join a b (by
      intro h hs k hk
      rcases List.mem_cons.mp hk with eq | mem
      · exact eq ▸ h
      · exact hs _ mem)

abbrev ClosedCache (next : Nat → List Nat) (test : Nat → List Nat → Bool) :=
  Std.DHashMap Nat (fun s => Checked (Closed next test s))

def visit (next : Nat → List Nat) (test : Nat → List Nat → Bool) :
    Nat → (s : Nat) → StateM (ClosedCache next test) (Checked (Closed next test s))
  | 0, _ => pure failed
  | fuel+1, s => do
    if let some prev := (← get).get? s then return prev
    let es := next s
    if h : test s es = true then
      let cs ← collect (fun e => visit next test fuel (child e)) es
      let res : Checked (Closed next test s) := ⟨cs.ok, fun ok => .intro h (cs.sound ok)⟩
      modify (·.insert s res)
      return res
    else return failed

theorem simulate {T : Tables} {endState : Nat} {g : Graph} {ids : Index} {s ts}
    (p : SweepPath T endState s ts)
    (closed : Closed (successors T) (localOK g ids endState) s) :
    ∃ v, imageId ids s = v+1 ∧ GraphPath g v ts := by
  induction p with
  | done =>
    obtain ⟨ok,_⟩ := closed
    have h := (Bool.and_eq_true_iff.mp ok).1
    exact ⟨0, by simpa using h, .done⟩
  | @step s e ts mem _ ih =>
    obtain ⟨ok,sub⟩ := closed
    obtain ⟨v,hv,path⟩ := ih (sub e mem)
    have eh := List.all_eq_true.mp (Bool.and_eq_true_iff.mp ok).2 e mem
    change representsEdge g (imageId ids s) (imageId ids (child e)) (record e) = true at eh
    rw [hv] at eh
    have hh' : imageId ids s ≠ 0 ∧
        ((imageId ids s = v+1 ∧ record e = 0) ∨
         (v*128 + record e) ∈ outgoing g (imageId ids s - 1)) := by
      simpa [representsEdge] using eh
    obtain ⟨nonzero, hh⟩ := hh'
    refine ⟨imageId ids s - 1, by omega, ?_⟩
    rcases hh with ⟨eq,zero⟩ | edge
    · rw [eq, zero]
      exact .skip path
    · have small : record e < 128 := Nat.mod_lt _ (by decide)
      have keyChild : child (v*128+record e) = v := by unfold child; omega
      have keyTag : record (v*128+record e) = record e := by unfold record at *; omega
      rw [← keyTag]
      apply GraphPath.step edge
      rwa [keyChild]

def coverage (m : Nat) (g : Graph) (ids : Index) :=
  ((visit (successors (tabs m)) (localOK g ids (terminal m)) 140 (initial m)).run ∅).1

end K28.Finite
