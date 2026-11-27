import SweepCore.CaseTree
import SweepCore.PathBounds

namespace K28.Finite

abbrev Group := Fin 3
abbrev Masks := Group → Nat
abbrev Traces := Group → List Nat

structure Conflict where
  x : Group
  tx : Nat
  y : Group
  ty : Nat
  gate : Nat
deriving Inhabited, Repr

def sizeOfGroup (i : Group) : Nat := if i = 0 then 10 else 9

/-- One plus the zero-based C++ tag. Zero is reserved for a silent edge. -/
def tag (g r : Nat) := (g - 10)*10 + r

def pairConflicts (x y : Group) : List Conflict :=
  (List.range' 10 9).flatMap fun g =>
    (List.range' 1 (sizeOfGroup x + sizeOfGroup y - g - 1)).map fun l =>
      ⟨x, tag g (g - sizeOfGroup y + l), y, tag (28-g) l, g⟩

def conflicts := pairConflicts 0 1 ++ pairConflicts 1 2 ++ pairConflicts 2 0

def Compatible (p : Traces) : Prop :=
  ∀ c ∈ conflicts, c.tx ∈ p c.x → c.ty ∉ p c.y

def Fits (b : Masks) (p : Traces) : Prop := ∀ i, permits (b i) (p i)

def forbid (b : Masks) (i : Group) (t : Nat) : Masks :=
  fun j => if j = i then b j ||| 2^t else b j

private theorem fits_forbid {b : Masks} {p : Traces} {i : Group} {t : Nat}
    (h : Fits b p) (absent : t ∉ p i) : Fits (forbid b i t) p := by
  intro j a ha
  by_cases eq : j = i
  · subst j
    have ne : t ≠ a := fun e => absent (e ▸ ha)
    simp [forbid, h i a ha, ne]
  · simpa [forbid, eq] using h j a ha

def startsTree : List (Nat × Nat) → Nat → CaseTree
  | [], owner => extraCases owner
  | (idx,bit)::cs, owner =>
    .split idx (startsTree cs owner) (startsTree cs (owner+bit))

def allCases : CaseTree :=
  let central := (conflicts.zipIdx.filter (fun q => q.1.gate == 14)).map Prod.snd
  startsTree (central.zipIdx.map fun (idx,i) => (idx,2^i)) 0

def leaves : CaseTree → Masks → List Masks
  | .leaf, b => [b]
  | .split k l r, b =>
    match conflicts[k]? with
    | none => []
    | some c => leaves l (forbid b c.x c.tx) ++ leaves r (forbid b c.y c.ty)

def Excludes (g h : Graph) (rg rh : Nat) (b : Masks) : Prop :=
  ∀ p : Traces, GraphPath g rg (p 0) → GraphPath h rh (p 1) → GraphPath h rh (p 2) →
    Compatible p → Fits b p → score (p 0) + score (p 1) + score (p 2) < 50

structure Checked (p : Prop) where
  ok : Bool
  sound : ok = true → p

def failed {p : Prop} : Checked p := ⟨false, by simp⟩

def join {p q r : Prop} (a : Checked p) (b : Checked q) (f : p → q → r) : Checked r :=
  ⟨a.ok && b.ok, fun h => f (a.sound (Bool.and_eq_true_iff.mp h).1) (b.sound (Bool.and_eq_true_iff.mp h).2)⟩

def audit {g h : Graph} {rg rh : Nat} (dbG : Bounds g rg) (dbH : Bounds h rh) :
    (q : CaseTree) → (b : Masks) → Checked (Excludes g h rg rh b)
  | .leaf, b =>
    match dbG.get? (b 0), dbH.get? (b 1), dbH.get? (b 2) with
    | some a, some c, some d =>
      if he : a.value = 0 ∨ c.value = 0 ∨ d.value = 0 ∨ a.value+c.value+d.value < 53 then
        ⟨true, by
          intro _ p pa pc pd _ safe
          have ha := a.sound _ pa (safe 0)
          have hc := c.sound _ pc (safe 1)
          have hd := d.sound _ pd (safe 2)
          omega⟩
      else failed
    | _, _, _ => failed
  | .split k l r, b =>
    match hk : conflicts[k]? with
    | none => failed
    | some c =>
      join (audit dbG dbH l (forbid b c.x c.tx)) (audit dbG dbH r (forbid b c.y c.ty)) (by
        intro hl hr p pa pc pd comp safe
        by_cases used : c.tx ∈ p c.x
        · have mem : c ∈ conflicts := List.mem_of_getElem? hk
          exact hr p pa pc pd comp (fits_forbid safe (comp c mem used))
        · exact hl p pa pc pd comp (fits_forbid safe used))

def noBans : Masks := fun _ => 0

def runAudit (g h : Graph) (rg rh : Nat) : Checked (Excludes g h rg rh noBans) :=
  let cases := allCases
  let bs := leaves cases noBans
  let dbG := makeBounds g rg (bs.map (· 0))
  let dbH := makeBounds h rh (bs.flatMap (fun b => [b 1,b 2]))
  audit dbG dbH cases noBans

def readGraph (text : String) : Graph :=
  ((text.splitOn "\n").dropLast.map fun line =>
    (line.splitOn " ").filterMap String.toNat?).toArray

def graph10 := readGraph (include_str "Certificates/graph10.txt")
def graph9 := readGraph (include_str "Certificates/graph9.txt")
def root10 := graph10.size - 1
def root9 := graph9.size - 1

#print axioms audit
end K28.Finite
