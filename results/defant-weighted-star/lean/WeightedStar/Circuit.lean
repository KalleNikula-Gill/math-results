import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Order

namespace DefantCircuit

structure Ops (A : Type) where
  z : A
  u : A
  a : A → A → A
  m : A → A → A

def sum (o : Ops A) (values : List A) : A := values.foldr o.a o.z

def step (o : Ops A) (poly : Nat → A) (a m : Nat) (row : List A) : List A :=
  (List.range (row.length + m)).map fun j =>
    sum o ((List.range (min j m + 1)).map fun s =>
      o.m (row.getD (j-s) o.z) (poly (a-1+m-s)))

def star (o : Ops A) (poly : Nat → A) : A :=
  let row := (List.replicate 96 ()).foldl
    (fun l _ => step o poly 30 1 l)
    ((List.replicate 10 ()).foldl (fun l _ => step o poly 1 23 l) [o.u])
  sum o ((List.range row.length).map fun j => o.m (row.getD j o.z) (poly j))

structure Pres (f : A → B) (o : Ops A) (p : Ops B) : Prop where
  z : f o.z = p.z
  u : f o.u = p.u
  a : ∀ x y, f (o.a x y) = p.a (f x) (f y)
  m : ∀ x y, f (o.m x y) = p.m (f x) (f y)

theorem getD_map (f : A → B) (l : List A) (d : A) (i : Nat) :
    f (l.getD i d) = (l.map f).getD i (f d) := by
  induction l generalizing i with
  | nil => simp
  | cons h t ih => cases i <;> simp

variable {A B : Type} {f : A → B} {o : Ops A} {p : Ops B}

theorem sum_map (h : Pres f o p) (l : List A) :
    f (sum o l) = sum p (l.map f) := by
  induction l with
  | nil => exact h.z
  | cons x xs ih => simp only [sum, List.foldr_cons, List.map_cons] at ih ⊢; rw [h.a, ih]

theorem step_map (h : Pres f o p) (l : Nat → A) (a m : Nat) (row : List A) :
    (step o l a m row).map f = step p (fun d => f (l d)) a m (row.map f) := by
  simp only [step, List.length_map, List.map_map, Function.comp_def, sum_map h, h.m,
    getD_map, h.z]

theorem iterate_map (h : Pres f o p) (l : Nat → A) (a m : Nat) (seeds : List Unit)
    (r : List A) :
    (seeds.foldl (fun v _ => step o l a m v) r).map f =
    seeds.foldl (fun v _ => step p (fun d => f (l d)) a m v) (r.map f) := by
  induction seeds generalizing r with
  | nil => rfl
  | cons u us ih => simp only [List.foldl_cons, ih, step_map h]

theorem star_map (h : Pres f o p) (l : Nat → A) :
    f (star o l) = star p (fun d => f (l d)) := by
  let row := (List.replicate 96 ()).foldl
    (fun v _ => step o l 30 1 v)
    ((List.replicate 10 ()).foldl (fun v _ => step o l 1 23 v) [o.u])
  have eq : row.map f = (List.replicate 96 ()).foldl
    (fun v _ => step p (fun d => f (l d)) 30 1 v)
    ((List.replicate 10 ()).foldl (fun v _ => step p (fun d => f (l d)) 1 23 v) [p.u]) := by
    simp only [row, iterate_map h, List.map_cons, List.map_nil, h.u]
  unfold star
  change f (sum o ((List.range row.length).map _)) = _
  rw [sum_map h, ← eq]
  simp only [List.length_map, List.map_map, Function.comp_def, h.m, getD_map, h.z]; rfl

end DefantCircuit

namespace DefantCircuit

open Polynomial

structure Jet where
  v : Rat
  d : Rat
  dd : Rat
  deriving Inhabited

def jetOps : Ops Jet :=
  ⟨⟨0,0,0⟩, ⟨1,0,0⟩,
    fun a b => ⟨a.v+b.v,a.d+b.d,a.dd+b.dd⟩,
    fun a b => ⟨a.v*b.v,a.d*b.v+a.v*b.d,a.dd*b.v+2*a.d*b.d+a.v*b.dd⟩⟩

noncomputable def polyOps : Ops ℚ[X] := ⟨0, 1, (· + ·), (· * ·)⟩

def x0 : Rat := -1/258

noncomputable def jet (p : ℚ[X]) : Jet :=
  ⟨p.eval x0,p.derivative.eval x0,p.derivative.derivative.eval x0⟩

lemma jetPres : Pres jet polyOps jetOps := by
  constructor
  · simp [jet, polyOps, jetOps]
  · simp [jet, polyOps, jetOps]
  · intro a b
    simp [jet, polyOps, jetOps, derivative_add]
  · intro a b
    simp only [jet, polyOps, jetOps, derivative_mul, derivative_add, eval_add, eval_mul]
    congr 1; all_goals try ring

def choose (n k : Nat) : Nat := n.descFactorial k / k.factorial

theorem choose_spec (n k : Nat) : choose n k = n.choose k :=
  (Nat.choose_eq_descFactorial_div_factorial n k).symm

def narCoeff (h j : Nat) : Rat :=
  (choose (h+1) j : Rat) * (choose (h+1) (j+1) : Rat) / (h+1 : Nat)

noncomputable def nar (h : Nat) : ℚ[X] :=
  sum polyOps ((List.range (h+1)).map fun j => monomial j (narCoeff h j))

def monJet (j : Nat) (c : Rat) : Jet :=
  ⟨c*x0^j, c*(j : Rat)*x0^(j-1),
   c*(j : Rat)*((j-1 : Nat) : Rat)*x0^(j-2)⟩

lemma monJet_eq (j : Nat) (c : Rat) :
    jet (monomial j c) = monJet j c := by
  cases j with
  | zero => simp [jet, monJet]
  | succ k =>
    simp only [jet, monJet, derivative_monomial, eval_monomial, Nat.add_sub_cancel,
      Nat.cast_succ]
    congr 1

def narJet (h : Nat) : Jet :=
  sum jetOps ((List.range (h+1)).map fun j => monJet j (narCoeff h j))

lemma narJet_eq (h : Nat) : jet (nar h) = narJet h := by
  simp [nar, narJet, sum_map jetPres, List.map_map, Function.comp_def, monJet_eq]

def packed : Jet := star jetOps narJet

noncomputable def normalizedStar : ℚ[X] := star polyOps nar

theorem star_eval : jet normalizedStar = packed := by
  simp [normalizedStar, packed, star_map jetPres, narJet_eq]

def certificateBounds (s : Jet) : Prop :=
  let gap := x0^2 * (s.v * s.dd - s.d^2)
  s.v ≠ 0 ∧ 12223800 * s.v^2 < gap ∧ gap < 12223801 * s.v^2

instance (s : Jet) : Decidable (certificateBounds s) := by
  unfold certificateBounds
  infer_instance

def witnessCheck : Bool := decide (certificateBounds packed)

theorem bounds_of_decide (s : Jet) (h : decide (certificateBounds s) = true) :
    certificateBounds s := of_decide_eq_true h

end DefantCircuit
