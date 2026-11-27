import K28.Coordinates

namespace K28
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem cases28 {P : Fin 28 → Prop}
    (h0 : P 0)
    (h1 : P 1)
    (h2 : P 2)
    (h3 : P 3)
    (h4 : P 4)
    (h5 : P 5)
    (h6 : P 6)
    (h7 : P 7)
    (h8 : P 8)
    (h9 : P 9)
    (h10 : P 10)
    (h11 : P 11)
    (h12 : P 12)
    (h13 : P 13)
    (h14 : P 14)
    (h15 : P 15)
    (h16 : P 16)
    (h17 : P 17)
    (h18 : P 18)
    (h19 : P 19)
    (h20 : P 20)
    (h21 : P 21)
    (h22 : P 22)
    (h23 : P 23)
    (h24 : P 24)
    (h25 : P 25)
    (h26 : P 26)
    (h27 : P 27) : ∀ i, P i := by
  intro i
  have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 := by omega
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst i <;> assumption


def pairCost (l k : Fin 28) : Nat :=
  sumFin k.val fun j => sumFin j.val fun i =>
    threeMatchings intCost (witness ⟨i.val, by omega⟩) (witness ⟨j.val, by omega⟩) (witness k) (witness l)
def lastCost (l : Fin 28) : Nat := sumFin l.val fun k => pairCost l ⟨k.val, by omega⟩
def rowTotals : Array Nat := #[0, 0, 0, 1, 2, 6, 2, 8, 23, 44, 80, 106, 177, 232, 320, 345, 372, 350, 88, 160, 267, 328, 422, 537, 650, 767, 897, 1050]

end K28
