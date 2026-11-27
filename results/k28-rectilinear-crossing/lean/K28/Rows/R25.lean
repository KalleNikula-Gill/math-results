import K28.Rows.R24

namespace K28
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def cells : Array Nat := #[0, 0, 1, 3, 5, 9, 8, 7, 7, 0, 0, 3, 0, 1, 0, 6, 12, 26, 72, 81, 81, 96, 107, 115, 127]
private theorem c0 : pairCost 25 0 = cells[0]! := by decide +kernel
private theorem c1 : pairCost 25 1 = cells[1]! := by decide +kernel
private theorem c2 : pairCost 25 2 = cells[2]! := by decide +kernel
private theorem c3 : pairCost 25 3 = cells[3]! := by decide +kernel
private theorem c4 : pairCost 25 4 = cells[4]! := by decide +kernel
private theorem c5 : pairCost 25 5 = cells[5]! := by decide +kernel
private theorem c6 : pairCost 25 6 = cells[6]! := by decide +kernel
private theorem c7 : pairCost 25 7 = cells[7]! := by decide +kernel
private theorem c8 : pairCost 25 8 = cells[8]! := by decide +kernel
private theorem c9 : pairCost 25 9 = cells[9]! := by decide +kernel
private theorem c10 : pairCost 25 10 = cells[10]! := by decide +kernel
private theorem c11 : pairCost 25 11 = cells[11]! := by decide +kernel
private theorem c12 : pairCost 25 12 = cells[12]! := by decide +kernel
private theorem c13 : pairCost 25 13 = cells[13]! := by decide +kernel
private theorem c14 : pairCost 25 14 = cells[14]! := by decide +kernel
private theorem c15 : pairCost 25 15 = cells[15]! := by decide +kernel
private theorem c16 : pairCost 25 16 = cells[16]! := by decide +kernel
private theorem c17 : pairCost 25 17 = cells[17]! := by decide +kernel
private theorem c18 : pairCost 25 18 = cells[18]! := by decide +kernel
private theorem c19 : pairCost 25 19 = cells[19]! := by decide +kernel
private theorem c20 : pairCost 25 20 = cells[20]! := by decide +kernel
private theorem c21 : pairCost 25 21 = cells[21]! := by decide +kernel
private theorem c22 : pairCost 25 22 = cells[22]! := by decide +kernel
private theorem c23 : pairCost 25 23 = cells[23]! := by decide +kernel
private theorem c24 : pairCost 25 24 = cells[24]! := by decide +kernel
theorem row25 : lastCost 25 = rowTotals[25]! := by
  unfold lastCost
  calc
    _ = sumFin 25 (fun k => cells[k.val]!) := by
      apply congrArg (sumFin _)
      funext k
      change Fin 25 at k
      have h : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 ∨ k = 17 ∨ k = 18 ∨ k = 19 ∨ k = 20 ∨ k = 21 ∨ k = 22 ∨ k = 23 ∨ k = 24 := by omega
      rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst k
      · exact c0
      · exact c1
      · exact c2
      · exact c3
      · exact c4
      · exact c5
      · exact c6
      · exact c7
      · exact c8
      · exact c9
      · exact c10
      · exact c11
      · exact c12
      · exact c13
      · exact c14
      · exact c15
      · exact c16
      · exact c17
      · exact c18
      · exact c19
      · exact c20
      · exact c21
      · exact c22
      · exact c23
      · exact c24
    _ = rowTotals[25]! := by decide +kernel
end K28
