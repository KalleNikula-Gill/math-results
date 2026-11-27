import K28.Rows.R21

namespace K28
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def cells : Array Nat := #[0, 0, 1, 3, 5, 9, 8, 7, 7, 0, 0, 3, 0, 1, 0, 6, 12, 26, 72, 81, 82, 99]
private theorem c0 : pairCost 22 0 = cells[0]! := by decide +kernel
private theorem c1 : pairCost 22 1 = cells[1]! := by decide +kernel
private theorem c2 : pairCost 22 2 = cells[2]! := by decide +kernel
private theorem c3 : pairCost 22 3 = cells[3]! := by decide +kernel
private theorem c4 : pairCost 22 4 = cells[4]! := by decide +kernel
private theorem c5 : pairCost 22 5 = cells[5]! := by decide +kernel
private theorem c6 : pairCost 22 6 = cells[6]! := by decide +kernel
private theorem c7 : pairCost 22 7 = cells[7]! := by decide +kernel
private theorem c8 : pairCost 22 8 = cells[8]! := by decide +kernel
private theorem c9 : pairCost 22 9 = cells[9]! := by decide +kernel
private theorem c10 : pairCost 22 10 = cells[10]! := by decide +kernel
private theorem c11 : pairCost 22 11 = cells[11]! := by decide +kernel
private theorem c12 : pairCost 22 12 = cells[12]! := by decide +kernel
private theorem c13 : pairCost 22 13 = cells[13]! := by decide +kernel
private theorem c14 : pairCost 22 14 = cells[14]! := by decide +kernel
private theorem c15 : pairCost 22 15 = cells[15]! := by decide +kernel
private theorem c16 : pairCost 22 16 = cells[16]! := by decide +kernel
private theorem c17 : pairCost 22 17 = cells[17]! := by decide +kernel
private theorem c18 : pairCost 22 18 = cells[18]! := by decide +kernel
private theorem c19 : pairCost 22 19 = cells[19]! := by decide +kernel
private theorem c20 : pairCost 22 20 = cells[20]! := by decide +kernel
private theorem c21 : pairCost 22 21 = cells[21]! := by decide +kernel
theorem row22 : lastCost 22 = rowTotals[22]! := by
  unfold lastCost
  calc
    _ = sumFin 22 (fun k => cells[k.val]!) := by
      apply congrArg (sumFin _)
      funext k
      change Fin 22 at k
      have h : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 ∨ k = 17 ∨ k = 18 ∨ k = 19 ∨ k = 20 ∨ k = 21 := by omega
      rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst k
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
    _ = rowTotals[22]! := by decide +kernel
end K28
