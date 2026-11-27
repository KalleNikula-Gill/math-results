import K28.Rows.R22

namespace K28
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def cells : Array Nat := #[0, 0, 1, 3, 5, 9, 8, 7, 7, 0, 0, 3, 0, 1, 0, 6, 12, 26, 72, 81, 83, 100, 113]
private theorem c0 : pairCost 23 0 = cells[0]! := by decide +kernel
private theorem c1 : pairCost 23 1 = cells[1]! := by decide +kernel
private theorem c2 : pairCost 23 2 = cells[2]! := by decide +kernel
private theorem c3 : pairCost 23 3 = cells[3]! := by decide +kernel
private theorem c4 : pairCost 23 4 = cells[4]! := by decide +kernel
private theorem c5 : pairCost 23 5 = cells[5]! := by decide +kernel
private theorem c6 : pairCost 23 6 = cells[6]! := by decide +kernel
private theorem c7 : pairCost 23 7 = cells[7]! := by decide +kernel
private theorem c8 : pairCost 23 8 = cells[8]! := by decide +kernel
private theorem c9 : pairCost 23 9 = cells[9]! := by decide +kernel
private theorem c10 : pairCost 23 10 = cells[10]! := by decide +kernel
private theorem c11 : pairCost 23 11 = cells[11]! := by decide +kernel
private theorem c12 : pairCost 23 12 = cells[12]! := by decide +kernel
private theorem c13 : pairCost 23 13 = cells[13]! := by decide +kernel
private theorem c14 : pairCost 23 14 = cells[14]! := by decide +kernel
private theorem c15 : pairCost 23 15 = cells[15]! := by decide +kernel
private theorem c16 : pairCost 23 16 = cells[16]! := by decide +kernel
private theorem c17 : pairCost 23 17 = cells[17]! := by decide +kernel
private theorem c18 : pairCost 23 18 = cells[18]! := by decide +kernel
private theorem c19 : pairCost 23 19 = cells[19]! := by decide +kernel
private theorem c20 : pairCost 23 20 = cells[20]! := by decide +kernel
private theorem c21 : pairCost 23 21 = cells[21]! := by decide +kernel
private theorem c22 : pairCost 23 22 = cells[22]! := by decide +kernel
theorem row23 : lastCost 23 = rowTotals[23]! := by
  unfold lastCost
  calc
    _ = sumFin 23 (fun k => cells[k.val]!) := by
      apply congrArg (sumFin _)
      funext k
      change Fin 23 at k
      have h : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 ∨ k = 17 ∨ k = 18 ∨ k = 19 ∨ k = 20 ∨ k = 21 ∨ k = 22 := by omega
      rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst k
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
    _ = rowTotals[23]! := by decide +kernel
end K28
