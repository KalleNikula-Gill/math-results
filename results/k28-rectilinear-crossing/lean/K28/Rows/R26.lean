import K28.Rows.R25

namespace K28
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def cells : Array Nat := #[0, 0, 1, 3, 5, 9, 8, 7, 0, 1, 1, 4, 1, 2, 1, 13, 12, 36, 68, 77, 89, 98, 99, 107, 121, 134]
private theorem c0 : pairCost 26 0 = cells[0]! := by decide +kernel
private theorem c1 : pairCost 26 1 = cells[1]! := by decide +kernel
private theorem c2 : pairCost 26 2 = cells[2]! := by decide +kernel
private theorem c3 : pairCost 26 3 = cells[3]! := by decide +kernel
private theorem c4 : pairCost 26 4 = cells[4]! := by decide +kernel
private theorem c5 : pairCost 26 5 = cells[5]! := by decide +kernel
private theorem c6 : pairCost 26 6 = cells[6]! := by decide +kernel
private theorem c7 : pairCost 26 7 = cells[7]! := by decide +kernel
private theorem c8 : pairCost 26 8 = cells[8]! := by decide +kernel
private theorem c9 : pairCost 26 9 = cells[9]! := by decide +kernel
private theorem c10 : pairCost 26 10 = cells[10]! := by decide +kernel
private theorem c11 : pairCost 26 11 = cells[11]! := by decide +kernel
private theorem c12 : pairCost 26 12 = cells[12]! := by decide +kernel
private theorem c13 : pairCost 26 13 = cells[13]! := by decide +kernel
private theorem c14 : pairCost 26 14 = cells[14]! := by decide +kernel
private theorem c15 : pairCost 26 15 = cells[15]! := by decide +kernel
private theorem c16 : pairCost 26 16 = cells[16]! := by decide +kernel
private theorem c17 : pairCost 26 17 = cells[17]! := by decide +kernel
private theorem c18 : pairCost 26 18 = cells[18]! := by decide +kernel
private theorem c19 : pairCost 26 19 = cells[19]! := by decide +kernel
private theorem c20 : pairCost 26 20 = cells[20]! := by decide +kernel
private theorem c21 : pairCost 26 21 = cells[21]! := by decide +kernel
private theorem c22 : pairCost 26 22 = cells[22]! := by decide +kernel
private theorem c23 : pairCost 26 23 = cells[23]! := by decide +kernel
private theorem c24 : pairCost 26 24 = cells[24]! := by decide +kernel
private theorem c25 : pairCost 26 25 = cells[25]! := by decide +kernel
theorem row26 : lastCost 26 = rowTotals[26]! := by
  unfold lastCost
  calc
    _ = sumFin 26 (fun k => cells[k.val]!) := by
      apply congrArg (sumFin _)
      funext k
      change Fin 26 at k
      have h : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 ∨ k = 17 ∨ k = 18 ∨ k = 19 ∨ k = 20 ∨ k = 21 ∨ k = 22 ∨ k = 23 ∨ k = 24 ∨ k = 25 := by omega
      rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst k
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
      · exact c25
    _ = rowTotals[26]! := by decide +kernel
end K28
