import K28.Rows.R23

namespace K28
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def cells : Array Nat := #[0, 0, 1, 3, 5, 9, 8, 7, 0, 1, 1, 4, 1, 2, 1, 7, 13, 27, 71, 80, 83, 98, 109, 119]
private theorem c0 : pairCost 24 0 = cells[0]! := by decide +kernel
private theorem c1 : pairCost 24 1 = cells[1]! := by decide +kernel
private theorem c2 : pairCost 24 2 = cells[2]! := by decide +kernel
private theorem c3 : pairCost 24 3 = cells[3]! := by decide +kernel
private theorem c4 : pairCost 24 4 = cells[4]! := by decide +kernel
private theorem c5 : pairCost 24 5 = cells[5]! := by decide +kernel
private theorem c6 : pairCost 24 6 = cells[6]! := by decide +kernel
private theorem c7 : pairCost 24 7 = cells[7]! := by decide +kernel
private theorem c8 : pairCost 24 8 = cells[8]! := by decide +kernel
private theorem c9 : pairCost 24 9 = cells[9]! := by decide +kernel
private theorem c10 : pairCost 24 10 = cells[10]! := by decide +kernel
private theorem c11 : pairCost 24 11 = cells[11]! := by decide +kernel
private theorem c12 : pairCost 24 12 = cells[12]! := by decide +kernel
private theorem c13 : pairCost 24 13 = cells[13]! := by decide +kernel
private theorem c14 : pairCost 24 14 = cells[14]! := by decide +kernel
private theorem c15 : pairCost 24 15 = cells[15]! := by decide +kernel
private theorem c16 : pairCost 24 16 = cells[16]! := by decide +kernel
private theorem c17 : pairCost 24 17 = cells[17]! := by decide +kernel
private theorem c18 : pairCost 24 18 = cells[18]! := by decide +kernel
private theorem c19 : pairCost 24 19 = cells[19]! := by decide +kernel
private theorem c20 : pairCost 24 20 = cells[20]! := by decide +kernel
private theorem c21 : pairCost 24 21 = cells[21]! := by decide +kernel
private theorem c22 : pairCost 24 22 = cells[22]! := by decide +kernel
private theorem c23 : pairCost 24 23 = cells[23]! := by decide +kernel
theorem row24 : lastCost 24 = rowTotals[24]! := by
  unfold lastCost
  calc
    _ = sumFin 24 (fun k => cells[k.val]!) := by
      apply congrArg (sumFin _)
      funext k
      change Fin 24 at k
      have h : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 ∨ k = 17 ∨ k = 18 ∨ k = 19 ∨ k = 20 ∨ k = 21 ∨ k = 22 ∨ k = 23 := by omega
      rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst k
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
    _ = rowTotals[24]! := by decide +kernel
end K28
