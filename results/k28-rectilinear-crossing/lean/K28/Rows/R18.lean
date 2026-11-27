import K28.Rows.R17

namespace K28
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def cells : Array Nat := #[0, 0, 1, 3, 5, 9, 8, 7, 7, 0, 0, 3, 0, 1, 0, 6, 12, 26]
private theorem c0 : pairCost 18 0 = cells[0]! := by decide +kernel
private theorem c1 : pairCost 18 1 = cells[1]! := by decide +kernel
private theorem c2 : pairCost 18 2 = cells[2]! := by decide +kernel
private theorem c3 : pairCost 18 3 = cells[3]! := by decide +kernel
private theorem c4 : pairCost 18 4 = cells[4]! := by decide +kernel
private theorem c5 : pairCost 18 5 = cells[5]! := by decide +kernel
private theorem c6 : pairCost 18 6 = cells[6]! := by decide +kernel
private theorem c7 : pairCost 18 7 = cells[7]! := by decide +kernel
private theorem c8 : pairCost 18 8 = cells[8]! := by decide +kernel
private theorem c9 : pairCost 18 9 = cells[9]! := by decide +kernel
private theorem c10 : pairCost 18 10 = cells[10]! := by decide +kernel
private theorem c11 : pairCost 18 11 = cells[11]! := by decide +kernel
private theorem c12 : pairCost 18 12 = cells[12]! := by decide +kernel
private theorem c13 : pairCost 18 13 = cells[13]! := by decide +kernel
private theorem c14 : pairCost 18 14 = cells[14]! := by decide +kernel
private theorem c15 : pairCost 18 15 = cells[15]! := by decide +kernel
private theorem c16 : pairCost 18 16 = cells[16]! := by decide +kernel
private theorem c17 : pairCost 18 17 = cells[17]! := by decide +kernel
theorem row18 : lastCost 18 = rowTotals[18]! := by
  unfold lastCost
  calc
    _ = sumFin 18 (fun k => cells[k.val]!) := by
      apply congrArg (sumFin _)
      funext k
      change Fin 18 at k
      have h : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 ∨ k = 17 := by omega
      rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst k
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
    _ = rowTotals[18]! := by decide +kernel
end K28
