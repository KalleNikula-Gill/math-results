import K28.Rows.R14

namespace K28
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def cells : Array Nat := #[0, 0, 0, 0, 1, 1, 7, 14, 21, 36, 45, 42, 45, 66, 67]
private theorem c0 : pairCost 15 0 = cells[0]! := by decide +kernel
private theorem c1 : pairCost 15 1 = cells[1]! := by decide +kernel
private theorem c2 : pairCost 15 2 = cells[2]! := by decide +kernel
private theorem c3 : pairCost 15 3 = cells[3]! := by decide +kernel
private theorem c4 : pairCost 15 4 = cells[4]! := by decide +kernel
private theorem c5 : pairCost 15 5 = cells[5]! := by decide +kernel
private theorem c6 : pairCost 15 6 = cells[6]! := by decide +kernel
private theorem c7 : pairCost 15 7 = cells[7]! := by decide +kernel
private theorem c8 : pairCost 15 8 = cells[8]! := by decide +kernel
private theorem c9 : pairCost 15 9 = cells[9]! := by decide +kernel
private theorem c10 : pairCost 15 10 = cells[10]! := by decide +kernel
private theorem c11 : pairCost 15 11 = cells[11]! := by decide +kernel
private theorem c12 : pairCost 15 12 = cells[12]! := by decide +kernel
private theorem c13 : pairCost 15 13 = cells[13]! := by decide +kernel
private theorem c14 : pairCost 15 14 = cells[14]! := by decide +kernel
theorem row15 : lastCost 15 = rowTotals[15]! := by
  unfold lastCost
  calc
    _ = sumFin 15 (fun k => cells[k.val]!) := by
      apply congrArg (sumFin _)
      funext k
      change Fin 15 at k
      have h : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 := by omega
      rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst k
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
    _ = rowTotals[15]! := by decide +kernel
end K28
