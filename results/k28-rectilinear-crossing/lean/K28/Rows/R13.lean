import K28.Rows.R12

namespace K28
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def cells : Array Nat := #[0, 0, 0, 0, 1, 1, 7, 14, 21, 36, 36, 51, 65]
private theorem c0 : pairCost 13 0 = cells[0]! := by decide +kernel
private theorem c1 : pairCost 13 1 = cells[1]! := by decide +kernel
private theorem c2 : pairCost 13 2 = cells[2]! := by decide +kernel
private theorem c3 : pairCost 13 3 = cells[3]! := by decide +kernel
private theorem c4 : pairCost 13 4 = cells[4]! := by decide +kernel
private theorem c5 : pairCost 13 5 = cells[5]! := by decide +kernel
private theorem c6 : pairCost 13 6 = cells[6]! := by decide +kernel
private theorem c7 : pairCost 13 7 = cells[7]! := by decide +kernel
private theorem c8 : pairCost 13 8 = cells[8]! := by decide +kernel
private theorem c9 : pairCost 13 9 = cells[9]! := by decide +kernel
private theorem c10 : pairCost 13 10 = cells[10]! := by decide +kernel
private theorem c11 : pairCost 13 11 = cells[11]! := by decide +kernel
private theorem c12 : pairCost 13 12 = cells[12]! := by decide +kernel
theorem row13 : lastCost 13 = rowTotals[13]! := by
  unfold lastCost
  calc
    _ = sumFin 13 (fun k => cells[k.val]!) := by
      apply congrArg (sumFin _)
      funext k
      change Fin 13 at k
      have h : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 := by omega
      rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst k
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
    _ = rowTotals[13]! := by decide +kernel
end K28
