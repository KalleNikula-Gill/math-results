import K28.Rows.R10

namespace K28
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def cells : Array Nat := #[0, 0, 0, 0, 1, 1, 7, 10, 12, 33, 42]
private theorem c0 : pairCost 11 0 = cells[0]! := by decide +kernel
private theorem c1 : pairCost 11 1 = cells[1]! := by decide +kernel
private theorem c2 : pairCost 11 2 = cells[2]! := by decide +kernel
private theorem c3 : pairCost 11 3 = cells[3]! := by decide +kernel
private theorem c4 : pairCost 11 4 = cells[4]! := by decide +kernel
private theorem c5 : pairCost 11 5 = cells[5]! := by decide +kernel
private theorem c6 : pairCost 11 6 = cells[6]! := by decide +kernel
private theorem c7 : pairCost 11 7 = cells[7]! := by decide +kernel
private theorem c8 : pairCost 11 8 = cells[8]! := by decide +kernel
private theorem c9 : pairCost 11 9 = cells[9]! := by decide +kernel
private theorem c10 : pairCost 11 10 = cells[10]! := by decide +kernel
theorem row11 : lastCost 11 = rowTotals[11]! := by
  unfold lastCost
  calc
    _ = sumFin 11 (fun k => cells[k.val]!) := by
      apply congrArg (sumFin _)
      funext k
      change Fin 11 at k
      have h : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 := by omega
      rcases h with h | h | h | h | h | h | h | h | h | h | h <;> subst k
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
    _ = rowTotals[11]! := by decide +kernel
end K28
