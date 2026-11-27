import K28.Rows.R08

namespace K28
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def cells : Array Nat := #[0, 0, 0, 0, 1, 1, 7, 14, 21]
private theorem c0 : pairCost 9 0 = cells[0]! := by decide +kernel
private theorem c1 : pairCost 9 1 = cells[1]! := by decide +kernel
private theorem c2 : pairCost 9 2 = cells[2]! := by decide +kernel
private theorem c3 : pairCost 9 3 = cells[3]! := by decide +kernel
private theorem c4 : pairCost 9 4 = cells[4]! := by decide +kernel
private theorem c5 : pairCost 9 5 = cells[5]! := by decide +kernel
private theorem c6 : pairCost 9 6 = cells[6]! := by decide +kernel
private theorem c7 : pairCost 9 7 = cells[7]! := by decide +kernel
private theorem c8 : pairCost 9 8 = cells[8]! := by decide +kernel
theorem row9 : lastCost 9 = rowTotals[9]! := by
  unfold lastCost
  calc
    _ = sumFin 9 (fun k => cells[k.val]!) := by
      apply congrArg (sumFin _)
      funext k
      change Fin 9 at k
      have h : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 := by omega
      rcases h with h | h | h | h | h | h | h | h | h <;> subst k
      · exact c0
      · exact c1
      · exact c2
      · exact c3
      · exact c4
      · exact c5
      · exact c6
      · exact c7
      · exact c8
    _ = rowTotals[9]! := by decide +kernel
end K28
