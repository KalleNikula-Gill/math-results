import K28.Rows.R07

namespace K28
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def cells : Array Nat := #[0, 0, 0, 0, 1, 1, 7, 14]
private theorem c0 : pairCost 8 0 = cells[0]! := by decide +kernel
private theorem c1 : pairCost 8 1 = cells[1]! := by decide +kernel
private theorem c2 : pairCost 8 2 = cells[2]! := by decide +kernel
private theorem c3 : pairCost 8 3 = cells[3]! := by decide +kernel
private theorem c4 : pairCost 8 4 = cells[4]! := by decide +kernel
private theorem c5 : pairCost 8 5 = cells[5]! := by decide +kernel
private theorem c6 : pairCost 8 6 = cells[6]! := by decide +kernel
private theorem c7 : pairCost 8 7 = cells[7]! := by decide +kernel
theorem row8 : lastCost 8 = rowTotals[8]! := by
  unfold lastCost
  calc
    _ = sumFin 8 (fun k => cells[k.val]!) := by
      apply congrArg (sumFin _)
      funext k
      change Fin 8 at k
      have h : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega
      rcases h with h | h | h | h | h | h | h | h <;> subst k
      · exact c0
      · exact c1
      · exact c2
      · exact c3
      · exact c4
      · exact c5
      · exact c6
      · exact c7
    _ = rowTotals[8]! := by decide +kernel
end K28
