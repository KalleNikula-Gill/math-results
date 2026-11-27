import K28.Rows.R05

namespace K28
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def cells : Array Nat := #[0, 0, 0, 0, 1, 1]
private theorem c0 : pairCost 6 0 = cells[0]! := by decide +kernel
private theorem c1 : pairCost 6 1 = cells[1]! := by decide +kernel
private theorem c2 : pairCost 6 2 = cells[2]! := by decide +kernel
private theorem c3 : pairCost 6 3 = cells[3]! := by decide +kernel
private theorem c4 : pairCost 6 4 = cells[4]! := by decide +kernel
private theorem c5 : pairCost 6 5 = cells[5]! := by decide +kernel
theorem row6 : lastCost 6 = rowTotals[6]! := by
  unfold lastCost
  calc
    _ = sumFin 6 (fun k => cells[k.val]!) := by
      apply congrArg (sumFin _)
      funext k
      change Fin 6 at k
      have h : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by omega
      rcases h with h | h | h | h | h | h <;> subst k
      · exact c0
      · exact c1
      · exact c2
      · exact c3
      · exact c4
      · exact c5
    _ = rowTotals[6]! := by decide +kernel
end K28
