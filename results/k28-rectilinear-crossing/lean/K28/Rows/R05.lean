import K28.Rows.R04

namespace K28
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def cells : Array Nat := #[0, 0, 1, 3, 2]
private theorem c0 : pairCost 5 0 = cells[0]! := by decide +kernel
private theorem c1 : pairCost 5 1 = cells[1]! := by decide +kernel
private theorem c2 : pairCost 5 2 = cells[2]! := by decide +kernel
private theorem c3 : pairCost 5 3 = cells[3]! := by decide +kernel
private theorem c4 : pairCost 5 4 = cells[4]! := by decide +kernel
theorem row5 : lastCost 5 = rowTotals[5]! := by
  unfold lastCost
  calc
    _ = sumFin 5 (fun k => cells[k.val]!) := by
      apply congrArg (sumFin _)
      funext k
      change Fin 5 at k
      have h : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
      rcases h with h | h | h | h | h <;> subst k
      · exact c0
      · exact c1
      · exact c2
      · exact c3
      · exact c4
    _ = rowTotals[5]! := by decide +kernel
end K28
