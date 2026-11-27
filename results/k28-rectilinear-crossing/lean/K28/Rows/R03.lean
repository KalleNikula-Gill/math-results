import K28.Rows.R02

namespace K28
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def cells : Array Nat := #[0, 0, 1]
private theorem c0 : pairCost 3 0 = cells[0]! := by decide +kernel
private theorem c1 : pairCost 3 1 = cells[1]! := by decide +kernel
private theorem c2 : pairCost 3 2 = cells[2]! := by decide +kernel
theorem row3 : lastCost 3 = rowTotals[3]! := by
  unfold lastCost
  calc
    _ = sumFin 3 (fun k => cells[k.val]!) := by
      apply congrArg (sumFin _)
      funext k
      change Fin 3 at k
      have h : k = 0 ∨ k = 1 ∨ k = 2 := by omega
      rcases h with h | h | h <;> subst k
      · exact c0
      · exact c1
      · exact c2
    _ = rowTotals[3]! := by decide +kernel
end K28
