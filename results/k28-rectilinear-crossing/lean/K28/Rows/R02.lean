import K28.Rows.R01

namespace K28
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def cells : Array Nat := #[0, 0]
private theorem c0 : pairCost 2 0 = cells[0]! := by decide +kernel
private theorem c1 : pairCost 2 1 = cells[1]! := by decide +kernel
theorem row2 : lastCost 2 = rowTotals[2]! := by
  unfold lastCost
  calc
    _ = sumFin 2 (fun k => cells[k.val]!) := by
      apply congrArg (sumFin _)
      funext k
      change Fin 2 at k
      have h : k = 0 ∨ k = 1 := by omega
      rcases h with h | h <;> subst k
      · exact c0
      · exact c1
    _ = rowTotals[2]! := by decide +kernel
end K28
