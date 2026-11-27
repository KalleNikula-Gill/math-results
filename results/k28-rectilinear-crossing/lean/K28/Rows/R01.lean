import K28.Rows.R00

namespace K28
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def cells : Array Nat := #[0]
private theorem c0 : pairCost 1 0 = cells[0]! := by decide +kernel
theorem row1 : lastCost 1 = rowTotals[1]! := by
  unfold lastCost
  calc
    _ = sumFin 1 (fun k => cells[k.val]!) := by
      apply congrArg (sumFin _)
      funext k
      change Fin 1 at k
      have h : k = 0 := by omega
      subst k
      exact c0
    _ = rowTotals[1]! := by decide +kernel
end K28
