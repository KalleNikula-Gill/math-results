import K28.Rows.R03

namespace K28
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def cells : Array Nat := #[0, 0, 0, 2]
private theorem c0 : pairCost 4 0 = cells[0]! := by decide +kernel
private theorem c1 : pairCost 4 1 = cells[1]! := by decide +kernel
private theorem c2 : pairCost 4 2 = cells[2]! := by decide +kernel
private theorem c3 : pairCost 4 3 = cells[3]! := by decide +kernel
theorem row4 : lastCost 4 = rowTotals[4]! := by
  unfold lastCost
  calc
    _ = sumFin 4 (fun k => cells[k.val]!) := by
      apply congrArg (sumFin _)
      funext k
      change Fin 4 at k
      have h : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
      rcases h with h | h | h | h <;> subst k
      · exact c0
      · exact c1
      · exact c2
      · exact c3
    _ = rowTotals[4]! := by decide +kernel
end K28
