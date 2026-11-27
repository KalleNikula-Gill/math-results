import K28.Rows.R06

namespace K28
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def cells : Array Nat := #[0, 0, 0, 0, 1, 1, 6]
private theorem c0 : pairCost 7 0 = cells[0]! := by decide +kernel
private theorem c1 : pairCost 7 1 = cells[1]! := by decide +kernel
private theorem c2 : pairCost 7 2 = cells[2]! := by decide +kernel
private theorem c3 : pairCost 7 3 = cells[3]! := by decide +kernel
private theorem c4 : pairCost 7 4 = cells[4]! := by decide +kernel
private theorem c5 : pairCost 7 5 = cells[5]! := by decide +kernel
private theorem c6 : pairCost 7 6 = cells[6]! := by decide +kernel
theorem row7 : lastCost 7 = rowTotals[7]! := by
  unfold lastCost
  calc
    _ = sumFin 7 (fun k => cells[k.val]!) := by
      apply congrArg (sumFin _)
      funext k
      change Fin 7 at k
      have h : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega
      rcases h with h | h | h | h | h | h | h <;> subst k
      · exact c0
      · exact c1
      · exact c2
      · exact c3
      · exact c4
      · exact c5
      · exact c6
    _ = rowTotals[7]! := by decide +kernel
end K28
