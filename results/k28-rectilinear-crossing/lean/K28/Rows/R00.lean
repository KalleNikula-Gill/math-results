import K28.GeneralPosition

namespace K28
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem row0 : lastCost 0 = rowTotals[0]! := by decide +kernel
end K28
