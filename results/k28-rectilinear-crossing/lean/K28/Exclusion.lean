import SweepCore.SweepPaths

namespace K28.Finite

set_option Elab.async false
set_option maxHeartbeats 0

/-- The three large closed computations in this module use Lean's native
evaluator. The graph and the state map are untrusted certificate data. -/
private theorem graphCasesChecked :
    (runAudit graph10 graph9 root10 root9).ok = true := by native_decide

private theorem cover10_checked : (coverage 10 graph10 index10).ok = true := by native_decide
private theorem cover9_checked : (coverage 9 graph9 index9).ok = true := by native_decide

private theorem root10_checked : imageId index10 (initial 10) = root10+1 := by native_decide
private theorem root9_checked : imageId index9 (initial 9) = root9+1 := by native_decide

theorem projected_paths_below_fifty (p : Traces)
    (ha : SweepPath (tabs 10) (terminal 10) (initial 10) (p 0))
    (hb : SweepPath (tabs 9) (terminal 9) (initial 9) (p 1))
    (hc : SweepPath (tabs 9) (terminal 9) (initial 9) (p 2))
    (compat : Compatible p) : score (p 0) + score (p 1) + score (p 2) < 50 := by
  have ca := (coverage 10 graph10 index10).sound cover10_checked
  have cb := (coverage 9 graph9 index9).sound cover9_checked
  obtain ⟨i,hi,pa⟩ := simulate ha ca
  obtain ⟨j,hj,pb⟩ := simulate hb cb
  obtain ⟨k,hk,pc⟩ := simulate hc cb
  rw [root10_checked] at hi
  rw [root9_checked] at hj hk
  have hi' : i = root10 := by omega
  have hj' : j = root9 := by omega
  have hk' : k = root9 := by omega
  subst i j k
  apply (runAudit graph10 graph9 root10 root9).sound graphCasesChecked p pa pb pc compat
  intro i t _
  simp [noBans]

#print axioms simulate
#print axioms projected_paths_below_fifty

end K28.Finite
