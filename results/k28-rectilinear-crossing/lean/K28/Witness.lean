import K28.Rows.R27

namespace K28
theorem witness_count : intCrossings witness = 7234 := by
  change sumFin 28 lastCost = 7234
  have eq : lastCost = (fun i : Fin 28 => rowTotals[i.val]!) := by
    funext i
    exact cases28 (P := fun i => lastCost i = rowTotals[i.val]!) row0 row1 row2 row3 row4 row5 row6 row7 row8 row9 row10 row11 row12 row13 row14 row15 row16 row17 row18 row19 row20 row21 row22 row23 row24 row25 row26 row27 i
  rw [eq]
  decide +kernel

theorem drawing_with_7234 : ∃ p : Drawing 28 ℝ, GeneralPosition p ∧ crossings p = 7234 :=
  ⟨toReal ∘ witness, generalPosition_toReal witness_gp, (crossings_toReal witness_gp).trans witness_count⟩

#print axioms witness_gp
#print axioms witness_count
#print axioms drawing_with_7234
end K28
