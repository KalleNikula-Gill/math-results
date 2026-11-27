import K28.CertificateBase

namespace K28
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def gpRow (i : Fin 28) : Prop :=
  ∀ j k, i ≠ j → i ≠ k → j ≠ k → orient (witness i) (witness j) (witness k) ≠ 0

private theorem gp0 : gpRow 0 := by unfold gpRow; decide +kernel
private theorem gp1 : gpRow 1 := by unfold gpRow; decide +kernel
private theorem gp2 : gpRow 2 := by unfold gpRow; decide +kernel
private theorem gp3 : gpRow 3 := by unfold gpRow; decide +kernel
private theorem gp4 : gpRow 4 := by unfold gpRow; decide +kernel
private theorem gp5 : gpRow 5 := by unfold gpRow; decide +kernel
private theorem gp6 : gpRow 6 := by unfold gpRow; decide +kernel
private theorem gp7 : gpRow 7 := by unfold gpRow; decide +kernel
private theorem gp8 : gpRow 8 := by unfold gpRow; decide +kernel
private theorem gp9 : gpRow 9 := by unfold gpRow; decide +kernel
private theorem gp10 : gpRow 10 := by unfold gpRow; decide +kernel
private theorem gp11 : gpRow 11 := by unfold gpRow; decide +kernel
private theorem gp12 : gpRow 12 := by unfold gpRow; decide +kernel
private theorem gp13 : gpRow 13 := by unfold gpRow; decide +kernel
private theorem gp14 : gpRow 14 := by unfold gpRow; decide +kernel
private theorem gp15 : gpRow 15 := by unfold gpRow; decide +kernel
private theorem gp16 : gpRow 16 := by unfold gpRow; decide +kernel
private theorem gp17 : gpRow 17 := by unfold gpRow; decide +kernel
private theorem gp18 : gpRow 18 := by unfold gpRow; decide +kernel
private theorem gp19 : gpRow 19 := by unfold gpRow; decide +kernel
private theorem gp20 : gpRow 20 := by unfold gpRow; decide +kernel
private theorem gp21 : gpRow 21 := by unfold gpRow; decide +kernel
private theorem gp22 : gpRow 22 := by unfold gpRow; decide +kernel
private theorem gp23 : gpRow 23 := by unfold gpRow; decide +kernel
private theorem gp24 : gpRow 24 := by unfold gpRow; decide +kernel
private theorem gp25 : gpRow 25 := by unfold gpRow; decide +kernel
private theorem gp26 : gpRow 26 := by unfold gpRow; decide +kernel
private theorem gp27 : gpRow 27 := by unfold gpRow; decide +kernel

theorem witness_gp : GeneralPosition witness := by
  constructor
  · unfold Function.Injective
    decide +kernel
  · exact cases28 gp0 gp1 gp2 gp3 gp4 gp5 gp6 gp7 gp8 gp9 gp10 gp11 gp12 gp13 gp14 gp15 gp16 gp17 gp18 gp19 gp20 gp21 gp22 gp23 gp24 gp25 gp26 gp27

end K28
