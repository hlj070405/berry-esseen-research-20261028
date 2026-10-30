module

public import BerryEsseen.N2GaussianArgument
public import BerryEsseen.N2NeededData

@[expose] public section

/-! 2026-10-29: consume directed rational Gaussian argument and rounding
gates before any rectangle leaves use the rounded prices. -/

noncomputable section

namespace BerryEsseen.N2NeededGaussian

open GaussianTools RationalGaussianPrices N2GaussianArgument N2NeededData

theorem lowerPrice_family {ι : Type*} (m : ℕ) (t z R : ι → ℚ)
    (hGate : ∀ i, ArgumentGate (t i) (z i))
    (hRound : ∀ i, R i ≤ PhiLower m (z i)) (i : ι) :
    (R i : ℝ) ≤ Phi ((t i : ℝ) / Real.sqrt 2) :=
  rounded_price_le_Phi m (t i) (z i) (R i) (hGate i) (hRound i)

/-- Needed indices zero through four are source rows 005 through 009. -/
def pilotIndex (i : Fin 5) : Fin 65 := ⟨i.val, lt_trans i.isLt (by decide : 5 < 65)⟩

theorem argumentsGate_pilot : ∀ i : Fin 5,
    ArgumentGate (lowerQ (pilotIndex i)) (gaussianZ (pilotIndex i)) := by
  unfold ArgumentGate
  decide +kernel

theorem roundingBound_pilot : ∀ i : Fin 5,
    gaussianR (pilotIndex i) ≤ PhiLower 12 (gaussianZ (pilotIndex i)) := by
  decide +kernel

theorem lowerPrice_real_pilot (i : Fin 5) :
    (gaussianR (pilotIndex i) : ℝ) ≤ Phi (N2FiniteCover.lower (pilotIndex i) / Real.sqrt 2) := by
  have hp := lowerPrice_family 12
    (fun j : Fin 5 => lowerQ (pilotIndex j))
    (fun j : Fin 5 => gaussianZ (pilotIndex j))
    (fun j : Fin 5 => gaussianR (pilotIndex j))
    argumentsGate_pilot roundingBound_pilot i
  simpa only [lowerQ_cast] using hp

/-- Every needed original row uses its own directed literal argument. -/
theorem argumentsGate : ∀ i : Fin 65, ArgumentGate (lowerQ i) (gaussianZ i) := by
  unfold ArgumentGate
  decide +kernel

/-- The uniform order twelve is checked against each row's literal rounded price. -/
theorem roundingBound : ∀ i : Fin 65, gaussianR i ≤ PhiLower 12 (gaussianZ i) := by
  decide +kernel

theorem lowerPrice_real (i : Fin 65) :
    (gaussianR i : ℝ) ≤ Phi (N2FiniteCover.lower i / Real.sqrt 2) := by
  have hp := rounded_price_le_Phi 12 (lowerQ i) (gaussianZ i) (gaussianR i)
    (argumentsGate i) (roundingBound i)
  simpa only [lowerQ_cast] using hp

end BerryEsseen.N2NeededGaussian

#print axioms BerryEsseen.N2NeededGaussian.lowerPrice_family
#print axioms BerryEsseen.N2NeededGaussian.argumentsGate_pilot
#print axioms BerryEsseen.N2NeededGaussian.roundingBound_pilot
#print axioms BerryEsseen.N2NeededGaussian.lowerPrice_real_pilot
#print axioms BerryEsseen.N2NeededGaussian.argumentsGate
#print axioms BerryEsseen.N2NeededGaussian.roundingBound
#print axioms BerryEsseen.N2NeededGaussian.lowerPrice_real
