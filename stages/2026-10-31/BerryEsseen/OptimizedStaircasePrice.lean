module

public import BerryEsseen.StopLossShape

@[expose] public section

/-!
The genuine infimum-width stop-loss price for the original canonical
normalized closed CDF, and its same-law Berry--Esseen residual bound.
The reference law is fixed at the positive-side caps (a0,O1) throughout
the infimum. No optimal width, automatic prefix gate, or new acquisition
assumption is introduced.
-/

namespace BerryEsseen.OptimizedStaircasePrice

open MeasureTheory
open scoped BigOperators

noncomputable section

/-- All proved positive-width prices pass to the actual Q of that same
two-group reference law. The eta prefix gate remains explicit. -/
theorem canonical_normalized_closedCDF_le_Q
    (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ) (n k : ℕ) (hn : 0 < n) (hk : k ≤ n)
    (a0 a1 O1 Δ η t : ℝ) (ha0 : 0 ≤ a0) (ha1 : 0 ≤ a1) (hO1 : 0 ≤ O1)
    (hcap : a0 + a1 ≤ Δ) (hΔ : Δ < 1) (hη : 0 < η)
    (hinner0 : ∀ᵐ u ∂(CanonicalSign.residual0 μ hμ : Measure ℝ), u ≤ a0)
    (hinner1 : ∀ᵐ u ∂(CanonicalSign.residual1 μ hμ : Measure ℝ), -a1 ≤ u)
    (houter1 : ∀ᵐ u ∂(CanonicalSign.residual1 μ hμ : Measure ℝ), u ≤ O1)
    (hPrefix : ∀ r : ℕ, 1 ≤ r → r ≤ n - k →
      Staircase.prefixMass (fun j => CoupledPrice.canonicalBinomialWeight μ n (k + j)) r ≤
        η * ((r : ℝ) * (1 - Δ))) :
    (normalizedIidSumLaw μ n).real (Set.Iic (ConditionalResidual.canonicalThreshold μ hμ n k t)) ≤
      Staircase.lowerMass (CoupledPrice.canonicalBinomialWeight μ n) k + η *
        (t + StopLossShape.Q
          (TwoMoment.coupledReferenceLaw (CanonicalSign.residual0 μ hμ : Measure ℝ)
            (CanonicalSign.residual1 μ hμ : Measure ℝ) a0 O1 n k)
          (t + CoupledPrice.canonicalBinomialWeight μ n k / η)) := by
  have hinf := StopLossShape.cdf_le_inf_price
    (TwoMoment.coupledReferenceLaw (CanonicalSign.residual0 μ hμ : Measure ℝ)
      (CanonicalSign.residual1 μ hμ : Measure ℝ) a0 O1 n k)
    (t + CoupledPrice.canonicalBinomialWeight μ n k / η)
    ((normalizedIidSumLaw μ n).real (Set.Iic (ConditionalResidual.canonicalThreshold μ hμ n k t)))
    (Staircase.lowerMass (CoupledPrice.canonicalBinomialWeight μ n) k + η * t) η hη
    (by
      intro w hw
      have hp := StaircasePrices.canonical_normalized_closedCDF_le_stopLoss_width
        μ hμ n k hn hk a0 a1 O1 Δ η t w ha0 ha1 hO1 hcap hΔ hη hw
        hinner0 hinner1 houter1 hPrefix
      simpa only [StopLossShape.price_eq_staircase_widthReferencePrice, mul_add, add_assoc] using hp)
  simpa only [mul_add, add_assoc] using hinf

/-- The actual original-law target coefficient is retained. The lower
third-moment price uses exactly the same canonical noise and allocation
as the fixed reference law, including the proved zero-noise boundary. -/
theorem canonical_targetResidual_le_Q
    (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ) (n k : ℕ) (hn : 0 < n) (hk : k ≤ n)
    (a0 a1 O1 Δ δ η t ci : ℝ) (ha0 : 0 ≤ a0) (ha1 : 0 ≤ a1) (hO1 : 0 ≤ O1)
    (hcapΔ : a0 + a1 ≤ Δ) (hΔ : Δ < 1) (hδ : 0 < δ) (hcapδ : a0 + a1 ≤ δ) (hη : 0 < η)
    (hinner0 : ∀ᵐ u ∂(CanonicalSign.residual0 μ hμ : Measure ℝ), u ≤ a0)
    (hinner1 : ∀ᵐ u ∂(CanonicalSign.residual1 μ hμ : Measure ℝ), -a1 ≤ u)
    (houter1 : ∀ᵐ u ∂(CanonicalSign.residual1 μ hμ : Measure ℝ), u ≤ O1)
    (hPrefix : ∀ r : ℕ, 1 ≤ r → r ≤ n - k →
      Staircase.prefixMass (fun j => CoupledPrice.canonicalBinomialWeight μ n (k + j)) r ≤
        η * ((r : ℝ) * (1 - Δ)))
    (hci0 : 0 ≤ ci) (hci : ci ≤ esseenConstant / Real.sqrt (n : ℝ)) :
    ConditionalResidual.positiveTargetResidual μ n (ConditionalResidual.canonicalThreshold μ hμ n k t) ≤
      Staircase.lowerMass (CoupledPrice.canonicalBinomialWeight μ n) k + η *
        (t + StopLossShape.Q
          (TwoMoment.coupledReferenceLaw (CanonicalSign.residual0 μ hμ : Measure ℝ)
            (CanonicalSign.residual1 μ hμ : Measure ℝ) a0 O1 n k)
          (t + CoupledPrice.canonicalBinomialWeight μ n k / η)) -
        GaussianTools.Phi (ConditionalResidual.canonicalThreshold μ hμ n k t) -
        ci * MomentBudget.gDelta (CanonicalSign.p μ) (CanonicalSign.noiseVariance μ hμ) δ
          (ConditionalResidual.actualAllocation μ hμ) := by
  have hCDF := canonical_normalized_closedCDF_le_Q
    μ hμ n k hn hk a0 a1 O1 Δ η t ha0 ha1 hO1 hcapΔ hΔ hη hinner0 hinner1 houter1 hPrefix
  have hfloor := ConditionalResidual.canonical_actual_allocation_floor
    μ hμ a0 a1 δ ha0 ha1 hδ hcapδ hinner0 hinner1
  have hρ : 0 ≤ thirdAbsoluteMoment μ :=
    integral_nonneg (fun x => pow_nonneg (abs_nonneg x) 3)
  have hcost : ci * MomentBudget.gDelta (CanonicalSign.p μ) (CanonicalSign.noiseVariance μ hμ) δ
      (ConditionalResidual.actualAllocation μ hμ) ≤
      esseenConstant * thirdAbsoluteMoment μ / Real.sqrt (n : ℝ) := by
    calc
      _ ≤ ci * thirdAbsoluteMoment μ := mul_le_mul_of_nonneg_left hfloor hci0
      _ ≤ (esseenConstant / Real.sqrt (n : ℝ)) * thirdAbsoluteMoment μ :=
        mul_le_mul_of_nonneg_right hci hρ
      _ = _ := by ring
  unfold ConditionalResidual.positiveTargetResidual
  linarith only [hCDF, hcost]

end

end BerryEsseen.OptimizedStaircasePrice

#print axioms BerryEsseen.OptimizedStaircasePrice.canonical_normalized_closedCDF_le_Q
#print axioms BerryEsseen.OptimizedStaircasePrice.canonical_targetResidual_le_Q
