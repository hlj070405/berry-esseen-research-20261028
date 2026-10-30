module

public import BerryEsseen.EnlargedFrozenReference
public import BerryEsseen.P39NoiseGate
public import BerryEsseen.ProbabilityGaussianPrice

@[expose] public section

/-! 2026-10-29: the actual canonical closed-CDF residual, a fixed two-group
reference law, and the whole-noise analytic gate at N=26/P39. Actual support,
variance ceilings and the acquired lower noise remain separate inputs. -/

noncomputable section
open MeasureTheory Set

namespace BerryEsseen.P39FrozenNoise

def referenceCost (μ : ProbabilityMeasure ℝ) (k : ℕ) (a0 O1 Z0 Z1 η t : ℝ) : ℝ :=
  Staircase.lowerMass (CoupledPrice.canonicalBinomialWeight μ 26) k + η *
    (t + StopLossShape.Q
      (DoubleBinomialReference.law a0 Z0 (26 - k) O1 Z1 k)
      (t + CoupledPrice.canonicalBinomialWeight μ 26 k / η))

theorem canonical_threshold_eq_noiseArgument (μ : ProbabilityMeasure ℝ)
    (hμ : StandardizedLaw μ) (k : ℕ) (t : ℝ) :
    ConditionalResidual.canonicalThreshold μ hμ 26 k t =
      P39NoiseGate.noiseArgument (CanonicalSign.p μ) ((k : ℝ) + t)
        (26 * CanonicalSign.noiseVariance μ hμ) := by
  rw [ProbabilityGaussianPrice.canonicalThreshold_eq_argument]
  unfold ProbabilityGaussianPrice.argument ProbabilityGaussianPrice.numerator
    ProbabilityGaussianPrice.variance P39NoiseGate.noiseArgument
    MomentBudgetNoise.variance P39Reference.v
  norm_num only [Nat.cast_ofNat]
  congr 2
  ring

/-- This is an inequality for the original distribution's actual normalized
closed-CDF error. The reference law is fixed over the noise slice. -/
theorem canonical_targetResidual_le_enlarged_noise_lower
    (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ) (k : ℕ) (hk : k ≤ 26)
    (a0 a1 O1 B0 B1 Z0 Z1 Δ δ η t lLower : ℝ)
    (ha0 : 0 ≤ a0) (ha1 : 0 ≤ a1) (hO1 : 0 ≤ O1)
    (hB0 : 0 < B0) (hB1 : 0 < B1) (haB0 : a0 ≤ B0) (hOB1 : O1 ≤ B1)
    (hcapΔ : a0 + a1 ≤ Δ) (hΔ : Δ < 1) (hδ : 0 < δ)
    (hδhi : δ ≤ 7 / 100) (hcapδ : a0 + a1 ≤ δ) (hη : 0 < η)
    (hinner0 : ∀ᵐ u ∂(CanonicalSign.residual0 μ hμ : Measure ℝ), u ≤ a0)
    (hinner1 : ∀ᵐ u ∂(CanonicalSign.residual1 μ hμ : Measure ℝ), -a1 ≤ u)
    (houter1 : ∀ᵐ u ∂(CanonicalSign.residual1 μ hμ : Measure ℝ), u ≤ O1)
    (hPrefix : ∀ r : ℕ, 1 ≤ r → r ≤ 26 - k →
      Staircase.prefixMass (fun j => CoupledPrice.canonicalBinomialWeight μ 26 (k + j)) r ≤
        η * ((r : ℝ) * (1 - Δ)))
    (hZ0 : TwoMoment.lawSecondMoment (CanonicalSign.residual0 μ hμ : Measure ℝ) ≤ Z0)
    (hZ1 : TwoMoment.lawSecondMoment (CanonicalSign.residual1 μ hμ : Measure ℝ) ≤ Z1)
    (hp : CanonicalSign.p μ ∈ Icc (39 / 100 : ℝ) (2 / 5))
    (hphase : (k : ℝ) + t ≤ 21 / 2)
    (hlLower : lLower ∈ Icc (0 : ℝ) (1 / 4))
    (hAcquired : lLower ≤ 26 * CanonicalSign.noiseVariance μ hμ)
    (hNoise : 26 * CanonicalSign.noiseVariance μ hμ ≤ 1 / 4) :
    ConditionalResidual.positiveTargetResidual μ 26
        (ConditionalResidual.canonicalThreshold μ hμ 26 k t) ≤
      referenceCost μ k B0 B1 Z0 Z1 η t +
        P39NoiseGate.price (CanonicalSign.p μ) ((k : ℝ) + t)
          (esseenConstant / Real.sqrt 26) δ
          (ConditionalResidual.actualAllocation μ hμ) lLower -
            3 / 2600 * (26 * CanonicalSign.noiseVariance μ hμ - lLower) := by
  have hc : 0 ≤ esseenConstant / Real.sqrt (26 : ℝ) :=
    (by norm_num : (0 : ℝ) ≤ 2 / 25).trans P39NoiseGate.actual_cost_lower
  have hb := EnlargedFrozenReference.canonical_targetResidual_le_enlarged_frozen_Q μ hμ 26 k
    (by norm_num) hk a0 a1 O1 B0 B1 Z0 Z1 Δ δ η t (esseenConstant / Real.sqrt 26)
    ha0 ha1 hO1 hB0 hB1 haB0 hOB1 hcapΔ hΔ hδ hcapδ hη
    hinner0 hinner1 houter1 hPrefix hc le_rfl hZ0 hZ1
  have he := P39NoiseGate.canonical_frozen_reference_endpoint μ hμ
    ((k : ℝ) + t) δ lLower (referenceCost μ k B0 B1 Z0 Z1 η t)
    hp hphase hδ hδhi hlLower hAcquired hNoise
  apply le_trans _ he
  rw [canonical_threshold_eq_noiseArgument μ hμ k t]
  rw [canonical_threshold_eq_noiseArgument μ hμ k t] at hb
  simpa only [referenceCost, P39NoiseGate.price,
    show (26 * CanonicalSign.noiseVariance μ hμ) / 26 =
      CanonicalSign.noiseVariance μ hμ by ring,
    sub_eq_add_neg, mul_neg, add_assoc] using hb

/-- The original equal-cap interface is a special case; the general theorem
above keeps enlarged reference caps out of the original moment budget. -/
theorem canonical_targetResidual_le_noise_lower
    (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ) (k : ℕ) (hk : k ≤ 26)
    (a0 a1 O1 Z0 Z1 Δ δ η t lLower : ℝ)
    (ha0 : 0 < a0) (ha1 : 0 ≤ a1) (hO1 : 0 < O1)
    (hcapΔ : a0 + a1 ≤ Δ) (hΔ : Δ < 1) (hδ : 0 < δ)
    (hδhi : δ ≤ 7 / 100) (hcapδ : a0 + a1 ≤ δ) (hη : 0 < η)
    (hinner0 : ∀ᵐ u ∂(CanonicalSign.residual0 μ hμ : Measure ℝ), u ≤ a0)
    (hinner1 : ∀ᵐ u ∂(CanonicalSign.residual1 μ hμ : Measure ℝ), -a1 ≤ u)
    (houter1 : ∀ᵐ u ∂(CanonicalSign.residual1 μ hμ : Measure ℝ), u ≤ O1)
    (hPrefix : ∀ r : ℕ, 1 ≤ r → r ≤ 26 - k →
      Staircase.prefixMass (fun j => CoupledPrice.canonicalBinomialWeight μ 26 (k + j)) r ≤
        η * ((r : ℝ) * (1 - Δ)))
    (hZ0 : TwoMoment.lawSecondMoment (CanonicalSign.residual0 μ hμ : Measure ℝ) ≤ Z0)
    (hZ1 : TwoMoment.lawSecondMoment (CanonicalSign.residual1 μ hμ : Measure ℝ) ≤ Z1)
    (hp : CanonicalSign.p μ ∈ Icc (39 / 100 : ℝ) (2 / 5))
    (hphase : (k : ℝ) + t ≤ 21 / 2)
    (hlLower : lLower ∈ Icc (0 : ℝ) (1 / 4))
    (hAcquired : lLower ≤ 26 * CanonicalSign.noiseVariance μ hμ)
    (hNoise : 26 * CanonicalSign.noiseVariance μ hμ ≤ 1 / 4) :
    ConditionalResidual.positiveTargetResidual μ 26
        (ConditionalResidual.canonicalThreshold μ hμ 26 k t) ≤
      referenceCost μ k a0 O1 Z0 Z1 η t +
        P39NoiseGate.price (CanonicalSign.p μ) ((k : ℝ) + t)
          (esseenConstant / Real.sqrt 26) δ
          (ConditionalResidual.actualAllocation μ hμ) lLower -
            3 / 2600 * (26 * CanonicalSign.noiseVariance μ hμ - lLower) :=
  canonical_targetResidual_le_enlarged_noise_lower μ hμ k hk
    a0 a1 O1 a0 O1 Z0 Z1 Δ δ η t lLower
    ha0.le ha1 hO1.le ha0 hO1 le_rfl le_rfl hcapΔ hΔ hδ hδhi hcapδ hη
    hinner0 hinner1 houter1 hPrefix hZ0 hZ1 hp hphase hlLower hAcquired hNoise

end BerryEsseen.P39FrozenNoise

#print axioms BerryEsseen.P39FrozenNoise.canonical_threshold_eq_noiseArgument
#print axioms BerryEsseen.P39FrozenNoise.canonical_targetResidual_le_enlarged_noise_lower
#print axioms BerryEsseen.P39FrozenNoise.canonical_targetResidual_le_noise_lower
