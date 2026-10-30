module

public import BerryEsseen.CoupledPrice
public import BerryEsseen.GaussianTools

@[expose] public section

/-!
The original standardized law's positive BE residual, priced by its
canonical common-residual CDF bound and its own third-moment budget.
The noise and allocation always come from the same canonical laws.
Zero noise is proved separately before joining the positive-noise floor.
-/

namespace BerryEsseen.ConditionalResidual

open MeasureTheory
open scoped BigOperators

noncomputable section

/-- This is the actual canonical allocation when noise is positive.
At zero noise Lean's total division makes it zero; no physical
identification of a zero-noise allocation ratio is asserted. -/
def actualAllocation (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ) : ℝ :=
  CanonicalSign.p μ * MomentBudget.residualSecondMoment (CanonicalSign.residual1 μ hμ) /
    CanonicalSign.noiseVariance μ hμ

private theorem law_eq_dirac_zero_of_second_zero (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hSq : Integrable (fun u : ℝ => u ^ 2) ν) (hs : (∫ u : ℝ, u ^ 2 ∂ν) = 0) :
    ν = Measure.dirac 0 := by
  have hzsq := (integral_eq_zero_iff_of_nonneg_ae
    (Filter.Eventually.of_forall (fun u : ℝ => sq_nonneg u)) hSq).mp hs
  have hz : (fun u : ℝ => u) =ᵐ[ν] (fun _ => 0) := hzsq.mono (fun u hu => sq_eq_zero_iff.mp hu)
  calc
    ν = ν.map id := (Measure.map_id).symm
    _ = ν.map (fun _ : ℝ => (0 : ℝ)) := Measure.map_congr hz
    _ = Measure.dirac 0 := by simp

/-- Positive actual sign weights force both residual laws to be the
zero law when their actual weighted second moment vanishes. -/
theorem canonical_zero_noise_laws (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (hs : CanonicalSign.noiseVariance μ hμ = 0) :
    (CanonicalSign.residual0 μ hμ : Measure ℝ) = Measure.dirac 0 ∧
      (CanonicalSign.residual1 μ hμ : Measure ℝ) = Measure.dirac 0 := by
  have hp := CanonicalSign.p_pos μ hμ
  have hq := CanonicalSign.q_pos μ hμ
  have hz0 := MomentBudget.residualSecondMoment_nonneg (CanonicalSign.residual0 μ hμ)
  have hz1 := MomentBudget.residualSecondMoment_nonneg (CanonicalSign.residual1 μ hμ)
  have hterm0 := mul_nonneg hq.le hz0
  have hterm1 := mul_nonneg hp.le hz1
  change CanonicalSign.q μ * MomentBudget.residualSecondMoment (CanonicalSign.residual0 μ hμ) +
    CanonicalSign.p μ * MomentBudget.residualSecondMoment (CanonicalSign.residual1 μ hμ) = 0 at hs
  have hprod0 : CanonicalSign.q μ * MomentBudget.residualSecondMoment (CanonicalSign.residual0 μ hμ) = 0 :=
    by linarith
  have hprod1 : CanonicalSign.p μ * MomentBudget.residualSecondMoment (CanonicalSign.residual1 μ hμ) = 0 :=
    by linarith
  have hs0 := (mul_eq_zero.mp hprod0).resolve_left hq.ne'
  have hs1 := (mul_eq_zero.mp hprod1).resolve_left hp.ne'
  exact ⟨law_eq_dirac_zero_of_second_zero _ (CanonicalSign.residual0_centered μ hμ).integrable_second hs0,
    law_eq_dirac_zero_of_second_zero _ (CanonicalSign.residual1_centered μ hμ).integrable_second hs1⟩

theorem canonical_zero_noise_moments (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (hs : CanonicalSign.noiseVariance μ hμ = 0) :
    MomentBudget.residualSecondMoment (CanonicalSign.residual0 μ hμ) = 0 ∧
    MomentBudget.residualSecondMoment (CanonicalSign.residual1 μ hμ) = 0 ∧
    MomentBudget.residualCubicMoment (CanonicalSign.residual0 μ hμ) = 0 ∧
    MomentBudget.residualCubicMoment (CanonicalSign.residual1 μ hμ) = 0 ∧
    actualAllocation μ hμ = 0 := by
  obtain ⟨h0, h1⟩ := canonical_zero_noise_laws μ hμ hs
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [MomentBudget.residualSecondMoment, h0]
  · simp [MomentBudget.residualSecondMoment, h1]
  · simp [MomentBudget.residualCubicMoment, h0]
  · simp [MomentBudget.residualCubicMoment, h1]
  · simp [actualAllocation, hs]

/-- The original law's actual rho at the zero-noise boundary is the
Bernoulli value, derived from its canonical actual third-moment identity. -/
theorem canonical_zero_noise_thirdMoment (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (hs : CanonicalSign.noiseVariance μ hμ = 0) :
    thirdAbsoluteMoment μ =
      (CanonicalSign.p μ * CanonicalSign.q μ *
        (1 - 2 * (CanonicalSign.p μ * CanonicalSign.q μ))) /
        (Real.sqrt (CanonicalSign.p μ * CanonicalSign.q μ)) ^ 3 := by
  obtain ⟨hs0, hs1, hm0, hm1, _⟩ := canonical_zero_noise_moments μ hμ hs
  have hid := CanonicalSign.thirdAbsoluteMoment_identity μ hμ
  have hc : CanonicalSign.scale μ hμ = Real.sqrt (CanonicalSign.p μ * CanonicalSign.q μ) := by
    rw [CanonicalSign.scale_eq_sqrt, hs, add_zero]
  rw [hs0, hs1, hm0, hm1, hc] at hid
  have hden : 0 < (Real.sqrt (CanonicalSign.p μ * CanonicalSign.q μ)) ^ 3 :=
    pow_pos (Real.sqrt_pos.mpr (mul_pos (CanonicalSign.p_pos μ hμ) (CanonicalSign.q_pos μ hμ))) _
  apply (eq_div_iff hden.ne').mpr
  simpa only [zero_add, add_zero, mul_zero, sub_zero] using hid

/-- The zero-noise floor is independent of the allocation symbol. -/
theorem gDelta_zero_noise (p δ α : ℝ) :
    MomentBudget.gDelta p 0 δ α =
      (p * (1 - p) * (1 - 2 * (p * (1 - p)))) / (Real.sqrt (p * (1 - p))) ^ 3 := by
  simp [MomentBudget.gDelta]

theorem canonical_zero_noise_rho_eq_gDelta (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (δ : ℝ) (hs : CanonicalSign.noiseVariance μ hμ = 0) :
    thirdAbsoluteMoment μ = MomentBudget.gDelta (CanonicalSign.p μ)
      (CanonicalSign.noiseVariance μ hμ) δ (actualAllocation μ hμ) := by
  rw [hs, gDelta_zero_noise]
  simpa only [CanonicalSign.q] using canonical_zero_noise_thirdMoment μ hμ hs

theorem canonical_actual_allocation_floor_of_pos
    (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (a0 a1 δ : ℝ) (ha0 : 0 ≤ a0) (ha1 : 0 ≤ a1) (hδ : 0 < δ) (hcap : a0 + a1 ≤ δ)
    (hupper0 : ∀ᵐ u ∂(CanonicalSign.residual0 μ hμ : Measure ℝ), u ≤ a0)
    (hlower1 : ∀ᵐ u ∂(CanonicalSign.residual1 μ hμ : Measure ℝ), -a1 ≤ u)
    (hs : 0 < CanonicalSign.noiseVariance μ hμ) :
    MomentBudget.gDelta (CanonicalSign.p μ) (CanonicalSign.noiseVariance μ hμ) δ
      (actualAllocation μ hμ) ≤ thirdAbsoluteMoment μ := by
  have hfloor := MomentBudget.actual_allocation_floor
    (CanonicalSign.residual0 μ hμ) (CanonicalSign.residual1 μ hμ)
    (CanonicalSign.residual0_centered μ hμ) (CanonicalSign.residual1_centered μ hμ)
    (CanonicalSign.p μ) (CanonicalSign.noiseVariance μ hμ) (actualAllocation μ hμ) a0 a1 δ
    (CanonicalSign.p_pos μ hμ) (CanonicalSign.p_lt_one μ hμ) hs rfl rfl ha0 ha1 hδ hcap
    hupper0 hlower1 (CanonicalSign.residual0_sign μ hμ)
    (by simpa only [CanonicalSign.q] using CanonicalSign.residual1_sign μ hμ)
  rw [← CanonicalSign.law_eq_normalizedResidualMixture μ hμ] at hfloor
  exact hfloor

/-- The actual-law allocation floor, with the zero-noise boundary fully
included rather than passed to an unidentified allocation or law. -/
theorem canonical_actual_allocation_floor
    (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (a0 a1 δ : ℝ) (ha0 : 0 ≤ a0) (ha1 : 0 ≤ a1) (hδ : 0 < δ) (hcap : a0 + a1 ≤ δ)
    (hupper0 : ∀ᵐ u ∂(CanonicalSign.residual0 μ hμ : Measure ℝ), u ≤ a0)
    (hlower1 : ∀ᵐ u ∂(CanonicalSign.residual1 μ hμ : Measure ℝ), -a1 ≤ u) :
    MomentBudget.gDelta (CanonicalSign.p μ) (CanonicalSign.noiseVariance μ hμ) δ
      (actualAllocation μ hμ) ≤ thirdAbsoluteMoment μ := by
  by_cases hs : CanonicalSign.noiseVariance μ hμ = 0
  · exact (canonical_zero_noise_rho_eq_gDelta μ hμ δ hs).symm.le
  · exact canonical_actual_allocation_floor_of_pos μ hμ a0 a1 δ ha0 ha1 hδ hcap hupper0 hlower1
      (lt_of_le_of_ne (CanonicalSign.noiseVariance_nonneg μ hμ) (Ne.symm hs))

/-- The fixed affine threshold used by the original normalized CDF bound. -/
def canonicalThreshold (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (n k : ℕ) (t : ℝ) : ℝ :=
  ((k : ℝ) + t - (n : ℝ) * CanonicalSign.p μ) /
    (CanonicalSign.scale μ hμ * Real.sqrt (n : ℝ))

/-- The actual positive closed-CDF Berry--Esseen target residual. -/
def positiveTargetResidual (μ : ProbabilityMeasure ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  (normalizedIidSumLaw μ n).real (Set.Iic x) - GaussianTools.Phi x -
    esseenConstant * thirdAbsoluteMoment μ / Real.sqrt (n : ℝ)

/-- Same-law CDF price and actual third-moment floor control the original
target residual. The pricing coefficient may be any value in the stated
interval; no rho upper bound or coefficient equality is assumed. -/
theorem canonical_targetResidual_le_clippedReferencePrice
    (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ) (n k : ℕ) (hn : 0 < n) (hk : k ≤ n)
    (a0 a1 O0 Δ δ h t ci : ℝ) (ha0 : 0 ≤ a0) (ha1 : 0 ≤ a1) (hO0 : 0 ≤ O0)
    (hcapΔ : a0 + a1 ≤ Δ) (hΔ : Δ < 1) (hδ : 0 < δ) (hcapδ : a0 + a1 ≤ δ) (hh : 0 < h)
    (hinner0 : ∀ᵐ u ∂(CanonicalSign.residual0 μ hμ : Measure ℝ), u ≤ a0)
    (hinner1 : ∀ᵐ u ∂(CanonicalSign.residual1 μ hμ : Measure ℝ), -a1 ≤ u)
    (houter0 : ∀ᵐ u ∂(CanonicalSign.residual0 μ hμ : Measure ℝ), -O0 ≤ u)
    (hGate : ∀ r : ℕ, 1 ≤ r → r ≤ n - k →
      Staircase.prefixMass (fun j => CoupledPrice.canonicalBinomialWeight μ n (k + j)) r /
          CoupledPrice.canonicalBinomialWeight μ n k ≤
        2 * (r : ℝ) * (1 - Δ) / h + (r : ℝ) ^ 2 * (1 - Δ) ^ 2 / h ^ 2)
    (hci0 : 0 ≤ ci) (hci : ci ≤ esseenConstant / Real.sqrt (n : ℝ)) :
    positiveTargetResidual μ n (canonicalThreshold μ hμ n k t) ≤
      Staircase.lowerMass (CoupledPrice.canonicalBinomialWeight μ n) k -
        CoupledPrice.canonicalBinomialWeight μ n k +
        (CoupledPrice.canonicalBinomialWeight μ n k / h ^ 2) *
          CoupledPrice.clippedReferencePrice (CanonicalSign.residual0 μ hμ : Measure ℝ)
            (CanonicalSign.residual1 μ hμ : Measure ℝ) O0 a1 n k (t + h) -
        GaussianTools.Phi (canonicalThreshold μ hμ n k t) -
        ci * MomentBudget.gDelta (CanonicalSign.p μ) (CanonicalSign.noiseVariance μ hμ) δ
          (actualAllocation μ hμ) := by
  have hCDF := CoupledPrice.canonical_normalized_closedCDF_le_clippedReferencePrice
    μ hμ n k hn hk a0 a1 O0 Δ h t ha0 ha1 hO0 hcapΔ hΔ hh hinner0 hinner1 houter0 hGate
  have hfloor := canonical_actual_allocation_floor μ hμ a0 a1 δ ha0 ha1 hδ hcapδ hinner0 hinner1
  have hρ : 0 ≤ thirdAbsoluteMoment μ :=
    integral_nonneg (fun x => pow_nonneg (abs_nonneg x) 3)
  have hfloorCost := mul_le_mul_of_nonneg_left hfloor hci0
  have htargetCost := mul_le_mul_of_nonneg_right hci hρ
  have hcost : ci * MomentBudget.gDelta (CanonicalSign.p μ) (CanonicalSign.noiseVariance μ hμ) δ
      (actualAllocation μ hμ) ≤ esseenConstant * thirdAbsoluteMoment μ / Real.sqrt (n : ℝ) := by
    calc
      _ ≤ ci * thirdAbsoluteMoment μ := hfloorCost
      _ ≤ (esseenConstant / Real.sqrt (n : ℝ)) * thirdAbsoluteMoment μ := htargetCost
      _ = _ := by ring
  unfold positiveTargetResidual canonicalThreshold
  linarith only [hCDF, hcost]

end

end BerryEsseen.ConditionalResidual

#print axioms BerryEsseen.ConditionalResidual.canonical_zero_noise_laws
#print axioms BerryEsseen.ConditionalResidual.canonical_zero_noise_thirdMoment
#print axioms BerryEsseen.ConditionalResidual.canonical_actual_allocation_floor
#print axioms BerryEsseen.ConditionalResidual.canonical_targetResidual_le_clippedReferencePrice
