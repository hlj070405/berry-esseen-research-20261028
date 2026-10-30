module

public import BerryEsseen.P39FactorialTailEnvelope
public import BerryEsseen.P39FactorialTailDomain
public import BerryEsseen.P39CoupledMomentCredit
public import BerryEsseen.P39LeftGaussianCredit
public import BerryEsseen.Reflection

@[expose] public section

/-! 2026-10-31: the original count-10 lattice threshold, uniformly in
the acquired continuous probability/noise domain. The actual CDF is
priced first; actual rho then pays both the Gaussian and reference tail.
The same original maximum is used in the final height contradiction. -/

noncomputable section

open MeasureTheory Set

namespace BerryEsseen.P39Count10ZeroPhase

open CanonicalSign CentralGap NoiseCoordinates GaussianTools

theorem reference_tail_upper {p lambda : ℝ}
    (hp : p ∈ Icc (39 / 100 : ℝ) (2 / 5)) (hl : lambda ∈ Icc (0 : ℝ) (1 / 5)) :
    P39FactorialTailDomain.eta p lambda *
      StopLossShape.Q (P39FactorialTailDomain.reference p lambda) (P39FactorialTailDomain.A p lambda) ≤
      (7 / 50 : ℝ) * lambda ^ 2 - (7 / 25 : ℝ) * lambda ^ 3 := by
  have he := P39FactorialTailEnvelope.weighted_Q_le
    (P39FactorialTailDomain.eta p lambda) (P39FactorialTailDomain.V p lambda)
    (P39FactorialTailDomain.A p lambda) lambda
    ⟨P39FactorialTailDomain.eta_nonneg hp hl, P39FactorialTailDomain.eta_upper hp hl⟩ hl
    ⟨P39FactorialTailDomain.V_nonneg hp hl, P39FactorialTailDomain.V_upper hp hl⟩
    (P39FactorialTailDomain.scaledThreshold_mem hp hl) (P39FactorialTailDomain.gap_upper hp hl)
  simpa only [P39FactorialTailDomain.reference, P39FactorialTailDomain.B,
    P39FactorialTailEnvelope.cap] using he

theorem original_residual_upper (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (H C : ℝ) (hm : ContactVariation.PositiveClosedMaximum μ 26 H C)
    (hprev : Extremizer.fixedNSup 25 ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10)
    (hp : p μ ∈ Icc (39 / 100 : ℝ) (2 / 5)) :
    ConditionalResidual.positiveTargetResidual μ 26 (ConditionalResidual.canonicalThreshold μ h 26 10 0) ≤
      -(1 / 9000 : ℝ) - (67 / 271200 : ℝ) * noiseLevel μ h 26 := by
  let lambda := noiseLevel μ h 26
  have hl0 : 0 ≤ lambda := mul_nonneg (Nat.cast_nonneg 26) (noiseVariance_nonneg μ h)
  have hl1 : lambda < (1 : ℝ) / 5 :=
    P39CoupledMomentCredit.original_noiseLevel_lt μ h H C hm hprev hC hρ hp
  have hl : lambda ∈ Icc (0 : ℝ) (1 / 5) := ⟨hl0, hl1.le⟩
  have hd := P39CoupledInwardNoise.original_d_bounds μ h H C hm hprev hC hρ hp
  have hcap := (P39CoupledInwardNoise.original_inward_lt_d μ h H C hm hprev hC hρ hp).le
  have hCDF := P39LeftAllocationReduction.original_closedCDF_le_leftReference μ h H C hm hprev hC hρ hp
    (P39CoupledInwardNoise.d lambda) (by linarith only [hd.2]) hcap 10 (by decide) (by decide) 0
  simp only [add_zero, zero_add] at hCDF
  rw [← P39FactorialTailDomain.eta_eq_leftEta,
    ← P39FactorialTailDomain.reference_eq_leftReference,
    P39FactorialTailDomain.threshold_eq_A hp hl] at hCDF
  have htail := reference_tail_upper hp hl
  have hbase := P39LeftGaussianCredit.count10_noisy_baseline_upper hp hl
  have hr := P39CoupledMomentCredit.original_thirdMoment_credit μ h H C hm hprev hC hρ hp
  have hs : noiseVariance μ h = lambda / 26 :=
    (P39LeftAllocationReduction.noiseLevel_div_twenty_six μ h).symm
  rw [hs] at hr
  have hρ0 : 0 ≤ thirdAbsoluteMoment μ :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (Extremizer.thirdAbsoluteMoment_ge_one μ h)
  have hcost : (803 / 10000 : ℝ) * thirdAbsoluteMoment μ ≤
      esseenConstant * thirdAbsoluteMoment μ / Real.sqrt 26 := by
    have hh := mul_le_mul_of_nonneg_right P39LeftAllocationReduction.cost_le_target hρ0
    simpa only [P39LeftAllocationReduction.cost, div_mul_eq_mul_div] using hh
  have hcharge := (mul_le_mul_of_nonneg_left hr (by norm_num : (0 : ℝ) ≤ 803 / 10000)).trans hcost
  have hbalance := P39FactorialTailEnvelope.noise_price_gate lambda hl0
  have harg : ConditionalResidual.canonicalThreshold μ h 26 10 0 =
      P39NoiseGate.noiseArgument (p μ) 10 lambda := by
    simpa only [lambda, noiseLevel, Nat.cast_ofNat, add_zero] using
      P39FrozenNoise.canonical_threshold_eq_noiseArgument μ h 10 0
  rw [harg] at hCDF
  unfold ConditionalResidual.positiveTargetResidual
  norm_num only [Nat.cast_ofNat]
  rw [harg]
  unfold P39CoupledMomentCredit.credit at hcharge
  change (normalizedIidSumLaw μ 26).real (Iic (P39NoiseGate.noiseArgument (p μ) 10 lambda)) -
      Phi (P39NoiseGate.noiseArgument (p μ) 10 lambda) -
        esseenConstant * thirdAbsoluteMoment μ / Real.sqrt 26 ≤
      -(1 / 9000 : ℝ) - (67 / 271200 : ℝ) * lambda
  linarith only [hCDF, htail, hbase, hcharge, hbalance]

theorem original_height_ne_ten (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (H C : ℝ) (hm : ContactVariation.PositiveClosedMaximum μ 26 H C)
    (hprev : Extremizer.fixedNSup 25 ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10)
    (hp : p μ ∈ Icc (39 / 100 : ℝ) (2 / 5)) :
    CentralGapConditionalIntegral.canonicalHeight μ h 26 H ≠ (10 : ℝ) := by
  intro hh
  have hu := original_residual_upper μ h H C hm hprev hC hρ hp
  have hnum : 10 - 26 * p μ = scale μ h * H := by
    unfold CentralGapConditionalIntegral.canonicalHeight at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith only [hh]
  have hthreshold : ConditionalResidual.canonicalThreshold μ h 26 10 0 = H / Real.sqrt 26 := by
    unfold ConditionalResidual.canonicalThreshold
    norm_num only [Nat.cast_ofNat, add_zero]
    rw [hnum]
    exact mul_div_mul_left H (Real.sqrt 26) (scale_pos μ h).ne'
  rw [hthreshold] at hu
  have hs : Real.sqrt (26 : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 26)).ne'
  have hcdf : (normalizedIidSumLaw μ 26).real (Iic (H / Real.sqrt 26)) =
      (MixtureSum.iidSumLaw (μ : Measure ℝ) 26).real (Iic H) := by
    rw [Reflection.normalized_closedCDF_eq_raw μ 26 (by decide) (H / Real.sqrt 26)]
    norm_num only [Nat.cast_ofNat]
    have harg : Real.sqrt (26 : ℝ) * (H / Real.sqrt 26) = H := by field_simp [hs]
    rw [harg]
  unfold ConditionalResidual.positiveTargetResidual at hu
  norm_num only [Nat.cast_ofNat] at hu
  rw [hcdf] at hu
  have ha := hm.attainment
  norm_num only [Nat.cast_ofNat] at ha
  rw [ha] at hu
  have hρ0 : 0 ≤ thirdAbsoluteMoment μ :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (Extremizer.thirdAbsoluteMoment_ge_one μ h)
  have he : 0 ≤ (C - esseenConstant) * thirdAbsoluteMoment μ / Real.sqrt 26 :=
    div_nonneg (mul_nonneg (sub_nonneg.mpr hC) hρ0) (Real.sqrt_nonneg _)
  have heq : (C - esseenConstant) * thirdAbsoluteMoment μ / Real.sqrt 26 =
      C * thirdAbsoluteMoment μ / Real.sqrt 26 -
        esseenConstant * thirdAbsoluteMoment μ / Real.sqrt 26 := by ring
  rw [heq] at he
  have hl0 : 0 ≤ noiseLevel μ h 26 := mul_nonneg (Nat.cast_nonneg 26) (noiseVariance_nonneg μ h)
  linarith only [hu, he, hl0]

end BerryEsseen.P39Count10ZeroPhase

#print axioms BerryEsseen.P39Count10ZeroPhase.reference_tail_upper
#print axioms BerryEsseen.P39Count10ZeroPhase.original_residual_upper
#print axioms BerryEsseen.P39Count10ZeroPhase.original_height_ne_ten
