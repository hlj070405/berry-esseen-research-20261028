module

public import BerryEsseen.P39ModeBaselineMonotonicity
public import BerryEsseen.P39ModeNoiseUpperBounds
public import BerryEsseen.P39CoarseNoiseIncrement
public import BerryEsseen.UniformCoupledReference
public import BerryEsseen.P39FrozenNoise
public import BerryEsseen.Reflection

@[expose] public section

/-! 2026-10-30: exclude the entire original N26/P39 count-11 phase.
The actual CDF is priced before its actual third-moment target is
subtracted. Count variance licenses reference enlargement, while total
noise licenses the Gaussian loss; these are different actual quantities.
The original maximum is retained throughout, including at the final
height contradiction. No old profile or free resource plane is used. -/

noncomputable section

open MeasureTheory Set

namespace BerryEsseen.P39ModeTailExclusion

open CanonicalSign CentralGap NoiseCoordinates GaussianTools
open P39ModeEtaEndpointPrices

local instance : IsProbabilityMeasure reference := reference_probability

/-- The fixed reference and fixed lambda remain unchanged as t varies. -/
def envelope (p lambda t : ℝ) : ℝ :=
  PositivePhasePriceConvex.phasePrice reference (BinomialWeights.lowerPrefix 26 11 p)
    (7 / 50) (219 / 200) (11 - 26 * p) (26 * MomentBudgetNoise.variance p + lambda)
    ((2 / 25) * (P39Reference.rho0 p + (19 / 10) * lambda / 26)) t

theorem envelope_noise_form (p lambda t : ℝ) :
    envelope p lambda t = BinomialWeights.lowerPrefix 26 11 p +
      (7 / 50 : ℝ) * (t + StopLossShape.Q reference (219 / 200 + t)) -
      Phi (P39NoiseGate.noiseArgument p (11 + t) lambda) -
      (2 / 25) * (P39Reference.rho0 p + (19 / 10) * lambda / 26) := by
  have harg : ((11 - 26 * p) + t) / Real.sqrt (26 * MomentBudgetNoise.variance p + lambda) =
      P39NoiseGate.noiseArgument p (11 + t) lambda := by
    unfold P39NoiseGate.noiseArgument
    congr 1
    ring
  unfold envelope PositivePhasePriceConvex.phasePrice
  rw [harg]

theorem argument_eq_zero_noise (r p : ℝ) :
    P39ModeEtaEndpointPrices.argument r p = P39NoiseGate.noiseArgument p r 0 := by
  simp only [P39ModeEtaEndpointPrices.argument, P39NoiseGate.noiseArgument,
    MomentBudgetNoise.variance, P39Reference.v, add_zero, mul_assoc]

theorem envelope_zero_upper {p lambda : ℝ} (hp : p ∈ strip)
    (hl : lambda ∈ Icc (0 : ℝ) (17 / 50)) : envelope p lambda 0 ≤ -(1 / 5000 : ℝ) := by
  have hb := P39ModeBaselineMonotonicity.base0_strip_upper hp
  unfold base0 at hb
  rw [argument_eq_zero_noise] at hb
  have hn := P39ModeNoiseUpperBounds.count11_noise_loss hp hl
  have hQ := mul_le_mul_of_nonneg_left actual_Q_upper0 (by norm_num : (0 : ℝ) ≤ 7 / 50)
  have hL := mul_le_mul_of_nonneg_left hl.2
    (by norm_num : (0 : ℝ) ≤ 11 / 1000 - (2 / 25) * (19 / 10) / 26)
  have hg := arithmetic_gate0
  rw [envelope_noise_form]
  simp only [add_zero, zero_add]
  nlinarith only [hb, hn, hQ, hL, hg]

theorem envelope_one_upper {p lambda : ℝ} (hp : p ∈ strip)
    (hl : lambda ∈ Icc (0 : ℝ) (17 / 50)) : envelope p lambda 1 ≤ -(1 / 5000 : ℝ) := by
  have hb := P39ModeBaselineMonotonicity.base1_strip_upper hp
  unfold base1 at hb
  rw [argument_eq_zero_noise] at hb
  have hn := P39ModeNoiseUpperBounds.count12_noise_loss hp hl.1
  have hQ := mul_le_mul_of_nonneg_left (add_le_add_left actual_Q_upper1 (1 : ℝ))
    (by norm_num : (0 : ℝ) ≤ 7 / 50)
  have hL := mul_le_mul_of_nonneg_left hl.2
    (by norm_num : (0 : ℝ) ≤ 1 / 40 - (2 / 25) * (19 / 10) / 26)
  have hg := arithmetic_gate1
  rw [envelope_noise_form, show (11 : ℝ) + 1 = 12 by norm_num,
    show (219 / 200 : ℝ) + 1 = 419 / 200 by norm_num]
  nlinarith only [hb, hn, hQ, hL, hg]

/-- The two endpoint estimates control the whole closed phase interval
through the proved convexity of the same fixed reference-law price. -/
theorem envelope_phase_upper {p lambda t : ℝ} (hp : p ∈ strip)
    (hl : lambda ∈ Icc (0 : ℝ) (17 / 50)) (ht : t ∈ Icc (0 : ℝ) 1) :
    envelope p lambda t ≤ -(1 / 5000 : ℝ) := by
  exact PositivePhasePriceConvex.phasePrice_le_of_endpoints reference reference_square_integrable
    (BinomialWeights.lowerPrefix 26 11 p) (7 / 50) (219 / 200) (11 - 26 * p)
    (26 * MomentBudgetNoise.variance p + lambda)
    ((2 / 25) * (P39Reference.rho0 p + (19 / 10) * lambda / 26)) 0 1 (-(1 / 5000))
    (P39NoiseGate.actual_variance_pos hp hl.1) (by norm_num)
    (by linarith only [hp.2]) (by norm_num)
    (envelope_zero_upper hp hl) (envelope_one_upper hp hl) t ht

/-- Start from the actual closed CDF, not a residual priced by gDelta.
The true total count variance is enlarged to the fixed reference only
after the actual-cap coupling has been licensed. -/
theorem original_closedCDF_le_uniform (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (H C : ℝ) (hm : ContactVariation.PositiveClosedMaximum μ 26 H C)
    (hprev : Extremizer.fixedNSup 25 ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10)
    (hp : p μ ∈ Icc (39 / 100 : ℝ) (2 / 5)) (t : ℝ) (ht : 0 ≤ t) :
    (normalizedIidSumLaw μ 26).real (Iic (ConditionalResidual.canonicalThreshold μ h 26 11 t)) ≤
      BinomialWeights.lowerPrefix 26 11 (p μ) +
        (7 / 50 : ℝ) * (t + StopLossShape.Q reference (219 / 200 + t)) := by
  have hs0 := RefinedLowMomentSupport.original_support μ h 26 (by decide) H C hm hprev hC hρ
  have hs : (μ : Measure ℝ).support ⊆ Icc (-(37 / 16 : ℝ)) (37 / 16) :=
    fun x hx => ⟨(hs0 hx).1.le, (hs0 hx).2.le⟩
  have hO := (P39Count11VarianceAcquisition.scale_and_outward_caps μ h hρ hp).2.2
  have houter : ∀ᵐ u ∂(residual1 μ h : Measure ℝ), u ≤ (5 : ℝ) / 8 :=
    (CanonicalResidualMomentBounds.residual1_upper_of_support μ h (37 / 16) hs).mono
      (fun _ hu => hu.trans hO)
  have hdelta := (CanonicalInwardBudget.original_inward_lt_seven_eightieths μ h
    26 (by decide) H C hm hprev hC hρ).le
  have haB : a0 μ h ≤ (5 : ℝ) / 8 := by linarith only [hdelta, a1_nonneg μ h]
  have hmode : ((26 + 1 : ℕ) : ℝ) * p μ ≤ ((11 + 2 : ℕ) : ℝ) := by
    norm_num only [Nat.reduceAdd, Nat.cast_ofNat]
    exact mode_condition hp
  have hCDF := BinomialPrefixGate.canonical_normalized_closedCDF_le_Q μ h 26 11
    (by decide) (by decide) (a0 μ h) (a1 μ h) (5 / 8) (7 / 80) t
    (a0_nonneg μ h) (a1_nonneg μ h) (by norm_num) hdelta (by norm_num)
    (CentralGap.residual0_upper μ h) (CentralGap.residual1_lower μ h) houter hmode
  dsimp only at hCDF
  have hEta : BinomialPrefixGate.tailEta 26 11 (7 / 80) (p μ) = eta (p μ) :=
    (eta_eq_tailEta (p μ)).symm
  rw [hEta, ← BinomialWeights.prefix_at_canonical μ 26 11] at hCDF
  have hV := P39Count11VarianceAcquisition.original_actualCountVariance_le μ h H C hm hprev hC hρ hp
  have hQ : StopLossShape.Q
      (TwoMoment.coupledReferenceLaw (residual0 μ h : Measure ℝ) (residual1 μ h : Measure ℝ)
        (a0 μ h) (5 / 8) 26 11)
      (t + CoupledPrice.canonicalBinomialWeight μ 26 11 / eta (p μ)) ≤
      StopLossShape.Q reference (t + CoupledPrice.canonicalBinomialWeight μ 26 11 / eta (p μ)) :=
    UniformCoupledReference.coupledReference_Q_le_uniform
      (residual0 μ h : Measure ℝ) (residual1 μ h : Measure ℝ)
      (a0 μ h) (5 / 8) (5 / 8) (8 / 25) 26 11 (by decide) (by decide)
      (a0_nonneg μ h) (by norm_num) (by norm_num) haB le_rfl hV _
  have hA : (219 / 200 : ℝ) ≤ CoupledPrice.canonicalBinomialWeight μ 26 11 / eta (p μ) := by
    simpa only [BinomialWeights.mass_at_canonical] using mass_div_eta_lower hp
  have hshift := (StopLossShape.Q_antitone reference reference_square_integrable)
    (show 219 / 200 + t ≤ t + CoupledPrice.canonicalBinomialWeight μ 26 11 / eta (p μ) by
      linarith only [hA])
  have hprice := mul_le_mul_of_nonneg_left (add_le_add_left (hQ.trans hshift) t) (eta_pos hp).le
  have hnonneg := add_nonneg ht (StopLossShape.Q_nonneg reference (219 / 200 + t))
  have hEtaPrice := mul_le_mul_of_nonneg_right (eta_le_seven_fiftieths hp) hnonneg
  nlinarith only [hCDF, hprice, hEtaPrice]

/-- The target subtracts the actual rho of the original law. Its acquired
rho credit is applied here, independently of any gDelta bound. -/
theorem original_residual_le_envelope (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (H C : ℝ) (hm : ContactVariation.PositiveClosedMaximum μ 26 H C)
    (hprev : Extremizer.fixedNSup 25 ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10)
    (hp : p μ ∈ Icc (39 / 100 : ℝ) (2 / 5)) (t : ℝ) (ht : 0 ≤ t) :
    ConditionalResidual.positiveTargetResidual μ 26 (ConditionalResidual.canonicalThreshold μ h 26 11 t) ≤
      envelope (p μ) (noiseLevel μ h 26) t := by
  have hCDF := original_closedCDF_le_uniform μ h H C hm hprev hC hρ hp t ht
  have hr := P39CoarseNoiseIncrement.original_thirdMoment_ge_rho0_add_noise μ h H C hm hprev hC hρ hp
  have hρ0 : 0 ≤ thirdAbsoluteMoment μ :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (Extremizer.thirdAbsoluteMoment_ge_one μ h)
  have hc := mul_le_mul_of_nonneg_right P39NoiseGate.actual_cost_lower hρ0
  have hcredit := mul_le_mul_of_nonneg_left hr (by norm_num : (0 : ℝ) ≤ 2 / 25)
  have hLambda : noiseLevel μ h 26 = 26 * noiseVariance μ h := rfl
  have hcharge : (2 / 25 : ℝ) * (P39Reference.rho0 (p μ) +
      (19 / 10) * noiseLevel μ h 26 / 26) ≤ esseenConstant * thirdAbsoluteMoment μ / Real.sqrt 26 := by
    have hcreditLambda : (2 / 25 : ℝ) * (P39Reference.rho0 (p μ) +
        (19 / 10) * noiseLevel μ h 26 / 26) ≤ (2 / 25) * thirdAbsoluteMoment μ := by
      rw [hLambda]
      convert hcredit using 1
      ring
    have hcost : (2 / 25 : ℝ) * thirdAbsoluteMoment μ ≤
        esseenConstant * thirdAbsoluteMoment μ / Real.sqrt 26 := by
      simpa only [div_mul_eq_mul_div] using hc
    exact hcreditLambda.trans hcost
  have hthreshold : ConditionalResidual.canonicalThreshold μ h 26 11 t =
      P39NoiseGate.noiseArgument (p μ) (11 + t) (noiseLevel μ h 26) := by
    simpa only [noiseLevel, Nat.cast_ofNat] using
      P39FrozenNoise.canonical_threshold_eq_noiseArgument μ h 11 t
  have hPhi := congrArg Phi hthreshold
  rw [envelope_noise_form]
  unfold ConditionalResidual.positiveTargetResidual
  norm_num only [Nat.cast_ofNat]
  nlinarith only [hCDF, hcharge, hPhi]

theorem original_count11_phase_upper (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (H C : ℝ) (hm : ContactVariation.PositiveClosedMaximum μ 26 H C)
    (hprev : Extremizer.fixedNSup 25 ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10)
    (hp : p μ ∈ Icc (39 / 100 : ℝ) (2 / 5)) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ConditionalResidual.positiveTargetResidual μ 26 (ConditionalResidual.canonicalThreshold μ h 26 11 t) ≤
      -(1 / 5000 : ℝ) := by
  have hl0 : 0 ≤ noiseLevel μ h 26 :=
    mul_nonneg (Nat.cast_nonneg 26) (noiseVariance_nonneg μ h)
  have hl1 := P39Count11VarianceAcquisition.original_noiseLevel_le μ h H C hm hprev hC hρ hp
  exact (original_residual_le_envelope μ h H C hm hprev hC hρ hp t ht.1).trans
    (envelope_phase_upper hp ⟨hl0, hl1⟩ ht)

theorem original_not_height_interval (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (H C : ℝ) (hm : ContactVariation.PositiveClosedMaximum μ 26 H C)
    (hprev : Extremizer.fixedNSup 25 ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10)
    (hp : p μ ∈ Icc (39 / 100 : ℝ) (2 / 5)) :
    CentralGapConditionalIntegral.canonicalHeight μ h 26 H ∉ Icc (11 : ℝ) 12 := by
  intro hheight
  let t := CentralGapConditionalIntegral.canonicalHeight μ h 26 H - 11
  have ht : t ∈ Icc (0 : ℝ) 1 := by
    dsimp only [t]
    constructor <;> linarith only [hheight.1, hheight.2]
  have hupper := original_count11_phase_upper μ h H C hm hprev hC hρ hp t ht
  have hnum : 11 + t - 26 * p μ = scale μ h * H := by
    dsimp only [t, CentralGapConditionalIntegral.canonicalHeight]
    norm_num only [Nat.cast_ofNat]
    ring
  have hthreshold : ConditionalResidual.canonicalThreshold μ h 26 11 t = H / Real.sqrt 26 := by
    unfold ConditionalResidual.canonicalThreshold
    norm_num only [Nat.cast_ofNat]
    rw [hnum]
    exact mul_div_mul_left H (Real.sqrt 26) (scale_pos μ h).ne'
  rw [hthreshold] at hupper
  have hs : Real.sqrt (26 : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 26)).ne'
  have hcdf : (normalizedIidSumLaw μ 26).real (Iic (H / Real.sqrt 26)) =
      (MixtureSum.iidSumLaw (μ : Measure ℝ) 26).real (Iic H) := by
    rw [Reflection.normalized_closedCDF_eq_raw μ 26 (by decide) (H / Real.sqrt 26)]
    norm_num only [Nat.cast_ofNat]
    have harg : Real.sqrt (26 : ℝ) * (H / Real.sqrt 26) = H := by field_simp [hs]
    rw [harg]
  have hres : ConditionalResidual.positiveTargetResidual μ 26 (H / Real.sqrt 26) =
      (C - esseenConstant) * thirdAbsoluteMoment μ / Real.sqrt 26 := by
    unfold ConditionalResidual.positiveTargetResidual
    norm_num only [Nat.cast_ofNat]
    rw [hcdf]
    have ha := hm.attainment
    norm_num only [Nat.cast_ofNat] at ha
    rw [ha]
    ring
  have hnonneg : 0 ≤ ConditionalResidual.positiveTargetResidual μ 26 (H / Real.sqrt 26) := by
    rw [hres]
    exact div_nonneg (mul_nonneg (sub_nonneg.mpr hC)
      ((by norm_num : (0 : ℝ) ≤ 1).trans (Extremizer.thirdAbsoluteMoment_ge_one μ h)))
      (Real.sqrt_nonneg _)
  linarith only [hupper, hnonneg]

end BerryEsseen.P39ModeTailExclusion

#print axioms BerryEsseen.P39ModeTailExclusion.envelope_zero_upper
#print axioms BerryEsseen.P39ModeTailExclusion.envelope_one_upper
#print axioms BerryEsseen.P39ModeTailExclusion.envelope_phase_upper
#print axioms BerryEsseen.P39ModeTailExclusion.original_closedCDF_le_uniform
#print axioms BerryEsseen.P39ModeTailExclusion.original_residual_le_envelope
#print axioms BerryEsseen.P39ModeTailExclusion.original_count11_phase_upper
#print axioms BerryEsseen.P39ModeTailExclusion.original_not_height_interval
