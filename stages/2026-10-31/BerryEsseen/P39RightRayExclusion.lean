module

public import BerryEsseen.P39ModeTailExclusion

@[expose] public section

/-! 2026-10-30: the whole right ray for the original N26/P39 maximum.
Only the acquired total noise and actual third-moment floor are needed;
the CDF is bounded by one, with no reference law or count subdivision. -/

noncomputable section

open MeasureTheory Set

namespace BerryEsseen.P39RightRayExclusion

open CanonicalSign GaussianTools

theorem gaussian_right_gate : (917 : ℝ) / 1000 ≤ Phi (7 / 5) := by
  have hq : (917 : ℚ) / 1000 ≤ RationalGaussianPrices.PhiLower 8 (7 / 5) := by
    decide +kernel
  have hcast : (917 : ℝ) / 1000 ≤ (RationalGaussianPrices.PhiLower 8 (7 / 5) : ℝ) := by
    calc
      (917 : ℝ) / 1000 = (((917 : ℚ) / 1000 : ℚ) : ℝ) := by norm_num
      _ ≤ _ := Rat.cast_le.mpr hq
  exact hcast.trans (by simpa using (RationalGaussianPrices.Phi_rational_bounds 8 (7 / 5)).1)

theorem noise_argument_ge {p lambda : ℝ}
    (hp : p ∈ Icc (39 / 100 : ℝ) (2 / 5))
    (hl : lambda ∈ Icc (0 : ℝ) (17 / 50)) :
    (7 : ℝ) / 5 ≤ P39NoiseGate.noiseArgument p 14 lambda := by
  have hV0 := P39NoiseGate.actual_variance_pos hp hl.1
  have hV1 := (P39NoiseGate.variance_bounds hp).2
  have hs := Real.sqrt_pos.mpr hV0
  have hsq := Real.sq_sqrt hV0.le
  have hupper : Real.sqrt (26 * MomentBudgetNoise.variance p + lambda) ≤ (18 : ℝ) / 7 := by
    nlinarith only [hs.le, hsq, hV1, hl.2]
  unfold P39NoiseGate.noiseArgument
  apply (le_div_iff₀ hs).mpr
  nlinarith only [hupper, hp.2]

theorem positive_residual_right (μ : ProbabilityMeasure ℝ) (x : ℝ)
    (hx : (7 : ℝ) / 5 ≤ x) (hρ : (21 : ℝ) / 20 ≤ thirdAbsoluteMoment μ) :
    ConditionalResidual.positiveTargetResidual μ 26 x ≤ -(1 / 1000 : ℝ) := by
  have hF : (normalizedIidSumLaw μ 26).real (Iic x) ≤ 1 := measureReal_le_one
  have hPhi : Phi (7 / 5 : ℝ) ≤ Phi x := measureReal_mono (Iic_subset_Iic.mpr hx)
  have hρ0 : 0 ≤ thirdAbsoluteMoment μ := by linarith only [hρ]
  have hcost := mul_le_mul_of_nonneg_right P39NoiseGate.actual_cost_lower hρ0
  have hcharge : (2 / 25 : ℝ) * thirdAbsoluteMoment μ ≤
      esseenConstant * thirdAbsoluteMoment μ / Real.sqrt 26 := by
    simpa only [div_mul_eq_mul_div] using hcost
  unfold ConditionalResidual.positiveTargetResidual
  norm_num only [Nat.cast_ofNat]
  linarith only [hF, hPhi, gaussian_right_gate, hcharge, hρ]

theorem original_thirdMoment_floor (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (H C : ℝ) (hm : ContactVariation.PositiveClosedMaximum μ 26 H C)
    (hprev : Extremizer.fixedNSup 25 ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10)
    (hp : p μ ∈ Icc (39 / 100 : ℝ) (2 / 5)) :
    (21 : ℝ) / 20 ≤ thirdAbsoluteMoment μ := by
  have hr := P39CoarseNoiseIncrement.original_thirdMoment_ge_rho0_add_noise
    μ h H C hm hprev hC hρ hp
  have hb := P39Reference.rho0_floor hp
  have hs := noiseVariance_nonneg μ h
  linarith only [hr, hb, hs]

theorem original_threshold_ge (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (H C : ℝ) (hm : ContactVariation.PositiveClosedMaximum μ 26 H C)
    (hprev : Extremizer.fixedNSup 25 ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10)
    (hp : p μ ∈ Icc (39 / 100 : ℝ) (2 / 5))
    (hheight : (14 : ℝ) ≤ CentralGapConditionalIntegral.canonicalHeight μ h 26 H) :
    (7 : ℝ) / 5 ≤ H / Real.sqrt 26 := by
  have hl0 : 0 ≤ NoiseCoordinates.noiseLevel μ h 26 :=
    mul_nonneg (Nat.cast_nonneg 26) (noiseVariance_nonneg μ h)
  have hl1 := P39Count11VarianceAcquisition.original_noiseLevel_le μ h H C hm hprev hC hρ hp
  have ha := noise_argument_ge hp ⟨hl0, hl1⟩
  have he := P39FrozenNoise.canonical_threshold_eq_noiseArgument μ h 14 0
  norm_num only [Nat.cast_ofNat, add_zero] at he
  change ConditionalResidual.canonicalThreshold μ h 26 14 0 =
    P39NoiseGate.noiseArgument (p μ) 14 (NoiseCoordinates.noiseLevel μ h 26) at he
  rw [← he] at ha
  have hc : 0 < scale μ h * Real.sqrt (26 : ℝ) :=
    mul_pos (scale_pos μ h) (Real.sqrt_pos.mpr (by norm_num))
  have hnum : 14 - 26 * p μ ≤ scale μ h * H := by
    unfold CentralGapConditionalIntegral.canonicalHeight at hheight
    norm_num only [Nat.cast_ofNat] at hheight
    linarith only [hheight]
  have ht : ConditionalResidual.canonicalThreshold μ h 26 14 0 ≤ H / Real.sqrt 26 := by
    unfold ConditionalResidual.canonicalThreshold
    norm_num only [Nat.cast_ofNat, add_zero]
    calc
      _ ≤ (scale μ h * H) / (scale μ h * Real.sqrt 26) := div_le_div_of_nonneg_right hnum hc.le
      _ = _ := mul_div_mul_left H (Real.sqrt 26) (scale_pos μ h).ne'
  exact ha.trans ht

theorem original_height_lt_fourteen (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (H C : ℝ) (hm : ContactVariation.PositiveClosedMaximum μ 26 H C)
    (hprev : Extremizer.fixedNSup 25 ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10)
    (hp : p μ ∈ Icc (39 / 100 : ℝ) (2 / 5)) :
    CentralGapConditionalIntegral.canonicalHeight μ h 26 H < (14 : ℝ) := by
  by_contra hh
  have harg := original_threshold_ge μ h H C hm hprev hC hρ hp (le_of_not_gt hh)
  have hr := original_thirdMoment_floor μ h H C hm hprev hC hρ hp
  have hu := positive_residual_right μ (H / Real.sqrt 26) harg hr
  have hs : Real.sqrt (26 : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 26)).ne'
  have hcdf : (normalizedIidSumLaw μ 26).real (Iic (H / Real.sqrt 26)) =
      (MixtureSum.iidSumLaw (μ : Measure ℝ) 26).real (Iic H) := by
    rw [Reflection.normalized_closedCDF_eq_raw μ 26 (by decide) (H / Real.sqrt 26)]
    norm_num only [Nat.cast_ofNat]
    have harg' : Real.sqrt (26 : ℝ) * (H / Real.sqrt 26) = H := by field_simp [hs]
    rw [harg']
  unfold ConditionalResidual.positiveTargetResidual at hu
  norm_num only [Nat.cast_ofNat] at hu
  rw [hcdf] at hu
  have ha := hm.attainment
  norm_num only [Nat.cast_ofNat] at ha
  rw [ha] at hu
  have hρ0 : 0 ≤ thirdAbsoluteMoment μ := by linarith only [hr]
  have he : 0 ≤ (C - esseenConstant) * thirdAbsoluteMoment μ / Real.sqrt 26 :=
    div_nonneg (mul_nonneg (sub_nonneg.mpr hC) hρ0) (Real.sqrt_nonneg _)
  have heq : (C - esseenConstant) * thirdAbsoluteMoment μ / Real.sqrt 26 =
      C * thirdAbsoluteMoment μ / Real.sqrt 26 -
        esseenConstant * thirdAbsoluteMoment μ / Real.sqrt 26 := by ring
  rw [heq] at he
  linarith only [hu, he]

end BerryEsseen.P39RightRayExclusion

#print axioms BerryEsseen.P39RightRayExclusion.gaussian_right_gate
#print axioms BerryEsseen.P39RightRayExclusion.noise_argument_ge
#print axioms BerryEsseen.P39RightRayExclusion.positive_residual_right
#print axioms BerryEsseen.P39RightRayExclusion.original_thirdMoment_floor
#print axioms BerryEsseen.P39RightRayExclusion.original_threshold_ge
#print axioms BerryEsseen.P39RightRayExclusion.original_height_lt_fourteen
