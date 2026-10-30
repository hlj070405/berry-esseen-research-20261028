module

public import BerryEsseen.P39RightRayExclusion

@[expose] public section

/-! 2026-10-30: localize the original N26/P39 threshold using the
acquired phase and total noise, without a count cover or support profile. -/

noncomputable section

open MeasureTheory Set

namespace BerryEsseen.P39HeightLocalization

open CanonicalSign

theorem original_height_gt_half_seventeen (μ : ProbabilityMeasure ℝ)
    (h : StandardizedLaw μ) (H C : ℝ)
    (hm : ContactVariation.PositiveClosedMaximum μ 26 H C)
    (hprev : Extremizer.fixedNSup 25 ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10)
    (hp : p μ ∈ Icc (39 / 100 : ℝ) (2 / 5)) :
    (17 : ℝ) / 2 < CentralGapConditionalIntegral.canonicalHeight μ h 26 H := by
  have hs := P39Count11VarianceAcquisition.original_noiseVariance_le
    μ h H C hm hprev hC hρ hp
  have hpq := (P39NoiseGate.variance_bounds hp).2
  change p μ * q μ ≤ (6 : ℝ) / 25 at hpq
  have hc2 := CanonicalSign.scale_sq μ h
  have hc0 := scale_pos μ h
  have hc : scale μ h ≤ (63 : ℝ) / 125 := by
    nlinarith only [hs, hpq, hc2, hc0]
  have he := UniformLowMomentRawAcquisition.original_phase_lower_bound
    μ h 26 (by decide) H C hm hprev hC hρ
  have hH2 := CanonicalHeightLocalization.threshold_square_le_of_phase 26 (by decide) H he
  norm_num only [Nat.cast_ofNat] at hH2
  have hH : |H| ≤ (13 : ℝ) / 4 := by
    have hsq := sq_abs H
    nlinarith only [hH2, hsq, abs_nonneg H]
  have hmul := mul_le_mul hc hH (abs_nonneg H) (by norm_num : (0 : ℝ) ≤ 63 / 125)
  have habs : |scale μ h * H| ≤ (819 : ℝ) / 500 := by
    rw [abs_mul, abs_of_pos hc0]
    nlinarith only [hmul]
  have hlo := (abs_le.mp habs).1
  unfold CentralGapConditionalIntegral.canonicalHeight
  norm_num only [Nat.cast_ofNat]
  linarith only [hlo, hp.1]

theorem original_height_window (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (H C : ℝ) (hm : ContactVariation.PositiveClosedMaximum μ 26 H C)
    (hprev : Extremizer.fixedNSup 25 ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10)
    (hp : p μ ∈ Icc (39 / 100 : ℝ) (2 / 5)) :
    CentralGapConditionalIntegral.canonicalHeight μ h 26 H ∈ Ioo (17 / 2 : ℝ) 14 :=
  ⟨original_height_gt_half_seventeen μ h H C hm hprev hC hρ hp,
    P39RightRayExclusion.original_height_lt_fourteen μ h H C hm hprev hC hρ hp⟩

end BerryEsseen.P39HeightLocalization

#print axioms BerryEsseen.P39HeightLocalization.original_height_gt_half_seventeen
#print axioms BerryEsseen.P39HeightLocalization.original_height_window
