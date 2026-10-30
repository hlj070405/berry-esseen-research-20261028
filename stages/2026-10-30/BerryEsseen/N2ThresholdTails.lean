module

public import BerryEsseen.UniversalCDFBound
public import BerryEsseen.RationalGaussianPrices
public import BerryEsseen.Extremizer

@[expose] public section

/-! 2026-10-29: analytic threshold tails for the positive original index-two
closed-CDF error. All atoms remain in Iic, and the raw threshold H is scaled
by sqrt 2 only through the proved actual-iid normalization identity. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open BerryEsseen.GaussianTools

namespace BerryEsseen.N2ThresholdTails

lemma normalized_closedCDF_at_raw (μ : ProbabilityMeasure ℝ) (H : ℝ) :
    (normalizedIidSumLaw μ 2).real (Iic (H / Real.sqrt 2)) =
      (MixtureSum.iidSumLaw (μ : Measure ℝ) 2).real (Iic H) := by
  have h := Reflection.normalized_closedCDF_eq_raw μ 2 (by norm_num) (H / Real.sqrt 2)
  have hs : Real.sqrt (2 : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  simpa only [Nat.cast_ofNat, mul_div_cancel₀ H hs] using h

/-- A single rational Taylor certificate for the actual Gaussian CDF. -/
theorem three_quarters_le_Phi_seven_tenths : (3 : ℝ) / 4 ≤ Phi (7 / 10) := by
  have hq : (3 : ℚ) / 4 ≤ RationalGaussianPrices.PhiLower 0 (7 / 10) := by
    norm_num [RationalGaussianPrices.PhiLower, RationalGaussianPrices.nonnegLower,
      RationalGaussianPrices.mulLower, RationalGaussianPrices.densityLower,
      RationalGaussianPrices.densityUpper, RationalGaussianPrices.rationalTaylor,
      RationalGaussianPrices.rationalError, Finset.sum_range_succ]
  have hc : (3 : ℝ) / 4 ≤ (RationalGaussianPrices.PhiLower 0 (7 / 10) : ℝ) := by
    calc
      (3 : ℝ) / 4 = (((3 : ℚ) / 4 : ℚ) : ℝ) := by norm_num
      _ ≤ _ := Rat.cast_le.mpr hq
  have harg : ((7 / 10 : ℚ) : ℝ) = (7 / 10 : ℝ) := by norm_num
  have hPhi : (RationalGaussianPrices.PhiLower 0 (7 / 10) : ℝ) ≤ Phi (7 / 10) := by
    simpa only [harg] using (RationalGaussianPrices.Phi_rational_bounds 0 (7 / 10)).1
  exact hc.trans hPhi

lemma seven_tenths_le_scaled (H : ℝ) (hH : 1 ≤ H) : (7 : ℝ) / 10 ≤ H / Real.sqrt 2 := by
  have hs0 : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hs : Real.sqrt (2 : ℝ) ≤ 10 / 7 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  apply (le_div_iff₀ hs0).mpr
  nlinarith only [hs, hH]

/-- Closed Cantelli on the actual normalized iid sum gives the raw two-summand price. -/
theorem raw_closedCDF_le_cantelli (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (H : ℝ) (hH : H ≤ 0) :
    (MixtureSum.iidSumLaw (μ : Measure ℝ) 2).real (Iic H) ≤ 2 / (2 + H ^ 2) := by
  obtain ⟨_, hi2, hm, hv⟩ := UniversalCDFBound.normalizedIidSumLaw_moments μ
    h.integrable_square h.mean_zero h.second_moment_one 2 (by norm_num)
  have hx : H / Real.sqrt 2 ≤ 0 := div_nonpos_of_nonpos_of_nonneg hH (Real.sqrt_nonneg _)
  have hc := UniversalCDFBound.closedCDF_neg_le_cantelli (normalizedIidSumLaw μ 2) hi2 hm hv
    (-(H / Real.sqrt 2)) (by linarith)
  simp only [neg_neg, neg_sq, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] at hc
  rw [normalized_closedCDF_at_raw μ H] at hc
  have heq : 1 / (1 + H ^ 2 / 2) = (2 : ℝ) / (2 + H ^ 2) := by
    field_simp [show (1 + H ^ 2 / 2 : ℝ) ≠ 0 by positivity,
      show (2 + H ^ 2 : ℝ) ≠ 0 by positivity]
  exact hc.trans_eq heq

theorem left_tail_rational (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (H : ℝ) (hH : H ≤ -9 / 4) :
    (MixtureSum.iidSumLaw (μ : Measure ℝ) 2).real (Iic H) - Phi (H / Real.sqrt 2) ≤ 32 / 113 := by
  have hCDF := raw_closedCDF_le_cantelli μ h H (by linarith)
  have hH2 : (81 : ℝ) / 16 ≤ H ^ 2 := by
    have hp := mul_nonneg (show 0 ≤ -H - 9 / 4 by linarith) (show 0 ≤ -H + 9 / 4 by linarith)
    nlinarith only [hp]
  have hprice : (2 : ℝ) / (2 + H ^ 2) ≤ 32 / 113 := by
    apply (div_le_iff₀ (show 0 < 2 + H ^ 2 by positivity)).mpr
    nlinarith only [hH2]
  have hPhi : 0 ≤ Phi (H / Real.sqrt 2) := measureReal_nonneg
  linarith only [hCDF, hprice, hPhi]

theorem right_tail_quarter (μ : ProbabilityMeasure ℝ) (H : ℝ) (hH : 1 ≤ H) :
    (MixtureSum.iidSumLaw (μ : Measure ℝ) 2).real (Iic H) - Phi (H / Real.sqrt 2) ≤ 1 / 4 := by
  have hF : (MixtureSum.iidSumLaw (μ : Measure ℝ) 2).real (Iic H) ≤ 1 := by
    rw [← normalized_closedCDF_at_raw μ H]
    exact measureReal_le_one
  have hP : Phi (7 / 10 : ℝ) ≤ Phi (H / Real.sqrt 2) :=
    measureReal_mono (Iic_subset_Iic.mpr (seven_tenths_le_scaled H hH))
  linarith only [hF, hP, three_quarters_le_Phi_seven_tenths]

/-- Every standardized law has its actual rho >= 1; there is no high-rho restriction. -/
theorem left_tail_two_sevenths_strict (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (H : ℝ) (hH : H ≤ -9 / 4) :
    (MixtureSum.iidSumLaw (μ : Measure ℝ) 2).real (Iic H) - Phi (H / Real.sqrt 2) <
      (2 : ℝ) / 7 * thirdAbsoluteMoment μ := by
  have hρ := Extremizer.thirdAbsoluteMoment_ge_one μ h
  have hp := mul_le_mul_of_nonneg_left hρ (by norm_num : (0 : ℝ) ≤ 2 / 7)
  have ht := left_tail_rational μ h H hH
  nlinarith only [hp, ht]

theorem right_tail_two_sevenths_strict (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (H : ℝ) (hH : 1 ≤ H) :
    (MixtureSum.iidSumLaw (μ : Measure ℝ) 2).real (Iic H) - Phi (H / Real.sqrt 2) <
      (2 : ℝ) / 7 * thirdAbsoluteMoment μ := by
  have hρ := Extremizer.thirdAbsoluteMoment_ge_one μ h
  have hp := mul_le_mul_of_nonneg_left hρ (by norm_num : (0 : ℝ) ≤ 2 / 7)
  have ht := right_tail_quarter μ H hH
  nlinarith only [hp, ht]

private lemma scaled_price_le_cap (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (C : ℝ)
    (hC : (2 : ℝ) / 7 * Real.sqrt 2 ≤ C) :
    (2 : ℝ) / 7 * thirdAbsoluteMoment μ ≤ C * thirdAbsoluteMoment μ / Real.sqrt 2 := by
  have hc : (2 : ℝ) / 7 ≤ C / Real.sqrt 2 :=
    (le_div_iff₀ (Real.sqrt_pos.mpr (by norm_num))).mpr hC
  have hρ0 : 0 ≤ thirdAbsoluteMoment μ := (show (0 : ℝ) ≤ 1 by norm_num).trans
    (Extremizer.thirdAbsoluteMoment_ge_one μ h)
  simpa only [div_mul_eq_mul_div] using mul_le_mul_of_nonneg_right hc hρ0

theorem left_tail_raw_cap (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (H C : ℝ)
    (hH : H ≤ -9 / 4) (hC : (2 : ℝ) / 7 * Real.sqrt 2 ≤ C) :
    (MixtureSum.iidSumLaw (μ : Measure ℝ) 2).real (Iic H) - Phi (H / Real.sqrt 2) <
      C * thirdAbsoluteMoment μ / Real.sqrt 2 :=
  (left_tail_two_sevenths_strict μ h H hH).trans_le (scaled_price_le_cap μ h C hC)

theorem right_tail_raw_cap (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (H C : ℝ)
    (hH : 1 ≤ H) (hC : (2 : ℝ) / 7 * Real.sqrt 2 ≤ C) :
    (MixtureSum.iidSumLaw (μ : Measure ℝ) 2).real (Iic H) - Phi (H / Real.sqrt 2) <
      C * thirdAbsoluteMoment μ / Real.sqrt 2 :=
  (right_tail_two_sevenths_strict μ h H hH).trans_le (scaled_price_le_cap μ h C hC)

theorem left_tail_esseen_strict (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (H : ℝ) (hH : H ≤ -9 / 4) :
    (MixtureSum.iidSumLaw (μ : Measure ℝ) 2).real (Iic H) - Phi (H / Real.sqrt 2) <
      esseenConstant * thirdAbsoluteMoment μ / Real.sqrt 2 :=
  left_tail_raw_cap μ h H esseenConstant hH UniversalCDFBound.two_sevenths_sqrt_two_lt_esseen.le

theorem right_tail_esseen_strict (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (H : ℝ) (hH : 1 ≤ H) :
    (MixtureSum.iidSumLaw (μ : Measure ℝ) 2).real (Iic H) - Phi (H / Real.sqrt 2) <
      esseenConstant * thirdAbsoluteMoment μ / Real.sqrt 2 :=
  right_tail_raw_cap μ h H esseenConstant hH UniversalCDFBound.two_sevenths_sqrt_two_lt_esseen.le

theorem positive_tail_raw_cap (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (H C : ℝ)
    (hH : H ≤ -9 / 4 ∨ 1 ≤ H) (hC : (2 : ℝ) / 7 * Real.sqrt 2 ≤ C) :
    (MixtureSum.iidSumLaw (μ : Measure ℝ) 2).real (Iic H) - Phi (H / Real.sqrt 2) <
      C * thirdAbsoluteMoment μ / Real.sqrt 2 := by
  rcases hH with hH | hH
  · exact left_tail_raw_cap μ h H C hH hC
  · exact right_tail_raw_cap μ h H C hH hC

/-- For this same law, a bound on the central interval extends to all raw
thresholds. The central estimate remains an explicit premise. -/
theorem per_law_positive_of_middle (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (L : ℝ) (hL : (2 : ℝ) / 7 ≤ L)
    (hmiddle : ∀ H ∈ Icc (-9 / 4 : ℝ) 1,
      (MixtureSum.iidSumLaw (μ : Measure ℝ) 2).real (Iic H) - Phi (H / Real.sqrt 2) ≤
        L * thirdAbsoluteMoment μ) :
    ∀ H, (MixtureSum.iidSumLaw (μ : Measure ℝ) 2).real (Iic H) - Phi (H / Real.sqrt 2) ≤
      L * thirdAbsoluteMoment μ := by
  intro H
  have hρ0 : 0 ≤ thirdAbsoluteMoment μ := (show (0 : ℝ) ≤ 1 by norm_num).trans
    (Extremizer.thirdAbsoluteMoment_ge_one μ h)
  have hpaid := mul_le_mul_of_nonneg_right hL hρ0
  by_cases hleft : H ≤ -9 / 4
  · exact (left_tail_two_sevenths_strict μ h H hleft).le.trans hpaid
  by_cases hright : 1 ≤ H
  · exact (right_tail_two_sevenths_strict μ h H hright).le.trans hpaid
  exact hmiddle H ⟨by linarith, by linarith⟩

/-- The remaining positive closed-CDF work is exactly the original central
threshold interval; this interface does not assert that its certificate passed. -/
theorem positiveRawClosedBound_of_middle (C : ℝ) (hC : (2 : ℝ) / 7 * Real.sqrt 2 ≤ C)
    (hmiddle : ∀ (μ : ProbabilityMeasure ℝ), StandardizedLaw μ → ∀ H ∈ Icc (-9 / 4 : ℝ) 1,
      (MixtureSum.iidSumLaw (μ : Measure ℝ) 2).real (Iic H) - Phi (H / Real.sqrt 2) ≤
        C * thirdAbsoluteMoment μ / Real.sqrt 2) : Reflection.PositiveRawClosedBound 2 C := by
  intro μ h H
  by_cases hleft : H ≤ -9 / 4
  · exact (left_tail_raw_cap μ h H C hleft hC).le
  by_cases hright : 1 ≤ H
  · exact (right_tail_raw_cap μ h H C hright hC).le
  exact hmiddle μ h H ⟨by linarith, by linarith⟩

end BerryEsseen.N2ThresholdTails

#print axioms BerryEsseen.N2ThresholdTails.three_quarters_le_Phi_seven_tenths
#print axioms BerryEsseen.N2ThresholdTails.raw_closedCDF_le_cantelli
#print axioms BerryEsseen.N2ThresholdTails.left_tail_two_sevenths_strict
#print axioms BerryEsseen.N2ThresholdTails.right_tail_two_sevenths_strict
#print axioms BerryEsseen.N2ThresholdTails.left_tail_esseen_strict
#print axioms BerryEsseen.N2ThresholdTails.right_tail_esseen_strict
#print axioms BerryEsseen.N2ThresholdTails.positive_tail_raw_cap
#print axioms BerryEsseen.N2ThresholdTails.per_law_positive_of_middle
#print axioms BerryEsseen.N2ThresholdTails.positiveRawClosedBound_of_middle
