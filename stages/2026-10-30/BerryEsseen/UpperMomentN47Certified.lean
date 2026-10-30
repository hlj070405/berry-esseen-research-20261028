module

public import BerryEsseen.UpperMomentN47FirstIntegral
public import BerryEsseen.UpperMomentN47RemainingIntegrals
public import BerryEsseen.UpperMomentN47Budget

@[expose] public section

/-! 2026-10-30: the fixed n47 upper-moment certificate, joined to the
original closed CDF. The three finite integrals use kernel-checked rows;
the genuine infinite Gaussian tail uses a short analytic rational bound.
This proves the stated moment band, not the all-n conjecture. -/

noncomputable section

open MeasureTheory Set

namespace BerryEsseen.UpperMomentN47Certified

open UpperMomentN47Budget (U L A V s)

theorem profile_lt :
    UpperMomentAbsoluteProfile.profile U (UpperMomentDamping.G U U) A V s < 533 / 5000 := by
  apply UpperMomentN47Budget.profile_lt_of_rows
  · have hh := UpperMomentN47FirstIntegral.first_integral_le
    norm_num only [UpperMomentN47IntegralChecks.row1_sum, Int.cast_ofNat] at hh ⊢
    exact hh
  · have hh := UpperMomentN47RemainingIntegrals.actual_second_integral_le_rows
    norm_num only [UpperMomentN47IntegralChecks.row2_sum, Int.cast_ofNat] at hh ⊢
    exact hh
  · have hh := UpperMomentN47RemainingIntegrals.actual_third_integral_le_rows
    norm_num only [UpperMomentN47IntegralChecks.row3_sum, Int.cast_ofNat] at hh ⊢
    exact hh

theorem actual_cdf_lt (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hρ : thirdAbsoluteMoment μ ≤ U) (x : ℝ) :
    |(normalizedIidSumLaw μ 47).real (Iic x) - GaussianTools.Phi x| < 533 / 5000 :=
  UpperMomentN47Budget.actual_cdf_lt_of_profile μ h hρ profile_lt x

/-- The original high INITIAL-grid left endpoint keeps the stronger
coefficient 0.405. The lower moment enters only after the absolute price. -/
theorem actual_cdf_lt_405 (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hρ : thirdAbsoluteMoment μ ≤ U) (hL : L ≤ thirdAbsoluteMoment μ) (x : ℝ) :
    |(normalizedIidSumLaw μ 47).real (Iic x) - GaussianTools.Phi x| <
      (81 / 200) * thirdAbsoluteMoment μ / Real.sqrt 47 :=
  UpperMomentN47Budget.actual_cdf_lt_405_of_profile μ h hρ hL profile_lt x

/-- A simple wider moment band follows from the same absolute price,
with no new numerical evaluation. -/
theorem actual_cdf_lt_407 (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hρ : thirdAbsoluteMoment μ ≤ U) (hL : (9 / 5 : ℝ) ≤ thirdAbsoluteMoment μ) (x : ℝ) :
    |(normalizedIidSumLaw μ 47).real (Iic x) - GaussianTools.Phi x| <
      (407 / 1000) * thirdAbsoluteMoment μ / Real.sqrt 47 := by
  have hr : 0 < Real.sqrt (47 : ℝ) := by positivity
  have hh := mul_lt_mul_of_pos_left (actual_cdf_lt μ h hρ x) hr
  have hb : Real.sqrt (47 : ℝ) * (533 / 5000) < (407 / 1000) * (9 / 5) := by
    apply (mul_le_mul_of_nonneg_right UpperMomentN47Budget.sqrt47_le
      (by norm_num : (0 : ℝ) ≤ 533 / 5000)).trans_lt
    norm_num
  have hl := mul_le_mul_of_nonneg_left hL (by norm_num : (0 : ℝ) ≤ 407 / 1000)
  apply (lt_div_iff₀ hr).mpr
  simpa only [mul_comm] using hh.trans (hb.trans_le hl)

/-- Same-law, all real thresholds, closed CDF, arbitrary support: the
original Esseen target at n47 on 9/5 <= rho <= 7361/4000. -/
theorem sharp_on_moment_band (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hρ : thirdAbsoluteMoment μ ≤ U) (hL : (9 / 5 : ℝ) ≤ thirdAbsoluteMoment μ) (x : ℝ) :
    |(normalizedIidSumLaw μ 47).real (Iic x) - GaussianTools.Phi x| <
      esseenConstant * thirdAbsoluteMoment μ / Real.sqrt 47 := by
  have htarget : (407 : ℝ) / 1000 < esseenConstant :=
    lt_trans (by norm_num : (407 : ℝ) / 1000 < 4097 / 10000)
      FiniteHighMomentTails.target4097_lt_esseen
  have hρ0 : 0 < thirdAbsoluteMoment μ := (by norm_num : (0 : ℝ) < 9 / 5).trans_le hL
  have hp := div_pos hρ0 (by positivity : (0 : ℝ) < Real.sqrt 47)
  have hb := mul_lt_mul_of_pos_right htarget hp
  have he : ∀ c : ℝ, c * (thirdAbsoluteMoment μ / Real.sqrt 47) =
      c * thirdAbsoluteMoment μ / Real.sqrt 47 := by intro c; ring
  simp_rw [he] at hb
  exact (actual_cdf_lt_407 μ h hρ hL x).trans hb

end BerryEsseen.UpperMomentN47Certified

#print axioms BerryEsseen.UpperMomentN47Certified.profile_lt
#print axioms BerryEsseen.UpperMomentN47Certified.actual_cdf_lt
#print axioms BerryEsseen.UpperMomentN47Certified.actual_cdf_lt_405
#print axioms BerryEsseen.UpperMomentN47Certified.sharp_on_moment_band
