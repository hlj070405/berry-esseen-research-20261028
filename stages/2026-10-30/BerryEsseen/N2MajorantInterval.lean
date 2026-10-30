module

public import BerryEsseen.N2MomentMajorant
public import BerryEsseen.ThirdMomentRegion
public import BerryEsseen.GaussianTools

@[expose] public section

/-! 2026-10-29: consume an original two-summand majorant on its whole
closed threshold interval, with the same law, moment price, and normalization. -/

noncomputable section

open MeasureTheory Set

namespace BerryEsseen.N2MajorantInterval

open N2MomentMajorant GaussianTools

/-- The upper CDF endpoint and lower Gaussian endpoint give the full original interval. -/
theorem original_interval (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (c : Coefficients) (R l u H ε L : ℝ)
    (hR : ∀ᵐ x ∂(μ : Measure ℝ), |x| ≤ R) (hH : H ∈ Icc l u)
    (hPointwise : ∀ x y : ℝ, |x| ≤ R → |y| ≤ R →
      closedIndicator u x y ≤ majorant c x y + ε)
    (hPrice : expected c (ZeroBias.gamma μ) (thirdAbsoluteMoment μ) + ε ≤
      Phi (l / Real.sqrt 2) + L * thirdAbsoluteMoment μ) :
    (MixtureSum.iidSumLaw (μ : Measure ℝ) 2).real (Iic H) - Phi (H / Real.sqrt 2) ≤
      L * thirdAbsoluteMoment μ := by
  let : IsProbabilityMeasure (MixtureSum.iidSumLaw (μ : Measure ℝ) 2) := by
    rw [MixtureSum.iidSumLaw_eq_convPower]
    simp only [MixtureSum.convPower]
    infer_instance
  have hF : (MixtureSum.iidSumLaw (μ : Measure ℝ) 2).real (Iic H) ≤
      (MixtureSum.iidSumLaw (μ : Measure ℝ) 2).real (Iic u) :=
    measureReal_mono (Iic_subset_Iic.mpr hH.2)
  have hb := closedCDF_le_expected_add_const μ h c R u ε hR hPointwise
  have harg : l / Real.sqrt 2 ≤ H / Real.sqrt 2 :=
    div_le_div_of_nonneg_right hH.1 (Real.sqrt_nonneg _)
  have hPhi : Phi (l / Real.sqrt 2) ≤ Phi (H / Real.sqrt 2) :=
    measureReal_mono (Iic_subset_Iic.mpr harg)
  linarith only [hF, hb, hPrice, hPhi]

/-- Strict coefficient slack transfers to the original Esseen cost using the actual positive moment. -/
theorem original_interval_esseen_strict (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (c : Coefficients) (R l u H ε L : ℝ)
    (hR : ∀ᵐ x ∂(μ : Measure ℝ), |x| ≤ R) (hH : H ∈ Icc l u)
    (hPointwise : ∀ x y : ℝ, |x| ≤ R → |y| ≤ R →
      closedIndicator u x y ≤ majorant c x y + ε)
    (hPrice : expected c (ZeroBias.gamma μ) (thirdAbsoluteMoment μ) + ε ≤
      Phi (l / Real.sqrt 2) + L * thirdAbsoluteMoment μ)
    (hL : L * Real.sqrt 2 < esseenConstant) :
    (MixtureSum.iidSumLaw (μ : Measure ℝ) 2).real (Iic H) - Phi (H / Real.sqrt 2) <
      esseenConstant * thirdAbsoluteMoment μ / Real.sqrt 2 := by
  have hs : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hc : L < esseenConstant / Real.sqrt 2 := (lt_div_iff₀ hs).mpr hL
  have hρ : 0 < thirdAbsoluteMoment μ :=
    lt_of_lt_of_le zero_lt_one (ThirdMomentRegion.one_le_third μ h)
  have hp := mul_lt_mul_of_pos_right hc hρ
  have hp' : L * thirdAbsoluteMoment μ <
      esseenConstant * thirdAbsoluteMoment μ / Real.sqrt 2 := by
    simpa only [div_mul_eq_mul_div] using hp
  exact (original_interval μ h c R l u H ε L hR hH hPointwise hPrice).trans_lt hp'

end BerryEsseen.N2MajorantInterval

#print axioms BerryEsseen.N2MajorantInterval.original_interval
#print axioms BerryEsseen.N2MajorantInterval.original_interval_esseen_strict
