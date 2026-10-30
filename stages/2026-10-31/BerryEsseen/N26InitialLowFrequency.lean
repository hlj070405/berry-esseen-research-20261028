module

public import BerryEsseen.N26P39ResourceAcquisition
public import BerryEsseen.LowFrequencyLeading
public import BerryEsseen.ThirdMomentRegion

@[expose] public section

/-! 2026-10-30: the first actual N26 low-frequency price, acquired from
the original law's support and rho. This only bounds I0 on (0,1/2]; it
does not supply the middle/high-frequency or complete Fourier price. -/

noncomputable section

open MeasureTheory Set
open BerryEsseen.CharacteristicExpansion BerryEsseen.LowFrequencyError
open BerryEsseen.LowFrequencyLeading

namespace BerryEsseen.N26InitialLowFrequency

theorem sixth_integrable_of_support (μ : ProbabilityMeasure ℝ)
    (hs : (μ : Measure ℝ).support ⊆ Icc (-(12 / 5 : ℝ)) (12 / 5)) :
    Integrable (fun x : ℝ => |x| ^ 6) (μ : Measure ℝ) :=
  ConservedResource.integrable_abs_pow_of_bounded_support μ (12 / 5) hs 6

theorem sixth_cap_of_support (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hs : (μ : Measure ℝ).support ⊆ Icc (-(12 / 5 : ℝ)) (12 / 5))
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) :
    sixthMoment μ ≤ (94566 : ℝ) / 18125 := by
  have h5 := ConservedResource.integrable_abs_pow_of_bounded_support μ (12 / 5) hs 5
  have hb : ∀ᵐ x ∂(μ : Measure ℝ), |x| ^ 6 ≤ (12 / 5 : ℝ) * |x| ^ 5 := by
    filter_upwards [(μ : Measure ℝ).support_mem_ae] with x hx
    have hp := mul_le_mul_of_nonneg_right (abs_le.mpr (hs hx))
      (pow_nonneg (abs_nonneg x) 5)
    simpa only [← pow_succ', show 5 + 1 = 6 by norm_num] using hp
  have hi := integral_mono_ae (sixth_integrable_of_support μ hs)
    (h5.const_mul (12 / 5)) hb
  rw [integral_const_mul] at hi
  have hm := (N26P39ResourceAcquisition.moment_caps_of_support μ h hs hρ).2
  change sixthMoment μ ≤ (12 / 5 : ℝ) * _ at hi
  linarith only [hi, hm]

/-- The sharp signed/absolute-third region supplies this conservative cap. -/
theorem gamma_cap (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) :
    |gamma μ| ≤ (53 : ℝ) / 100 := by
  have hr0 : 0 ≤ thirdAbsoluteMoment μ := integral_nonneg fun x =>
    pow_nonneg (abs_nonneg x) 3
  have hr2 : thirdAbsoluteMoment μ ^ 2 ≤ (121 : ℝ) / 100 := by
    have hh := (sq_le_sq₀ hr0 (by norm_num : (0 : ℝ) ≤ 11 / 10)).mpr hρ
    norm_num at hh
    exact hh
  have hregion := ThirdMomentRegion.signed_third_region μ h
  change (gamma μ ^ 2 + 2) ^ 2 ≤
    thirdAbsoluteMoment μ ^ 2 * (gamma μ ^ 2 + 4) at hregion
  have hw := mul_le_mul_of_nonneg_right hr2
    (show 0 ≤ gamma μ ^ 2 + 4 by positivity)
  have hg2 : gamma μ ^ 2 ≤ (2809 : ℝ) / 10000 := by
    by_contra hn
    have hgt : (2809 : ℝ) / 10000 < gamma μ ^ 2 := lt_of_not_ge hn
    have hp := mul_nonneg (sub_nonneg.mpr hgt.le)
      (show 0 ≤ gamma μ ^ 2 + (2809 : ℝ) / 10000 by positivity)
    nlinarith only [hregion, hw, hp]
  exact (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 53 / 100)).mp
    (by rw [sq_abs]; norm_num; exact hg2)

theorem fourth_lower_of_support (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hs : (μ : Measure ℝ).support ⊆ Icc (-(12 / 5 : ℝ)) (12 / 5)) :
    1 ≤ moment μ 4 := by
  have h4 := ConservedResource.integrable_pow_of_bounded_support μ (12 / 5) hs 4
  have h2 := h.integrable_square.const_mul (2 : ℝ)
  have h42 : Integrable (fun x : ℝ => x ^ 4 - 2 * x ^ 2) (μ : Measure ℝ) := h4.sub h2
  have hnonneg : 0 ≤ ∫ x : ℝ, x ^ 4 - 2 * x ^ 2 + 1 ∂(μ : Measure ℝ) := by
    apply integral_nonneg
    intro x
    change 0 ≤ x ^ 4 - 2 * x ^ 2 + 1
    nlinarith only [sq_nonneg (x ^ 2 - 1)]
  rw [integral_add h42 (integrable_const 1), integral_sub h4 h2,
    integral_const_mul, h.second_moment_one, integral_const, probReal_univ, one_smul] at hnonneg
  change 0 ≤ moment μ 4 - 2 * 1 + 1 at hnonneg
  linarith only [hnonneg]

theorem quartic_cap_of_support (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hs : (μ : Measure ℝ).support ⊆ Icc (-(12 / 5 : ℝ)) (12 / 5))
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) :
    |quarticCoeff μ| ≤ (1 : ℝ) / 12 := by
  have hlo := fourth_lower_of_support μ h hs
  have hhi := (N26P39ResourceAcquisition.moment_caps_of_support μ h hs hρ).1
  rw [← moment_four_eq_abs] at hhi
  unfold quarticCoeff
  rw [abs_le]
  constructor <;> linarith only [hlo, hhi]

theorem fifth_cap_of_support (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hs : (μ : Measure ℝ).support ⊆ Icc (-(12 / 5 : ℝ)) (12 / 5))
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) :
    |fifthCoeff μ| ≤ (63 : ℝ) / 1000 := by
  have hg := gamma_cap μ h hρ
  have hm := (N26P39ResourceAcquisition.moment_caps_of_support μ h hs hρ).2
  have hm5 : |moment μ 5| ≤ (15761 : ℝ) / 7250 := by
    calc
      _ ≤ ∫ x : ℝ, |x ^ 5| ∂(μ : Measure ℝ) := abs_integral_le_integral_abs
      _ = ∫ x : ℝ, |x| ^ 5 ∂(μ : Measure ℝ) :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => abs_pow x 5)
      _ ≤ _ := hm
  have hz := abs_sub (10 * gamma μ) (moment μ 5)
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 10)] at hz
  unfold fifthCoeff
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 120)]
  linarith only [hz, hg, hm5]

lemma gaussianMass_cap : gaussianMass ≤ (63 : ℝ) / 50 := by
  linarith only [gaussianMass_le]

lemma factorF_cap : factorF 26 ≤ (663 : ℝ) / 625 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 26)
  have hn := Real.sqrt_nonneg (26 : ℝ)
  have hu : Real.sqrt (26 : ℝ) ≤ 51 / 10 := by nlinarith only [hs, hn]
  have h25 : Real.sqrt (25 : ℝ) = 5 := by
    rw [show (25 : ℝ) = 5 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 5)]
  rw [factorF_eq 26 (by decide)]
  norm_num [h25]
  linarith only [hu]

lemma triangleL0_cap :
    triangleL0 26 (53 / 100) (1 / 12) (63 / 1000) (63 / 50) ≤ (29 : ℝ) / 250 := by
  unfold triangleL0
  nlinarith only [factorF_cap]

lemma triangleLH_cap :
    triangleLH 26 (53 / 100) (1 / 12) (63 / 50) ≤ (127 : ℝ) / 1000 := by
  unfold triangleLH
  nlinarith only [factorF_cap]

lemma coefficientL2_cap :
    coefficientL2 26 (1014 / 725) (53 / 100) (94566 / 18125) (1 / 12) (63 / 1000) ≤
      (23 : ℝ) / 125 := by
  norm_num [coefficientL2, sixthPrice, totalSixthPrice, rateA, rateB]

/-- All numerical inputs are consequences of this same original law.
The actual H is unrestricted and the actual I0 is absolutely integrable. -/
theorem low_frequency_of_support (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hs : (μ : Measure ℝ).support ⊆ Icc (-(12 / 5 : ℝ)) (12 / 5))
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) (H : ℝ) :
    IntegrableOn (lowIntegrand μ 26 H) (Ioc (0 : ℝ) (1 / 2)) ∧
      Real.sqrt (26 : ℝ) * I0 μ 26 H ≤
        29 / 250 + 127 / 1000 * |H| + (23 / 125) / Real.sqrt (26 : ℝ) := by
  have hM := (N26P39ResourceAcquisition.moment_caps_of_support μ h hs hρ).1
  rw [← moment_four_eq_abs] at hM
  have hc := low_frequency_triangle μ h (sixth_integrable_of_support μ hs) 26 (by decide)
    H (53 / 100) (1014 / 725) (94566 / 18125) (1 / 12) (63 / 1000) (63 / 50)
    (gamma_cap μ h hρ) (by norm_num) hM (by norm_num) (sixth_cap_of_support μ h hs hρ)
    (quartic_cap_of_support μ h hs hρ) (fifth_cap_of_support μ h hs hρ) gaussianMass_cap
  refine ⟨hc.1, hc.2.trans ?_⟩
  exact add_le_add
    (add_le_add triangleL0_cap (mul_le_mul_of_nonneg_right triangleLH_cap (abs_nonneg H)))
    (div_le_div_of_nonneg_right coefficientL2_cap (Real.sqrt_nonneg _))

/-- The literal signed imaginary quotient is L1 under the same assumptions. -/
theorem signed_integrable_of_support (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hs : (μ : Measure ℝ).support ⊆ Icc (-(12 / 5 : ℝ)) (12 / 5))
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) (H : ℝ) :
    IntegrableOn (fun t => (pureExp (-(H * t)) * actualV μ 26 t).im / t ^ 3)
      (Ioc (0 : ℝ) (1 / 2)) := by
  have hi := (low_frequency_of_support μ h hs hρ H).1
  have hm : Measurable (fun t => (pureExp (-(H * t)) * actualV μ 26 t).im / t ^ 3) := by
    have hf := measurable_actual_charFun μ
    unfold actualV gaussianComparator pureExp
    fun_prop
  apply hi.mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  simp only [Real.norm_eq_abs, abs_div, abs_of_nonneg (pow_nonneg ht.1.le 3), lowIntegrand]
  exact le_rfl

/-- The all-law N25 predecessor acquires the support before the I0 price.
There is no incoming defect/raw price or free numerical moment premise. -/
theorem original_low_frequency (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (H C : ℝ) (hm : ContactVariation.PositiveClosedMaximum μ 26 H C)
    (hprev : Extremizer.fixedNSup 25 ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) :
    IntegrableOn (lowIntegrand μ 26 H) (Ioc (0 : ℝ) (1 / 2)) ∧
      Real.sqrt (26 : ℝ) * I0 μ 26 H ≤
        29 / 250 + 127 / 1000 * |H| + (23 / 125) / Real.sqrt (26 : ℝ) :=
  low_frequency_of_support μ h
    (N26P39ResourceAcquisition.original_support μ h H C hm hprev hC hρ) hρ H

theorem original_signed_integrable (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (H C : ℝ) (hm : ContactVariation.PositiveClosedMaximum μ 26 H C)
    (hprev : Extremizer.fixedNSup 25 ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) :
    IntegrableOn (fun t => (pureExp (-(H * t)) * actualV μ 26 t).im / t ^ 3)
      (Ioc (0 : ℝ) (1 / 2)) :=
  signed_integrable_of_support μ h
    (N26P39ResourceAcquisition.original_support μ h H C hm hprev hC hρ) hρ H

end BerryEsseen.N26InitialLowFrequency

#print axioms BerryEsseen.N26InitialLowFrequency.gamma_cap
#print axioms BerryEsseen.N26InitialLowFrequency.sixth_cap_of_support
#print axioms BerryEsseen.N26InitialLowFrequency.low_frequency_of_support
#print axioms BerryEsseen.N26InitialLowFrequency.original_low_frequency
#print axioms BerryEsseen.N26InitialLowFrequency.original_signed_integrable
