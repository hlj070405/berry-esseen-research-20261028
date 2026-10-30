module

public import BerryEsseen.N26InitialLowFrequency
public import BerryEsseen.LowMomentGaussianBand
public import BerryEsseen.FourierSplit

@[expose] public section

/-! 2026-10-30: assembly of the literal N26 Fourier remainder, including
the comparator on the whole (.5,infinity) ray and the actual CF tail above
.9. The unconditional bound uses only |CF|≤1 in that tail and is coarse;
it is not the raw price or the numerical closure required for P39. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open BerryEsseen.CharacteristicExpansion BerryEsseen.HighFrequencyComparator

namespace BerryEsseen.N26InitialFourierEnvelope

lemma sqrt_twenty_six_upper : Real.sqrt (26 : ℝ) ≤ 51 / 10 := by
  nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 26), Real.sqrt_nonneg (26 : ℝ)]

lemma sqrt_twenty_six_lower : (5 : ℝ) ≤ Real.sqrt (26 : ℝ) := by
  nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 26), Real.sqrt_nonneg (26 : ℝ)]

/-- On the entire comparator ray, the inverse-cube Gaussian is dominated
by a genuine Gaussian primitive, rather than a finite-band price. -/
lemma gaussian_inverse_cube_le (t : ℝ) (ht : 1 / 2 ≤ t) :
    Real.exp (-13 * t ^ 2) / t ^ 3 ≤ 16 * (t * Real.exp (-13 * t ^ 2)) := by
  have ht0 : 0 < t := by linarith only [ht]
  apply (div_le_iff₀ (pow_pos ht0 3)).mpr
  have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) ht 4
  have hp := mul_le_mul_of_nonneg_left hpow (Real.exp_nonneg (-13 * t ^ 2))
  norm_num at hp
  simp only [← neg_mul] at hp
  nlinarith only [hp]

/-- Both original Gaussian-cubic terms are retained on (.5,infinity). -/
theorem comparator_cost_le (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) :
    Real.sqrt (26 : ℝ) * (∫ t in Ioi (1 / 2 : ℝ), comparatorQuotient μ 26 t) ≤
      (204 : ℝ) / 1625 + 901 / 25000 := by
  have hg := N26InitialLowFrequency.gamma_cap μ h hρ
  have hti : IntegrableOn (fun t : ℝ => t * Real.exp (-13 * t ^ 2)) (Ioi (1 / 2 : ℝ)) :=
    (integrable_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 13)).integrableOn
  have hi0 : IntegrableOn (fun t : ℝ => Real.exp (-13 * t ^ 2)) (Ioi (1 / 2 : ℝ)) :=
    (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 13)).integrableOn
  have hb : (∫ t in Ioi (1 / 2 : ℝ), comparatorQuotient μ 26 t) ≤
      16 * (∫ t in Ioi (1 / 2 : ℝ), t * Real.exp (-13 * t ^ 2)) +
        (689 / 300 : ℝ) * (∫ t in Ioi (1 / 2 : ℝ), Real.exp (-13 * t ^ 2)) := by
    calc
      _ ≤ ∫ t in Ioi (1 / 2 : ℝ),
          16 * (t * Real.exp (-13 * t ^ 2)) + (689 / 300 : ℝ) * Real.exp (-13 * t ^ 2) := by
        apply integral_mono_ae (integrableOn_comparatorQuotient μ 26 (by decide))
          ((hti.const_mul 16).add (hi0.const_mul (689 / 300)))
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have ht0 : 0 < t := lt_trans (by norm_num) ht
        have hm := quotient_le_majorant μ 26 t (53 / 100) ht0 hg
        norm_num at hm
        simp only [← neg_mul] at hm
        change comparatorQuotient μ 26 t ≤
          16 * (t * Real.exp (-13 * t ^ 2)) + (689 / 300 : ℝ) * Real.exp (-13 * t ^ 2)
        exact hm.trans (add_le_add (gaussian_inverse_cube_le t ht.le) le_rfl)
      _ = _ := by
        rw [integral_add (hti.const_mul 16) (hi0.const_mul (689 / 300)),
          integral_const_mul, integral_const_mul]
  have hfirst := integral_mul_gaussian_Ioi (13 : ℝ) (1 / 2) (by norm_num)
  have hsecond := gaussian_tail_le (13 : ℝ) (1 / 2) (by norm_num) (by norm_num)
  norm_num at hfirst hsecond
  simp only [← neg_mul, ← neg_div] at hfirst hsecond
  have hraw : (∫ t in Ioi (1 / 2 : ℝ), comparatorQuotient μ 26 t) ≤
      ((8 / 13 : ℝ) + 53 / 300) * Real.exp (-(13 : ℝ) / 4) := by
    rw [hfirst] at hb
    linarith only [hb, hsecond]
  have hpriced : (∫ t in Ioi (1 / 2 : ℝ), comparatorQuotient μ 26 t) ≤
      ((8 / 13 : ℝ) + 53 / 300) * (1 / 25) := by
    exact hraw.trans (mul_le_mul_of_nonneg_left
      LowMomentGaussianBand.exp_neg_thirteen_quarters_le (by norm_num))
  calc
    _ ≤ Real.sqrt (26 : ℝ) * (((8 / 13 : ℝ) + 53 / 300) * (1 / 25)) :=
      mul_le_mul_of_nonneg_left hpriced (Real.sqrt_nonneg _)
    _ ≤ (51 / 10 : ℝ) * (((8 / 13 : ℝ) + 53 / 300) * (1 / 25)) :=
      mul_le_mul_of_nonneg_right sqrt_twenty_six_upper (by norm_num)
    _ = _ := by norm_num

theorem comparator_cost_cap (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) :
    Real.sqrt (26 : ℝ) * (∫ t in Ioi (1 / 2 : ℝ), comparatorQuotient μ 26 t) ≤
      (81 : ℝ) / 500 :=
  (comparator_cost_le μ h hρ).trans (by norm_num)

/-- The exact infinite inverse-cube tail integral at the original cutoff. -/
lemma inverse_cube_integral :
    (∫ t in Ioi HighFrequencyDamping.cutoff, 1 / t ^ 3) = (50 : ℝ) / 81 := by
  have hi := integral_Ioi_rpow_of_lt (a := (-3 : ℝ)) (by norm_num)
    (c := (9 / 10 : ℝ)) (by norm_num)
  norm_num at hi
  simpa only [HighFrequencyDamping.cutoff, one_div] using hi

theorem cf_tail_nonneg (μ : ProbabilityMeasure ℝ) :
    0 ≤ Real.sqrt (26 : ℝ) * (∫ t in Ioi HighFrequencyDamping.cutoff,
      HighFrequencyDamping.initialIntegrand μ 26 t) := by
  apply mul_nonneg (Real.sqrt_nonneg _)
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 ≤ t := by norm_num [HighFrequencyDamping.cutoff] at ht; linarith only [ht]
  exact div_nonneg (norm_nonneg _) (pow_nonneg ht0 3)

/-- The genuine whole CF tail is finite and has this deliberately coarse
price using only the probability-law estimate |CF|≤1. -/
theorem cf_tail_coarse (μ : ProbabilityMeasure ℝ) :
    Real.sqrt (26 : ℝ) * (∫ t in Ioi HighFrequencyDamping.cutoff,
      HighFrequencyDamping.initialIntegrand μ 26 t) ≤ (85 : ℝ) / 27 := by
  have hc : 0 < HighFrequencyDamping.cutoff := by norm_num [HighFrequencyDamping.cutoff]
  have hb : (∫ t in Ioi HighFrequencyDamping.cutoff,
      HighFrequencyDamping.initialIntegrand μ 26 t) ≤
      ∫ t in Ioi HighFrequencyDamping.cutoff, 1 / t ^ 3 := by
    apply integral_mono_ae
      (FourierSplit.integrableOn_cfQuotient_ray μ 26 HighFrequencyDamping.cutoff hc)
      (FourierSplit.integrableOn_inverse_cube_ray HighFrequencyDamping.cutoff hc)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hn : ‖charFun (μ : Measure ℝ) t ^ 26‖ ≤ 1 := by
      rw [norm_pow]
      simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg _)
        (norm_charFun_le_one (μ := (μ : Measure ℝ)) t) 26
    exact div_le_div_of_nonneg_right hn (pow_nonneg (hc.trans ht).le 3)
  rw [inverse_cube_integral] at hb
  calc
    _ ≤ Real.sqrt (26 : ℝ) * (50 / 81) := mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg _)
    _ ≤ (51 / 10 : ℝ) * (50 / 81) :=
      mul_le_mul_of_nonneg_right sqrt_twenty_six_upper (by norm_num)
    _ = _ := by norm_num

lemma two_div_pi_cap : (2 : ℝ) / Real.pi ≤ 2 / 3 := by
  apply (div_le_iff₀ Real.pi_pos).mpr
  linarith only [Real.pi_gt_three]

lemma low_remainder_cap : (23 / 125 : ℝ) / Real.sqrt (26 : ℝ) ≤ 23 / 625 := by
  apply (div_le_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 26))).mpr
  linarith only [sqrt_twenty_six_lower]

lemma affine_constant_cap (T : ℝ) (hT : 0 ≤ T) :
    FourierSplit.KF 26 (29 / 250) (23 / 125) (63 / 500) T (81 / 500) ≤
      551 / 1875 + (2 / 3 : ℝ) * T := by
  unfold FourierSplit.KF
  calc
    _ ≤ (2 / 3 : ℝ) * (29 / 250 + (23 / 125) / Real.sqrt (26 : ℝ) +
        63 / 500 + T + 81 / 500) :=
      mul_le_mul_of_nonneg_right two_div_pi_cap (by positivity)
    _ ≤ (2 / 3 : ℝ) * (29 / 250 + 23 / 625 + 63 / 500 + T + 81 / 500) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      linarith only [low_remainder_cap]
    _ = _ := by ring

lemma affine_slope_cap : FourierSplit.sF (127 / 1000) ≤ (127 : ℝ) / 1500 := by
  unfold FourierSplit.sF
  apply (div_le_iff₀ Real.pi_pos).mpr
  linarith only [Real.pi_gt_three]

/-- Every non-tail price is proved. The sole additional price hypothesis
concerns the literal actual CF integral on the complete (.9,infinity) ray. -/
theorem value_le_of_support_and_tail (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hs : (μ : Measure ℝ).support ⊆ Icc (-(12 / 5 : ℝ)) (12 / 5))
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) (H T : ℝ)
    (htail : Real.sqrt (26 : ℝ) * (∫ t in Ioi HighFrequencyDamping.cutoff,
      HighFrequencyDamping.initialIntegrand μ 26 t) ≤ T) :
    |FourierRemainder.value μ 26 H| ≤
      551 / 1875 + (2 / 3 : ℝ) * T + (127 / 1500) * |H| := by
  have hT : 0 ≤ T := (cf_tail_nonneg μ).trans htail
  have hmiddle := LowMomentGaussianBand.initial_segment_cost_le_of_support μ h hs hρ
  have henvelope := FourierSplit.value_le_affine_envelope μ h 26 (by decide) H
    (29 / 250) (127 / 1000) (23 / 125) (63 / 500) T (81 / 500)
    (N26InitialLowFrequency.low_frequency_of_support μ h hs hρ H).2
    (hmiddle.trans (by norm_num)) htail (comparator_cost_cap μ h hρ)
  exact henvelope.trans (add_le_add (affine_constant_cap T hT)
    (mul_le_mul_of_nonneg_right affine_slope_cap (abs_nonneg H)))

/-- A complete, unconditional but coarse bound on the literal Fourier
remainder, together with absolute integrability of its original integrand. -/
theorem envelope_of_support (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hs : (μ : Measure ℝ).support ⊆ Icc (-(12 / 5 : ℝ)) (12 / 5))
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) (H : ℝ) :
    IntegrableOn (FourierRemainder.originalIntegrand μ 26 H) (Ioi 0) ∧
      |FourierRemainder.value μ 26 H| ≤ (12 : ℝ) / 5 + (17 / 200) * |H| := by
  refine ⟨FourierRemainder.integrable_originalIntegrand μ h 26 (by decide) H, ?_⟩
  have hb := value_le_of_support_and_tail μ h hs hρ H (85 / 27) (cf_tail_coarse μ)
  exact hb.trans (by nlinarith only [abs_nonneg H])

theorem original_value_le_of_tail (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (H C : ℝ) (hm : ContactVariation.PositiveClosedMaximum μ 26 H C)
    (hprev : Extremizer.fixedNSup 25 ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) (T : ℝ)
    (htail : Real.sqrt (26 : ℝ) * (∫ t in Ioi HighFrequencyDamping.cutoff,
      HighFrequencyDamping.initialIntegrand μ 26 t) ≤ T) :
    |FourierRemainder.value μ 26 H| ≤
      551 / 1875 + (2 / 3 : ℝ) * T + (127 / 1500) * |H| :=
  value_le_of_support_and_tail μ h
    (N26P39ResourceAcquisition.original_support μ h H C hm hprev hC hρ) hρ H T htail

/-- Original maximum/global-predecessor acquisition, without incoming
raw, defect, phase, moment, gamma, comparator or CF-tail numerical prices. -/
theorem original_envelope (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (H C : ℝ) (hm : ContactVariation.PositiveClosedMaximum μ 26 H C)
    (hprev : Extremizer.fixedNSup 25 ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) :
    IntegrableOn (FourierRemainder.originalIntegrand μ 26 H) (Ioi 0) ∧
      |FourierRemainder.value μ 26 H| ≤ (12 : ℝ) / 5 + (17 / 200) * |H| :=
  envelope_of_support μ h
    (N26P39ResourceAcquisition.original_support μ h H C hm hprev hC hρ) hρ H

end BerryEsseen.N26InitialFourierEnvelope

#print axioms BerryEsseen.N26InitialFourierEnvelope.comparator_cost_le
#print axioms BerryEsseen.N26InitialFourierEnvelope.inverse_cube_integral
#print axioms BerryEsseen.N26InitialFourierEnvelope.cf_tail_coarse
#print axioms BerryEsseen.N26InitialFourierEnvelope.value_le_of_support_and_tail
#print axioms BerryEsseen.N26InitialFourierEnvelope.envelope_of_support
#print axioms BerryEsseen.N26InitialFourierEnvelope.original_value_le_of_tail
#print axioms BerryEsseen.N26InitialFourierEnvelope.original_envelope
