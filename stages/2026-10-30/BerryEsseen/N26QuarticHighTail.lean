module

public import BerryEsseen.N26InitialFourierEnvelope

@[expose] public section

/-! 2026-10-30: a fixed quartic-CF band [.9,31/20] followed by the
complete inverse-cube tail to infinity. All prices concern the same actual
law. The resulting Fourier bound is not a bound on the conserved raw;
the latter also contains moment coefficients and an H-quadratic term. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open BerryEsseen.CharacteristicExpansion

namespace BerryEsseen.N26QuarticHighTail

def quarticTailPrice : ℝ :=
  (51 / 10) * ((18 / 25) ^ 13 * (50 / 81 - 200 / 961) + 200 / 961)

lemma quarticTailPrice_eq : quarticTailPrice =
    (312335239707468227436 : ℝ) / 286400318145751953125 := by
  norm_num [quarticTailPrice]

lemma quarticTailPrice_lt : quarticTailPrice < (11 : ℝ) / 10 := by
  norm_num [quarticTailPrice]

/-- The convex quartic polynomial is controlled on the entire squared
frequency interval by a secant with positive slope. -/
lemma quartic_polynomial_cap (z : ℝ)
    (hz0 : 81 / 100 ≤ z) (hz1 : z ≤ 961 / 400) :
    1 - z + (11 / 30 : ℝ) * z ^ 2 ≤ 18 / 25 := by
  have hp := mul_nonneg (sub_nonneg.mpr hz0) (sub_nonneg.mpr hz1)
  have hsec : z ^ 2 ≤ ((81 / 100 : ℝ) + 961 / 400) * z -
      (81 / 100 : ℝ) * (961 / 400) := by nlinarith only [hp]
  have hweight := mul_le_mul_of_nonneg_left hsec (by norm_num : (0 : ℝ) ≤ 11 / 30)
  have hlinear := mul_le_mul_of_nonneg_left hz1
    (by norm_num : (0 : ℝ) ≤ (11 / 30) * (81 / 100 + 961 / 400) - 1)
  nlinarith only [hweight, hlinear]

theorem norm_charFun_sq_le_band (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (h4 : Integrable (fun x : ℝ => x ^ 4) (μ : Measure ℝ))
    (hcap : moment μ 4 ≤ 7 / 5) (t : ℝ) (ht : t ∈ Icc (9 / 10 : ℝ) (31 / 20)) :
    ‖charFun (μ : Measure ℝ) t‖ ^ 2 ≤ (18 : ℝ) / 25 := by
  have ht0 : 0 ≤ t := by linarith only [ht.1]
  have hs0 := (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 9 / 10) ht0).mpr ht.1
  have hs1 := (sq_le_sq₀ ht0 (by norm_num : (0 : ℝ) ≤ 31 / 20)).mpr ht.2
  norm_num at hs0 hs1
  have hp := quartic_polynomial_cap (t ^ 2) hs0 hs1
  have hq := norm_charFun_sq_le_quartic μ h h4 t
  have hm := mul_le_mul_of_nonneg_right hcap (show (0 : ℝ) ≤ t ^ 4 by positivity)
  nlinarith only [hp, hq, hm]

/-- The original CF power is (|CF|²)^13; no sign or moment is substituted. -/
theorem norm_charFun_pow_le_band (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (h4 : Integrable (fun x : ℝ => x ^ 4) (μ : Measure ℝ))
    (hcap : moment μ 4 ≤ 7 / 5) (t : ℝ) (ht : t ∈ Icc (9 / 10 : ℝ) (31 / 20)) :
    ‖charFun (μ : Measure ℝ) t ^ 26‖ ≤ (18 / 25 : ℝ) ^ 13 := by
  have hpow := pow_le_pow_left₀ (sq_nonneg ‖charFun (μ : Measure ℝ) t‖)
    (norm_charFun_sq_le_band μ h h4 hcap t ht) 13
  rw [norm_pow]
  convert hpow using 1; ring

lemma inverse_cube_far_integral :
    (∫ t in Ioi (31 / 20 : ℝ), 1 / t ^ 3) = (200 : ℝ) / 961 := by
  have hi := integral_Ioi_rpow_of_lt (a := (-3 : ℝ)) (by norm_num)
    (c := (31 / 20 : ℝ)) (by norm_num)
  norm_num at hi
  simpa only [one_div] using hi

lemma inverse_cube_band_integral :
    (∫ t in Ioc HighFrequencyDamping.cutoff (31 / 20 : ℝ), 1 / t ^ 3) =
      (50 : ℝ) / 81 - 200 / 961 := by
  have hi := FourierSplit.integrableOn_inverse_cube_ray HighFrequencyDamping.cutoff
    (by norm_num [HighFrequencyDamping.cutoff])
  have hband := hi.mono_set
    (show Ioc HighFrequencyDamping.cutoff (31 / 20 : ℝ) ⊆ Ioi HighFrequencyDamping.cutoff from
      fun _ ht => ht.1)
  have hfar := FourierSplit.integrableOn_inverse_cube_ray (31 / 20 : ℝ) (by norm_num)
  have hs := setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hband hfar
  rw [Ioc_union_Ioi_eq_Ioi (by norm_num [HighFrequencyDamping.cutoff] :
    HighFrequencyDamping.cutoff ≤ (31 / 20 : ℝ)),
    N26InitialFourierEnvelope.inverse_cube_integral, inverse_cube_far_integral] at hs
  linarith only [hs]

lemma initialIntegrand_le_inverse_cube (μ : ProbabilityMeasure ℝ) (t : ℝ) (ht : 0 ≤ t) :
    HighFrequencyDamping.initialIntegrand μ 26 t ≤ 1 / t ^ 3 := by
  apply div_le_div_of_nonneg_right _ (pow_nonneg ht 3)
  rw [norm_pow]
  simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg _)
    (norm_charFun_le_one (μ := (μ : Measure ℝ)) t) 26

/-- The complete real infinite tail, including genuine L1 on both pieces. -/
theorem cf_tail_le_price (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (h4 : Integrable (fun x : ℝ => x ^ 4) (μ : Measure ℝ))
    (hcap : moment μ 4 ≤ 7 / 5) :
    Real.sqrt (26 : ℝ) * (∫ t in Ioi HighFrequencyDamping.cutoff,
      HighFrequencyDamping.initialIntegrand μ 26 t) ≤ quarticTailPrice := by
  have hc : 0 < HighFrequencyDamping.cutoff := by norm_num [HighFrequencyDamping.cutoff]
  have hi := FourierSplit.integrableOn_cfQuotient_ray μ 26 HighFrequencyDamping.cutoff hc
  have hband := hi.mono_set
    (show Ioc HighFrequencyDamping.cutoff (31 / 20 : ℝ) ⊆ Ioi HighFrequencyDamping.cutoff from
      fun _ ht => ht.1)
  have hfar := FourierSplit.integrableOn_cfQuotient_ray μ 26 (31 / 20 : ℝ) (by norm_num)
  have hinv := FourierSplit.integrableOn_inverse_cube_ray HighFrequencyDamping.cutoff hc
  have hinvBand := hinv.mono_set
    (show Ioc HighFrequencyDamping.cutoff (31 / 20 : ℝ) ⊆ Ioi HighFrequencyDamping.cutoff from
      fun _ ht => ht.1)
  have hinvFar := FourierSplit.integrableOn_inverse_cube_ray (31 / 20 : ℝ) (by norm_num)
  have hb : (∫ t in Ioc HighFrequencyDamping.cutoff (31 / 20 : ℝ),
      HighFrequencyDamping.initialIntegrand μ 26 t) ≤
      (18 / 25 : ℝ) ^ 13 * ((50 : ℝ) / 81 - 200 / 961) := by
    rw [← inverse_cube_band_integral, ← integral_const_mul]
    apply integral_mono_ae hband (hinvBand.const_mul ((18 / 25 : ℝ) ^ 13))
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ht0 : 0 < t := hc.trans ht.1
    have hp := norm_charFun_pow_le_band μ h h4 hcap t
      (by exact ⟨by simpa only [HighFrequencyDamping.cutoff] using ht.1.le, ht.2⟩)
    have hd := div_le_div_of_nonneg_right hp (pow_nonneg ht0.le 3)
    change ‖charFun (μ : Measure ℝ) t ^ 26‖ / t ^ 3 ≤ (18 / 25 : ℝ) ^ 13 * (1 / t ^ 3)
    convert hd using 1 <;> ring
  have hf : (∫ t in Ioi (31 / 20 : ℝ), HighFrequencyDamping.initialIntegrand μ 26 t) ≤
      (200 : ℝ) / 961 := by
    rw [← inverse_cube_far_integral]
    apply integral_mono_ae hfar hinvFar
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact initialIntegrand_le_inverse_cube μ t
      ((by norm_num : (0 : ℝ) ≤ 31 / 20).trans ht.le)
  have hsplit := setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hband hfar
  rw [Ioc_union_Ioi_eq_Ioi (by norm_num [HighFrequencyDamping.cutoff] :
    HighFrequencyDamping.cutoff ≤ (31 / 20 : ℝ))] at hsplit
  have htotal : (∫ t in Ioi HighFrequencyDamping.cutoff,
      HighFrequencyDamping.initialIntegrand μ 26 t) ≤
      (18 / 25 : ℝ) ^ 13 * ((50 : ℝ) / 81 - 200 / 961) + 200 / 961 := by
    rw [hsplit]
    exact add_le_add hb hf
  calc
    _ ≤ Real.sqrt (26 : ℝ) *
        ((18 / 25 : ℝ) ^ 13 * ((50 : ℝ) / 81 - 200 / 961) + 200 / 961) :=
      mul_le_mul_of_nonneg_left htotal (Real.sqrt_nonneg _)
    _ ≤ (51 / 10 : ℝ) *
        ((18 / 25 : ℝ) ^ 13 * ((50 : ℝ) / 81 - 200 / 961) + 200 / 961) :=
      mul_le_mul_of_nonneg_right N26InitialFourierEnvelope.sqrt_twenty_six_upper (by norm_num)
    _ = quarticTailPrice := rfl

/-- Support and rho acquire the actual fourth moment below 7/5. -/
theorem cf_tail_bound_of_support (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hs : (μ : Measure ℝ).support ⊆ Icc (-(12 / 5 : ℝ)) (12 / 5))
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) :
    IntegrableOn (HighFrequencyDamping.initialIntegrand μ 26) (Ioi HighFrequencyDamping.cutoff) ∧
      Real.sqrt (26 : ℝ) * (∫ t in Ioi HighFrequencyDamping.cutoff,
        HighFrequencyDamping.initialIntegrand μ 26 t) ≤ (11 : ℝ) / 10 := by
  have h4 := ConservedResource.integrable_pow_of_bounded_support μ (12 / 5) hs 4
  have hcap := (N26P39ResourceAcquisition.moment_caps_of_support μ h hs hρ).1
  rw [← moment_four_eq_abs] at hcap
  refine ⟨FourierSplit.integrableOn_cfQuotient_ray μ 26 HighFrequencyDamping.cutoff
    (by norm_num [HighFrequencyDamping.cutoff]), ?_⟩
  exact (cf_tail_le_price μ h h4 (by linarith only [hcap])).trans quarticTailPrice_lt.le

theorem fourier_envelope_of_support (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hs : (μ : Measure ℝ).support ⊆ Icc (-(12 / 5 : ℝ)) (12 / 5))
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) (H : ℝ) :
    IntegrableOn (FourierRemainder.originalIntegrand μ 26 H) (Ioi 0) ∧
      |FourierRemainder.value μ 26 H| ≤ (642 : ℝ) / 625 + (127 / 1500) * |H| := by
  refine ⟨FourierRemainder.integrable_originalIntegrand μ h 26 (by decide) H, ?_⟩
  have hb := N26InitialFourierEnvelope.value_le_of_support_and_tail μ h hs hρ H (11 / 10)
    (cf_tail_bound_of_support μ h hs hρ).2
  convert hb using 1; ring

theorem original_cf_tail (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (H C : ℝ) (hm : ContactVariation.PositiveClosedMaximum μ 26 H C)
    (hprev : Extremizer.fixedNSup 25 ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) :
    IntegrableOn (HighFrequencyDamping.initialIntegrand μ 26) (Ioi HighFrequencyDamping.cutoff) ∧
      Real.sqrt (26 : ℝ) * (∫ t in Ioi HighFrequencyDamping.cutoff,
        HighFrequencyDamping.initialIntegrand μ 26 t) ≤ (11 : ℝ) / 10 :=
  cf_tail_bound_of_support μ h
    (N26P39ResourceAcquisition.original_support μ h H C hm hprev hC hρ) hρ

theorem original_fourier_envelope (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (H C : ℝ) (hm : ContactVariation.PositiveClosedMaximum μ 26 H C)
    (hprev : Extremizer.fixedNSup 25 ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) :
    IntegrableOn (FourierRemainder.originalIntegrand μ 26 H) (Ioi 0) ∧
      |FourierRemainder.value μ 26 H| ≤ (642 : ℝ) / 625 + (127 / 1500) * |H| :=
  fourier_envelope_of_support μ h
    (N26P39ResourceAcquisition.original_support μ h H C hm hprev hC hρ) hρ H

end BerryEsseen.N26QuarticHighTail

#print axioms BerryEsseen.N26QuarticHighTail.norm_charFun_pow_le_band
#print axioms BerryEsseen.N26QuarticHighTail.inverse_cube_band_integral
#print axioms BerryEsseen.N26QuarticHighTail.cf_tail_le_price
#print axioms BerryEsseen.N26QuarticHighTail.cf_tail_bound_of_support
#print axioms BerryEsseen.N26QuarticHighTail.fourier_envelope_of_support
#print axioms BerryEsseen.N26QuarticHighTail.original_cf_tail
#print axioms BerryEsseen.N26QuarticHighTail.original_fourier_envelope
