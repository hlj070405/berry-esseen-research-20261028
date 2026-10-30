module

public import BerryEsseen.N26QuarticHighTail
public import BerryEsseen.ClassicalDamping

@[expose] public section

/-! 2026-10-30: the existing global cosine-cubic inequality controls the
actual CF on [.9,2] and [2,9/4] at rho <= 1.1.  Beyond 9/4 the complete
inverse-cube tail is retained, so genuine lattice CF peaks are allowed.
The tail estimate itself needs no bounded-support premise. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open BerryEsseen.CharacteristicExpansion

namespace BerryEsseen.N26CubicHighTail

def cubicPolynomial (t : ℝ) : ℝ := 1 - t ^ 2 + (21 / 50) * t ^ 3

def cubicTailPrice : ℝ :=
  (51 / 10) * ((1 / 2) ^ 13 * (50 / 81 - 1 / 8) +
    (3 / 4) ^ 13 * (1 / 8 - 8 / 81) + 8 / 81)

lemma cubicTailPrice_eq : cubicTailPrice =
    (4901308573 : ℝ) / 9663676416 := by
  norm_num [cubicTailPrice]

lemma cubicTailPrice_lt : cubicTailPrice < (127 : ℝ) / 250 := by
  norm_num [cubicTailPrice]

/-- Each certificate is the cubic's exact secant gap, plus a nonnegative
linear term.  It controls the entire interval, without sampled gates. -/
lemma cubic_polynomial_first_cap (t : ℝ)
    (ht0 : 9 / 10 ≤ t) (ht1 : t ≤ 2) :
    cubicPolynomial t ≤ (1 : ℝ) / 2 := by
  have hp : 0 ≤ (t - 9 / 10) * (2 - t) *
      ((21 / 50 : ℝ) * (t + 9 / 10 + 2) - 1) := by
    apply mul_nonneg (mul_nonneg (by linarith) (by linarith))
    linarith only [ht0]
  have hl : 0 ≤ (619 / 5000 : ℝ) * (t - 9 / 10) :=
    mul_nonneg (by norm_num) (by linarith only [ht0])
  dsimp only [cubicPolynomial]
  nlinarith only [hp, hl]

lemma cubic_polynomial_second_cap (t : ℝ)
    (ht0 : 2 ≤ t) (ht1 : t ≤ 9 / 4) :
    cubicPolynomial t ≤ (3 : ℝ) / 4 := by
  have hp : 0 ≤ (t - 2) * (9 / 4 - t) *
      ((21 / 50 : ℝ) * (t + 2 + 9 / 4) - 1) := by
    apply mul_nonneg (mul_nonneg (by linarith) (by linarith))
    linarith only [ht0]
  have hl : 0 ≤ (1157 / 800 : ℝ) * (9 / 4 - t) :=
    mul_nonneg (by norm_num) (by linarith only [ht1])
  dsimp only [cubicPolynomial]
  nlinarith only [hp, hl]

/-- The coefficient remains rho+1 from the true independent-difference
third absolute moment.  It is specialized at rho <= 11/10 only here. -/
theorem norm_charFun_sq_le_cubic (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10)
    (t : ℝ) (ht : 0 ≤ t) :
    ‖charFun (μ : Measure ℝ) t‖ ^ 2 ≤ cubicPolynomial t := by
  have hc := ClassicalDamping.charFun_norm_sq_le μ h t
  rw [abs_of_nonneg ht] at hc
  have hm := mul_le_mul_of_nonneg_right hρ (show (0 : ℝ) ≤ t ^ 3 by positivity)
  dsimp only [cubicPolynomial]
  nlinarith only [hc, hm]

theorem norm_charFun_sq_le_first_band (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10)
    (t : ℝ) (ht : t ∈ Icc (9 / 10 : ℝ) 2) :
    ‖charFun (μ : Measure ℝ) t‖ ^ 2 ≤ (1 : ℝ) / 2 := by
  exact (norm_charFun_sq_le_cubic μ h hρ t (by linarith only [ht.1])).trans
    (cubic_polynomial_first_cap t ht.1 ht.2)

theorem norm_charFun_sq_le_second_band (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10)
    (t : ℝ) (ht : t ∈ Icc (2 : ℝ) (9 / 4)) :
    ‖charFun (μ : Measure ℝ) t‖ ^ 2 ≤ (3 : ℝ) / 4 := by
  exact (norm_charFun_sq_le_cubic μ h hρ t (by linarith only [ht.1])).trans
    (cubic_polynomial_second_cap t ht.1 ht.2)

theorem norm_charFun_pow_le_first_band (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10)
    (t : ℝ) (ht : t ∈ Icc (9 / 10 : ℝ) 2) :
    ‖charFun (μ : Measure ℝ) t ^ 26‖ ≤ (1 / 2 : ℝ) ^ 13 := by
  have hp := pow_le_pow_left₀ (sq_nonneg ‖charFun (μ : Measure ℝ) t‖)
    (norm_charFun_sq_le_first_band μ h hρ t ht) 13
  rw [norm_pow]
  convert hp using 1; ring

theorem norm_charFun_pow_le_second_band (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10)
    (t : ℝ) (ht : t ∈ Icc (2 : ℝ) (9 / 4)) :
    ‖charFun (μ : Measure ℝ) t ^ 26‖ ≤ (3 / 4 : ℝ) ^ 13 := by
  have hp := pow_le_pow_left₀ (sq_nonneg ‖charFun (μ : Measure ℝ) t‖)
    (norm_charFun_sq_le_second_band μ h hρ t ht) 13
  rw [norm_pow]
  convert hp using 1; ring

lemma inverse_cube_two_integral :
    (∫ t in Ioi (2 : ℝ), 1 / t ^ 3) = (1 : ℝ) / 8 := by
  have hi := integral_Ioi_rpow_of_lt (a := (-3 : ℝ)) (by norm_num)
    (c := (2 : ℝ)) (by norm_num)
  norm_num at hi
  simpa only [one_div] using hi

lemma inverse_cube_far_integral :
    (∫ t in Ioi (9 / 4 : ℝ), 1 / t ^ 3) = (8 : ℝ) / 81 := by
  have hi := integral_Ioi_rpow_of_lt (a := (-3 : ℝ)) (by norm_num)
    (c := (9 / 4 : ℝ)) (by norm_num)
  norm_num at hi
  simpa only [one_div] using hi

lemma inverse_cube_first_band_integral :
    (∫ t in Ioc HighFrequencyDamping.cutoff (2 : ℝ), 1 / t ^ 3) =
      (50 : ℝ) / 81 - 1 / 8 := by
  have hi := FourierSplit.integrableOn_inverse_cube_ray HighFrequencyDamping.cutoff
    (by norm_num [HighFrequencyDamping.cutoff])
  have hb := hi.mono_set
    (show Ioc HighFrequencyDamping.cutoff (2 : ℝ) ⊆ Ioi HighFrequencyDamping.cutoff from
      fun _ ht => ht.1)
  have hf := FourierSplit.integrableOn_inverse_cube_ray (2 : ℝ) (by norm_num)
  have hs := setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hb hf
  rw [Ioc_union_Ioi_eq_Ioi (by norm_num [HighFrequencyDamping.cutoff] :
    HighFrequencyDamping.cutoff ≤ (2 : ℝ)),
    N26InitialFourierEnvelope.inverse_cube_integral, inverse_cube_two_integral] at hs
  linarith only [hs]

lemma inverse_cube_second_band_integral :
    (∫ t in Ioc (2 : ℝ) (9 / 4), 1 / t ^ 3) = (1 : ℝ) / 8 - 8 / 81 := by
  have hi := FourierSplit.integrableOn_inverse_cube_ray (2 : ℝ) (by norm_num)
  have hb := hi.mono_set (show Ioc (2 : ℝ) (9 / 4) ⊆ Ioi (2 : ℝ) from
    fun _ ht => ht.1)
  have hf := FourierSplit.integrableOn_inverse_cube_ray (9 / 4 : ℝ) (by norm_num)
  have hs := setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hb hf
  rw [Ioc_union_Ioi_eq_Ioi (by norm_num : (2 : ℝ) ≤ 9 / 4),
    inverse_cube_two_integral, inverse_cube_far_integral] at hs
  linarith only [hs]

/-- The same actual CF is integrated on both fixed bands and on the
entire remaining ray.  Each term has genuine L1 before comparison. -/
theorem cf_tail_le_price (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) :
    Real.sqrt (26 : ℝ) * (∫ t in Ioi HighFrequencyDamping.cutoff,
      HighFrequencyDamping.initialIntegrand μ 26 t) ≤ cubicTailPrice := by
  have hc : 0 < HighFrequencyDamping.cutoff := by norm_num [HighFrequencyDamping.cutoff]
  have hi := FourierSplit.integrableOn_cfQuotient_ray μ 26 HighFrequencyDamping.cutoff hc
  have hfirst := hi.mono_set
    (show Ioc HighFrequencyDamping.cutoff (2 : ℝ) ⊆ Ioi HighFrequencyDamping.cutoff from
      fun _ ht => ht.1)
  have htwo := FourierSplit.integrableOn_cfQuotient_ray μ 26 (2 : ℝ) (by norm_num)
  have hsecond := htwo.mono_set
    (show Ioc (2 : ℝ) (9 / 4) ⊆ Ioi (2 : ℝ) from fun _ ht => ht.1)
  have hfar := FourierSplit.integrableOn_cfQuotient_ray μ 26 (9 / 4 : ℝ) (by norm_num)
  have hinv := FourierSplit.integrableOn_inverse_cube_ray HighFrequencyDamping.cutoff hc
  have hinvFirst := hinv.mono_set
    (show Ioc HighFrequencyDamping.cutoff (2 : ℝ) ⊆ Ioi HighFrequencyDamping.cutoff from
      fun _ ht => ht.1)
  have hinvTwo := FourierSplit.integrableOn_inverse_cube_ray (2 : ℝ) (by norm_num)
  have hinvSecond := hinvTwo.mono_set
    (show Ioc (2 : ℝ) (9 / 4) ⊆ Ioi (2 : ℝ) from fun _ ht => ht.1)
  have hinvFar := FourierSplit.integrableOn_inverse_cube_ray (9 / 4 : ℝ) (by norm_num)
  have hb1 : (∫ t in Ioc HighFrequencyDamping.cutoff (2 : ℝ),
      HighFrequencyDamping.initialIntegrand μ 26 t) ≤
      (1 / 2 : ℝ) ^ 13 * ((50 : ℝ) / 81 - 1 / 8) := by
    rw [← inverse_cube_first_band_integral, ← integral_const_mul]
    apply integral_mono_ae hfirst (hinvFirst.const_mul ((1 / 2 : ℝ) ^ 13))
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ht0 : 0 < t := hc.trans ht.1
    have hp := norm_charFun_pow_le_first_band μ h hρ t
      (by exact ⟨by simpa only [HighFrequencyDamping.cutoff] using ht.1.le, ht.2⟩)
    have hd := div_le_div_of_nonneg_right hp (pow_nonneg ht0.le 3)
    change ‖charFun (μ : Measure ℝ) t ^ 26‖ / t ^ 3 ≤ (1 / 2 : ℝ) ^ 13 * (1 / t ^ 3)
    convert hd using 1 <;> ring
  have hb2 : (∫ t in Ioc (2 : ℝ) (9 / 4),
      HighFrequencyDamping.initialIntegrand μ 26 t) ≤
      (3 / 4 : ℝ) ^ 13 * ((1 : ℝ) / 8 - 8 / 81) := by
    rw [← inverse_cube_second_band_integral, ← integral_const_mul]
    apply integral_mono_ae hsecond (hinvSecond.const_mul ((3 / 4 : ℝ) ^ 13))
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ht0 : 0 < t := lt_trans (by norm_num : (0 : ℝ) < 2) ht.1
    have hp := norm_charFun_pow_le_second_band μ h hρ t ⟨ht.1.le, ht.2⟩
    have hd := div_le_div_of_nonneg_right hp (pow_nonneg ht0.le 3)
    change ‖charFun (μ : Measure ℝ) t ^ 26‖ / t ^ 3 ≤ (3 / 4 : ℝ) ^ 13 * (1 / t ^ 3)
    convert hd using 1 <;> ring
  have hf : (∫ t in Ioi (9 / 4 : ℝ), HighFrequencyDamping.initialIntegrand μ 26 t) ≤
      (8 : ℝ) / 81 := by
    rw [← inverse_cube_far_integral]
    apply integral_mono_ae hfar hinvFar
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact N26QuarticHighTail.initialIntegrand_le_inverse_cube μ t
      ((by norm_num : (0 : ℝ) ≤ 9 / 4).trans ht.le)
  have hsplit1 := setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hfirst htwo
  rw [Ioc_union_Ioi_eq_Ioi (by norm_num [HighFrequencyDamping.cutoff] :
    HighFrequencyDamping.cutoff ≤ (2 : ℝ))] at hsplit1
  have hsplit2 := setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hsecond hfar
  rw [Ioc_union_Ioi_eq_Ioi (by norm_num : (2 : ℝ) ≤ 9 / 4)] at hsplit2
  have htotal : (∫ t in Ioi HighFrequencyDamping.cutoff,
      HighFrequencyDamping.initialIntegrand μ 26 t) ≤
      (1 / 2 : ℝ) ^ 13 * ((50 : ℝ) / 81 - 1 / 8) +
        (3 / 4 : ℝ) ^ 13 * ((1 : ℝ) / 8 - 8 / 81) + 8 / 81 := by
    rw [hsplit1, hsplit2]
    linarith only [hb1, hb2, hf]
  calc
    _ ≤ Real.sqrt (26 : ℝ) *
        ((1 / 2 : ℝ) ^ 13 * ((50 : ℝ) / 81 - 1 / 8) +
          (3 / 4 : ℝ) ^ 13 * ((1 : ℝ) / 8 - 8 / 81) + 8 / 81) :=
      mul_le_mul_of_nonneg_left htotal (Real.sqrt_nonneg _)
    _ ≤ (51 / 10 : ℝ) *
        ((1 / 2 : ℝ) ^ 13 * ((50 : ℝ) / 81 - 1 / 8) +
          (3 / 4 : ℝ) ^ 13 * ((1 : ℝ) / 8 - 8 / 81) + 8 / 81) :=
      mul_le_mul_of_nonneg_right N26InitialFourierEnvelope.sqrt_twenty_six_upper (by norm_num)
    _ = cubicTailPrice := rfl

theorem cf_tail_bound (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) :
    IntegrableOn (HighFrequencyDamping.initialIntegrand μ 26) (Ioi HighFrequencyDamping.cutoff) ∧
      Real.sqrt (26 : ℝ) * (∫ t in Ioi HighFrequencyDamping.cutoff,
        HighFrequencyDamping.initialIntegrand μ 26 t) ≤ (127 : ℝ) / 250 := by
  refine ⟨FourierSplit.integrableOn_cfQuotient_ray μ 26 HighFrequencyDamping.cutoff
    (by norm_num [HighFrequencyDamping.cutoff]), ?_⟩
  exact (cf_tail_le_price μ h hρ).trans cubicTailPrice_lt.le

lemma fourier_intercept_cap :
    (551 : ℝ) / 1875 + (2 / 3) * cubicTailPrice ≤ 79 / 125 := by
  norm_num [cubicTailPrice]

theorem fourier_envelope_of_support (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hs : (μ : Measure ℝ).support ⊆ Icc (-(12 / 5 : ℝ)) (12 / 5))
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) (H : ℝ) :
    IntegrableOn (FourierRemainder.originalIntegrand μ 26 H) (Ioi 0) ∧
      |FourierRemainder.value μ 26 H| ≤ (79 : ℝ) / 125 + (127 / 1500) * |H| := by
  refine ⟨FourierRemainder.integrable_originalIntegrand μ h 26 (by decide) H, ?_⟩
  have hb := N26InitialFourierEnvelope.value_le_of_support_and_tail μ h hs hρ H
    cubicTailPrice (cf_tail_le_price μ h hρ)
  linarith only [hb, fourier_intercept_cap]

/-- The original-law tail estimate is stronger than required: its support
and contact hypotheses are unnecessary once standardization and rho hold. -/
theorem original_cf_tail (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (H C : ℝ) (hm : ContactVariation.PositiveClosedMaximum μ 26 H C)
    (hprev : Extremizer.fixedNSup 25 ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) :
    IntegrableOn (HighFrequencyDamping.initialIntegrand μ 26) (Ioi HighFrequencyDamping.cutoff) ∧
      Real.sqrt (26 : ℝ) * (∫ t in Ioi HighFrequencyDamping.cutoff,
        HighFrequencyDamping.initialIntegrand μ 26 t) ≤ (127 : ℝ) / 250 :=
  cf_tail_bound μ h hρ

theorem original_fourier_envelope (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (H C : ℝ) (hm : ContactVariation.PositiveClosedMaximum μ 26 H C)
    (hprev : Extremizer.fixedNSup 25 ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) :
    IntegrableOn (FourierRemainder.originalIntegrand μ 26 H) (Ioi 0) ∧
      |FourierRemainder.value μ 26 H| ≤ (79 : ℝ) / 125 + (127 / 1500) * |H| :=
  fourier_envelope_of_support μ h
    (N26P39ResourceAcquisition.original_support μ h H C hm hprev hC hρ) hρ H

end BerryEsseen.N26CubicHighTail

#print axioms BerryEsseen.N26CubicHighTail.norm_charFun_sq_le_cubic
#print axioms BerryEsseen.N26CubicHighTail.norm_charFun_pow_le_first_band
#print axioms BerryEsseen.N26CubicHighTail.norm_charFun_pow_le_second_band
#print axioms BerryEsseen.N26CubicHighTail.cf_tail_le_price
#print axioms BerryEsseen.N26CubicHighTail.cf_tail_bound
#print axioms BerryEsseen.N26CubicHighTail.fourier_envelope_of_support
#print axioms BerryEsseen.N26CubicHighTail.original_cf_tail
#print axioms BerryEsseen.N26CubicHighTail.original_fourier_envelope
