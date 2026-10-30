module

public import BerryEsseen.UniversalCDFBound

@[expose] public section

/-! 2026-10-30: the exact rational targets and infinite moment tails used
by the independent n=3, n=4 and n=5 reconstruction. The bounds concern actual
closed CDFs of arbitrary standardized laws; no numerical certificate is
assumed. The remaining finite moment intervals are separate obligations. -/

noncomputable section

open MeasureTheory Set

namespace BerryEsseen.FiniteHighMomentTails

theorem target4097_lt_esseen : (4097 : ℝ) / 10000 < esseenConstant := by
  have hs10 := Real.sq_sqrt (show (0 : ℝ) ≤ 10 by norm_num)
  have h10 : (1581 : ℝ) / 500 < Real.sqrt 10 := by
    nlinarith [Real.sqrt_nonneg (10 : ℝ)]
  have hp := Real.pi_lt_d6
  have hs2 := Real.sq_sqrt (show 0 ≤ 2 * Real.pi by positivity)
  have h2 : Real.sqrt (2 * Real.pi) < (250663 : ℝ) / 100000 := by
    nlinarith [Real.sqrt_nonneg (2 * Real.pi)]
  have hden : 0 < 6 * Real.sqrt (2 * Real.pi) := by positivity
  unfold esseenConstant
  apply (lt_div_iff₀ hden).mpr
  nlinarith only [h10, h2]

theorem target4087_lt_n3_price : (4087 : ℝ) / 10000 < 59 * Real.sqrt 3 / 250 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hl : (433 : ℝ) / 250 < Real.sqrt 3 := by nlinarith [Real.sqrt_nonneg (3 : ℝ)]
  linarith only [hl]

theorem n3_compact_upper_above_switch : (27 : ℝ) / 20 * Real.sqrt 3 < 117 / 50 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  nlinarith [Real.sqrt_nonneg (3 : ℝ)]

theorem n3_high_tail (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hρ : (117 : ℝ) / 50 ≤ thirdAbsoluteMoment μ) (x : ℝ) :
    |(normalizedIidSumLaw μ 3).real (Iic x) - GaussianTools.Phi x| <
      (59 : ℝ) / 250 * thirdAbsoluteMoment μ := by
  have hh := UniversalCDFBound.iid_abs_error_le μ h 3 (by norm_num) x
  have hm := mul_le_mul_of_nonneg_left hρ (by norm_num : (0 : ℝ) ≤ 59 / 250)
  linarith only [hh, hm]

theorem n4_high_tail (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hρ : (27 : ℝ) / 10 ≤ thirdAbsoluteMoment μ) (x : ℝ) :
    |(normalizedIidSumLaw μ 4).real (Iic x) - GaussianTools.Phi x| <
      (4097 : ℝ) / 10000 * (thirdAbsoluteMoment μ / 2) := by
  have hh := UniversalCDFBound.iid_abs_error_le μ h 4 (by norm_num) x
  have hm := mul_le_mul_of_nonneg_left hρ (by norm_num : (0 : ℝ) ≤ 4097 / 20000)
  linarith only [hh, hm]

theorem sqrt_five_lt_nine_fourths : Real.sqrt (5 : ℝ) < 9 / 4 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  nlinarith [Real.sqrt_nonneg (5 : ℝ)]

theorem n5_high_tail_ratio (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hρ : (121 : ℝ) / 40 ≤ thirdAbsoluteMoment μ) (x : ℝ) :
    Real.sqrt 5 * |(normalizedIidSumLaw μ 5).real (Iic x) - GaussianTools.Phi x| /
      thirdAbsoluteMoment μ < 99 / 242 := by
  have hρp : 0 < thirdAbsoluteMoment μ := lt_of_lt_of_le (by norm_num) hρ
  have hh := UniversalCDFBound.iid_abs_error_le μ h 5 (by norm_num) x
  have hl := mul_le_mul_of_nonneg_left hh (Real.sqrt_nonneg (5 : ℝ))
  have hs := sqrt_five_lt_nine_fourths
  have hr := mul_le_mul_of_nonneg_left hρ (by norm_num : (0 : ℝ) ≤ 99 / 242)
  apply (div_lt_iff₀ hρp).mpr
  nlinarith only [hl, hs, hr]

theorem n5_high_tail (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hρ : (121 : ℝ) / 40 ≤ thirdAbsoluteMoment μ) (x : ℝ) :
    |(normalizedIidSumLaw μ 5).real (Iic x) - GaussianTools.Phi x| <
      (4097 : ℝ) / 10000 * (thirdAbsoluteMoment μ / Real.sqrt 5) := by
  have hρp : 0 < thirdAbsoluteMoment μ := lt_of_lt_of_le (by norm_num) hρ
  have hs : 0 < Real.sqrt (5 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hh := (div_lt_iff₀ hρp).mp (n5_high_tail_ratio μ h hρ x)
  rw [← mul_div_assoc]
  apply (lt_div_iff₀ hs).mpr
  have htarget : (99 / 242 : ℝ) * thirdAbsoluteMoment μ <
      (4097 / 10000 : ℝ) * thirdAbsoluteMoment μ := by
    exact mul_lt_mul_of_pos_right (by norm_num) hρp
  nlinarith only [hh, htarget]

end BerryEsseen.FiniteHighMomentTails

#print axioms BerryEsseen.FiniteHighMomentTails.target4097_lt_esseen
#print axioms BerryEsseen.FiniteHighMomentTails.target4087_lt_n3_price
#print axioms BerryEsseen.FiniteHighMomentTails.n3_compact_upper_above_switch
#print axioms BerryEsseen.FiniteHighMomentTails.n3_high_tail
#print axioms BerryEsseen.FiniteHighMomentTails.n4_high_tail
#print axioms BerryEsseen.FiniteHighMomentTails.n5_high_tail_ratio
#print axioms BerryEsseen.FiniteHighMomentTails.n5_high_tail
