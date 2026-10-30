module

public import BerryEsseen.InitialSupport
public import BerryEsseen.UniformLowMomentFourierInitial

@[expose] public section

/-! 2026-10-30: retain the slack in the same analytic support polynomial.
The fixed radius 37/16 gives a strict ray exclusion, using the original
predecessor and actual signed moments, without a parameter search. -/

noncomputable section

open MeasureTheory Set

namespace BerryEsseen.RefinedLowMomentSupport

open SupportRays GaussianContactApplication AnalyticConstants ContactVariation ContactMajorant

theorem cubicCost_neg (r : ℝ) (hr : 37 / 16 ≤ r) :
    cubicCost (11 / 10) (127 / 500) r < 0 := by
  have hy : 0 ≤ r - 37 / 16 := by linarith only [hr]
  have he : cubicCost (11 / 10) (127 / 500) r =
      -(4513529 / 2560000 : ℝ) - (244791 / 32000) * (r - 37 / 16) -
        (423 / 80) * (r - 37 / 16) ^ 2 - (r - 37 / 16) ^ 3 := by
    unfold cubicCost
    ring
  nlinarith only [he, hy, sq_nonneg (r - 37 / 16), pow_nonneg hy 3]

theorem envelope_neg (r : ℝ) (hr : 37 / 16 ≤ r) :
    envelope (11 / 10) (127 / 500) r < 0 := by
  have hy : 0 ≤ r - 37 / 16 := by linarith only [hr]
  have he : envelope (11 / 10) (127 / 500) r =
      -(87206501 / 5120000000 : ℝ) - (141216579 / 64000000) * (r - 37 / 16) -
        (267627 / 160000) * (r - 37 / 16) ^ 2 - (677 / 2000) * (r - 37 / 16) ^ 3 := by
    unfold envelope gaussianPrice cubicCost
    ring
  nlinarith only [he, hy, sq_nonneg (r - 37 / 16), pow_nonneg hy 3]

theorem actualCost_le (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n x : ℝ) (hn : 25 ≤ n) (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) :
    SupportRays.actualCost μ n x ≤ cubicCost (11 / 10) (127 / 500) |x| := by
  have hρ0 : 0 ≤ thirdAbsoluteMoment μ :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (Extremizer.thirdAbsoluteMoment_ge_one μ h)
  have hβ := (SignedMoment.abs_signed_lt_127_500 μ h hρ).le
  have hs := mul_le_mul_of_nonneg_right hρ (sq_nonneg x)
  have hb : SignedMoment.signedSecondMoment μ * x ≤ (127 / 500 : ℝ) * |x| := by
    calc
      _ ≤ |SignedMoment.signedSecondMoment μ * x| := le_abs_self _
      _ = |SignedMoment.signedSecondMoment μ| * |x| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right hβ (abs_nonneg x)
  have he : thirdAbsoluteMoment μ * scaleExcess n ≤ (11 / 10 : ℝ) * (2 / 125) := by
    exact (mul_le_mul_of_nonneg_left (scaleExcess_lt_two_125 n hn).le hρ0).trans
      (mul_le_mul_of_nonneg_right hρ (by norm_num))
  unfold SupportRays.actualCost cubicCost
  rw [sq_abs]
  nlinarith only [hs, hb, he]

theorem ray_neg (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n H C x : ℝ) (hn : 25 ≤ n) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) (hx : 37 / 16 ≤ |x|) :
    hermiteProjection n H x + C * SupportRays.actualCost μ n x < 0 := by
  have hc : (819 / 2000 : ℝ) ≤ C := esseenConstant_gt_819_2000.le.trans hC
  have hC0 : 0 ≤ C := by linarith only [hc]
  have hp := mul_le_mul_of_nonneg_left (actualCost_le μ h n x hn hρ) hC0
  have hq := mul_le_mul_of_nonpos_right hc (cubicCost_neg |x| hx).le
  have hG := hermiteProjection_le_price n H x hn (by linarith only [hx])
  have hE := envelope_neg |x| hx
  unfold envelope at hE
  linarith only [hp, hq, hG, hE]

theorem support_of_predecessor (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (hn : 25 ≤ n) (H C : ℝ) (hm : PositiveClosedMaximum μ n H C)
    (hprev : PredecessorBound μ n C) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) :
    (μ : Measure ℝ).support ⊆ Ioo (-(37 / 16 : ℝ)) (37 / 16) := by
  intro x hxs
  apply abs_lt.mp
  by_contra hnot
  have hr : (37 : ℝ) / 16 ≤ |x| := le_of_not_gt hnot
  have hnR : (25 : ℝ) ≤ n := by exact_mod_cast hn
  have hneg := ray_neg μ h n H C x hnR hC hρ hr
  have hmajor := sqrt_mul_D_le μ n hn H C hm hprev x
  rw [SupportContact.D_eq_zero_on_support μ h n (by omega) H C hm x hxs, mul_zero] at hmajor
  linarith only [hneg, hmajor]

theorem original_support (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (hn : 26 ≤ n) (H C : ℝ) (hm : PositiveClosedMaximum μ n H C)
    (hprev : Extremizer.fixedNSup (n - 1) ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) :
    (μ : Measure ℝ).support ⊆ Ioo (-(37 / 16 : ℝ)) (37 / 16) :=
  support_of_predecessor μ h n (by omega) H C hm
    (UniformLowMomentFourierInitial.predecessor_bound μ h n hn C hprev hC) hC hρ

end BerryEsseen.RefinedLowMomentSupport

#print axioms BerryEsseen.RefinedLowMomentSupport.ray_neg
#print axioms BerryEsseen.RefinedLowMomentSupport.support_of_predecessor
#print axioms BerryEsseen.RefinedLowMomentSupport.original_support
