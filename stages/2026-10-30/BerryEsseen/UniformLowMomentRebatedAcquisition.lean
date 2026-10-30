module

public import BerryEsseen.UniformLowMomentPeriodicHighTail
public import BerryEsseen.P39RebatedPricePolynomial

@[expose] public section

/-! 2026-10-30: a uniform second acquisition at each actual n>=26.
The first acquisition supplies D<1 and phase>=5/6 before the true event
tail or retained curvature is used. The final resource preserves the
actual gap integral and the exact score-excess term. Changing C only
evaluates the same raw function; the conserved identity always uses the
original maximum at the original actual C. -/

noncomputable section

open MeasureTheory Set
open BerryEsseen.GaussianTools BerryEsseen.RawResourceEnvelope

namespace BerryEsseen.UniformLowMomentRebatedAcquisition

theorem initial_coefficient_lower :
    (7 : ℝ) / 50 ≤ ConservedPhaseBudget.coefficient (5 / 6) 1 1 := by
  norm_num [ConservedPhaseBudget.coefficient]

theorem initial_coefficient_input_nonneg :
    (0 : ℝ) ≤ (819 / 2000) * 1 - 1 / 15 := by norm_num

/-- The joint scalar certificate is independent of the actual sample
count. Only the true Fourier intercept is supplied to this helper. -/
theorem rebated_raw_le_of_support_nonneg (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hs : (μ : Measure ℝ).support ⊆ Icc (-(12 / 5 : ℝ)) (12 / 5))
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) (n : ℕ) (H C KF : ℝ) (hH : 0 ≤ H)
    (hC0 : (819 : ℝ) / 2000 ≤ C) (hC1 : C ≤ (20487 : ℝ) / 50000)
    (hFourier : |FourierRemainder.value μ n H| ≤ KF + (127 / 1500) * |H|) :
    ConservedResource.raw μ n H C - (7 / 50 : ℝ) * H ^ 2 ≤ KF + (508 : ℝ) / 625 := by
  have hjoint := RawGapProjectionBounds.joint_base_gaussian_le_of_pointwise μ h
    (12 / 5) (by norm_num) hs C (H * phi (H / Real.sqrt (n : ℝ)))
    ((61 / 50 : ℝ) - 509 / 1250 - (123 / 250 + 127 / 1500) * H + (887 / 2000) * H ^ 2)
    (by
      intro t ht
      have hp := P39RebatedPricePolynomial.positive_pointwise |t| H C
        (phi (H / Real.sqrt (n : ℝ))) (ContactVariation.momentSlope μ t)
        (abs_nonneg t) (abs_le.mpr ht) hH hC0 hC1 (phi_nonneg _)
        (N26ProjectedRawAcquisition.phi_le_two_fifths _)
        (ProjectedRawPricePolynomial.neg_momentSlope_le_cubicMajorant μ h hρ t)
      simpa only [sq_abs] using hp)
  have hCK := mul_le_mul_of_nonneg_left
    (N26ProjectedRawAcquisition.CK1_upper μ h hs hρ C hC0 hC1) hH
  have hQ := mul_le_mul_of_nonneg_left
    (UniformLowMomentRawAcquisition.quadTerm_lower μ h hρ n H C hC0) (sq_nonneg H)
  have hF := (le_abs_self (FourierRemainder.value μ n H)).trans hFourier
  rw [abs_of_nonneg hH] at hF
  rw [raw_eq_actual_terms]
  unfold baseTerm linearTerm
  nlinarith only [hjoint, hCK, hQ, hF]

theorem rebated_raw_le_of_support_nonpos (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hs : (μ : Measure ℝ).support ⊆ Icc (-(12 / 5 : ℝ)) (12 / 5))
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) (n : ℕ) (H C KF : ℝ) (hH : H ≤ 0)
    (hC0 : (819 : ℝ) / 2000 ≤ C) (hC1 : C ≤ (20487 : ℝ) / 50000)
    (hFourier : |FourierRemainder.value μ n H| ≤ KF + (127 / 1500) * |H|) :
    ConservedResource.raw μ n H C - (7 / 50 : ℝ) * H ^ 2 ≤ KF + (508 : ℝ) / 625 := by
  have he := raw_le_negative_envelope μ n H C ((20487 / 50000 : ℝ) * (9 / 8))
    (-(173 / 250)) (607 / 2000) KF (127 / 1500) hH
    (N26ProjectedRawAcquisition.baseTerm_upper μ h hs hρ C hC0 hC1)
    (UniformLowMomentRawAcquisition.linearTerm_lower μ h hs hρ n H C hC0 hC1)
    (UniformLowMomentRawAcquisition.quadTerm_lower μ h hρ n H C hC0) hFourier
  have hp := P39RebatedPricePolynomial.negative_axis_price |H|
  rw [sq_abs] at hp
  nlinarith only [he, hp]

theorem rebated_raw_le_of_support (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hs : (μ : Measure ℝ).support ⊆ Icc (-(12 / 5 : ℝ)) (12 / 5))
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) (n : ℕ) (H C KF : ℝ)
    (hC0 : (819 : ℝ) / 2000 ≤ C) (hC1 : C ≤ (20487 : ℝ) / 50000)
    (hFourier : |FourierRemainder.value μ n H| ≤ KF + (127 / 1500) * |H|) :
    ConservedResource.raw μ n H C - (7 / 50 : ℝ) * H ^ 2 ≤ KF + (508 : ℝ) / 625 := by
  rcases le_total 0 H with hH | hH
  · exact rebated_raw_le_of_support_nonneg μ h hs hρ n H C KF hH hC0 hC1 hFourier
  · exact rebated_raw_le_of_support_nonpos μ h hs hρ n H C KF hH hC0 hC1 hFourier

/-- The true periodic event price is acquired from the uniform first pass
of this same μ and actual n before the raw function is evaluated at CE. -/
theorem original_rebated_raw_esseenConstant_bound
    (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (hn : 26 ≤ n) (H C : ℝ)
    (hm : ContactVariation.PositiveClosedMaximum μ n H C)
    (hprev : Extremizer.fixedNSup (n - 1) ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) :
    ConservedResource.raw μ n H esseenConstant - (7 / 50 : ℝ) * H ^ 2 ≤ (92 : ℝ) / 75 := by
  have hs := UniformLowMomentFourierInitial.original_support μ h n hn H C hm hprev hC hρ
  have hFourier := (UniformLowMomentPeriodicHighTail.original_fourier_envelope μ h
    n hn H C hm hprev hC hρ).2
  have hCE1 : esseenConstant ≤ (20487 : ℝ) / 50000 := by
    linarith only [GaussianOwnScore.esseenConstant_lt_409733]
  have hb := rebated_raw_le_of_support μ h hs hρ n H esseenConstant (776 / 1875)
    AnalyticConstants.esseenConstant_gt_819_2000.le hCE1 hFourier
  norm_num at hb
  linarith only [hb]

theorem original_rebated_charged_raw_bound
    (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (hn : 26 ≤ n) (H C : ℝ)
    (hm : ContactVariation.PositiveClosedMaximum μ n H C)
    (hprev : Extremizer.fixedNSup (n - 1) ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) :
    ChargedConservedTransfer.chargedRaw μ n H C - (7 / 50 : ℝ) * H ^ 2 ≤ (92 : ℝ) / 75 := by
  have hscore := LowMomentRawScoreReduction.chargedRaw_le_raw_esseenConstant μ h
    (UniformLowMomentFourierInitial.original_support μ h n hn H C hm hprev hC hρ) hρ
    n (by omega) H C hC
  exact (sub_le_sub_right hscore _).trans
    (original_rebated_raw_esseenConstant_bound μ h n hn H C hm hprev hC hρ)

/-- Retain both the actual gap cost and the exact excess score cost after
changing only the evaluation score in raw. All first-pass licenses come
from already proved uniform original-law acquisition. -/
theorem original_joint_resource_with_excess
    (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (hn : 26 ≤ n) (H C : ℝ)
    (hm : ContactVariation.PositiveClosedMaximum μ n H C)
    (hprev : Extremizer.fixedNSup (n - 1) ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) :
    ((n : ℝ) * thirdAbsoluteMoment μ - LowMomentRawScoreReduction.scoreCoefficient μ H) *
        (C - esseenConstant) +
      ConservedTransfer.kappa * n * GapDefect.actualPhysicalDefect μ +
      (n : ℝ) * Real.sqrt n * ContactGapSum.actualL μ n H ≤ (92 : ℝ) / 75 := by
  have hs := UniformLowMomentFourierInitial.original_support μ h n hn H C hm hprev hC hρ
  have hd := UniformLowMomentRawAcquisition.original_defect_lt_one μ h n hn H C hm hprev hC hρ
  have he := UniformLowMomentRawAcquisition.original_phase_lower_bound μ h n hn H C hm hprev hC hρ
  have hu := ConservedPhaseBudget.resource_with_phase_curvature μ h
    (12 / 5) (by norm_num) hs n (by omega) H C (5 / 6) 1 1 hm
    (Extremizer.thirdAbsoluteMoment_ge_one μ h) hd.le he initial_coefficient_input_nonneg
  have hscore := LowMomentRawScoreReduction.raw_score_difference μ n H esseenConstant C
  have hprice := original_rebated_raw_esseenConstant_bound μ h n hn H C hm hprev hC hρ
  have hcurv := mul_le_mul_of_nonneg_right initial_coefficient_lower (sq_nonneg H)
  nlinarith only [hu, hscore, hprice, hcurv]

/-- The coefficient of the retained excess is positive for every actual
n>=26; neither a new law nor a maximum at CE is used. -/
theorem score_gap_lower (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hs : (μ : Measure ℝ).support ⊆ Icc (-(12 / 5 : ℝ)) (12 / 5))
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) (n : ℕ) (hn : 26 ≤ n) (H : ℝ) :
    (6 : ℝ) ≤ (n : ℝ) * thirdAbsoluteMoment μ -
      LowMomentRawScoreReduction.scoreCoefficient μ H := by
  have hB := LowMomentRawScoreReduction.scoreCoefficient_le_twenty μ h hs hρ H
  have hp := mul_le_mul_of_nonneg_left (Extremizer.thirdAbsoluteMoment_ge_one μ h)
    (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hnR : (26 : ℝ) ≤ n := by exact_mod_cast hn
  nlinarith only [hB, hp, hnR]

theorem original_joint_resource_bound (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (hn : 26 ≤ n) (H C : ℝ)
    (hm : ContactVariation.PositiveClosedMaximum μ n H C)
    (hprev : Extremizer.fixedNSup (n - 1) ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) :
    ConservedTransfer.kappa * n * GapDefect.actualPhysicalDefect μ +
      (n : ℝ) * Real.sqrt n * ContactGapSum.actualL μ n H ≤ (92 : ℝ) / 75 := by
  have hjoint := original_joint_resource_with_excess μ h n hn H C hm hprev hC hρ
  have hcoef := score_gap_lower μ h
    (UniformLowMomentFourierInitial.original_support μ h n hn H C hm hprev hC hρ) hρ n hn H
  have hexcess := mul_nonneg (show 0 ≤ (n : ℝ) * thirdAbsoluteMoment μ -
    LowMomentRawScoreReduction.scoreCoefficient μ H by linarith only [hcoef])
    (sub_nonneg.mpr hC)
  linarith only [hjoint, hexcess]

theorem original_defect_bound (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (hn : 26 ≤ n) (H C : ℝ)
    (hm : ContactVariation.PositiveClosedMaximum μ n H C)
    (hprev : Extremizer.fixedNSup (n - 1) ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) :
    GapDefect.actualPhysicalDefect μ ≤ 18400 / ((997 : ℝ) * n) := by
  have hjoint := original_joint_resource_bound μ h n hn H C hm hprev hC hρ
  have hL := ContactGapSum.actualL_nonneg μ h (12 / 5) (by norm_num)
    (UniformLowMomentFourierInitial.original_support μ h n hn H C hm hprev hC hρ)
    n (by omega) H C hm
  have hgap : 0 ≤ (n : ℝ) * Real.sqrt n * ContactGapSum.actualL μ n H := by positivity
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  apply (le_div_iff₀ (by positivity : 0 < (997 : ℝ) * n)).mpr
  unfold ConservedTransfer.kappa at hjoint
  nlinarith only [hjoint, hgap]

end BerryEsseen.UniformLowMomentRebatedAcquisition

#print axioms BerryEsseen.UniformLowMomentRebatedAcquisition.initial_coefficient_lower
#print axioms BerryEsseen.UniformLowMomentRebatedAcquisition.rebated_raw_le_of_support_nonneg
#print axioms BerryEsseen.UniformLowMomentRebatedAcquisition.rebated_raw_le_of_support_nonpos
#print axioms BerryEsseen.UniformLowMomentRebatedAcquisition.original_rebated_raw_esseenConstant_bound
#print axioms BerryEsseen.UniformLowMomentRebatedAcquisition.original_rebated_charged_raw_bound
#print axioms BerryEsseen.UniformLowMomentRebatedAcquisition.original_joint_resource_with_excess
#print axioms BerryEsseen.UniformLowMomentRebatedAcquisition.score_gap_lower
#print axioms BerryEsseen.UniformLowMomentRebatedAcquisition.original_joint_resource_bound
#print axioms BerryEsseen.UniformLowMomentRebatedAcquisition.original_defect_bound
