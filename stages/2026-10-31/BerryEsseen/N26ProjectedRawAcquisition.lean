module

public import BerryEsseen.ProjectedRawPricePolynomial
public import BerryEsseen.RawGapProjectionBounds
public import BerryEsseen.SignedFourthProjection
public import BerryEsseen.N26CubicHighTail
public import BerryEsseen.LowMomentRawScoreReduction
public import BerryEsseen.GaussianOwnScore

@[expose] public section

/-! 2026-10-30: acquire an initial charged resource for the same original
N26 law. The full-law predecessor supplies the support before any moment,
Fourier, defect or phase price is used. The joint gap projection retains
the same coordinate in the base and Gaussian linear terms. Changing C
only evaluates the literal raw function; no maximum at CE is assumed. -/

noncomputable section

open MeasureTheory Set
open BerryEsseen.GaussianTools BerryEsseen.RawResourceEnvelope

namespace BerryEsseen.N26ProjectedRawAcquisition

theorem phi_le_two_fifths (t : ℝ) : phi t ≤ (2 : ℝ) / 5 := by
  rw [GaussianPrices.phi_eq_phi_zero_mul_exp]
  have he : Real.exp (-(t ^ 2 / 2)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (div_nonneg (sq_nonneg t) (by norm_num)))
  exact (mul_le_mul_of_nonneg_left he (phi_nonneg 0)).trans
    (by simpa only [mul_one] using GaussianPrices.phi_zero_lt_2_5.le)

theorem quadTerm_lower (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) (H C : ℝ)
    (hC : (819 : ℝ) / 2000 ≤ C) :
    (607 : ℝ) / 2000 ≤ quadTerm μ 26 H C := by
  have hγ := N26InitialLowFrequency.gamma_cap μ h hρ
  change |ZeroBias.gamma μ| ≤ (53 : ℝ) / 100 at hγ
  have hb := quadTerm_ge_signed_price μ 26 H C (819 / 2000) 1 (-(53 / 100)) 0 (2 / 5)
    (by norm_num) hC (by norm_num) (Extremizer.thirdAbsoluteMoment_ge_one μ h)
    (abs_le.mp hγ).1 (by norm_num) (phi_nonneg _) (phi_le_two_fifths _)
  norm_num at hb
  exact hb

theorem baseTerm_upper (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hs : (μ : Measure ℝ).support ⊆ Icc (-(12 / 5 : ℝ)) (12 / 5))
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) (C : ℝ)
    (hC0 : (819 : ℝ) / 2000 ≤ C) (hC1 : C ≤ (20487 : ℝ) / 50000) :
    baseTerm μ C ≤ (20487 / 50000 : ℝ) * (9 / 8) := by
  have hC : 0 ≤ C := by linarith only [hC0]
  exact (mul_le_mul_of_nonneg_left
    (RawGapProjectionBounds.baseBracket_le_nine_eighths μ h hs hρ) hC).trans
      (mul_le_mul_of_nonneg_right hC1 (by norm_num))

theorem CK1_upper (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hs : (μ : Measure ℝ).support ⊆ Icc (-(12 / 5 : ℝ)) (12 / 5))
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) (C : ℝ)
    (hC0 : (819 : ℝ) / 2000 ≤ C) (hC1 : C ≤ (20487 : ℝ) / 50000) :
    C * ContactWeightedMoment.K1 μ ≤ (123 : ℝ) / 250 := by
  have hC : 0 ≤ C := by linarith only [hC0]
  have hK := SignedFourthProjection.abs_K1_lt_six_fifths μ h hs hρ
  have hp := mul_le_mul_of_nonneg_left ((le_abs_self _).trans hK.le) hC
  have hcap := mul_le_mul_of_nonneg_right hC1 (by norm_num : (0 : ℝ) ≤ 6 / 5)
  nlinarith only [hp, hcap]

theorem linearTerm_lower (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hs : (μ : Measure ℝ).support ⊆ Icc (-(12 / 5 : ℝ)) (12 / 5))
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) (H C : ℝ)
    (hC0 : (819 : ℝ) / 2000 ≤ C) (hC1 : C ≤ (20487 : ℝ) / 50000) :
    -(173 / 250 : ℝ) ≤ linearTerm μ 26 H C := by
  have hC : 0 ≤ C := by linarith only [hC0]
  have hK := SignedFourthProjection.abs_K1_lt_six_fifths μ h hs hρ
  have hCK := mul_le_mul_of_nonneg_left (abs_le.mp hK.le).1 hC
  have hcap := mul_le_mul_of_nonneg_right hC1 (by norm_num : (0 : ℝ) ≤ 6 / 5)
  have hU := (RawGapProjectionBounds.gaussianLinearGap_low_moment_bounds μ h hs).1
  have hphi0 := phi_nonneg (H / Real.sqrt (26 : ℝ))
  have hphi1 := phi_le_two_fifths (H / Real.sqrt (26 : ℝ))
  have hphiU := mul_le_mul_of_nonneg_left hU hphi0
  unfold linearTerm
  nlinarith only [hCK, hcap, hphiU, hphi1]

/-- The positive axis uses the joint projection before any separate
maximization of the base and Gaussian linear terms. -/
theorem raw_le_of_support_nonneg (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hs : (μ : Measure ℝ).support ⊆ Icc (-(12 / 5 : ℝ)) (12 / 5))
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) (H C : ℝ) (hH : 0 ≤ H)
    (hC0 : (819 : ℝ) / 2000 ≤ C) (hC1 : C ≤ (20487 : ℝ) / 50000) :
    ConservedResource.raw μ 26 H C ≤ (17 : ℝ) / 10 := by
  have hjoint := RawGapProjectionBounds.joint_base_gaussian_le_of_pointwise μ h
    (12 / 5) (by norm_num) hs C (H * phi (H / Real.sqrt (26 : ℝ)))
    ((17 / 10 : ℝ) - 79 / 125 - (123 / 250 + 127 / 1500) * H + (607 / 2000) * H ^ 2)
    (by
      intro t ht
      have hp := ProjectedRawPricePolynomial.positive_pointwise |t| H C
        (phi (H / Real.sqrt (26 : ℝ))) (ContactVariation.momentSlope μ t)
        (abs_nonneg t) (abs_le.mpr ht) hH hC0 hC1 (phi_nonneg _)
        (phi_le_two_fifths _)
        (ProjectedRawPricePolynomial.neg_momentSlope_le_cubicMajorant μ h hρ t)
      simpa only [sq_abs] using hp)
  have hCK := mul_le_mul_of_nonneg_left (CK1_upper μ h hs hρ C hC0 hC1) hH
  have hQ := mul_le_mul_of_nonneg_left (quadTerm_lower μ h hρ H C hC0) (sq_nonneg H)
  have hF := (le_abs_self (FourierRemainder.value μ 26 H)).trans
    (N26CubicHighTail.fourier_envelope_of_support μ h hs hρ H).2
  rw [abs_of_nonneg hH] at hF
  rw [raw_eq_actual_terms]
  unfold baseTerm linearTerm
  nlinarith only [hjoint, hCK, hQ, hF]

theorem raw_le_of_support_nonpos (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hs : (μ : Measure ℝ).support ⊆ Icc (-(12 / 5 : ℝ)) (12 / 5))
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) (H C : ℝ) (hH : H ≤ 0)
    (hC0 : (819 : ℝ) / 2000 ≤ C) (hC1 : C ≤ (20487 : ℝ) / 50000) :
    ConservedResource.raw μ 26 H C ≤ (17 : ℝ) / 10 := by
  have he := raw_le_negative_envelope μ 26 H C ((20487 / 50000 : ℝ) * (9 / 8))
    (-(173 / 250)) (607 / 2000) (79 / 125) (127 / 1500) hH
    (baseTerm_upper μ h hs hρ C hC0 hC1) (linearTerm_lower μ h hs hρ H C hC0 hC1)
    (quadTerm_lower μ h hρ H C hC0)
    (N26CubicHighTail.fourier_envelope_of_support μ h hs hρ H).2
  have hp := ProjectedRawPricePolynomial.negative_axis_price |H|
  rw [sq_abs] at hp
  nlinarith only [he, hp]

/-- A price for evaluations of the same raw function at every C in this
interval; C need not be the score of a positive closed maximum here. -/
theorem raw_le_seventeen_tenths_of_support
    (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hs : (μ : Measure ℝ).support ⊆ Icc (-(12 / 5 : ℝ)) (12 / 5))
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) (H C : ℝ)
    (hC0 : (819 : ℝ) / 2000 ≤ C) (hC1 : C ≤ (20487 : ℝ) / 50000) :
    ConservedResource.raw μ 26 H C ≤ (17 : ℝ) / 10 := by
  rcases le_total 0 H with hH | hH
  · exact raw_le_of_support_nonneg μ h hs hρ H C hH hC0 hC1
  · exact raw_le_of_support_nonpos μ h hs hρ H C hH hC0 hC1

/-- The actual all-law predecessor acquires support for the original μ;
only then is the literal raw function evaluated at CE. -/
theorem original_raw_esseenConstant_bound (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (H C : ℝ) (hm : ContactVariation.PositiveClosedMaximum μ 26 H C)
    (hprev : Extremizer.fixedNSup 25 ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) :
    ConservedResource.raw μ 26 H esseenConstant ≤ (17 : ℝ) / 10 := by
  have hs := N26P39ResourceAcquisition.original_support μ h H C hm hprev hC hρ
  apply raw_le_seventeen_tenths_of_support μ h hs hρ H esseenConstant
    AnalyticConstants.esseenConstant_gt_819_2000.le
  linarith only [GaussianOwnScore.esseenConstant_lt_409733]

/-- Exact charging transfers the CE evaluation to the original, possibly
larger actual C. It does not assert an uncharged price at that actual C. -/
theorem original_charged_raw_bound (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (H C : ℝ) (hm : ContactVariation.PositiveClosedMaximum μ 26 H C)
    (hprev : Extremizer.fixedNSup 25 ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) :
    ChargedConservedTransfer.chargedRaw μ 26 H C ≤ (17 : ℝ) / 10 :=
  (LowMomentRawScoreReduction.chargedRaw_le_raw_esseenConstant μ h
    (N26P39ResourceAcquisition.original_support μ h H C hm hprev hC hρ) hρ
    26 (by decide) H C hC).trans
      (original_raw_esseenConstant_bound μ h H C hm hprev hC hρ)

/-- The initial physical defect is acquired from the proved charged price,
without an incoming raw, defect or phase numerical premise. -/
theorem original_defect_bound (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (H C : ℝ) (hm : ContactVariation.PositiveClosedMaximum μ 26 H C)
    (hprev : Extremizer.fixedNSup 25 ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) :
    GapDefect.actualPhysicalDefect μ ≤ (12750 : ℝ) / 12961 := by
  have hρ1 := Extremizer.thirdAbsoluteMoment_ge_one μ h
  have hCE : 0 ≤ esseenConstant := by
    linarith only [AnalyticConstants.esseenConstant_gt_819_2000]
  have hp := mul_le_mul_of_nonneg_left hρ1 hCE
  have hfirst : (17 : ℝ) / 10 < 26 * (esseenConstant * thirdAbsoluteMoment μ) := by
    nlinarith only [hp, AnalyticConstants.esseenConstant_gt_819_2000]
  have hd := ChargedConservedTransfer.defect_bound μ h (12 / 5) (by norm_num)
    (N26P39ResourceAcquisition.original_support μ h H C hm hprev hC hρ)
    26 (by decide) H C (17 / 10) hm
    (original_charged_raw_bound μ h H C hm hprev hC hρ) hfirst
  convert hd using 1
  norm_num [ConservedTransfer.kappa]

theorem original_phase_lower_bound (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (H C : ℝ) (hm : ContactVariation.PositiveClosedMaximum μ 26 H C)
    (hprev : Extremizer.fixedNSup 25 ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) :
    (87 : ℝ) / 104 ≤ ConservedTransfer.phase 26 H := by
  have he := ChargedConservedTransfer.phase_lower_bound μ h (12 / 5) (by norm_num)
    (N26P39ResourceAcquisition.original_support μ h H C hm hprev hC hρ)
    26 (by decide) H C (17 / 10) hm
    (original_charged_raw_bound μ h H C hm hprev hC hρ)
  norm_num at he
  exact he

theorem original_defect_lt_one (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (H C : ℝ) (hm : ContactVariation.PositiveClosedMaximum μ 26 H C)
    (hprev : Extremizer.fixedNSup 25 ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) :
    GapDefect.actualPhysicalDefect μ < 1 :=
  (original_defect_bound μ h H C hm hprev hC hρ).trans_lt (by norm_num)

theorem original_zero_absent (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (H C : ℝ) (hm : ContactVariation.PositiveClosedMaximum μ 26 H C)
    (hprev : Extremizer.fixedNSup 25 ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) :
    (0 : ℝ) ∉ (μ : Measure ℝ).support := by
  apply GapDefect.zero_notMem_support_of_defect_small μ h
  have hd := original_defect_lt_one μ h H C hm hprev hC hρ
  have hr := Extremizer.thirdAbsoluteMoment_ge_one μ h
  have hsqrt := N26P39ResourceAcquisition.sqrt_ten_lower
  have hp := mul_nonneg (show 0 ≤ Real.sqrt 10 - 1 by linarith only [hsqrt])
    (sub_nonneg.mpr hr)
  nlinarith only [hd, hsqrt, hp]

end BerryEsseen.N26ProjectedRawAcquisition

#print axioms BerryEsseen.N26ProjectedRawAcquisition.quadTerm_lower
#print axioms BerryEsseen.N26ProjectedRawAcquisition.raw_le_of_support_nonneg
#print axioms BerryEsseen.N26ProjectedRawAcquisition.raw_le_of_support_nonpos
#print axioms BerryEsseen.N26ProjectedRawAcquisition.raw_le_seventeen_tenths_of_support
#print axioms BerryEsseen.N26ProjectedRawAcquisition.original_raw_esseenConstant_bound
#print axioms BerryEsseen.N26ProjectedRawAcquisition.original_charged_raw_bound
#print axioms BerryEsseen.N26ProjectedRawAcquisition.original_defect_bound
#print axioms BerryEsseen.N26ProjectedRawAcquisition.original_phase_lower_bound
#print axioms BerryEsseen.N26ProjectedRawAcquisition.original_zero_absent
