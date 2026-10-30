module

public import BerryEsseen.UniformLowMomentFourierInitial
public import BerryEsseen.N26ProjectedRawAcquisition

@[expose] public section

/-! 2026-10-30: a uniform first acquisition for each actual integer n>=26.
The raw price varies with sqrt(n); the conserved defect normalization
always uses that same actual n. The original full-law predecessor first
acquires support. No periodic event or second-pass defect conclusion is
used to acquire the first charged price, defect ceiling or phase floor. -/

noncomputable section

open MeasureTheory Set
open BerryEsseen.GaussianTools BerryEsseen.RawResourceEnvelope
open BerryEsseen.N26ProjectedRawAcquisition

namespace BerryEsseen.UniformLowMomentRawAcquisition

def rawBudget (n : ℕ) : ℝ := 11 / 8 + Real.sqrt (n : ℝ) / 15

theorem quadTerm_lower (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) (n : ℕ) (H C : ℝ)
    (hC : (819 : ℝ) / 2000 ≤ C) :
    (607 : ℝ) / 2000 ≤ quadTerm μ n H C := by
  have hγ := N26InitialLowFrequency.gamma_cap μ h hρ
  change |ZeroBias.gamma μ| ≤ (53 : ℝ) / 100 at hγ
  have hb := quadTerm_ge_signed_price μ n H C (819 / 2000) 1 (-(53 / 100)) 0 (2 / 5)
    (by norm_num) hC (by norm_num) (Extremizer.thirdAbsoluteMoment_ge_one μ h)
    (abs_le.mp hγ).1 (by norm_num) (phi_nonneg _) (phi_le_two_fifths _)
  norm_num at hb
  exact hb

theorem linearTerm_lower (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hs : (μ : Measure ℝ).support ⊆ Icc (-(12 / 5 : ℝ)) (12 / 5))
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) (n : ℕ) (H C : ℝ)
    (hC0 : (819 : ℝ) / 2000 ≤ C) (hC1 : C ≤ (20487 : ℝ) / 50000) :
    -(173 / 250 : ℝ) ≤ linearTerm μ n H C := by
  have hC : 0 ≤ C := by linarith only [hC0]
  have hK := SignedFourthProjection.abs_K1_lt_six_fifths μ h hs hρ
  have hCK := mul_le_mul_of_nonneg_left (abs_le.mp hK.le).1 hC
  have hcap := mul_le_mul_of_nonneg_right hC1 (by norm_num : (0 : ℝ) ≤ 6 / 5)
  have hU := (RawGapProjectionBounds.gaussianLinearGap_low_moment_bounds μ h hs).1
  have hphiU := mul_le_mul_of_nonneg_left hU (phi_nonneg (H / Real.sqrt (n : ℝ)))
  have hphi1 := phi_le_two_fifths (H / Real.sqrt (n : ℝ))
  unfold linearTerm
  nlinarith only [hCK, hcap, hphiU, hphi1]

theorem raw_le_of_support_nonneg (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hs : (μ : Measure ℝ).support ⊆ Icc (-(12 / 5 : ℝ)) (12 / 5))
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) (n : ℕ) (H C KF : ℝ) (hH : 0 ≤ H)
    (hC0 : (819 : ℝ) / 2000 ≤ C) (hC1 : C ≤ (20487 : ℝ) / 50000)
    (hFourier : |FourierRemainder.value μ n H| ≤ KF + (127 / 1500) * |H|) :
    ConservedResource.raw μ n H C ≤ KF + (267 : ℝ) / 250 := by
  have hjoint := RawGapProjectionBounds.joint_base_gaussian_le_of_pointwise μ h
    (12 / 5) (by norm_num) hs C (H * phi (H / Real.sqrt (n : ℝ)))
    ((17 / 10 : ℝ) - 79 / 125 - (123 / 250 + 127 / 1500) * H + (607 / 2000) * H ^ 2)
    (by
      intro t ht
      have hp := ProjectedRawPricePolynomial.positive_pointwise |t| H C
        (phi (H / Real.sqrt (n : ℝ))) (ContactVariation.momentSlope μ t)
        (abs_nonneg t) (abs_le.mpr ht) hH hC0 hC1 (phi_nonneg _)
        (phi_le_two_fifths _)
        (ProjectedRawPricePolynomial.neg_momentSlope_le_cubicMajorant μ h hρ t)
      simpa only [sq_abs] using hp)
  have hCK := mul_le_mul_of_nonneg_left (CK1_upper μ h hs hρ C hC0 hC1) hH
  have hQ := mul_le_mul_of_nonneg_left (quadTerm_lower μ h hρ n H C hC0) (sq_nonneg H)
  have hF := (le_abs_self (FourierRemainder.value μ n H)).trans hFourier
  rw [abs_of_nonneg hH] at hF
  rw [raw_eq_actual_terms]
  unfold baseTerm linearTerm
  nlinarith only [hjoint, hCK, hQ, hF]

theorem raw_le_of_support_nonpos (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hs : (μ : Measure ℝ).support ⊆ Icc (-(12 / 5 : ℝ)) (12 / 5))
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) (n : ℕ) (H C KF : ℝ) (hH : H ≤ 0)
    (hC0 : (819 : ℝ) / 2000 ≤ C) (hC1 : C ≤ (20487 : ℝ) / 50000)
    (hFourier : |FourierRemainder.value μ n H| ≤ KF + (127 / 1500) * |H|) :
    ConservedResource.raw μ n H C ≤ KF + (267 : ℝ) / 250 := by
  have he := raw_le_negative_envelope μ n H C ((20487 / 50000 : ℝ) * (9 / 8))
    (-(173 / 250)) (607 / 2000) KF (127 / 1500) hH
    (baseTerm_upper μ h hs hρ C hC0 hC1) (linearTerm_lower μ h hs hρ n H C hC0 hC1)
    (quadTerm_lower μ h hρ n H C hC0) hFourier
  have hp := ProjectedRawPricePolynomial.negative_axis_price |H|
  rw [sq_abs] at hp
  nlinarith only [he, hp]

theorem raw_le_of_support (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hs : (μ : Measure ℝ).support ⊆ Icc (-(12 / 5 : ℝ)) (12 / 5))
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) (n : ℕ) (H C KF : ℝ)
    (hC0 : (819 : ℝ) / 2000 ≤ C) (hC1 : C ≤ (20487 : ℝ) / 50000)
    (hFourier : |FourierRemainder.value μ n H| ≤ KF + (127 / 1500) * |H|) :
    ConservedResource.raw μ n H C ≤ KF + (267 : ℝ) / 250 := by
  rcases le_total 0 H with hH | hH
  · exact raw_le_of_support_nonneg μ h hs hρ n H C KF hH hC0 hC1 hFourier
  · exact raw_le_of_support_nonpos μ h hs hρ n H C KF hH hC0 hC1 hFourier

/-- A single elementary square-root comparison pays the varying budget
for every actual integer n>=26. No fixed raw bound is asserted. -/
theorem rawBudget_lt_kappa_mul_n (n : ℕ) (hn : 26 ≤ n) :
    rawBudget n < ConservedTransfer.kappa * n := by
  have hnR : (26 : ℝ) ≤ n := by exact_mod_cast hn
  have hs0 := Real.sqrt_nonneg (n : ℝ)
  have hs2 := Real.sq_sqrt (Nat.cast_nonneg n)
  have hs5 : (5 : ℝ) ≤ Real.sqrt (n : ℝ) := by nlinarith only [hnR, hs0, hs2]
  have hp := mul_nonneg (sub_nonneg.mpr hs5) hs0
  have hsqrt : Real.sqrt (n : ℝ) ≤ (n : ℝ) / 5 := by nlinarith only [hp, hs2]
  unfold rawBudget ConservedTransfer.kappa
  nlinarith only [hsqrt, hnR]

theorem original_raw_esseenConstant_bound (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (hn : 26 ≤ n) (H C : ℝ)
    (hm : ContactVariation.PositiveClosedMaximum μ n H C)
    (hprev : Extremizer.fixedNSup (n - 1) ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) :
    ConservedResource.raw μ n H esseenConstant ≤ rawBudget n := by
  have hs := UniformLowMomentFourierInitial.original_support μ h n hn H C hm hprev hC hρ
  have hFourier := (UniformLowMomentFourierInitial.original_fourier_envelope μ h
    n hn H C hm hprev hC hρ).2
  have hCE1 : esseenConstant ≤ (20487 : ℝ) / 50000 := by
    linarith only [GaussianOwnScore.esseenConstant_lt_409733]
  have hb := raw_le_of_support μ h hs hρ n H esseenConstant
    (3 / 10 + Real.sqrt (n : ℝ) / 15)
    AnalyticConstants.esseenConstant_gt_819_2000.le hCE1 hFourier
  unfold rawBudget
  nlinarith only [hb]

theorem original_charged_raw_bound (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (hn : 26 ≤ n) (H C : ℝ)
    (hm : ContactVariation.PositiveClosedMaximum μ n H C)
    (hprev : Extremizer.fixedNSup (n - 1) ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) :
    ChargedConservedTransfer.chargedRaw μ n H C ≤ rawBudget n :=
  (LowMomentRawScoreReduction.chargedRaw_le_raw_esseenConstant μ h
    (UniformLowMomentFourierInitial.original_support μ h n hn H C hm hprev hC hρ) hρ
    n (by omega) H C hC).trans
      (original_raw_esseenConstant_bound μ h n hn H C hm hprev hC hρ)

theorem original_defect_bound (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (hn : 26 ≤ n) (H C : ℝ)
    (hm : ContactVariation.PositiveClosedMaximum μ n H C)
    (hprev : Extremizer.fixedNSup (n - 1) ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) :
    GapDefect.actualPhysicalDefect μ ≤ rawBudget n / (ConservedTransfer.kappa * n) := by
  have hn0 : 0 < n := by omega
  have hCE : 0 ≤ esseenConstant := by
    linarith only [AnalyticConstants.esseenConstant_gt_819_2000]
  have hp := mul_le_mul_of_nonneg_left (Extremizer.thirdAbsoluteMoment_ge_one μ h) hCE
  have hscore : ConservedTransfer.kappa < esseenConstant * thirdAbsoluteMoment μ := by
    unfold ConservedTransfer.kappa
    linarith only [hp, AnalyticConstants.esseenConstant_gt_819_2000]
  have hscoreN := mul_lt_mul_of_pos_left hscore (Nat.cast_pos.mpr hn0)
  have hfirst : rawBudget n < (n : ℝ) * (esseenConstant * thirdAbsoluteMoment μ) := by
    nlinarith only [rawBudget_lt_kappa_mul_n n hn, hscoreN]
  exact ChargedConservedTransfer.defect_bound μ h (12 / 5) (by norm_num)
    (UniformLowMomentFourierInitial.original_support μ h n hn H C hm hprev hC hρ)
    n hn0 H C (rawBudget n) hm
    (original_charged_raw_bound μ h n hn H C hm hprev hC hρ) hfirst

theorem original_defect_lt_one (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (hn : 26 ≤ n) (H C : ℝ)
    (hm : ContactVariation.PositiveClosedMaximum μ n H C)
    (hprev : Extremizer.fixedNSup (n - 1) ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) :
    GapDefect.actualPhysicalDefect μ < 1 := by
  apply (original_defect_bound μ h n hn H C hm hprev hC hρ).trans_lt
  apply (div_lt_iff₀ (mul_pos ConservedTransfer.kappa_pos (Nat.cast_pos.mpr (by omega)))).mpr
  simpa only [one_mul] using rawBudget_lt_kappa_mul_n n hn

theorem original_phase_lower_bound (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (hn : 26 ≤ n) (H C : ℝ)
    (hm : ContactVariation.PositiveClosedMaximum μ n H C)
    (hprev : Extremizer.fixedNSup (n - 1) ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) :
    (5 : ℝ) / 6 ≤ ConservedTransfer.phase n H := by
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have he := ChargedConservedTransfer.phase_lower_bound μ h (12 / 5) (by norm_num)
    (UniformLowMomentFourierInitial.original_support μ h n hn H C hm hprev hC hρ)
    n (by omega) H C (rawBudget n) hm
    (original_charged_raw_bound μ h n hn H C hm hprev hC hρ)
  have hk := mul_le_mul_of_nonneg_right
    (show ConservedTransfer.kappa ≤ (1 : ℝ) / 15 by norm_num [ConservedTransfer.kappa])
    (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hr15 : rawBudget n ≤ (n : ℝ) / 15 := by
    nlinarith only [rawBudget_lt_kappa_mul_n n hn, hk]
  have hratio : 5 * rawBudget n / (2 * (n : ℝ)) ≤ (1 : ℝ) / 6 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * (n : ℝ))).mpr
    nlinarith only [hr15]
  linarith only [he, hratio]

theorem original_zero_absent (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (hn : 26 ≤ n) (H C : ℝ)
    (hm : ContactVariation.PositiveClosedMaximum μ n H C)
    (hprev : Extremizer.fixedNSup (n - 1) ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) :
    (0 : ℝ) ∉ (μ : Measure ℝ).support := by
  apply GapDefect.zero_notMem_support_of_defect_small μ h
  have hd := original_defect_lt_one μ h n hn H C hm hprev hC hρ
  have hr := Extremizer.thirdAbsoluteMoment_ge_one μ h
  have hsqrt := N26P39ResourceAcquisition.sqrt_ten_lower
  have hp := mul_nonneg (show 0 ≤ Real.sqrt 10 - 1 by linarith only [hsqrt])
    (sub_nonneg.mpr hr)
  nlinarith only [hd, hsqrt, hp]

end BerryEsseen.UniformLowMomentRawAcquisition

#print axioms BerryEsseen.UniformLowMomentRawAcquisition.raw_le_of_support_nonneg
#print axioms BerryEsseen.UniformLowMomentRawAcquisition.raw_le_of_support_nonpos
#print axioms BerryEsseen.UniformLowMomentRawAcquisition.rawBudget_lt_kappa_mul_n
#print axioms BerryEsseen.UniformLowMomentRawAcquisition.original_raw_esseenConstant_bound
#print axioms BerryEsseen.UniformLowMomentRawAcquisition.original_charged_raw_bound
#print axioms BerryEsseen.UniformLowMomentRawAcquisition.original_defect_bound
#print axioms BerryEsseen.UniformLowMomentRawAcquisition.original_defect_lt_one
#print axioms BerryEsseen.UniformLowMomentRawAcquisition.original_phase_lower_bound
#print axioms BerryEsseen.UniformLowMomentRawAcquisition.original_zero_absent
