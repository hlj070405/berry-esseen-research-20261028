module

public import BerryEsseen.InitialSupport
public import BerryEsseen.GaussianRecurrence
public import BerryEsseen.ConservedTransfer
public import BerryEsseen.ConservedPhaseBudget
public import BerryEsseen.PhysicalResourcePlane

@[expose] public section

/-! 2026-10-30: forward original-law acquisition for N26/B0/P39.
The all-law predecessor acquires the first support bound. A literal raw
price then acquires the displayed defect ceiling. From that ceiling the
endpoint and theta prices below are proved, rather than read from a row.
These deliberately coarse prices do not assert the stronger 32-round
P39 profile. The required raw/Fourier numerical price is still explicit. -/

noncomputable section

open MeasureTheory Set

namespace BerryEsseen.N26P39ResourceAcquisition

open CanonicalSign CentralGap NoiseCoordinates GapDefect JointDefect
open PhysicalDefect ConservedTransfer GaussianTools

def defectCeiling : ℝ := 61823769 / 104000000

/-- The exact unrebated raw price sufficient for the old P39 defect ceiling.
It is smaller than the stored raw price 108264383/10^8. -/
def directRawBudget : ℝ := kappa * 26 * defectCeiling

def firstRawBudget : ℝ := 108264383 / 100000000
def firstDefectCeiling : ℝ := firstRawBudget / (kappa * 26)
def firstPhaseFloor : ℝ := 1 - 5 * firstRawBudget / (2 * 26)
def phaseCurvature : ℝ := ConservedPhaseBudget.coefficient firstPhaseFloor 1 firstDefectCeiling

theorem directRawBudget_eq : directRawBudget = 20546099231 / 20000000000 := by
  norm_num [directRawBudget, kappa, defectCeiling]

theorem directRawBudget_lt_first : directRawBudget < firstRawBudget := by
  norm_num [directRawBudget, firstRawBudget, kappa, defectCeiling]

theorem phaseCurvature_eq :
    phaseCurvature = 888169072992010989 / 5391776000000000000 := by
  norm_num [phaseCurvature, ConservedPhaseBudget.coefficient, firstPhaseFloor,
    firstDefectCeiling, firstRawBudget, kappa]

lemma sqrt_ten_lower : (31 : ℝ) / 10 ≤ Real.sqrt 10 := by
  nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 10), Real.sqrt_nonneg (10 : ℝ)]

/-- The full original C25 premise is applied to the same original marginal. -/
theorem predecessor_bound (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (C : ℝ) (hprev : Extremizer.fixedNSup 25 ≤ esseenConstant)
    (hC : esseenConstant ≤ C) : ContactMajorant.PredecessorBound μ 26 C := by
  intro t
  have h := GaussianRecurrence.predecessor_cdf_upper μ hμ 25 (by decide) t
  have hρ := Extremizer.thirdAbsoluteMoment_pos μ hμ
  have hc := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hprev.trans hC) hρ.le)
    (Real.sqrt_nonneg (25 : ℝ))
  change (MixtureSum.iidSumLaw (μ : Measure ℝ) 25).real (Iic t) ≤
    Phi (t / Real.sqrt (25 : ℝ)) + C * thirdAbsoluteMoment μ / Real.sqrt (25 : ℝ)
  change (MixtureSum.iidSumLaw (μ : Measure ℝ) 25).real (Iic t) ≤
    Phi (t / Real.sqrt (25 : ℝ)) + Extremizer.fixedNSup 25 * thirdAbsoluteMoment μ /
      Real.sqrt (25 : ℝ) at h
  linarith only [h, hc]

theorem original_support (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (H C : ℝ) (hm : ContactVariation.PositiveClosedMaximum μ 26 H C)
    (hprev : Extremizer.fixedNSup 25 ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) :
    (μ : Measure ℝ).support ⊆ Icc (-(12 / 5 : ℝ)) (12 / 5) := by
  have hs := InitialSupport.low_moment_support μ h 26 (by decide) H C hm
    (predecessor_bound μ h C hprev hC) hC hρ
  intro x hx
  exact ⟨(hs hx).1.le, (hs hx).2.le⟩

/-- The displayed fourth-moment polynomial is nonnegative on the
whole acquired support interval; its factorization supplies the proof. -/
theorem fourth_polynomial_majorant (y : ℝ) (hy : 0 ≤ y) (hR : y ≤ 12 / 5) :
    y ^ 4 ≤ (578 / 145 : ℝ) * y ^ 3 - (577 / 145 : ℝ) * y ^ 2 + 144 / 145 := by
  have hf : 0 ≤ (y - 1) ^ 2 * (12 / 5 - y) * (y + 12 / 29) := by
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hR)) (by linarith only [hy])
  have he : (y - 1) ^ 2 * (12 / 5 - y) * (y + 12 / 29) =
      (578 / 145 : ℝ) * y ^ 3 - (577 / 145 : ℝ) * y ^ 2 + 144 / 145 - y ^ 4 := by ring
  rw [he] at hf
  linarith only [hf]

theorem fifth_polynomial_majorant (y : ℝ) (hy : 0 ≤ y) (hR : y ≤ 12 / 5) :
    y ^ 5 ≤ (8511 / 725 : ℝ) * y ^ 3 - (10954 / 725 : ℝ) * y ^ 2 + 3168 / 725 := by
  have hf : 0 ≤ (y - 1) ^ 2 * (12 / 5 - y) * (y ^ 2 + 22 / 5 * y + 264 / 145) := by
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hR)) (by positivity)
  have he : (y - 1) ^ 2 * (12 / 5 - y) * (y ^ 2 + 22 / 5 * y + 264 / 145) =
      (8511 / 725 : ℝ) * y ^ 3 - (10954 / 725 : ℝ) * y ^ 2 + 3168 / 725 - y ^ 5 := by ring
  rw [he] at hf
  linarith only [hf]

/-- Keep the actual rho in both moment prices. In particular subsequent
C/rho interpolation can use these two prices at the same actual rho. -/
theorem moment_affine_of_support (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hs : (μ : Measure ℝ).support ⊆ Icc (-(12 / 5 : ℝ)) (12 / 5)) :
    (∫ x : ℝ, |x| ^ 4 ∂(μ : Measure ℝ)) ≤ 1 + (578 / 145 : ℝ) * (thirdAbsoluteMoment μ - 1) ∧
      (∫ x : ℝ, |x| ^ 5 ∂(μ : Measure ℝ)) ≤ 1 + (8511 / 725 : ℝ) * (thirdAbsoluteMoment μ - 1) := by
  have h2 := ConservedResource.integrable_abs_pow_of_bounded_support μ (12 / 5) hs 2
  have h4 := ConservedResource.integrable_abs_pow_of_bounded_support μ (12 / 5) hs 4
  have h5 := ConservedResource.integrable_abs_pow_of_bounded_support μ (12 / 5) hs 5
  have h34 : Integrable (fun x : ℝ => (578 / 145 : ℝ) * |x| ^ 3 -
      (577 / 145 : ℝ) * |x| ^ 2) (μ : Measure ℝ) :=
    (h.integrable_cube.const_mul (578 / 145)).sub (h2.const_mul (577 / 145))
  have h35 : Integrable (fun x : ℝ => (8511 / 725 : ℝ) * |x| ^ 3 -
      (10954 / 725 : ℝ) * |x| ^ 2) (μ : Measure ℝ) :=
    (h.integrable_cube.const_mul (8511 / 725)).sub (h2.const_mul (10954 / 725))
  have hsquare : (∫ x : ℝ, |x| ^ 2 ∂(μ : Measure ℝ)) = 1 := by
    simpa only [sq_abs] using h.second_moment_one
  have hb4 : ∀ᵐ x ∂(μ : Measure ℝ), |x| ^ 4 ≤
      (578 / 145 : ℝ) * |x| ^ 3 - (577 / 145 : ℝ) * |x| ^ 2 + 144 / 145 := by
    filter_upwards [(μ : Measure ℝ).support_mem_ae] with x hx
    exact fourth_polynomial_majorant |x| (abs_nonneg _) (abs_le.mpr (hs hx))
  have hb5 : ∀ᵐ x ∂(μ : Measure ℝ), |x| ^ 5 ≤
      (8511 / 725 : ℝ) * |x| ^ 3 - (10954 / 725 : ℝ) * |x| ^ 2 + 3168 / 725 := by
    filter_upwards [(μ : Measure ℝ).support_mem_ae] with x hx
    exact fifth_polynomial_majorant |x| (abs_nonneg _) (abs_le.mpr (hs hx))
  have hi4 := integral_mono_ae h4
    (h34.add (integrable_const (144 / 145))) hb4
  have hi5 := integral_mono_ae h5
    (h35.add (integrable_const (3168 / 725))) hb5
  simp only [Pi.add_apply] at hi4 hi5
  rw [integral_add h34 (integrable_const (144 / 145)),
    integral_sub (h.integrable_cube.const_mul (578 / 145)) (h2.const_mul (577 / 145)),
    integral_const_mul, integral_const_mul, hsquare, integral_const, probReal_univ, one_smul] at hi4
  rw [integral_add h35 (integrable_const (3168 / 725)),
    integral_sub (h.integrable_cube.const_mul (8511 / 725)) (h2.const_mul (10954 / 725)),
    integral_const_mul, integral_const_mul, hsquare, integral_const, probReal_univ, one_smul] at hi5
  change (∫ x : ℝ, |x| ^ 4 ∂(μ : Measure ℝ)) ≤
    (578 / 145 : ℝ) * thirdAbsoluteMoment μ - (577 / 145 : ℝ) * 1 + 144 / 145 at hi4
  change (∫ x : ℝ, |x| ^ 5 ∂(μ : Measure ℝ)) ≤
    (8511 / 725 : ℝ) * thirdAbsoluteMoment μ - (10954 / 725 : ℝ) * 1 + 3168 / 725 at hi5
  constructor <;> linarith only [hi4, hi5]

/-- The actual source moment numbers are corollaries of the affine
same-rho bounds, before any raw, defect or variance price is used. -/
theorem moment_caps_of_support (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hs : (μ : Measure ℝ).support ⊆ Icc (-(12 / 5 : ℝ)) (12 / 5))
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) :
    (∫ x : ℝ, |x| ^ 4 ∂(μ : Measure ℝ)) ≤ (1014 : ℝ) / 725 ∧
      (∫ x : ℝ, |x| ^ 5 ∂(μ : Measure ℝ)) ≤ (15761 : ℝ) / 7250 := by
  obtain ⟨h4, h5⟩ := moment_affine_of_support μ h hs
  constructor <;> linarith only [h4, h5, hρ]

theorem original_moment_affine (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (H C : ℝ) (hm : ContactVariation.PositiveClosedMaximum μ 26 H C)
    (hprev : Extremizer.fixedNSup 25 ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) :
    (∫ x : ℝ, |x| ^ 4 ∂(μ : Measure ℝ)) ≤ 1 + (578 / 145 : ℝ) * (thirdAbsoluteMoment μ - 1) ∧
      (∫ x : ℝ, |x| ^ 5 ∂(μ : Measure ℝ)) ≤ 1 + (8511 / 725 : ℝ) * (thirdAbsoluteMoment μ - 1) :=
  moment_affine_of_support μ h (original_support μ h H C hm hprev hC hρ)

theorem original_moment_caps (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (H C : ℝ) (hm : ContactVariation.PositiveClosedMaximum μ 26 H C)
    (hprev : Extremizer.fixedNSup 25 ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) :
    (∫ x : ℝ, |x| ^ 4 ∂(μ : Measure ℝ)) ≤ (1014 : ℝ) / 725 ∧
      (∫ x : ℝ, |x| ^ 5 ∂(μ : Measure ℝ)) ≤ (15761 : ℝ) / 7250 :=
  moment_caps_of_support μ h (original_support μ h H C hm hprev hC hρ) hρ

/-- No defect, support, phase, endpoint or noise number is an incoming
resource premise here. The missing analytic price is about the literal raw. -/
theorem defect_of_direct_raw (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (H C : ℝ) (hm : ContactVariation.PositiveClosedMaximum μ 26 H C)
    (hprev : Extremizer.fixedNSup 25 ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10)
    (hraw : ConservedResource.raw μ 26 H C ≤ directRawBudget) :
    actualPhysicalDefect μ ≤ defectCeiling := by
  have hρ1 := Extremizer.thirdAbsoluteMoment_ge_one μ h
  have hc : (819 / 2000 : ℝ) ≤ C :=
    AnalyticConstants.esseenConstant_gt_819_2000.le.trans hC
  have hprod : (819 / 2000 : ℝ) ≤ C * thirdAbsoluteMoment μ := by
    nlinarith only [hc, mul_nonneg (by linarith only [hc] : 0 ≤ C)
      (sub_nonneg.mpr hρ1)]
  have hfirst : directRawBudget < (26 : ℝ) * (C * thirdAbsoluteMoment μ) := by
    dsimp only [directRawBudget, kappa, defectCeiling]
    linarith only [hprod]
  have hd := ConservedTransfer.defect_bound μ h (12 / 5) (by norm_num)
    (original_support μ h H C hm hprev hC hρ) 26 (by decide) H C directRawBudget hm hC hraw hfirst
  convert hd using 1
  norm_num [directRawBudget, kappa, defectCeiling]

/-- The first pass acquires its own defect and phase licenses before the
second, rebated raw price is used. Neither license is assumed from the
desired final defect ceiling. Both raw inequalities concern the same μ,H,C. -/
theorem defect_of_phase_raw (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (H C : ℝ) (hm : ContactVariation.PositiveClosedMaximum μ 26 H C)
    (hprev : Extremizer.fixedNSup 25 ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10)
    (hraw : ConservedResource.raw μ 26 H C ≤ firstRawBudget)
    (hrebate : ConservedResource.raw μ 26 H C - phaseCurvature * H ^ 2 ≤ directRawBudget) :
    actualPhysicalDefect μ ≤ defectCeiling := by
  have hs := original_support μ h H C hm hprev hC hρ
  have hρ1 := Extremizer.thirdAbsoluteMoment_ge_one μ h
  have hc : (819 / 2000 : ℝ) ≤ C :=
    AnalyticConstants.esseenConstant_gt_819_2000.le.trans hC
  have hprod : (819 / 2000 : ℝ) ≤ C * thirdAbsoluteMoment μ := by
    nlinarith only [hc, mul_nonneg (by linarith only [hc] : 0 ≤ C)
      (sub_nonneg.mpr hρ1)]
  have hfirst : firstRawBudget < (26 : ℝ) * (C * thirdAbsoluteMoment μ) := by
    dsimp only [firstRawBudget]
    linarith only [hprod]
  have hd : actualPhysicalDefect μ ≤ firstDefectCeiling :=
    ConservedTransfer.defect_bound μ h (12 / 5) (by norm_num) hs 26 (by decide)
      H C firstRawBudget hm hC hraw hfirst
  have he : firstPhaseFloor ≤ phase 26 H :=
    ConservedTransfer.phase_lower_bound μ h (12 / 5) (by norm_num) hs 26 (by decide)
      H C firstRawBudget hm hC hraw
  have hA : 0 ≤ (819 / 2000 : ℝ) * 1 - firstDefectCeiling / 15 := by
    norm_num [firstDefectCeiling, firstRawBudget, kappa]
  have hb := ConservedPhaseBudget.defect_phase_budget μ h (12 / 5) (by norm_num) hs
    26 (by decide) H C firstPhaseFloor 1 firstDefectCeiling hm hC hρ1 hd he hA
  change kappa * (26 : ℝ) * actualPhysicalDefect μ ≤
    ConservedResource.raw μ 26 H C - phaseCurvature * H ^ 2 at hb
  have hh := hb.trans hrebate
  dsimp only [directRawBudget] at hh
  exact (mul_le_mul_iff_right₀ (show 0 < kappa * (26 : ℝ) by norm_num [kappa])).mp hh

theorem zero_absent_of_defect (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hD : actualPhysicalDefect μ ≤ defectCeiling) :
    (0 : ℝ) ∉ (μ : Measure ℝ).support := by
  apply zero_notMem_support_of_defect_small μ h
  have hr := Extremizer.thirdAbsoluteMoment_ge_one μ h
  have hp := mul_nonneg (show 0 ≤ Real.sqrt 10 - 1 by linarith only [sqrt_ten_lower])
    (sub_nonneg.mpr hr)
  norm_num only [defectCeiling] at hD
  nlinarith only [hD, sqrt_ten_lower, hp]

/-- These two bounds use the original centered variance identity. -/
theorem firstMoment_endpoint_upper (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    positiveFirstMoment μ * Aminus μ ≤ p μ ∧
      positiveFirstMoment μ * Aplus μ ≤ q μ := by
  have hm := positiveFirstMoment_pos μ h
  have ht := theta_nonneg μ h
  have hs := positiveFirstMoment_sq μ h
  constructor
  · have ha : Aminus μ ≤ positiveFirstMoment μ / q μ := by
      have hd := deltaMinus_nonneg μ h
      change 0 ≤ positiveFirstMoment μ / q μ - Aminus μ at hd
      linarith only [hd]
    calc
      _ ≤ positiveFirstMoment μ * (positiveFirstMoment μ / q μ) :=
        mul_le_mul_of_nonneg_left ha hm.le
      _ = positiveFirstMoment μ ^ 2 / q μ := by ring
      _ = p μ * (1 - theta μ h) := by
        apply (div_eq_iff (q_pos μ h).ne').mpr
        nlinarith only [hs]
      _ ≤ p μ := by nlinarith only [mul_nonneg (p_pos μ h).le ht]
  · have ha : Aplus μ ≤ positiveFirstMoment μ / p μ := by
      have hd := deltaPlus_nonneg μ h
      change 0 ≤ positiveFirstMoment μ / p μ - Aplus μ at hd
      linarith only [hd]
    calc
      _ ≤ positiveFirstMoment μ * (positiveFirstMoment μ / p μ) :=
        mul_le_mul_of_nonneg_left ha hm.le
      _ = positiveFirstMoment μ ^ 2 / p μ := by ring
      _ = q μ * (1 - theta μ h) := by
        apply (div_eq_iff (p_pos μ h).ne').mpr
        nlinarith only [hs]
      _ ≤ q μ := by nlinarith only [mul_nonneg (q_pos μ h).le ht]

/-- Two genuine endpoint costs follow before any iterative profile is used. -/
theorem endpoint_costs (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hz : (0 : ℝ) ∉ (μ : Measure ℝ).support) :
    (Real.sqrt 10 - 1) * thirdAbsoluteMoment μ ≤
        actualPhysicalDefect μ + 6 * q μ * Aminus μ ∧
      (Real.sqrt 10 - 1) * thirdAbsoluteMoment μ ≤
        actualPhysicalDefect μ + 6 * p μ * Aplus μ := by
  have hj := actualJ_le_central_correction μ h hz
  have hg := gamma_le_rho μ h
  obtain ⟨hm, hp⟩ := firstMoment_endpoint_upper μ h
  have hminus := mul_le_mul_of_nonneg_right hp (Aminus_nonneg μ h)
  have hplus := mul_le_mul_of_nonneg_right hm (Aplus_nonneg μ h)
  unfold actualPhysicalDefect
  constructor <;> nlinarith only [hj, hg, hminus, hplus]

theorem endpoints_of_defect (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hp : p μ ∈ Icc (39 / 100 : ℝ) (2 / 5))
    (hD : actualPhysicalDefect μ ≤ defectCeiling) :
    (2 / 5 : ℝ) ≤ Aminus μ ∧ (3 / 5 : ℝ) ≤ Aplus μ := by
  obtain ⟨hm, hpl⟩ := endpoint_costs μ h (zero_absent_of_defect μ h hD)
  have hr := Extremizer.thirdAbsoluteMoment_ge_one μ h
  have hbase : (21 / 10 : ℝ) ≤ (Real.sqrt 10 - 1) * thirdAbsoluteMoment μ := by
    nlinarith only [sqrt_ten_lower, mul_nonneg
      (show 0 ≤ Real.sqrt 10 - 1 by linarith only [sqrt_ten_lower]) (sub_nonneg.mpr hr)]
  have hq : q μ ≤ (61 / 100 : ℝ) := by unfold q; linarith only [hp.1]
  have hqm := mul_le_mul_of_nonneg_right hq (Aminus_nonneg μ h)
  have hpp := mul_le_mul_of_nonneg_right hp.2 (Aplus_nonneg μ h)
  norm_num only [defectCeiling] at hD
  constructor <;> nlinarith only [hm, hpl, hbase, hD, hqm, hpp]

/-- The same acquired endpoint prices pay for both actual variance shares. -/
theorem theta_of_defect (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hp : p μ ∈ Icc (39 / 100 : ℝ) (2 / 5))
    (hD : actualPhysicalDefect μ ≤ defectCeiling) : theta μ h ≤ (1 : ℝ) / 12 := by
  have hz := zero_absent_of_defect μ h hD
  obtain ⟨ha, hb⟩ := endpoints_of_defect μ h hp hD
  have hj := joint_defect_moment μ h hz
  have hm := positiveFirstMoment_pos μ h
  have ham := Aminus_nonneg μ h
  have hap := Aplus_nonneg μ h
  have hdm := deltaMinus_nonneg μ h
  have hdp := deltaPlus_nonneg μ h
  have htm := thetaMinus_nonneg μ h
  have htp := thetaPlus_nonneg μ h
  have hbase : 0 ≤ positiveFirstMoment μ ^ 3 / (p μ ^ 2 * q μ ^ 2) *
      (6 + 2 * Real.sqrt 10) * (p μ - pStar) ^ 2 := by positivity
  have hgap : 0 ≤ 6 * positiveFirstMoment μ *
      ((Aminus μ + Aplus μ) * (deltaMinus μ + deltaPlus μ) + deltaMinus μ * deltaPlus μ) := by
    positivity
  have hcm : (36 / 5 : ℝ) ≤ 3 * (Real.sqrt 10 + 3) * Aminus μ := by
    have hm := mul_le_mul_of_nonneg_left ha
      (show 0 ≤ 3 * (Real.sqrt 10 + 3) by positivity)
    nlinarith only [hm, sqrt_ten_lower]
  have hcp : (36 / 5 : ℝ) ≤ 3 * (Real.sqrt 10 + 1) * Aplus μ := by
    have hm := mul_le_mul_of_nonneg_left hb
      (show 0 ≤ 3 * (Real.sqrt 10 + 1) by positivity)
    nlinarith only [hm, sqrt_ten_lower]
  have hnm := mul_le_mul_of_nonneg_right hcm htm
  have hnp := mul_le_mul_of_nonneg_right hcp htp
  change thetaMinus μ h + thetaPlus μ h ≤ (1 : ℝ) / 12
  norm_num only [defectCeiling] at hD
  nlinarith only [hj, hbase, hgap, hnm, hnp, hD]

theorem actual_joint_plane_of_defect (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hp : p μ ∈ Icc (39 / 100 : ℝ) (2 / 5))
    (hD : actualPhysicalDefect μ ≤ defectCeiling) :
    PhysicalResourcePlane.gapPrice (1 / 12) (2 / 5) (3 / 5) * (a0 μ h + a1 μ h) +
      noiseLevel μ h 26 * ((1 - ConditionalResidual.actualAllocation μ h) *
        PhysicalResourcePlane.noisePriceMinus 26 (1 / 12) (2 / 5) (6 / 25) +
        ConditionalResidual.actualAllocation μ h *
          PhysicalResourcePlane.noisePricePlus 26 (1 / 12) (3 / 5) (6 / 25)) ≤
      defectCeiling - PhysicalResourcePlane.biasPrice (39 / 100) (2 / 5) (1 / 12) (6 / 25) := by
  obtain ⟨ha, hb⟩ := endpoints_of_defect μ h hp hD
  have hv : p μ * q μ ≤ (6 / 25 : ℝ) := by
    have hmul := mul_nonneg (show 0 ≤ (2 / 5 : ℝ) - p μ by linarith only [hp.2])
      (show 0 ≤ (3 / 5 : ℝ) - p μ by linarith only [hp.2])
    unfold q
    nlinarith only [hmul]
  exact PhysicalResourcePlane.actual_resource_plane μ h (zero_absent_of_defect μ h hD)
    26 (by decide) (39 / 100) (2 / 5) (1 / 12) (2 / 5) (3 / 5) (6 / 25) defectCeiling
    (by norm_num) (by norm_num) hp (by norm_num) (theta_of_defect μ h hp hD)
    (by norm_num) (by norm_num) ha hb (by norm_num) hv hD

/-- A forward actual-law endpoint. The two incoming analytic obligations
are literal raw prices; no endpoint, theta, resource-plane, H0/H1 or
Lambda number is assumed. This is the coarse plane, not the old profile. -/
theorem actual_joint_plane_of_phase_raw (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (H C : ℝ) (hm : ContactVariation.PositiveClosedMaximum μ 26 H C)
    (hprev : Extremizer.fixedNSup 25 ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10)
    (hp : p μ ∈ Icc (39 / 100 : ℝ) (2 / 5))
    (hraw : ConservedResource.raw μ 26 H C ≤ firstRawBudget)
    (hrebate : ConservedResource.raw μ 26 H C - phaseCurvature * H ^ 2 ≤ directRawBudget) :
    PhysicalResourcePlane.gapPrice (1 / 12) (2 / 5) (3 / 5) * (a0 μ h + a1 μ h) +
      noiseLevel μ h 26 * ((1 - ConditionalResidual.actualAllocation μ h) *
        PhysicalResourcePlane.noisePriceMinus 26 (1 / 12) (2 / 5) (6 / 25) +
        ConditionalResidual.actualAllocation μ h *
          PhysicalResourcePlane.noisePricePlus 26 (1 / 12) (3 / 5) (6 / 25)) ≤
      defectCeiling - PhysicalResourcePlane.biasPrice (39 / 100) (2 / 5) (1 / 12) (6 / 25) :=
  actual_joint_plane_of_defect μ h hp (defect_of_phase_raw μ h H C hm hprev hC hρ hraw hrebate)

end BerryEsseen.N26P39ResourceAcquisition

#print axioms BerryEsseen.N26P39ResourceAcquisition.original_support
#print axioms BerryEsseen.N26P39ResourceAcquisition.original_moment_affine
#print axioms BerryEsseen.N26P39ResourceAcquisition.original_moment_caps
#print axioms BerryEsseen.N26P39ResourceAcquisition.defect_of_direct_raw
#print axioms BerryEsseen.N26P39ResourceAcquisition.defect_of_phase_raw
#print axioms BerryEsseen.N26P39ResourceAcquisition.endpoints_of_defect
#print axioms BerryEsseen.N26P39ResourceAcquisition.theta_of_defect
#print axioms BerryEsseen.N26P39ResourceAcquisition.actual_joint_plane_of_defect
#print axioms BerryEsseen.N26P39ResourceAcquisition.actual_joint_plane_of_phase_raw
