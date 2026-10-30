module

public import BerryEsseen.OuterGapCost
public import BerryEsseen.ConditionalCubic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-! 2026-10-28: the joint physical defect budget of the original law.
Sign-conditional cubic budgets, first moments, conditional variances,
central gaps and the convergent original gap resource share the same law. -/

noncomputable section

open MeasureTheory Set

namespace BerryEsseen.JointDefect

open CanonicalSign CentralGap NoiseCoordinates ZeroBias ZeroBiasStopLoss
open GapDefect PhysicalDefect OuterGapCost

def barAplus (μ : ProbabilityMeasure ℝ) : ℝ := positiveFirstMoment μ / p μ
def barAminus (μ : ProbabilityMeasure ℝ) : ℝ := positiveFirstMoment μ / q μ
def deltaPlus (μ : ProbabilityMeasure ℝ) : ℝ := barAplus μ - Aplus μ
def deltaMinus (μ : ProbabilityMeasure ℝ) : ℝ := barAminus μ - Aminus μ
def pStar : ℝ := (4 - Real.sqrt 10) / 2

private lemma integral_sign_groups (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (f : ℝ → ℝ) (hf : Integrable f (μ : Measure ℝ)) :
    (∫ x : ℝ, f x ∂(μ : Measure ℝ)) =
      q μ * (∫ x : ℝ, f x ∂(SignSplit.nonpositiveLaw μ h : Measure ℝ)) +
      p μ * (∫ x : ℝ, f x ∂(SignSplit.positiveLaw μ h : Measure ℝ)) := by
  have h0 := integrable_nonpositive μ h f hf
  have h1 := integrable_positive μ h f hf
  have heq := congrArg (fun ν : Measure ℝ => ∫ x : ℝ, f x ∂ν) (SignSplit.law_eq_sign_mixture μ h)
  rw [integral_add_measure (h0.smul_measure ENNReal.ofReal_ne_top)
      (h1.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
    ENNReal.toReal_ofReal (SignSplit.weights_pos μ h).2.le,
    ENNReal.toReal_ofReal (SignSplit.weights_pos μ h).1.le] at heq
  simpa only [q_eq_nonpositiveWeight, p, smul_eq_mul] using heq

private lemma positive_power_group (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (hn : 0 < n) (hi : Integrable (fun x : ℝ => positivePart x ^ n) (μ : Measure ℝ)) :
    (∫ x : ℝ, positivePart x ^ n ∂(μ : Measure ℝ)) =
      p μ * (∫ x : ℝ, x ^ n ∂(SignSplit.positiveLaw μ h : Measure ℝ)) := by
  have hg := integral_sign_groups μ h (fun x : ℝ => positivePart x ^ n) hi
  have h0 : (∫ x : ℝ, positivePart x ^ n ∂(SignSplit.nonpositiveLaw μ h : Measure ℝ)) = 0 := by
    calc
      _ = ∫ _ : ℝ, (0 : ℝ) ∂(SignSplit.nonpositiveLaw μ h : Measure ℝ) :=
        integral_congr_ae ((nonpositive_ae μ h).mono fun x hx => by
          change positivePart x ^ n = 0
          simp [positivePart, max_eq_right hx, Nat.ne_of_gt hn])
      _ = 0 := integral_zero _ _
  have h1 : (∫ x : ℝ, positivePart x ^ n ∂(SignSplit.positiveLaw μ h : Measure ℝ)) =
      ∫ x : ℝ, x ^ n ∂(SignSplit.positiveLaw μ h : Measure ℝ) :=
    integral_congr_ae ((positive_ae μ h).mono fun x hx => by
      change positivePart x ^ n = x ^ n
      rw [positivePart, max_eq_left hx.le])
  rw [h0, h1] at hg
  simpa only [mul_zero, zero_add] using hg

private lemma negative_power_group (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (hn : 0 < n) (hi : Integrable (fun x : ℝ => negativePart x ^ n) (μ : Measure ℝ)) :
    (∫ x : ℝ, negativePart x ^ n ∂(μ : Measure ℝ)) =
      q μ * (∫ x : ℝ, (-x) ^ n ∂(SignSplit.nonpositiveLaw μ h : Measure ℝ)) := by
  have hg := integral_sign_groups μ h (fun x : ℝ => negativePart x ^ n) hi
  have h0 : (∫ x : ℝ, negativePart x ^ n ∂(SignSplit.nonpositiveLaw μ h : Measure ℝ)) =
      ∫ x : ℝ, (-x) ^ n ∂(SignSplit.nonpositiveLaw μ h : Measure ℝ) :=
    integral_congr_ae ((nonpositive_ae μ h).mono fun x hx => by
      change negativePart x ^ n = (-x) ^ n
      rw [negativePart, max_eq_left (neg_nonneg.mpr hx)])
  have h1 : (∫ x : ℝ, negativePart x ^ n ∂(SignSplit.positiveLaw μ h : Measure ℝ)) = 0 := by
    calc
      _ = ∫ _ : ℝ, (0 : ℝ) ∂(SignSplit.positiveLaw μ h : Measure ℝ) :=
        integral_congr_ae ((positive_ae μ h).mono fun x hx => by
          change negativePart x ^ n = 0
          simp [negativePart, max_eq_right (neg_nonpos.mpr hx.le), Nat.ne_of_gt hn])
      _ = 0 := integral_zero _ _
  rw [h0, h1] at hg
  simpa only [mul_zero, add_zero] using hg

lemma positiveSecondMoment_group (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    positiveSecondMoment μ = p μ * (∫ x : ℝ, x ^ 2 ∂(SignSplit.positiveLaw μ h : Measure ℝ)) :=
  positive_power_group μ h 2 (by norm_num) (integrable_positivePart_sq μ h)

lemma negativeSecondMoment_group (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    negativeSecondMoment μ = q μ * (∫ x : ℝ, x ^ 2 ∂(SignSplit.nonpositiveLaw μ h : Measure ℝ)) := by
  unfold negativeSecondMoment
  simpa only [neg_sq] using negative_power_group μ h 2 (by norm_num) (integrable_negativePart_sq μ h)

lemma positiveThirdMoment_group (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    positiveThirdMoment μ = p μ * (∫ x : ℝ, x ^ 3 ∂(SignSplit.positiveLaw μ h : Measure ℝ)) :=
  positive_power_group μ h 3 (by norm_num) (integrable_positivePart_cube μ h)

lemma negativeThirdMoment_group (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    negativeThirdMoment μ = -(q μ) * (∫ x : ℝ, x ^ 3 ∂(SignSplit.nonpositiveLaw μ h : Measure ℝ)) := by
  have hg := negative_power_group μ h 3 (by norm_num) (integrable_negativePart_cube μ h)
  have heq : (fun x : ℝ => (-x) ^ 3) = (fun x : ℝ => -(x ^ 3)) := by ext x; ring
  rw [heq, integral_neg] at hg
  change negativeThirdMoment μ = _ at hg
  nlinarith only [hg]

lemma positiveFirstMoment_neg_group (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    positiveFirstMoment μ = -(q μ) * mean0 μ h := by
  have hm := mean_balance μ h
  have hp := positiveFirstMoment_eq_group μ h
  nlinarith

theorem barAplus_eq_mean1 (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    barAplus μ = mean1 μ h := by
  apply (div_eq_iff (p_pos μ h).ne').mpr
  nlinarith [positiveFirstMoment_eq_group μ h]

theorem barAminus_eq_neg_mean0 (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    barAminus μ = -mean0 μ h := by
  apply (div_eq_iff (q_pos μ h).ne').mpr
  nlinarith [positiveFirstMoment_neg_group μ h]

private lemma positive_conditional_budget (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    Aplus μ ≤ mean1 μ h ∧ mean1 μ h ^ 3 + 3 * Aplus μ * conditionalVariance1 μ h ≤
      ∫ x : ℝ, x ^ 3 ∂(SignSplit.positiveLaw μ h : Measure ℝ) := by
  have hl : ∀ᵐ x ∂(SignSplit.positiveLaw μ h : Measure ℝ), Aplus μ ≤ x := by
    filter_upwards [positiveLaw_support_ae μ h, positive_ae μ h] with x hx hp
    exact Aplus_le_support_nonnegative μ x hx hp.le
  exact ConditionalCubic.law_cube_budget (SignSplit.positiveLaw μ h : Measure ℝ)
    (integrable_positive μ h _ h.integrable_cube) (Aplus μ) hl

private lemma negative_conditional_budget (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    Aminus μ ≤ -mean0 μ h ∧ (-mean0 μ h) ^ 3 + 3 * Aminus μ * conditionalVariance0 μ h ≤
      -(∫ x : ℝ, x ^ 3 ∂(SignSplit.nonpositiveLaw μ h : Measure ℝ)) := by
  have hu : ∀ᵐ x ∂(SignSplit.nonpositiveLaw μ h : Measure ℝ), x ≤ -Aminus μ := by
    filter_upwards [nonpositiveLaw_support_ae μ h, nonpositive_ae μ h] with x hx hn
    exact support_nonpositive_le μ x hx hn
  have h3 := integrable_nonpositive μ h (fun x : ℝ => |x| ^ 3) h.integrable_cube
  have hm := ConditionalCubic.mean_ge_lower (SignSplit.nonpositiveLaw μ h : Measure ℝ)
    (fun x : ℝ => -x) measurable_neg
    (ConditionalCubic.integrable_abs_cube_neg (SignSplit.nonpositiveLaw μ h : Measure ℝ)
      (fun x : ℝ => x) h3) (Aminus μ) (hu.mono fun x hx => by linarith)
  rw [ConditionalCubic.mean, integral_neg] at hm
  change Aminus μ ≤ -mean0 μ h at hm
  refine ⟨hm, ?_⟩
  exact ConditionalCubic.reflected_cube_budget (SignSplit.nonpositiveLaw μ h : Measure ℝ)
    (fun x : ℝ => x) measurable_id (integrable_nonpositive μ h _ h.integrable_cube) (Aminus μ) hu

theorem deltaPlus_nonneg (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) : 0 ≤ deltaPlus μ := by
  unfold deltaPlus
  rw [barAplus_eq_mean1 μ h]
  exact sub_nonneg.mpr (positive_conditional_budget μ h).1

theorem deltaMinus_nonneg (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) : 0 ≤ deltaMinus μ := by
  unfold deltaMinus
  rw [barAminus_eq_neg_mean0 μ h]
  exact sub_nonneg.mpr (negative_conditional_budget μ h).1

theorem positiveSecondMoment_physical (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    positiveSecondMoment μ = thetaPlus μ h + positiveFirstMoment μ * barAplus μ := by
  rw [positiveSecondMoment_group μ h, barAplus_eq_mean1 μ h, positiveFirstMoment_eq_group μ h]
  unfold thetaPlus
  rw [conditionalVariance1_formula μ h]
  ring

theorem negativeSecondMoment_physical (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    negativeSecondMoment μ = thetaMinus μ h + positiveFirstMoment μ * barAminus μ := by
  rw [negativeSecondMoment_group μ h, barAminus_eq_neg_mean0 μ h, positiveFirstMoment_neg_group μ h]
  unfold thetaMinus
  rw [conditionalVariance0_formula μ h]
  ring

theorem positiveThirdMoment_physical_lower (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    positiveFirstMoment μ * barAplus μ ^ 2 + 3 * Aplus μ * thetaPlus μ h ≤ positiveThirdMoment μ := by
  calc
    _ = p μ * (mean1 μ h ^ 3 + 3 * Aplus μ * conditionalVariance1 μ h) := by
      rw [barAplus_eq_mean1 μ h, positiveFirstMoment_eq_group μ h]
      unfold thetaPlus
      ring
    _ ≤ p μ * (∫ x : ℝ, x ^ 3 ∂(SignSplit.positiveLaw μ h : Measure ℝ)) :=
      mul_le_mul_of_nonneg_left (positive_conditional_budget μ h).2 (p_pos μ h).le
    _ = _ := (positiveThirdMoment_group μ h).symm

theorem negativeThirdMoment_physical_lower (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    positiveFirstMoment μ * barAminus μ ^ 2 + 3 * Aminus μ * thetaMinus μ h ≤ negativeThirdMoment μ := by
  calc
    _ = q μ * ((-mean0 μ h) ^ 3 + 3 * Aminus μ * conditionalVariance0 μ h) := by
      rw [barAminus_eq_neg_mean0 μ h, positiveFirstMoment_neg_group μ h]
      unfold thetaMinus
      ring
    _ ≤ q μ * (-(∫ x : ℝ, x ^ 3 ∂(SignSplit.nonpositiveLaw μ h : Measure ℝ))) :=
      mul_le_mul_of_nonneg_left (negative_conditional_budget μ h).2 (q_pos μ h).le
    _ = _ := by rw [negativeThirdMoment_group μ h]; ring

theorem Rplus_physical (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    Rplus μ = thetaPlus μ h + positiveFirstMoment μ * deltaPlus μ := by
  unfold Rplus deltaPlus
  rw [positiveSecondMoment_physical μ h]
  ring

theorem Rminus_physical (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    Rminus μ = thetaMinus μ h + positiveFirstMoment μ * deltaMinus μ := by
  unfold Rminus deltaMinus
  rw [negativeSecondMoment_physical μ h]
  ring

theorem defect_ge_cubic_second_budget (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hz : (0 : ℝ) ∉ (μ : Measure ℝ).support) :
    (Real.sqrt 10 - 1) * positiveThirdMoment μ + (Real.sqrt 10 + 1) * negativeThirdMoment μ -
      6 * positiveFirstMoment μ * (Aminus μ ^ 2 + Aplus μ ^ 2 + Aminus μ * Aplus μ) +
      6 * Aplus μ * positiveSecondMoment μ + 6 * Aminus μ * negativeSecondMoment μ ≤
        actualPhysicalDefect μ := by
  have hJ := actualJ_le_central_add_excess μ h hz
  unfold actualCentralJ Tplus Tminus Rplus Rminus at hJ
  unfold actualPhysicalDefect
  rw [rho_eq_parts μ h, gamma_eq_parts μ h]
  nlinarith only [hJ]

/-- All three positive penalties are retained before the probability bias is completed to a square. -/
theorem joint_defect_bar (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hz : (0 : ℝ) ∉ (μ : Measure ℝ).support) :
    positiveFirstMoment μ * ((Real.sqrt 10 - 1) * barAplus μ ^ 2 +
      (Real.sqrt 10 + 1) * barAminus μ ^ 2 - 6 * barAminus μ * barAplus μ) +
      6 * positiveFirstMoment μ * ((Aminus μ + Aplus μ) * (deltaMinus μ + deltaPlus μ) +
        deltaMinus μ * deltaPlus μ) +
      3 * (Real.sqrt 10 + 3) * Aminus μ * thetaMinus μ h +
      3 * (Real.sqrt 10 + 1) * Aplus μ * thetaPlus μ h ≤ actualPhysicalDefect μ := by
  have hb := defect_ge_cubic_second_budget μ h hz
  have hp := mul_le_mul_of_nonneg_left (positiveThirdMoment_physical_lower μ h) sqrt_ten_sub_one_pos.le
  have hn := mul_le_mul_of_nonneg_left (negativeThirdMoment_physical_lower μ h)
    (show (0 : ℝ) ≤ Real.sqrt 10 + 1 by positivity)
  rw [positiveSecondMoment_physical μ h, negativeSecondMoment_physical μ h] at hb
  unfold deltaMinus deltaPlus
  nlinarith only [hb, hp, hn]

lemma p_star_polynomial (x : ℝ) :
    (Real.sqrt 10 + 1) * x ^ 2 + (Real.sqrt 10 - 1) * (1 - x) ^ 2 - 6 * x * (1 - x) =
      (6 + 2 * Real.sqrt 10) * (x - pStar) ^ 2 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 10)
  have hc : Real.sqrt 10 ^ 3 = 10 * Real.sqrt 10 := by
    calc
      Real.sqrt 10 ^ 3 = Real.sqrt 10 ^ 2 * Real.sqrt 10 := by ring
      _ = _ := by rw [hs]
  have hx := congrArg (fun z : ℝ => z * x) hs
  unfold pStar
  nlinarith only [hs, hc, hx]

theorem bias_eq_square (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    positiveFirstMoment μ * ((Real.sqrt 10 - 1) * barAplus μ ^ 2 +
      (Real.sqrt 10 + 1) * barAminus μ ^ 2 - 6 * barAminus μ * barAplus μ) =
      positiveFirstMoment μ ^ 3 / (p μ ^ 2 * q μ ^ 2) * (6 + 2 * Real.sqrt 10) *
        (p μ - pStar) ^ 2 := by
  calc
    _ = positiveFirstMoment μ ^ 3 / (p μ ^ 2 * q μ ^ 2) *
        ((Real.sqrt 10 + 1) * p μ ^ 2 + (Real.sqrt 10 - 1) * q μ ^ 2 - 6 * p μ * q μ) := by
      unfold barAplus barAminus
      field_simp [(p_pos μ h).ne', (q_pos μ h).ne']
      ring
    _ = _ := by
      have heq : (Real.sqrt 10 + 1) * p μ ^ 2 + (Real.sqrt 10 - 1) * q μ ^ 2 - 6 * p μ * q μ =
          (6 + 2 * Real.sqrt 10) * (p μ - pStar) ^ 2 := by
        simpa only [CanonicalSign.q] using p_star_polynomial (p μ)
      rw [heq]
      ring

/-- The full joint physical budget in the equivalent `m^3/v^2` coordinates. -/
theorem joint_defect_moment (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hz : (0 : ℝ) ∉ (μ : Measure ℝ).support) :
    positiveFirstMoment μ ^ 3 / (p μ ^ 2 * q μ ^ 2) * (6 + 2 * Real.sqrt 10) * (p μ - pStar) ^ 2 +
      6 * positiveFirstMoment μ * ((Aminus μ + Aplus μ) * (deltaMinus μ + deltaPlus μ) +
        deltaMinus μ * deltaPlus μ) +
      3 * (Real.sqrt 10 + 3) * Aminus μ * thetaMinus μ h +
      3 * (Real.sqrt 10 + 1) * Aplus μ * thetaPlus μ h ≤ actualPhysicalDefect μ := by
  have hb := joint_defect_bar μ h hz
  rw [bias_eq_square μ h] at hb
  exact hb

theorem biasCoefficient_eq_sqrt (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    positiveFirstMoment μ ^ 3 / (p μ ^ 2 * q μ ^ 2) =
      Real.sqrt (1 - theta μ h) ^ 3 / Real.sqrt (p μ * q μ) := by
  have hv := mul_pos (p_pos μ h) (q_pos μ h)
  have hm : positiveFirstMoment μ = Real.sqrt (p μ * q μ) * Real.sqrt (1 - theta μ h) := by
    calc
      positiveFirstMoment μ = Real.sqrt (positiveFirstMoment μ ^ 2) := by
        rw [Real.sqrt_sq_eq_abs, abs_of_pos (positiveFirstMoment_pos μ h)]
      _ = Real.sqrt ((p μ * q μ) * (1 - theta μ h)) := by rw [positiveFirstMoment_sq μ h]
      _ = _ := Real.sqrt_mul hv.le _
  rw [← mul_pow]
  apply (div_eq_div_iff (pow_ne_zero 2 hv.ne') (Real.sqrt_pos.mpr hv).ne').mpr
  calc
    positiveFirstMoment μ ^ 3 * Real.sqrt (p μ * q μ) =
        (Real.sqrt (p μ * q μ) * Real.sqrt (1 - theta μ h)) ^ 3 * Real.sqrt (p μ * q μ) := by rw [hm]
    _ = Real.sqrt (1 - theta μ h) ^ 3 * (Real.sqrt (p μ * q μ) ^ 2) ^ 2 := by ring
    _ = _ := by rw [Real.sq_sqrt hv.le]

theorem biasCoefficient_eq_radical (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    positiveFirstMoment μ ^ 3 / (p μ ^ 2 * q μ ^ 2) =
      (1 - theta μ h) ^ ((3 : ℝ) / 2) / Real.sqrt (p μ * q μ) := by
  have hr : (1 - theta μ h) ^ ((3 : ℝ) / 2) = Real.sqrt (1 - theta μ h) ^ (3 : ℕ) := by
    exact (Real.rpow_div_two_eq_sqrt (x := 1 - theta μ h) (3 : ℝ)
      (sub_pos.mpr (theta_lt_one μ h)).le).trans (Real.rpow_ofNat _ 3)
  rw [biasCoefficient_eq_sqrt μ h, hr]

/-- The manuscript's full radical form, with the same actual allocation variances. -/
theorem joint_defect (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hz : (0 : ℝ) ∉ (μ : Measure ℝ).support) :
    ((6 + 2 * Real.sqrt 10) * (1 - theta μ h) ^ ((3 : ℝ) / 2) / Real.sqrt (p μ * q μ)) *
        (p μ - pStar) ^ 2 +
      6 * positiveFirstMoment μ * ((Aminus μ + Aplus μ) * (deltaMinus μ + deltaPlus μ) +
        deltaMinus μ * deltaPlus μ) +
      3 * (Real.sqrt 10 + 3) * Aminus μ * thetaMinus μ h +
      3 * (Real.sqrt 10 + 1) * Aplus μ * thetaPlus μ h ≤ actualPhysicalDefect μ := by
  have hb := joint_defect_moment μ h hz
  rw [biasCoefficient_eq_radical μ h] at hb
  convert hb using 1
  ring

theorem joint_defect_of_small (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hsmall : actualPhysicalDefect μ < (Real.sqrt 10 - 1) * thirdAbsoluteMoment μ) :
    ((6 + 2 * Real.sqrt 10) * (1 - theta μ h) ^ ((3 : ℝ) / 2) / Real.sqrt (p μ * q μ)) *
        (p μ - pStar) ^ 2 +
      6 * positiveFirstMoment μ * ((Aminus μ + Aplus μ) * (deltaMinus μ + deltaPlus μ) +
        deltaMinus μ * deltaPlus μ) +
      3 * (Real.sqrt 10 + 3) * Aminus μ * thetaMinus μ h +
      3 * (Real.sqrt 10 + 1) * Aplus μ * thetaPlus μ h ≤ actualPhysicalDefect μ :=
  joint_defect μ h (zero_notMem_support_of_defect_small μ h hsmall)

end BerryEsseen.JointDefect

#print axioms BerryEsseen.JointDefect.positiveSecondMoment_physical
#print axioms BerryEsseen.JointDefect.negativeSecondMoment_physical
#print axioms BerryEsseen.JointDefect.positiveThirdMoment_physical_lower
#print axioms BerryEsseen.JointDefect.negativeThirdMoment_physical_lower
#print axioms BerryEsseen.JointDefect.Rplus_physical
#print axioms BerryEsseen.JointDefect.Rminus_physical
#print axioms BerryEsseen.JointDefect.joint_defect_moment
#print axioms BerryEsseen.JointDefect.biasCoefficient_eq_radical
#print axioms BerryEsseen.JointDefect.joint_defect
#print axioms BerryEsseen.JointDefect.joint_defect_of_small
