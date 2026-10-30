module

public import BerryEsseen.PearsonMoments
public import BerryEsseen.JointDefect

@[expose] public section

/-! 2026-10-29: actual fourth/fifth moment ceilings from acquired support
and the same law's sign-conditional means and variances. Every polynomial
is L1 by its actual bounded variable. The nonpositive conditional group
retains zero atoms; negating its coordinate does not reflect the original law. -/

noncomputable section

namespace BerryEsseen.PhysicalMomentUpper

open MeasureTheory Set
open CharacteristicExpansion CanonicalSign NoiseCoordinates JointDefect

def absoluteMoment (μ : ProbabilityMeasure ℝ) (k : ℕ) : ℝ :=
  ∫ x : ℝ, |x| ^ k ∂(μ : Measure ℝ)

def P4 (y m : ℝ) : ℝ := y ^ 2 + 2 * m * y + 3 * m ^ 2
def P5 (y m : ℝ) : ℝ := y ^ 3 + 2 * m * y ^ 2 + 3 * m ^ 2 * y + 4 * m ^ 3

variable {Ω : Type*} [MeasurableSpace Ω]

theorem integrable_abs_pow_of_bound (ν : Measure Ω) [IsFiniteMeasure ν]
    (Y : Ω → ℝ) (hY : Measurable Y) (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ᵐ ω ∂ν, |Y ω| ≤ R) (k : ℕ) :
    Integrable (fun ω => |Y ω| ^ k) ν := by
  have hm : AEStronglyMeasurable (fun ω => |Y ω| ^ k) ν := by fun_prop
  apply (integrable_const (R ^ k)).mono' hm
  filter_upwards [hbound] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
  exact pow_le_pow_left₀ (abs_nonneg _) hω k

theorem integrable_pow_of_bound (ν : Measure Ω) [IsFiniteMeasure ν]
    (Y : Ω → ℝ) (hY : Measurable Y) (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ᵐ ω ∂ν, |Y ω| ≤ R) (k : ℕ) : Integrable (fun ω => Y ω ^ k) ν := by
  apply (integrable_norm_iff (hY.pow_const k).aestronglyMeasurable).mp
  simpa only [Real.norm_eq_abs, abs_pow] using integrable_abs_pow_of_bound ν Y hY R hR hbound k

theorem absoluteMoment_le_radius_power (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (R : ℝ) (hR : 0 ≤ R) (hbound : ∀ᵐ x ∂(μ : Measure ℝ), |x| ≤ R) (j : ℕ) :
    absoluteMoment μ (3 + j) ≤ R ^ j * thirdAbsoluteMoment μ := by
  have hi := integrable_abs_pow_of_bound (μ : Measure ℝ) id measurable_id R hR hbound (3 + j)
  unfold absoluteMoment thirdAbsoluteMoment
  rw [← integral_const_mul]
  apply integral_mono_ae hi (h.integrable_cube.const_mul (R ^ j))
  filter_upwards [hbound] with x hx
  simp only [id_eq]
  rw [pow_add]
  have hp := pow_le_pow_left₀ (abs_nonneg x) hx j
  nlinarith only [mul_le_mul_of_nonneg_left hp (pow_nonneg (abs_nonneg x) 3)]

theorem absoluteMoment_le_radius_sub_three (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (R : ℝ) (hR : 0 ≤ R) (hbound : ∀ᵐ x ∂(μ : Measure ℝ), |x| ≤ R)
    (k : ℕ) (hk : 3 ≤ k) :
    absoluteMoment μ k ≤ R ^ (k - 3) * thirdAbsoluteMoment μ := by
  have hs : 3 + (k - 3) = k := Nat.add_sub_of_le hk
  simpa only [hs] using absoluteMoment_le_radius_power μ h R hR hbound (k - 3)

theorem initial_moment_caps (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (R rhoU : ℝ) (hR : 0 ≤ R) (hbound : ∀ᵐ x ∂(μ : Measure ℝ), |x| ≤ R)
    (hρ : thirdAbsoluteMoment μ ≤ rhoU) :
    moment μ 4 ≤ R * rhoU ∧ absoluteMoment μ 5 ≤ R ^ 2 * rhoU ∧
      sixthMoment μ ≤ R ^ 3 * rhoU := by
  have h4 := absoluteMoment_le_radius_power μ h R hR hbound 1
  have h5 := absoluteMoment_le_radius_power μ h R hR hbound 2
  have h6 := absoluteMoment_le_radius_power μ h R hR hbound 3
  simp only [pow_one] at h4
  refine ⟨?_, ?_, ?_⟩
  · rw [PearsonMoments.moment_four_eq_abs]
    exact h4.trans (mul_le_mul_of_nonneg_left hρ hR)
  · exact h5.trans (mul_le_mul_of_nonneg_left hρ (sq_nonneg _))
  · exact h6.trans (mul_le_mul_of_nonneg_left hρ (pow_nonneg hR 3))

private lemma abs_bound_of_nonnegative_bound (ν : Measure Ω) (Y : Ω → ℝ) (R : ℝ)
    (hbound : ∀ᵐ ω ∂ν, 0 ≤ Y ω ∧ Y ω ≤ R) : ∀ᵐ ω ∂ν, |Y ω| ≤ R :=
  hbound.mono (fun _ hω => by rw [abs_of_nonneg hω.1]; exact hω.2)

private lemma integrable_first_of_bound (ν : Measure Ω) [IsFiniteMeasure ν]
    (Y : Ω → ℝ) (hY : Measurable Y) (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ᵐ ω ∂ν, |Y ω| ≤ R) : Integrable Y ν := by
  simpa only [pow_one] using integrable_pow_of_bound ν Y hY R hR hbound 1

theorem integrable_fourth_remainder (ν : Measure Ω) [IsProbabilityMeasure ν]
    (Y : Ω → ℝ) (hY : Measurable Y) (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ᵐ ω ∂ν, |Y ω| ≤ R) :
    Integrable (fun ω => (Y ω - ConditionalCubic.mean ν Y) ^ 2 *
      P4 (Y ω) (ConditionalCubic.mean ν Y)) ν := by
  have h4 := integrable_pow_of_bound ν Y hY R hR hbound 4
  have h1 := integrable_first_of_bound ν Y hY R hR hbound
  have hcenter : Integrable (fun ω => Y ω - ConditionalCubic.mean ν Y) ν :=
    h1.sub (integrable_const _)
  convert (h4.sub (integrable_const (ConditionalCubic.mean ν Y ^ 4))).sub
    (hcenter.const_mul (4 * ConditionalCubic.mean ν Y ^ 3)) using 1
  ext ω
  simp only [Pi.sub_apply, P4]
  ring

theorem integrable_fifth_remainder (ν : Measure Ω) [IsProbabilityMeasure ν]
    (Y : Ω → ℝ) (hY : Measurable Y) (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ᵐ ω ∂ν, |Y ω| ≤ R) :
    Integrable (fun ω => (Y ω - ConditionalCubic.mean ν Y) ^ 2 *
      P5 (Y ω) (ConditionalCubic.mean ν Y)) ν := by
  have h5 := integrable_pow_of_bound ν Y hY R hR hbound 5
  have h1 := integrable_first_of_bound ν Y hY R hR hbound
  have hcenter : Integrable (fun ω => Y ω - ConditionalCubic.mean ν Y) ν :=
    h1.sub (integrable_const _)
  convert (h5.sub (integrable_const (ConditionalCubic.mean ν Y ^ 5))).sub
    (hcenter.const_mul (5 * ConditionalCubic.mean ν Y ^ 4)) using 1
  ext ω
  simp only [Pi.sub_apply, P5]
  ring

theorem fourth_taylor_identity (ν : Measure Ω) [IsProbabilityMeasure ν]
    (Y : Ω → ℝ) (hY : Measurable Y) (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ᵐ ω ∂ν, |Y ω| ≤ R) :
    (∫ ω, Y ω ^ 4 ∂ν) = ConditionalCubic.mean ν Y ^ 4 +
      ∫ ω, (Y ω - ConditionalCubic.mean ν Y) ^ 2 * P4 (Y ω) (ConditionalCubic.mean ν Y) ∂ν := by
  have h4 := integrable_pow_of_bound ν Y hY R hR hbound 4
  have h1 := integrable_first_of_bound ν Y hY R hR hbound
  have hcenter : Integrable (fun ω => Y ω - ConditionalCubic.mean ν Y) ν :=
    h1.sub (integrable_const _)
  have hp : Integrable (fun ω => Y ω ^ 4 - ConditionalCubic.mean ν Y ^ 4) ν :=
    h4.sub (integrable_const _)
  have heq : (fun ω => (Y ω - ConditionalCubic.mean ν Y) ^ 2 *
      P4 (Y ω) (ConditionalCubic.mean ν Y)) =
      (fun ω => Y ω ^ 4 - ConditionalCubic.mean ν Y ^ 4 -
        4 * ConditionalCubic.mean ν Y ^ 3 * (Y ω - ConditionalCubic.mean ν Y)) := by
    ext ω
    unfold P4
    ring
  rw [heq, integral_sub hp (hcenter.const_mul _), integral_sub h4 (integrable_const _),
    integral_const_mul, ConditionalCubic.integral_centered_eq_zero ν Y h1]
  simp

theorem fifth_taylor_identity (ν : Measure Ω) [IsProbabilityMeasure ν]
    (Y : Ω → ℝ) (hY : Measurable Y) (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ᵐ ω ∂ν, |Y ω| ≤ R) :
    (∫ ω, Y ω ^ 5 ∂ν) = ConditionalCubic.mean ν Y ^ 5 +
      ∫ ω, (Y ω - ConditionalCubic.mean ν Y) ^ 2 * P5 (Y ω) (ConditionalCubic.mean ν Y) ∂ν := by
  have h5 := integrable_pow_of_bound ν Y hY R hR hbound 5
  have h1 := integrable_first_of_bound ν Y hY R hR hbound
  have hcenter : Integrable (fun ω => Y ω - ConditionalCubic.mean ν Y) ν :=
    h1.sub (integrable_const _)
  have hp : Integrable (fun ω => Y ω ^ 5 - ConditionalCubic.mean ν Y ^ 5) ν :=
    h5.sub (integrable_const _)
  have heq : (fun ω => (Y ω - ConditionalCubic.mean ν Y) ^ 2 *
      P5 (Y ω) (ConditionalCubic.mean ν Y)) =
      (fun ω => Y ω ^ 5 - ConditionalCubic.mean ν Y ^ 5 -
        5 * ConditionalCubic.mean ν Y ^ 4 * (Y ω - ConditionalCubic.mean ν Y)) := by
    ext ω
    unfold P5
    ring
  rw [heq, integral_sub hp (hcenter.const_mul _), integral_sub h5 (integrable_const _),
    integral_const_mul, ConditionalCubic.integral_centered_eq_zero ν Y h1]
  simp

private lemma P4_le_endpoint (y m R : ℝ) (hy : 0 ≤ y) (hym : y ≤ R) (hm : 0 ≤ m) :
    P4 y m ≤ P4 R m := by
  have h2 := pow_le_pow_left₀ hy hym 2
  have hlin := mul_le_mul_of_nonneg_left hym (by positivity : 0 ≤ 2 * m)
  unfold P4
  nlinarith only [h2, hlin]

private lemma P5_le_endpoint (y m R : ℝ) (hy : 0 ≤ y) (hym : y ≤ R) (hm : 0 ≤ m) :
    P5 y m ≤ P5 R m := by
  have h2 := pow_le_pow_left₀ hy hym 2
  have h3 := pow_le_pow_left₀ hy hym 3
  have hquad := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ 2 * m)
  have hlin := mul_le_mul_of_nonneg_left hym (by positivity : 0 ≤ 3 * m ^ 2)
  unfold P5
  nlinarith only [h3, hquad, hlin]

theorem fourth_moment_upper (ν : Measure Ω) [IsProbabilityMeasure ν]
    (Y : Ω → ℝ) (hY : Measurable Y) (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ᵐ ω ∂ν, 0 ≤ Y ω ∧ Y ω ≤ R) :
    (∫ ω, Y ω ^ 4 ∂ν) ≤ ConditionalCubic.mean ν Y ^ 4 +
      ConditionalCubic.variance ν Y * P4 R (ConditionalCubic.mean ν Y) := by
  have hb := abs_bound_of_nonnegative_bound ν Y R hbound
  have h3 := integrable_abs_pow_of_bound ν Y hY R hR hb 3
  have hV := ConditionalCubic.integrable_centered_square ν Y hY h3
  have hm : 0 ≤ ConditionalCubic.mean ν Y := integral_nonneg_of_ae (hbound.mono fun _ hω => hω.1)
  have hi : (∫ ω, (Y ω - ConditionalCubic.mean ν Y) ^ 2 *
      P4 (Y ω) (ConditionalCubic.mean ν Y) ∂ν) ≤
      ConditionalCubic.variance ν Y * P4 R (ConditionalCubic.mean ν Y) := by
    rw [ConditionalCubic.variance, ← integral_mul_const]
    apply integral_mono_ae (integrable_fourth_remainder ν Y hY R hR hb) (hV.mul_const _)
    filter_upwards [hbound] with ω hω
    exact mul_le_mul_of_nonneg_left (P4_le_endpoint _ _ _ hω.1 hω.2 hm) (sq_nonneg _)
  rw [fourth_taylor_identity ν Y hY R hR hb]
  exact add_le_add le_rfl hi

theorem fifth_moment_upper (ν : Measure Ω) [IsProbabilityMeasure ν]
    (Y : Ω → ℝ) (hY : Measurable Y) (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ᵐ ω ∂ν, 0 ≤ Y ω ∧ Y ω ≤ R) :
    (∫ ω, Y ω ^ 5 ∂ν) ≤ ConditionalCubic.mean ν Y ^ 5 +
      ConditionalCubic.variance ν Y * P5 R (ConditionalCubic.mean ν Y) := by
  have hb := abs_bound_of_nonnegative_bound ν Y R hbound
  have h3 := integrable_abs_pow_of_bound ν Y hY R hR hb 3
  have hV := ConditionalCubic.integrable_centered_square ν Y hY h3
  have hm : 0 ≤ ConditionalCubic.mean ν Y := integral_nonneg_of_ae (hbound.mono fun _ hω => hω.1)
  have hi : (∫ ω, (Y ω - ConditionalCubic.mean ν Y) ^ 2 *
      P5 (Y ω) (ConditionalCubic.mean ν Y) ∂ν) ≤
      ConditionalCubic.variance ν Y * P5 R (ConditionalCubic.mean ν Y) := by
    rw [ConditionalCubic.variance, ← integral_mul_const]
    apply integral_mono_ae (integrable_fifth_remainder ν Y hY R hR hb) (hV.mul_const _)
    filter_upwards [hbound] with ω hω
    exact mul_le_mul_of_nonneg_left (P5_le_endpoint _ _ _ hω.1 hω.2 hm) (sq_nonneg _)
  rw [fifth_taylor_identity ν Y hY R hR hb]
  exact add_le_add le_rfl hi

private lemma integral_sign_groups (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (f : ℝ → ℝ) (hf : Integrable f (μ : Measure ℝ)) :
    (∫ x, f x ∂(μ : Measure ℝ)) =
      q μ * (∫ x, f x ∂(SignSplit.nonpositiveLaw μ h : Measure ℝ)) +
      p μ * (∫ x, f x ∂(SignSplit.positiveLaw μ h : Measure ℝ)) := by
  have h0 := integrable_nonpositive μ h f hf
  have h1 := integrable_positive μ h f hf
  have heq := congrArg (fun ν : Measure ℝ => ∫ x, f x ∂ν) (SignSplit.law_eq_sign_mixture μ h)
  rw [integral_add_measure (h0.smul_measure ENNReal.ofReal_ne_top)
      (h1.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
    ENNReal.toReal_ofReal (SignSplit.weights_pos μ h).2.le,
    ENNReal.toReal_ofReal (SignSplit.weights_pos μ h).1.le] at heq
  simpa only [q_eq_nonpositiveWeight, p, smul_eq_mul] using heq

private lemma absolute_power_groups (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (k : ℕ) (hi : Integrable (fun x : ℝ => |x| ^ k) (μ : Measure ℝ)) :
    absoluteMoment μ k = q μ * (∫ x, (-x) ^ k ∂(SignSplit.nonpositiveLaw μ h : Measure ℝ)) +
      p μ * (∫ x, x ^ k ∂(SignSplit.positiveLaw μ h : Measure ℝ)) := by
  have hg := integral_sign_groups μ h (fun x : ℝ => |x| ^ k) hi
  have h0 : (∫ x : ℝ, |x| ^ k ∂(SignSplit.nonpositiveLaw μ h : Measure ℝ)) =
      ∫ x : ℝ, (-x) ^ k ∂(SignSplit.nonpositiveLaw μ h : Measure ℝ) := by
    apply integral_congr_ae
    filter_upwards [nonpositive_ae μ h] with x hx
    rw [abs_of_nonpos hx]
  have h1 : (∫ x : ℝ, |x| ^ k ∂(SignSplit.positiveLaw μ h : Measure ℝ)) =
      ∫ x : ℝ, x ^ k ∂(SignSplit.positiveLaw μ h : Measure ℝ) := by
    apply integral_congr_ae
    filter_upwards [positive_ae μ h] with x hx
    rw [abs_of_nonneg hx.le]
  rw [h0, h1] at hg
  exact hg

private lemma original_abs_bound (μ : ProbabilityMeasure ℝ) (Rm Rp : ℝ)
    (hb : ∀ᵐ x ∂(μ : Measure ℝ), -Rm ≤ x ∧ x ≤ Rp) :
    ∀ᵐ x ∂(μ : Measure ℝ), |x| ≤ max Rm Rp := by
  filter_upwards [hb] with x hx
  apply abs_le.mpr
  constructor <;> linarith [le_max_left Rm Rp, le_max_right Rm Rp]

private lemma positive_bound (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (Rm Rp : ℝ)
    (hb : ∀ᵐ x ∂(μ : Measure ℝ), -Rm ≤ x ∧ x ≤ Rp) :
    ∀ᵐ x ∂(SignSplit.positiveLaw μ h : Measure ℝ), 0 ≤ x ∧ x ≤ Rp := by
  have hac : (SignSplit.positiveLaw μ h : Measure ℝ) ≪ (μ : Measure ℝ) :=
    ProbabilityTheory.cond_absolutelyContinuous
  filter_upwards [hac.ae_le hb, positive_ae μ h] with x hx hp
  exact ⟨hp.le, hx.2⟩

private lemma negative_bound (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (Rm Rp : ℝ)
    (hb : ∀ᵐ x ∂(μ : Measure ℝ), -Rm ≤ x ∧ x ≤ Rp) :
    ∀ᵐ x ∂(SignSplit.nonpositiveLaw μ h : Measure ℝ), 0 ≤ -x ∧ -x ≤ Rm := by
  have hac : (SignSplit.nonpositiveLaw μ h : Measure ℝ) ≪ (μ : Measure ℝ) :=
    ProbabilityTheory.cond_absolutelyContinuous
  filter_upwards [hac.ae_le hb, nonpositive_ae μ h] with x hx hn
  constructor <;> linarith

private lemma negative_mean (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    ConditionalCubic.mean (SignSplit.nonpositiveLaw μ h : Measure ℝ) (fun x : ℝ => -x) =
      barAminus μ := by
  rw [ConditionalCubic.mean_neg, barAminus_eq_neg_mean0 μ h]
  rfl

private lemma positive_mean (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    ConditionalCubic.mean (SignSplit.positiveLaw μ h : Measure ℝ) id = barAplus μ :=
  (barAplus_eq_mean1 μ h).symm

private lemma negative_variance (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    ConditionalCubic.variance (SignSplit.nonpositiveLaw μ h : Measure ℝ) (fun x : ℝ => -x) =
      conditionalVariance0 μ h := by
  rw [ConditionalCubic.variance_neg]
  rfl

private lemma positive_variance (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    ConditionalCubic.variance (SignSplit.positiveLaw μ h : Measure ℝ) id =
      conditionalVariance1 μ h := rfl

theorem actual_fourth_moment_conditional_upper (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (Rm Rp : ℝ) (hRm : 0 ≤ Rm) (hRp : 0 ≤ Rp)
    (hb : ∀ᵐ x ∂(μ : Measure ℝ), -Rm ≤ x ∧ x ≤ Rp) :
    moment μ 4 ≤ p μ * barAplus μ ^ 4 + q μ * barAminus μ ^ 4 +
      thetaPlus μ h * P4 Rp (barAplus μ) + thetaMinus μ h * P4 Rm (barAminus μ) := by
  have hp := fourth_moment_upper (SignSplit.positiveLaw μ h : Measure ℝ) id measurable_id Rp hRp
    (positive_bound μ h Rm Rp hb)
  have hn := fourth_moment_upper (SignSplit.nonpositiveLaw μ h : Measure ℝ)
    (fun x : ℝ => -x) measurable_neg Rm hRm (negative_bound μ h Rm Rp hb)
  rw [positive_mean, positive_variance] at hp
  rw [negative_mean, negative_variance] at hn
  simp only [id_eq] at hp
  have hpw := mul_le_mul_of_nonneg_left hp (p_pos μ h).le
  have hnw := mul_le_mul_of_nonneg_left hn (q_pos μ h).le
  have hi := integrable_abs_pow_of_bound (μ : Measure ℝ) id measurable_id (max Rm Rp)
    (hRm.trans (le_max_left _ _)) (original_abs_bound μ Rm Rp hb) 4
  rw [PearsonMoments.moment_four_eq_abs]
  change absoluteMoment μ 4 ≤ _
  rw [absolute_power_groups μ h 4 hi]
  unfold thetaPlus thetaMinus
  nlinarith only [hpw, hnw]

theorem actual_fifth_moment_conditional_upper (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (Rm Rp : ℝ) (hRm : 0 ≤ Rm) (hRp : 0 ≤ Rp)
    (hb : ∀ᵐ x ∂(μ : Measure ℝ), -Rm ≤ x ∧ x ≤ Rp) :
    absoluteMoment μ 5 ≤ p μ * barAplus μ ^ 5 + q μ * barAminus μ ^ 5 +
      thetaPlus μ h * P5 Rp (barAplus μ) + thetaMinus μ h * P5 Rm (barAminus μ) := by
  have hp := fifth_moment_upper (SignSplit.positiveLaw μ h : Measure ℝ) id measurable_id Rp hRp
    (positive_bound μ h Rm Rp hb)
  have hn := fifth_moment_upper (SignSplit.nonpositiveLaw μ h : Measure ℝ)
    (fun x : ℝ => -x) measurable_neg Rm hRm (negative_bound μ h Rm Rp hb)
  rw [positive_mean, positive_variance] at hp
  rw [negative_mean, negative_variance] at hn
  simp only [id_eq] at hp
  have hpw := mul_le_mul_of_nonneg_left hp (p_pos μ h).le
  have hnw := mul_le_mul_of_nonneg_left hn (q_pos μ h).le
  have hi := integrable_abs_pow_of_bound (μ : Measure ℝ) id measurable_id (max Rm Rp)
    (hRm.trans (le_max_left _ _)) (original_abs_bound μ Rm Rp hb) 5
  rw [absolute_power_groups μ h 5 hi]
  unfold thetaPlus thetaMinus
  nlinarith only [hpw, hnw]

theorem mean_base_fourth_eq_physical (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    p μ * barAplus μ ^ 4 + q μ * barAminus μ ^ 4 =
      (1 - theta μ h) ^ 2 * (1 - 3 * p μ * q μ) / (p μ * q μ) := by
  have hp : p μ ≠ 0 := (p_pos μ h).ne'
  have hq : q μ ≠ 0 := (q_pos μ h).ne'
  have hm4 : positiveFirstMoment μ ^ 4 = (p μ * q μ * (1 - theta μ h)) ^ 2 := by
    calc
      _ = (positiveFirstMoment μ ^ 2) ^ 2 := by ring
      _ = _ := by rw [positiveFirstMoment_sq μ h]
  have hs : p μ ^ 3 + q μ ^ 3 = 1 - 3 * p μ * q μ := by unfold q; ring
  have heq : p μ * (positiveFirstMoment μ / p μ) ^ 4 +
      q μ * (positiveFirstMoment μ / q μ) ^ 4 =
      positiveFirstMoment μ ^ 4 * (p μ ^ 3 + q μ ^ 3) / (p μ ^ 3 * q μ ^ 3) := by
    field_simp [hp, hq]
    ring
  unfold barAplus barAminus
  rw [heq, hm4, hs]
  field_simp [hp, hq]

end BerryEsseen.PhysicalMomentUpper

#print axioms BerryEsseen.PhysicalMomentUpper.integrable_abs_pow_of_bound
#print axioms BerryEsseen.PhysicalMomentUpper.absoluteMoment_le_radius_sub_three
#print axioms BerryEsseen.PhysicalMomentUpper.initial_moment_caps
#print axioms BerryEsseen.PhysicalMomentUpper.integrable_fourth_remainder
#print axioms BerryEsseen.PhysicalMomentUpper.integrable_fifth_remainder
#print axioms BerryEsseen.PhysicalMomentUpper.fourth_taylor_identity
#print axioms BerryEsseen.PhysicalMomentUpper.fifth_taylor_identity
#print axioms BerryEsseen.PhysicalMomentUpper.fourth_moment_upper
#print axioms BerryEsseen.PhysicalMomentUpper.fifth_moment_upper
#print axioms BerryEsseen.PhysicalMomentUpper.actual_fourth_moment_conditional_upper
#print axioms BerryEsseen.PhysicalMomentUpper.actual_fifth_moment_conditional_upper
#print axioms BerryEsseen.PhysicalMomentUpper.mean_base_fourth_eq_physical
