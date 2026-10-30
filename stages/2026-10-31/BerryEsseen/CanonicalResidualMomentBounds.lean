module

public import BerryEsseen.CommonProductHigherMoments
public import BerryEsseen.CentralGap
public import BerryEsseen.NoiseCoordinates
public import BerryEsseen.PhysicalMomentUpper
public import BerryEsseen.ZeroBias

@[expose] public section

noncomputable section

namespace BerryEsseen.CanonicalResidualMomentBounds

open MeasureTheory Set
open CanonicalSign

/-- These are actual L1 moments of the canonical laws; finite absolute third
moment of the original standardized law already suffices. -/
theorem residual_integrable_through_three (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    Integrable (fun u : ℝ => u) (residual0 μ h : Measure ℝ) ∧
    Integrable (fun u : ℝ => u ^ 2) (residual0 μ h : Measure ℝ) ∧
    Integrable (fun u : ℝ => u ^ 3) (residual0 μ h : Measure ℝ) ∧
    Integrable (fun u : ℝ => u) (residual1 μ h : Measure ℝ) ∧
    Integrable (fun u : ℝ => u ^ 2) (residual1 μ h : Measure ℝ) ∧
    Integrable (fun u : ℝ => u ^ 3) (residual1 μ h : Measure ℝ) := by
  have h0 := residual0_centered μ h
  have h1 := residual1_centered μ h
  exact ⟨h0.integrable_first, h0.integrable_second, h0.integrable_third,
    h1.integrable_first, h1.integrable_second, h1.integrable_third⟩

/-- The signed third moment of the original law, with its original sign
orientation, expanded in the same actual centered residual moments. -/
theorem signedThirdMoment_identity (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    ZeroBias.gamma μ * scale μ h ^ 3 =
      p μ * q μ * (q μ - p μ) +
        3 * p μ * q μ *
          ((∫ u : ℝ, u ^ 2 ∂(residual1 μ h : Measure ℝ)) -
            (∫ u : ℝ, u ^ 2 ∂(residual0 μ h : Measure ℝ))) +
        q μ * (∫ u : ℝ, u ^ 3 ∂(residual0 μ h : Measure ℝ)) +
        p μ * (∫ u : ℝ, u ^ 3 ∂(residual1 μ h : Measure ℝ)) := by
  have h0 := residual0_centered μ h
  have h1 := residual1_centered μ h
  have hs0 := MomentBudget.integrable_cube_add_const
    (residual0 μ h : Measure ℝ) (fun u : ℝ => u) (-(p μ))
    h0.integrable_first h0.integrable_second h0.integrable_third
  have hs1 := MomentBudget.integrable_cube_add_const
    (residual1 μ h : Measure ℝ) (fun u : ℝ => u) (1 - p μ)
    h1.integrable_first h1.integrable_second h1.integrable_third
  have hi0 : Integrable (fun u : ℝ => ((u - p μ) / scale μ h) ^ 3)
      (residual0 μ h : Measure ℝ) := by
    simpa only [div_pow, sub_eq_add_neg] using hs0.div_const (scale μ h ^ 3)
  have hi1 : Integrable (fun u : ℝ => ((u + (1 - p μ)) / scale μ h) ^ 3)
      (residual1 μ h : Measure ℝ) := by
    simpa only [div_pow] using hs1.div_const (scale μ h ^ 3)
  have ht := MomentBudget.integral_residualMixture (residual0 μ h) (residual1 μ h)
    (p μ) (scale μ h) (p_pos μ h).le (p_lt_one μ h).le
    (fun x : ℝ => x ^ 3) (by fun_prop) hi0 hi1
  change (∫ x : ℝ, x ^ 3 ∂(MomentBudget.residualMixtureLaw
    (residual0 μ h) (residual1 μ h) (p μ) (scale μ h)
    (p_pos μ h).le (p_lt_one μ h).le : Measure ℝ)) = _ at ht
  rw [← law_eq_residualMixture μ h] at ht
  simp_rw [div_pow] at ht
  rw [integral_div, integral_div] at ht
  have he0 := MomentBudget.integral_cube_add_const
    (residual0 μ h : Measure ℝ) (fun u : ℝ => u) (-(p μ))
    h0.integrable_first h0.integrable_second h0.integrable_third
  have he1 := MomentBudget.integral_cube_add_const
    (residual1 μ h : Measure ℝ) (fun u : ℝ => u) (1 - p μ)
    h1.integrable_first h1.integrable_second h1.integrable_third
  simp only [h0.mean_zero, h1.mean_zero, mul_zero, add_zero] at he0 he1
  simp only [sub_eq_add_neg] at ht he1
  rw [he0, he1] at ht
  have ht' := congrArg (fun z : ℝ => z * scale μ h ^ 3) ht
  have hc : scale μ h ≠ 0 := (scale_pos μ h).ne'
  field_simp [hc] at ht'
  change ZeroBias.gamma μ * scale μ h ^ 3 = _ at ht'
  calc
    _ = _ := ht'
    _ = _ := by unfold q; ring

/-- The absolute-third identity is reused from the canonical representation;
the two residual cubic integrals on its right remain signed. -/
theorem absoluteThirdMoment_identity (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    thirdAbsoluteMoment μ * scale μ h ^ 3 =
      p μ * q μ * (1 - 2 * (p μ * q μ)) +
        3 * p μ * q μ *
          ((∫ u : ℝ, u ^ 2 ∂(residual0 μ h : Measure ℝ)) +
            (∫ u : ℝ, u ^ 2 ∂(residual1 μ h : Measure ℝ))) -
        q μ * (∫ u : ℝ, u ^ 3 ∂(residual0 μ h : Measure ℝ)) +
        p μ * (∫ u : ℝ, u ^ 3 ∂(residual1 μ h : Measure ℝ)) := by
  simpa only [MomentBudget.residualSecondMoment, MomentBudget.residualCubicMoment,
    mul_assoc] using CanonicalSign.thirdAbsoluteMoment_identity μ h

/-- Solves for the actual negative-group signed cubic integral. Positivity of
the actual sign weight supplies the only denominator condition. -/
theorem residual0_cubic_eq (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    (∫ u : ℝ, u ^ 3 ∂(residual0 μ h : Measure ℝ)) =
      (2 * q μ * p μ ^ 3 +
        6 * p μ * q μ * (∫ u : ℝ, u ^ 2 ∂(residual0 μ h : Measure ℝ)) -
        (thirdAbsoluteMoment μ - ZeroBias.gamma μ) * scale μ h ^ 3) / (2 * q μ) := by
  apply (eq_div_iff (mul_ne_zero (by norm_num) (q_pos μ h).ne')).mpr
  have hr := absoluteThirdMoment_identity μ h
  have hg := signedThirdMoment_identity μ h
  dsimp only [q] at hr hg ⊢
  linear_combination hr - hg

/-- Solves for the actual positive-group signed cubic integral. -/
theorem residual1_cubic_eq (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    (∫ u : ℝ, u ^ 3 ∂(residual1 μ h : Measure ℝ)) =
      ((thirdAbsoluteMoment μ + ZeroBias.gamma μ) * scale μ h ^ 3 -
        2 * p μ * q μ ^ 3 -
        6 * p μ * q μ * (∫ u : ℝ, u ^ 2 ∂(residual1 μ h : Measure ℝ))) / (2 * p μ) := by
  apply (eq_div_iff (mul_ne_zero (by norm_num) (p_pos μ h).ne')).mpr
  have hr := absoluteThirdMoment_identity μ h
  have hg := signedThirdMoment_identity μ h
  dsimp only [q] at hr hg ⊢
  linear_combination -hr - hg

/-- The closed outer support cap allows endpoint atoms. -/
theorem residual0_lower_of_support (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (R : ℝ) (hbound : (μ : Measure ℝ).support ⊆ Icc (-R) R) :
    ∀ᵐ u ∂(residual0 μ h : Measure ℝ), -CentralGap.O0 μ h R ≤ u := by
  have hf : Measurable (fun x : ℝ => scale μ h * x + p μ) := by fun_prop
  change ∀ᵐ u ∂(SignSplit.nonpositiveLaw μ h : Measure ℝ).map
    (fun x : ℝ => scale μ h * x + p μ), -CentralGap.O0 μ h R ≤ u
  apply (ae_map_iff hf.aemeasurable measurableSet_Ici).mpr
  filter_upwards [CentralGap.nonpositiveLaw_support_ae μ h] with x hx
  have hm := mul_le_mul_of_nonneg_left (hbound hx).1 (scale_pos μ h).le
  change -(scale μ h * R - p μ) ≤ scale μ h * x + p μ
  nlinarith only [hm]

theorem residual1_upper_of_support (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (R : ℝ) (hbound : (μ : Measure ℝ).support ⊆ Icc (-R) R) :
    ∀ᵐ u ∂(residual1 μ h : Measure ℝ), u ≤ CentralGap.O1 μ h R := by
  have hf : Measurable (fun x : ℝ => scale μ h * x + -(q μ)) := by fun_prop
  change ∀ᵐ u ∂(SignSplit.positiveLaw μ h : Measure ℝ).map
    (fun x : ℝ => scale μ h * x + -(q μ)), u ≤ CentralGap.O1 μ h R
  apply (ae_map_iff hf.aemeasurable measurableSet_Iic).mpr
  filter_upwards [CentralGap.positiveLaw_support_ae μ h] with x hx
  have hm := mul_le_mul_of_nonneg_left (hbound hx).2 (scale_pos μ h).le
  change scale μ h * x + -(q μ) ≤ scale μ h * R - q μ
  nlinarith only [hm]

/-- Bounds are acquired from the original closed support and its actual
central gap. No numerical inward-cap or profile hypothesis is used. -/
theorem residual_support_of_support (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (R : ℝ) (hbound : (μ : Measure ℝ).support ⊆ Icc (-R) R) :
    0 ≤ CentralGap.O0 μ h R ∧ 0 ≤ CentralGap.O1 μ h R ∧
      (∀ᵐ u ∂(residual0 μ h : Measure ℝ),
        -CentralGap.O0 μ h R ≤ u ∧ u ≤ CentralGap.a0 μ h) ∧
      (∀ᵐ u ∂(residual1 μ h : Measure ℝ),
        -CentralGap.a1 μ h ≤ u ∧ u ≤ CentralGap.O1 μ h R) := by
  have hL := residual0_lower_of_support μ h R hbound
  have hU := residual1_upper_of_support μ h R hbound
  have hm0 := (residual0_centered μ h).mean_zero
  have hm1 := (residual1_centered μ h).mean_zero
  have hc0 := integral_mono_ae (integrable_const (-CentralGap.O0 μ h R))
    (residual0_centered μ h).integrable_first hL
  have hc1 := integral_mono_ae (residual1_centered μ h).integrable_first
    (integrable_const (CentralGap.O1 μ h R)) hU
  rw [hm0, integral_const, probReal_univ, one_smul] at hc0
  rw [hm1, integral_const, probReal_univ, one_smul] at hc1
  refine ⟨by linarith only [hc0], hc1, ?_, ?_⟩
  · filter_upwards [hL, CentralGap.residual0_upper μ h] with u hu hv
    exact ⟨hu, hv⟩
  · filter_upwards [CentralGap.residual1_lower μ h, hU] with u hu hv
    exact ⟨hu, hv⟩

/-- Every required higher residual power is genuinely L1 on acquired bounded
support; this theorem does not assume a fourth moment of an unbounded law. -/
theorem residual_integrable_pow_of_support (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (R : ℝ) (hbound : (μ : Measure ℝ).support ⊆ Icc (-R) R) (k : ℕ) :
    Integrable (fun u : ℝ => u ^ k) (residual0 μ h : Measure ℝ) ∧
      Integrable (fun u : ℝ => u ^ k) (residual1 μ h : Measure ℝ) := by
  obtain ⟨hO0, hO1, hb0, hb1⟩ := residual_support_of_support μ h R hbound
  have ha0 := CentralGap.a0_nonneg μ h
  have ha1 := CentralGap.a1_nonneg μ h
  constructor
  · apply PhysicalMomentUpper.integrable_pow_of_bound
      (residual0 μ h : Measure ℝ) id measurable_id
      (CentralGap.a0 μ h + CentralGap.O0 μ h R) (add_nonneg ha0 hO0) _ k
    filter_upwards [hb0] with u hu
    exact abs_le.mpr ⟨by dsimp; linarith only [hu.1, ha0],
      by dsimp; linarith only [hu.2, hO0]⟩
  · apply PhysicalMomentUpper.integrable_pow_of_bound
      (residual1 μ h : Measure ℝ) id measurable_id
      (CentralGap.a1 μ h + CentralGap.O1 μ h R) (add_nonneg ha1 hO1) _ k
    filter_upwards [hb1] with u hu
    exact abs_le.mpr ⟨by dsimp; linarith only [hu.1, hO1],
      by dsimp; linarith only [hu.2, ha1]⟩

end BerryEsseen.CanonicalResidualMomentBounds

#print axioms BerryEsseen.CanonicalResidualMomentBounds.residual_integrable_through_three
#print axioms BerryEsseen.CanonicalResidualMomentBounds.signedThirdMoment_identity
#print axioms BerryEsseen.CanonicalResidualMomentBounds.absoluteThirdMoment_identity
#print axioms BerryEsseen.CanonicalResidualMomentBounds.residual0_cubic_eq
#print axioms BerryEsseen.CanonicalResidualMomentBounds.residual1_cubic_eq
#print axioms BerryEsseen.CanonicalResidualMomentBounds.residual_support_of_support
#print axioms BerryEsseen.CanonicalResidualMomentBounds.residual_integrable_pow_of_support
