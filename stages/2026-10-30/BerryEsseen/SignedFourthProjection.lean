module

public import BerryEsseen.ContactWeightedMoment
public import BerryEsseen.ContactZeroBiasMoment
public import BerryEsseen.N26InitialLowFrequency

@[expose] public section

/-! 2026-10-30: same-law cancellation in the signed fourth moment.
The two residuals remove the constant and linear projections under the
original standardized law. Their covariance and variances are computed
by explicit integrable polynomial expansions. Nonnegative squares give
the bound without Cauchy--Schwarz, square roots, or a reflected law. -/

noncomputable section

open MeasureTheory Set

namespace BerryEsseen.SignedFourthProjection

def residual1 (μ : ProbabilityMeasure ℝ) (x : ℝ) : ℝ :=
  x ^ 2 - 1 - ZeroBias.gamma μ * x

def residual2 (μ : ProbabilityMeasure ℝ) (x : ℝ) : ℝ :=
  x * |x| - SignedMoment.signedSecondMoment μ - thirdAbsoluteMoment μ * x

private def expanded (a4 s4 a3 aAbs3 a2 s2 a1 a0 x : ℝ) : ℝ :=
  a4 * x ^ 4 + s4 * (x * |x| ^ 3) + a3 * x ^ 3 + aAbs3 * |x| ^ 3 +
    a2 * x ^ 2 + s2 * (x * |x|) + a1 * x + a0

private theorem integrable_expanded (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (h4 : Integrable (fun x : ℝ => x ^ 4) (μ : Measure ℝ))
    (a4 s4 a3 aAbs3 a2 s2 a1 a0 : ℝ) :
    Integrable (expanded a4 s4 a3 aAbs3 a2 s2 a1 a0) (μ : Measure ℝ) := by
  exact (((((((h4.const_mul a4).add
    ((ContactWeightedMoment.integrable_signedFourth μ h4).const_mul s4)).add
    ((ZeroBias.integrable_signed_cube μ h).const_mul a3)).add
    (h.integrable_cube.const_mul aAbs3)).add
    (h.integrable_square.const_mul a2)).add
    ((SignedMoment.integrable_signedSecondMoment μ h).const_mul s2)).add
    (h.integrable_mean.const_mul a1)).add (integrable_const a0)

private theorem integral_expanded (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (h4 : Integrable (fun x : ℝ => x ^ 4) (μ : Measure ℝ))
    (a4 s4 a3 aAbs3 a2 s2 a1 a0 : ℝ) :
    (∫ x, expanded a4 s4 a3 aAbs3 a2 s2 a1 a0 x ∂(μ : Measure ℝ)) =
      a4 * ContactZeroBiasMoment.fourthMoment μ + s4 * ContactWeightedMoment.signedFourthMoment μ +
      a3 * ZeroBias.gamma μ + aAbs3 * thirdAbsoluteMoment μ + a2 +
      s2 * SignedMoment.signedSecondMoment μ + a0 := by
  have hA := h4.const_mul a4
  have hB := (ContactWeightedMoment.integrable_signedFourth μ h4).const_mul s4
  have hC := (ZeroBias.integrable_signed_cube μ h).const_mul a3
  have hD := h.integrable_cube.const_mul aAbs3
  have hE := h.integrable_square.const_mul a2
  have hF := (SignedMoment.integrable_signedSecondMoment μ h).const_mul s2
  have hG := h.integrable_mean.const_mul a1
  have hAB : Integrable (fun x : ℝ => a4 * x ^ 4 + s4 * (x * |x| ^ 3))
      (μ : Measure ℝ) := hA.add hB
  have hABC : Integrable (fun x : ℝ => a4 * x ^ 4 + s4 * (x * |x| ^ 3) + a3 * x ^ 3)
      (μ : Measure ℝ) := hAB.add hC
  have hABCD : Integrable (fun x : ℝ => a4 * x ^ 4 + s4 * (x * |x| ^ 3) + a3 * x ^ 3 +
      aAbs3 * |x| ^ 3) (μ : Measure ℝ) := hABC.add hD
  have hABCDE : Integrable (fun x : ℝ => a4 * x ^ 4 + s4 * (x * |x| ^ 3) + a3 * x ^ 3 +
      aAbs3 * |x| ^ 3 + a2 * x ^ 2) (μ : Measure ℝ) := hABCD.add hE
  have hABCDEF : Integrable (fun x : ℝ => a4 * x ^ 4 + s4 * (x * |x| ^ 3) + a3 * x ^ 3 +
      aAbs3 * |x| ^ 3 + a2 * x ^ 2 + s2 * (x * |x|)) (μ : Measure ℝ) := hABCDE.add hF
  have hABCDEFG : Integrable (fun x : ℝ => a4 * x ^ 4 + s4 * (x * |x| ^ 3) + a3 * x ^ 3 +
      aAbs3 * |x| ^ 3 + a2 * x ^ 2 + s2 * (x * |x|) + a1 * x)
      (μ : Measure ℝ) := hABCDEF.add hG
  unfold expanded
  rw [integral_add hABCDEFG (integrable_const a0),
    integral_add hABCDEF hG, integral_add hABCDE hF, integral_add hABCD hE,
    integral_add hABC hD, integral_add hAB hC, integral_add hA hB,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_const_mul, integral_const_mul,
    h.second_moment_one, h.mean_zero, integral_const, probReal_univ, one_smul]
  simp only [ContactZeroBiasMoment.fourthMoment, ContactWeightedMoment.signedFourthMoment,
    ZeroBias.gamma, thirdAbsoluteMoment, SignedMoment.signedSecondMoment,
    mul_one, mul_zero, add_zero]

private theorem residual1_square_expanded (μ : ProbabilityMeasure ℝ) :
    (fun x => residual1 μ x ^ 2) =
      expanded 1 0 (-2 * ZeroBias.gamma μ) 0 (ZeroBias.gamma μ ^ 2 - 2) 0
        (2 * ZeroBias.gamma μ) 1 := by
  funext x
  simp only [residual1, expanded]
  ring

private theorem residual2_square_expanded (μ : ProbabilityMeasure ℝ) :
    (fun x => residual2 μ x ^ 2) =
      expanded 1 0 0 (-2 * thirdAbsoluteMoment μ) (thirdAbsoluteMoment μ ^ 2)
        (-2 * SignedMoment.signedSecondMoment μ)
        (2 * SignedMoment.signedSecondMoment μ * thirdAbsoluteMoment μ)
        (SignedMoment.signedSecondMoment μ ^ 2) := by
  funext x
  rcases le_total 0 x with hx | hx
  · simp only [residual2, expanded, abs_of_nonneg hx]
    ring
  · simp only [residual2, expanded, abs_of_nonpos hx]
    ring

private theorem residual_product_expanded (μ : ProbabilityMeasure ℝ) :
    (fun x => residual1 μ x * residual2 μ x) =
      expanded 0 1 (-thirdAbsoluteMoment μ) (-ZeroBias.gamma μ)
        (ZeroBias.gamma μ * thirdAbsoluteMoment μ - SignedMoment.signedSecondMoment μ) (-1)
        (thirdAbsoluteMoment μ + ZeroBias.gamma μ * SignedMoment.signedSecondMoment μ)
        (SignedMoment.signedSecondMoment μ) := by
  funext x
  rcases le_total 0 x with hx | hx
  · simp only [residual1, residual2, expanded, abs_of_nonneg hx]
    ring
  · simp only [residual1, residual2, expanded, abs_of_nonpos hx]
    ring

theorem integrable_residual1_square (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (h4 : Integrable (fun x : ℝ => x ^ 4) (μ : Measure ℝ)) :
    Integrable (fun x => residual1 μ x ^ 2) (μ : Measure ℝ) := by
  rw [residual1_square_expanded]
  exact integrable_expanded μ h h4 _ _ _ _ _ _ _ _

theorem integrable_residual2_square (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (h4 : Integrable (fun x : ℝ => x ^ 4) (μ : Measure ℝ)) :
    Integrable (fun x => residual2 μ x ^ 2) (μ : Measure ℝ) := by
  rw [residual2_square_expanded]
  exact integrable_expanded μ h h4 _ _ _ _ _ _ _ _

theorem integrable_residual_product (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (h4 : Integrable (fun x : ℝ => x ^ 4) (μ : Measure ℝ)) :
    Integrable (fun x => residual1 μ x * residual2 μ x) (μ : Measure ℝ) := by
  rw [residual_product_expanded]
  exact integrable_expanded μ h h4 _ _ _ _ _ _ _ _

/-- The variance remaining after removing the signed cubic projection. -/
theorem residual1_square_identity (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (h4 : Integrable (fun x : ℝ => x ^ 4) (μ : Measure ℝ)) :
    (∫ x, residual1 μ x ^ 2 ∂(μ : Measure ℝ)) =
      ContactZeroBiasMoment.fourthMoment μ - 1 - ZeroBias.gamma μ ^ 2 := by
  rw [residual1_square_expanded, integral_expanded μ h h4]
  ring

/-- The variance remaining after removing the absolute cubic projection. -/
theorem residual2_square_identity (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (h4 : Integrable (fun x : ℝ => x ^ 4) (μ : Measure ℝ)) :
    (∫ x, residual2 μ x ^ 2 ∂(μ : Measure ℝ)) =
      ContactZeroBiasMoment.fourthMoment μ - SignedMoment.signedSecondMoment μ ^ 2 -
        thirdAbsoluteMoment μ ^ 2 := by
  rw [residual2_square_expanded, integral_expanded μ h h4]
  ring

/-- The cancellation uses moments of one original law, including its signed gamma. -/
theorem residual_product_identity (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (h4 : Integrable (fun x : ℝ => x ^ 4) (μ : Measure ℝ)) :
    (∫ x, residual1 μ x * residual2 μ x ∂(μ : Measure ℝ)) =
      ContactWeightedMoment.signedFourthMoment μ - SignedMoment.signedSecondMoment μ -
        thirdAbsoluteMoment μ * ZeroBias.gamma μ := by
  rw [residual_product_expanded, integral_expanded μ h h4]
  ring

theorem combined_square_identity (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (h4 : Integrable (fun x : ℝ => x ^ 4) (μ : Measure ℝ)) (t : ℝ) :
    (∫ x, (residual1 μ x + t * residual2 μ x) ^ 2 ∂(μ : Measure ℝ)) =
      (ContactZeroBiasMoment.fourthMoment μ - 1 - ZeroBias.gamma μ ^ 2) +
      2 * t * (ContactWeightedMoment.signedFourthMoment μ - SignedMoment.signedSecondMoment μ -
        thirdAbsoluteMoment μ * ZeroBias.gamma μ) +
      t ^ 2 * (ContactZeroBiasMoment.fourthMoment μ - SignedMoment.signedSecondMoment μ ^ 2 -
        thirdAbsoluteMoment μ ^ 2) := by
  have hA := integrable_residual1_square μ h h4
  have hB := (integrable_residual_product μ h h4).const_mul (2 * t)
  have hC := (integrable_residual2_square μ h h4).const_mul (t ^ 2)
  have hAB : Integrable (fun x => residual1 μ x ^ 2 +
      2 * t * (residual1 μ x * residual2 μ x)) (μ : Measure ℝ) := hA.add hB
  have heq : (fun x => (residual1 μ x + t * residual2 μ x) ^ 2) =
      (fun x => residual1 μ x ^ 2 + 2 * t * (residual1 μ x * residual2 μ x) +
        t ^ 2 * residual2 μ x ^ 2) := by
    funext x
    ring
  rw [heq, integral_add hAB hC, integral_add hA hB,
    integral_const_mul, integral_const_mul, residual1_square_identity μ h h4,
    residual_product_identity μ h h4, residual2_square_identity μ h h4]

/-- Both signs follow from squares; this retains all three projection savings. -/
theorem abs_centered_signedFourth_le_average_variances
    (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (h4 : Integrable (fun x : ℝ => x ^ 4) (μ : Measure ℝ)) :
    |ContactWeightedMoment.signedFourthMoment μ - SignedMoment.signedSecondMoment μ -
      thirdAbsoluteMoment μ * ZeroBias.gamma μ| ≤
      ContactZeroBiasMoment.fourthMoment μ -
        (1 + ZeroBias.gamma μ ^ 2 + SignedMoment.signedSecondMoment μ ^ 2 +
          thirdAbsoluteMoment μ ^ 2) / 2 := by
  have hp : 0 ≤ ∫ x, (residual1 μ x + (1 : ℝ) * residual2 μ x) ^ 2
      ∂(μ : Measure ℝ) := integral_nonneg fun x => sq_nonneg _
  have hm : 0 ≤ ∫ x, (residual1 μ x + (-1 : ℝ) * residual2 μ x) ^ 2
      ∂(μ : Measure ℝ) := integral_nonneg fun x => sq_nonneg _
  rw [combined_square_identity μ h h4] at hp hm
  apply abs_le.mpr
  constructor <;> linarith only [hp, hm]

theorem abs_centered_signedFourth_le_fourth_sub_one
    (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (h4 : Integrable (fun x : ℝ => x ^ 4) (μ : Measure ℝ)) :
    |ContactWeightedMoment.signedFourthMoment μ - SignedMoment.signedSecondMoment μ -
      thirdAbsoluteMoment μ * ZeroBias.gamma μ| ≤ ContactZeroBiasMoment.fourthMoment μ - 1 := by
  have hcov := abs_centered_signedFourth_le_average_variances μ h h4
  have hρ := Extremizer.thirdAbsoluteMoment_ge_one μ h
  nlinarith only [hcov, hρ, sq_nonneg (ZeroBias.gamma μ),
    sq_nonneg (SignedMoment.signedSecondMoment μ), sq_nonneg (thirdAbsoluteMoment μ - 1)]

/-- Price the contact coefficient after the same-law fourth-moment cancellation. -/
theorem abs_K1_le_projection_bound (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (h4 : Integrable (fun x : ℝ => x ^ 4) (μ : Measure ℝ)) :
    |ContactWeightedMoment.K1 μ| ≤ ContactZeroBiasMoment.fourthMoment μ - 1 +
      2 * |SignedMoment.signedSecondMoment μ| +
      thirdAbsoluteMoment μ * |ZeroBias.gamma μ| / 2 := by
  have hcov := abs_centered_signedFourth_le_fourth_sub_one μ h h4
  have hρ0 : 0 ≤ thirdAbsoluteMoment μ :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (Extremizer.thirdAbsoluteMoment_ge_one μ h)
  have heq : ContactWeightedMoment.K1 μ =
      (ContactWeightedMoment.signedFourthMoment μ - SignedMoment.signedSecondMoment μ -
        thirdAbsoluteMoment μ * ZeroBias.gamma μ) -
      2 * SignedMoment.signedSecondMoment μ -
      thirdAbsoluteMoment μ * ZeroBias.gamma μ / 2 := by
    unfold ContactWeightedMoment.K1
    ring
  rw [heq]
  calc
    _ ≤ |ContactWeightedMoment.signedFourthMoment μ - SignedMoment.signedSecondMoment μ -
          thirdAbsoluteMoment μ * ZeroBias.gamma μ| +
        |2 * SignedMoment.signedSecondMoment μ| +
        |thirdAbsoluteMoment μ * ZeroBias.gamma μ / 2| := by
      have houter := abs_sub
        (ContactWeightedMoment.signedFourthMoment μ - SignedMoment.signedSecondMoment μ -
          thirdAbsoluteMoment μ * ZeroBias.gamma μ - 2 * SignedMoment.signedSecondMoment μ)
        (thirdAbsoluteMoment μ * ZeroBias.gamma μ / 2)
      have hinner := abs_sub
        (ContactWeightedMoment.signedFourthMoment μ - SignedMoment.signedSecondMoment μ -
          thirdAbsoluteMoment μ * ZeroBias.gamma μ)
        (2 * SignedMoment.signedSecondMoment μ)
      linarith only [houter, hinner]
    _ = |ContactWeightedMoment.signedFourthMoment μ - SignedMoment.signedSecondMoment μ -
          thirdAbsoluteMoment μ * ZeroBias.gamma μ| +
        2 * |SignedMoment.signedSecondMoment μ| +
        thirdAbsoluteMoment μ * |ZeroBias.gamma μ| / 2 := by
      rw [abs_mul, abs_div, abs_mul, abs_of_nonneg hρ0]
      norm_num
    _ ≤ _ := by linarith only [hcov]

/-- The acquired support and low third moment imply the rational cap 1.1995. -/
theorem abs_K1_le_2399_2000 (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hs : (μ : Measure ℝ).support ⊆ Icc (-(12 / 5 : ℝ)) (12 / 5))
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) :
    |ContactWeightedMoment.K1 μ| ≤ (2399 : ℝ) / 2000 := by
  have h4 := ConservedResource.integrable_pow_of_bounded_support μ (12 / 5) hs 4
  have hproj := abs_K1_le_projection_bound μ h h4
  have hβ := SignedMoment.abs_signed_lt_127_500 μ h hρ
  have hγ := N26InitialLowFrequency.gamma_cap μ h hρ
  change |ZeroBias.gamma μ| ≤ (53 : ℝ) / 100 at hγ
  have hM := (N26P39ResourceAcquisition.moment_caps_of_support μ h hs hρ).1
  simp only [ZeroBiasHigherMoments.abs_pow_four] at hM
  change ContactZeroBiasMoment.fourthMoment μ ≤ (1014 : ℝ) / 725 at hM
  have hMcoarse : ContactZeroBiasMoment.fourthMoment μ ≤ (7 : ℝ) / 5 := by
    linarith only [hM]
  have hp := mul_le_mul hρ hγ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 11 / 10)
  linarith only [hproj, hβ, hMcoarse, hp]

theorem abs_K1_lt_six_fifths (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hs : (μ : Measure ℝ).support ⊆ Icc (-(12 / 5 : ℝ)) (12 / 5))
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) :
    |ContactWeightedMoment.K1 μ| < (6 : ℝ) / 5 := by
  have hb := abs_K1_le_2399_2000 μ h hs hρ
  linarith only [hb]

end BerryEsseen.SignedFourthProjection

#print axioms BerryEsseen.SignedFourthProjection.residual1_square_identity
#print axioms BerryEsseen.SignedFourthProjection.residual2_square_identity
#print axioms BerryEsseen.SignedFourthProjection.residual_product_identity
#print axioms BerryEsseen.SignedFourthProjection.combined_square_identity
#print axioms BerryEsseen.SignedFourthProjection.abs_centered_signedFourth_le_fourth_sub_one
#print axioms BerryEsseen.SignedFourthProjection.abs_K1_le_projection_bound
#print axioms BerryEsseen.SignedFourthProjection.abs_K1_le_2399_2000
#print axioms BerryEsseen.SignedFourthProjection.abs_K1_lt_six_fifths
