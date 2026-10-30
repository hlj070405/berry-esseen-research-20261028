module

public import BerryEsseen.PhysicalResourcePlane
public import BerryEsseen.UniformLowMomentRebatedAcquisition

@[expose] public section

/-! 2026-10-30: the actual joint physical defect in canonical coordinates.
The inward caps, scale, noise level and allocation all belong to the
same original law. Multiplication by theta, never division by theta,
preserves the zero-noise boundary. The main coordinate bound acquires
neither support nor a numerical profile; the original-law corollaries
consume the already proved uniform resource and its actual zero exclusion. -/

noncomputable section

open MeasureTheory Set

namespace BerryEsseen.CanonicalJointDefectCoordinates

open CanonicalSign CentralGap NoiseCoordinates GapDefect JointDefect

/-- The finite-dimensional polynomial, evaluated below only at the actual
coordinates of the original law. Its lambda is the actual lambda_n. -/
def jointPolynomial (n : ℕ) (p a0 a1 lambda alpha : ℝ) : ℝ :=
  (n : ℝ) * p * (1 - p) *
      ((6 + 2 * Real.sqrt 10) * (p - pStar) ^ 2 +
        6 * ((a0 + a1) * (1 - (a0 + a1)) + a0 * a1)) +
    3 * lambda * ((Real.sqrt 10 + 3) * (p - a0) * (1 - alpha) +
      (Real.sqrt 10 + 1) * ((1 - p) - a1) * alpha)

theorem scale_mul_Aminus (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    scale μ h * Aminus μ = p μ - a0 μ h := by
  unfold a0
  ring

theorem scale_mul_Aplus (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    scale μ h * Aplus μ = q μ - a1 μ h := by
  unfold a1
  ring

theorem scale_mul_deltaMinus (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    scale μ h * deltaMinus μ = a0 μ h :=
  (PhysicalResourcePlane.inner0_eq_scale_delta μ h).symm

theorem scale_mul_deltaPlus (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    scale μ h * deltaPlus μ = a1 μ h :=
  (PhysicalResourcePlane.inner1_eq_scale_delta μ h).symm

/-- These two multiplication identities include zero noise and even n=0.
The actual allocation is never identified with a quotient by theta. -/
theorem scaled_theta_parts (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (n : ℕ) :
    (n : ℝ) * scale μ h ^ 2 * thetaMinus μ h =
        noiseLevel μ h n * (1 - ConditionalResidual.actualAllocation μ h) ∧
      (n : ℝ) * scale μ h ^ 2 * thetaPlus μ h =
        noiseLevel μ h n * ConditionalResidual.actualAllocation μ h := by
  have ha := PhysicalResourcePlane.actualAllocation_mul_theta μ h
  have hm : (1 - ConditionalResidual.actualAllocation μ h) * theta μ h = thetaMinus μ h := by
    have ht : theta μ h = thetaMinus μ h + thetaPlus μ h := rfl
    nlinarith only [ha, ht]
  have hl : (n : ℝ) * scale μ h ^ 2 * theta μ h = noiseLevel μ h n := by
    calc
      _ = (n : ℝ) * (scale μ h ^ 2 * theta μ h) := by ring
      _ = _ := by rw [scale_sq_mul_theta]; rfl
  constructor
  · calc
      _ = (n : ℝ) * scale μ h ^ 2 *
          ((1 - ConditionalResidual.actualAllocation μ h) * theta μ h) := by rw [hm]
      _ = ((n : ℝ) * scale μ h ^ 2 * theta μ h) *
          (1 - ConditionalResidual.actualAllocation μ h) := by ring
      _ = _ := by rw [hl]
  · calc
      _ = (n : ℝ) * scale μ h ^ 2 *
          (ConditionalResidual.actualAllocation μ h * theta μ h) := by rw [ha]
      _ = ((n : ℝ) * scale μ h ^ 2 * theta μ h) *
          ConditionalResidual.actualAllocation μ h := by ring
      _ = _ := by rw [hl]

theorem scaled_bias_coefficient (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    scale μ h ^ 3 * (positiveFirstMoment μ ^ 3 / (p μ ^ 2 * q μ ^ 2)) = p μ * q μ := by
  calc
    _ = (positiveFirstMoment μ * scale μ h) ^ 3 / (p μ ^ 2 * q μ ^ 2) := by ring
    _ = (p μ * q μ) ^ 3 / (p μ ^ 2 * q μ ^ 2) := by rw [positiveFirstMoment_mul_scale]
    _ = _ := by
      apply (div_eq_iff (mul_ne_zero (pow_ne_zero 2 (p_pos μ h).ne')
        (pow_ne_zero 2 (q_pos μ h).ne'))).mpr
      ring

private theorem scaled_joint_expression (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) :
    (n : ℝ) * scale μ h ^ 3 *
      (positiveFirstMoment μ ^ 3 / (p μ ^ 2 * q μ ^ 2) *
          (6 + 2 * Real.sqrt 10) * (p μ - pStar) ^ 2 +
        6 * positiveFirstMoment μ *
          ((Aminus μ + Aplus μ) * (deltaMinus μ + deltaPlus μ) + deltaMinus μ * deltaPlus μ) +
        3 * (Real.sqrt 10 + 3) * Aminus μ * thetaMinus μ h +
        3 * (Real.sqrt 10 + 1) * Aplus μ * thetaPlus μ h) =
      jointPolynomial n (p μ) (a0 μ h) (a1 μ h) (noiseLevel μ h n)
        (ConditionalResidual.actualAllocation μ h) := by
  obtain ⟨htm, htp⟩ := scaled_theta_parts μ h n
  calc
    _ = (n : ℝ) * (scale μ h ^ 3 *
            (positiveFirstMoment μ ^ 3 / (p μ ^ 2 * q μ ^ 2))) *
          (6 + 2 * Real.sqrt 10) * (p μ - pStar) ^ 2 +
        6 * (n : ℝ) * (positiveFirstMoment μ * scale μ h) *
          (((scale μ h * Aminus μ + scale μ h * Aplus μ) *
              (scale μ h * deltaMinus μ + scale μ h * deltaPlus μ)) +
            (scale μ h * deltaMinus μ) * (scale μ h * deltaPlus μ)) +
        3 * (Real.sqrt 10 + 3) * (scale μ h * Aminus μ) *
          ((n : ℝ) * scale μ h ^ 2 * thetaMinus μ h) +
        3 * (Real.sqrt 10 + 1) * (scale μ h * Aplus μ) *
          ((n : ℝ) * scale μ h ^ 2 * thetaPlus μ h) := by ring
    _ = _ := by
      simp only [scaled_bias_coefficient, positiveFirstMoment_mul_scale,
        scale_mul_Aminus, scale_mul_Aplus, scale_mul_deltaMinus, scale_mul_deltaPlus,
        htm, htp]
      unfold jointPolynomial q
      ring

/-- The canonical polynomial lower bound for the actual original law.
There is no profile, theta cap, endpoint floor or variance envelope input. -/
theorem actual_joint_defect_lower_bound (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hz : (0 : ℝ) ∉ (μ : Measure ℝ).support) (n : ℕ) (hn : 0 < n) :
    jointPolynomial n (p μ) (a0 μ h) (a1 μ h) (noiseLevel μ h n)
        (ConditionalResidual.actualAllocation μ h) ≤
      (n : ℝ) * scale μ h ^ 3 * actualPhysicalDefect μ := by
  have hj := JointDefect.joint_defect_moment μ h hz
  have hm := mul_le_mul_of_nonneg_left hj
    (mul_pos (Nat.cast_pos.mpr hn) (pow_pos (scale_pos μ h) 3)).le
  rw [scaled_joint_expression μ h n] at hm
  exact hm

/-- The original first pass acquires zero exclusion before the polynomial
is combined with the proved resource. The exact score-excess and actual
gap costs remain coupled to the same original law, n and H. -/
theorem original_canonical_resource_with_excess
    (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (hn : 26 ≤ n) (H C : ℝ)
    (hm : ContactVariation.PositiveClosedMaximum μ n H C)
    (hprev : Extremizer.fixedNSup (n - 1) ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) :
    ConservedTransfer.kappa *
        jointPolynomial n (p μ) (a0 μ h) (a1 μ h) (noiseLevel μ h n)
          (ConditionalResidual.actualAllocation μ h) +
      scale μ h ^ 3 *
        (((n : ℝ) * thirdAbsoluteMoment μ - LowMomentRawScoreReduction.scoreCoefficient μ H) *
            (C - esseenConstant) +
          (n : ℝ) * Real.sqrt n * ContactGapSum.actualL μ n H) ≤
      (92 / 75 : ℝ) * scale μ h ^ 3 := by
  have hz := UniformLowMomentRawAcquisition.original_zero_absent μ h n hn H C hm hprev hC hρ
  have hp := actual_joint_defect_lower_bound μ h hz n (by omega)
  have hk := mul_le_mul_of_nonneg_left hp ConservedTransfer.kappa_pos.le
  have hu := mul_le_mul_of_nonneg_left
    (UniformLowMomentRebatedAcquisition.original_joint_resource_with_excess μ h
      n hn H C hm hprev hC hρ) (pow_nonneg (scale_pos μ h).le 3)
  nlinarith only [hk, hu]

theorem original_canonical_resource_bound (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (hn : 26 ≤ n) (H C : ℝ)
    (hm : ContactVariation.PositiveClosedMaximum μ n H C)
    (hprev : Extremizer.fixedNSup (n - 1) ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) :
    ConservedTransfer.kappa *
        jointPolynomial n (p μ) (a0 μ h) (a1 μ h) (noiseLevel μ h n)
          (ConditionalResidual.actualAllocation μ h) +
      scale μ h ^ 3 * ((n : ℝ) * Real.sqrt n * ContactGapSum.actualL μ n H) ≤
      (92 / 75 : ℝ) * scale μ h ^ 3 := by
  have hz := UniformLowMomentRawAcquisition.original_zero_absent μ h n hn H C hm hprev hC hρ
  have hp := actual_joint_defect_lower_bound μ h hz n (by omega)
  have hk := mul_le_mul_of_nonneg_left hp ConservedTransfer.kappa_pos.le
  have hu := mul_le_mul_of_nonneg_left
    (UniformLowMomentRebatedAcquisition.original_joint_resource_bound μ h
      n hn H C hm hprev hC hρ) (pow_nonneg (scale_pos μ h).le 3)
  nlinarith only [hk, hu]

/-! 2026-10-30: retain the actual signed third moment before the
conditional cubic lower bounds are substituted. All scale and noise
normalizations below still use the same original law and actual n. -/

/-- A canonical lower polynomial that retains both actual third moments.
The c, rho and gamma arguments are evaluated at the same original law. -/
def signedCubicPolynomial (n : ℕ) (p a0 a1 lambda alpha c rho gamma : ℝ) : ℝ :=
  (n : ℝ) * c ^ 3 * (Real.sqrt 10 * rho - gamma) -
    6 * (n : ℝ) * p * (1 - p) *
      ((p - a0) ^ 2 + ((1 - p) - a1) ^ 2 + (p - a0) * ((1 - p) - a1)) +
    6 * ((1 - p) - a1) * (lambda * alpha + (n : ℝ) * p * (1 - p) ^ 2) +
    6 * (p - a0) * (lambda * (1 - alpha) + (n : ℝ) * (1 - p) * p ^ 2)

/-- The actual second moments keep their sign groups and use the
allocation multiplication identities, including zero noise. -/
theorem scaled_second_moments (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (n : ℕ) :
    (n : ℝ) * scale μ h ^ 2 * OuterGapCost.positiveSecondMoment μ =
        noiseLevel μ h n * ConditionalResidual.actualAllocation μ h + (n : ℝ) * p μ * q μ ^ 2 ∧
      (n : ℝ) * scale μ h ^ 2 * OuterGapCost.negativeSecondMoment μ =
        noiseLevel μ h n * (1 - ConditionalResidual.actualAllocation μ h) +
          (n : ℝ) * q μ * p μ ^ 2 := by
  obtain ⟨htm, htp⟩ := scaled_theta_parts μ h n
  have hbarp : scale μ h ^ 2 * (positiveFirstMoment μ * barAplus μ) = p μ * q μ ^ 2 := by
    unfold barAplus
    calc
      _ = (positiveFirstMoment μ * scale μ h) ^ 2 / p μ := by ring
      _ = (p μ * q μ) ^ 2 / p μ := by rw [positiveFirstMoment_mul_scale]
      _ = _ := by
        apply (div_eq_iff (p_pos μ h).ne').mpr
        ring
  have hbarm : scale μ h ^ 2 * (positiveFirstMoment μ * barAminus μ) = q μ * p μ ^ 2 := by
    unfold barAminus
    calc
      _ = (positiveFirstMoment μ * scale μ h) ^ 2 / q μ := by ring
      _ = (p μ * q μ) ^ 2 / q μ := by rw [positiveFirstMoment_mul_scale]
      _ = _ := by
        apply (div_eq_iff (q_pos μ h).ne').mpr
        ring
  constructor
  · rw [positiveSecondMoment_physical μ h]
    calc
      _ = (n : ℝ) * scale μ h ^ 2 * thetaPlus μ h +
          (n : ℝ) * (scale μ h ^ 2 * (positiveFirstMoment μ * barAplus μ)) := by ring
      _ = _ := by rw [htp, hbarp]; ring
  · rw [negativeSecondMoment_physical μ h]
    calc
      _ = (n : ℝ) * scale μ h ^ 2 * thetaMinus μ h +
          (n : ℝ) * (scale μ h ^ 2 * (positiveFirstMoment μ * barAminus μ)) := by ring
      _ = _ := by rw [htm, hbarm]; ring

private theorem scaled_signed_cubic_expression (μ : ProbabilityMeasure ℝ)
    (h : StandardizedLaw μ) (n : ℕ) :
    (n : ℝ) * scale μ h ^ 3 *
      (Real.sqrt 10 * thirdAbsoluteMoment μ - ZeroBias.gamma μ -
        6 * positiveFirstMoment μ * (Aminus μ ^ 2 + Aplus μ ^ 2 + Aminus μ * Aplus μ) +
        6 * Aplus μ * OuterGapCost.positiveSecondMoment μ +
        6 * Aminus μ * OuterGapCost.negativeSecondMoment μ) =
      signedCubicPolynomial n (p μ) (a0 μ h) (a1 μ h) (noiseLevel μ h n)
        (ConditionalResidual.actualAllocation μ h) (scale μ h) (thirdAbsoluteMoment μ)
        (ZeroBias.gamma μ) := by
  obtain ⟨hpos, hneg⟩ := scaled_second_moments μ h n
  calc
    _ = (n : ℝ) * scale μ h ^ 3 * (Real.sqrt 10 * thirdAbsoluteMoment μ - ZeroBias.gamma μ) -
        6 * (n : ℝ) * (positiveFirstMoment μ * scale μ h) *
          ((scale μ h * Aminus μ) ^ 2 + (scale μ h * Aplus μ) ^ 2 +
            (scale μ h * Aminus μ) * (scale μ h * Aplus μ)) +
        6 * (scale μ h * Aplus μ) *
          ((n : ℝ) * scale μ h ^ 2 * OuterGapCost.positiveSecondMoment μ) +
        6 * (scale μ h * Aminus μ) *
          ((n : ℝ) * scale μ h ^ 2 * OuterGapCost.negativeSecondMoment μ) := by ring
    _ = _ := by
      simp only [positiveFirstMoment_mul_scale, scale_mul_Aminus, scale_mul_Aplus, hpos, hneg]
      unfold signedCubicPolynomial q
      ring

/-- The signed cubic budget comes directly from the original D lower
bound, before the conditional cubic slacks are discarded. -/
theorem actual_signed_cubic_lower_bound (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hz : (0 : ℝ) ∉ (μ : Measure ℝ).support) (n : ℕ) (hn : 0 < n) :
    signedCubicPolynomial n (p μ) (a0 μ h) (a1 μ h) (noiseLevel μ h n)
        (ConditionalResidual.actualAllocation μ h) (scale μ h) (thirdAbsoluteMoment μ)
        (ZeroBias.gamma μ) ≤
      (n : ℝ) * scale μ h ^ 3 * actualPhysicalDefect μ := by
  have hj := JointDefect.defect_ge_cubic_second_budget μ h hz
  have hthird : (Real.sqrt 10 - 1) * PhysicalDefect.positiveThirdMoment μ +
      (Real.sqrt 10 + 1) * PhysicalDefect.negativeThirdMoment μ =
        Real.sqrt 10 * thirdAbsoluteMoment μ - ZeroBias.gamma μ := by
    rw [PhysicalDefect.rho_eq_parts μ h, PhysicalDefect.gamma_eq_parts μ h]
    ring
  rw [hthird] at hj
  have hs := mul_le_mul_of_nonneg_left hj
    (mul_pos (Nat.cast_pos.mpr hn) (pow_pos (scale_pos μ h) 3)).le
  rw [scaled_signed_cubic_expression μ h n] at hs
  exact hs

theorem original_signed_cubic_resource_with_excess
    (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (hn : 26 ≤ n) (H C : ℝ)
    (hm : ContactVariation.PositiveClosedMaximum μ n H C)
    (hprev : Extremizer.fixedNSup (n - 1) ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) :
    ConservedTransfer.kappa *
        signedCubicPolynomial n (p μ) (a0 μ h) (a1 μ h) (noiseLevel μ h n)
          (ConditionalResidual.actualAllocation μ h) (scale μ h) (thirdAbsoluteMoment μ)
          (ZeroBias.gamma μ) +
      scale μ h ^ 3 *
        (((n : ℝ) * thirdAbsoluteMoment μ - LowMomentRawScoreReduction.scoreCoefficient μ H) *
            (C - esseenConstant) +
          (n : ℝ) * Real.sqrt n * ContactGapSum.actualL μ n H) ≤
      (92 / 75 : ℝ) * scale μ h ^ 3 := by
  have hz := UniformLowMomentRawAcquisition.original_zero_absent μ h n hn H C hm hprev hC hρ
  have hp := actual_signed_cubic_lower_bound μ h hz n (by omega)
  have hk := mul_le_mul_of_nonneg_left hp ConservedTransfer.kappa_pos.le
  have hu := mul_le_mul_of_nonneg_left
    (UniformLowMomentRebatedAcquisition.original_joint_resource_with_excess μ h
      n hn H C hm hprev hC hρ) (pow_nonneg (scale_pos μ h).le 3)
  nlinarith only [hk, hu]

theorem original_signed_cubic_resource_bound
    (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (hn : 26 ≤ n) (H C : ℝ)
    (hm : ContactVariation.PositiveClosedMaximum μ n H C)
    (hprev : Extremizer.fixedNSup (n - 1) ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) :
    ConservedTransfer.kappa *
        signedCubicPolynomial n (p μ) (a0 μ h) (a1 μ h) (noiseLevel μ h n)
          (ConditionalResidual.actualAllocation μ h) (scale μ h) (thirdAbsoluteMoment μ)
          (ZeroBias.gamma μ) +
      scale μ h ^ 3 * ((n : ℝ) * Real.sqrt n * ContactGapSum.actualL μ n H) ≤
      (92 / 75 : ℝ) * scale μ h ^ 3 := by
  have hz := UniformLowMomentRawAcquisition.original_zero_absent μ h n hn H C hm hprev hC hρ
  have hp := actual_signed_cubic_lower_bound μ h hz n (by omega)
  have hk := mul_le_mul_of_nonneg_left hp ConservedTransfer.kappa_pos.le
  have hu := mul_le_mul_of_nonneg_left
    (UniformLowMomentRebatedAcquisition.original_joint_resource_bound μ h
      n hn H C hm hprev hC hρ) (pow_nonneg (scale_pos μ h).le 3)
  nlinarith only [hk, hu]

end BerryEsseen.CanonicalJointDefectCoordinates

#print axioms BerryEsseen.CanonicalJointDefectCoordinates.scaled_theta_parts
#print axioms BerryEsseen.CanonicalJointDefectCoordinates.scaled_bias_coefficient
#print axioms BerryEsseen.CanonicalJointDefectCoordinates.actual_joint_defect_lower_bound
#print axioms BerryEsseen.CanonicalJointDefectCoordinates.original_canonical_resource_with_excess
#print axioms BerryEsseen.CanonicalJointDefectCoordinates.original_canonical_resource_bound
#print axioms BerryEsseen.CanonicalJointDefectCoordinates.scaled_second_moments
#print axioms BerryEsseen.CanonicalJointDefectCoordinates.actual_signed_cubic_lower_bound
#print axioms BerryEsseen.CanonicalJointDefectCoordinates.original_signed_cubic_resource_with_excess
#print axioms BerryEsseen.CanonicalJointDefectCoordinates.original_signed_cubic_resource_bound
