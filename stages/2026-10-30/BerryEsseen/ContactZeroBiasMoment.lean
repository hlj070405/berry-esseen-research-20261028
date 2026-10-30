module

public import BerryEsseen.ContactPolynomial
public import BerryEsseen.ZeroBiasHigherMoments

@[expose] public section

/-! 2026-10-28: the actual zero-bias expectation of the contact majorant.
Fourth and fifth absolute moments are explicit input hypotheses. All
coefficients and moments belong to the same original probability law. -/

noncomputable section

open MeasureTheory Set

namespace BerryEsseen.ContactZeroBiasMoment

open ZeroBias ZeroBiasHigherMoments

def fourthMoment (μ : ProbabilityMeasure ℝ) : ℝ := ∫ x : ℝ, x ^ 4 ∂(μ : Measure ℝ)

def Kq (μ : ProbabilityMeasure ℝ) : ℝ :=
  absoluteMoment μ 5 / 4 - thirdAbsoluteMoment μ * fourthMoment μ / 2 -
    (3 / 2 : ℝ) * SignedMoment.signedSecondMoment μ * gamma μ + thirdAbsoluteMoment μ / 2

private def polynomialWeight (μ : ProbabilityMeasure ℝ) (t : ℝ) : ℝ :=
  |t| ^ 3 * tau μ t - (3 / 2 : ℝ) * thirdAbsoluteMoment μ * (t ^ 2 * tau μ t) -
    3 * SignedMoment.signedSecondMoment μ * (t * tau μ t) +
    thirdAbsoluteMoment μ / 2 * tau μ t

private def gaussianWeight (μ : ProbabilityMeasure ℝ) (n : ℕ) (H t : ℝ) : ℝ :=
  Real.sqrt n * (t * tau μ t) + (H / Real.sqrt n) / 2 * (t ^ 2 * tau μ t - tau μ t)

private lemma integrable_cube_tau (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (h5 : Integrable (fun x : ℝ => |x| ^ 5) (μ : Measure ℝ)) :
    Integrable (fun t : ℝ => |t| ^ 3 * tau μ t) := by
  simpa only [show (3 + 2 : ℕ) = 5 from rfl] using integrable_abs_pow_tau μ h 3 h5

private theorem integrable_polynomialWeight (μ : ProbabilityMeasure ℝ)
    (h : StandardizedLaw μ) (h4 : Integrable (fun x : ℝ => x ^ 4) (μ : Measure ℝ))
    (h5 : Integrable (fun x : ℝ => |x| ^ 5) (μ : Measure ℝ)) :
    Integrable (polynomialWeight μ) := by
  exact (((integrable_cube_tau μ h h5).sub
    ((integrable_square_tau μ h h4).const_mul ((3 / 2 : ℝ) * thirdAbsoluteMoment μ))).sub
    ((integrable_mul_tau μ h).const_mul (3 * SignedMoment.signedSecondMoment μ))).add
    ((integrable_tau μ h).const_mul (thirdAbsoluteMoment μ / 2))

theorem integral_polynomialWeight (μ : ProbabilityMeasure ℝ)
    (h : StandardizedLaw μ) (h4 : Integrable (fun x : ℝ => x ^ 4) (μ : Measure ℝ))
    (h5 : Integrable (fun x : ℝ => |x| ^ 5) (μ : Measure ℝ)) :
    (∫ t : ℝ, tau μ t * ContactVariation.momentSlope μ t) = Kq μ := by
  have hA := integrable_cube_tau μ h h5
  have hB := (integrable_square_tau μ h h4).const_mul ((3 / 2 : ℝ) * thirdAbsoluteMoment μ)
  have hC := (integrable_mul_tau μ h).const_mul (3 * SignedMoment.signedSecondMoment μ)
  have hD := (integrable_tau μ h).const_mul (thirdAbsoluteMoment μ / 2)
  have hAB : Integrable (fun t : ℝ => |t| ^ 3 * tau μ t -
      (3 / 2 : ℝ) * thirdAbsoluteMoment μ * (t ^ 2 * tau μ t)) := hA.sub hB
  have hABC : Integrable (fun t : ℝ => |t| ^ 3 * tau μ t -
      (3 / 2 : ℝ) * thirdAbsoluteMoment μ * (t ^ 2 * tau μ t) -
      3 * SignedMoment.signedSecondMoment μ * (t * tau μ t)) := hAB.sub hC
  have heq : (fun t : ℝ => tau μ t * ContactVariation.momentSlope μ t) = polynomialWeight μ := by
    funext t
    unfold polynomialWeight ContactVariation.momentSlope
    ring
  rw [heq]
  unfold polynomialWeight
  rw [integral_add hABC hD, integral_sub hAB hC, integral_sub hA hB,
    integral_const_mul, integral_const_mul, integral_const_mul,
    integral_abs_cube_tau μ h h5, integral_square_tau μ h h4,
    integral_mul_tau μ h, integral_tau μ h]
  unfold Kq fourthMoment
  ring

private theorem integrable_gaussianWeight (μ : ProbabilityMeasure ℝ)
    (h : StandardizedLaw μ) (h4 : Integrable (fun x : ℝ => x ^ 4) (μ : Measure ℝ))
    (n : ℕ) (H : ℝ) : Integrable (gaussianWeight μ n H) :=
  ((integrable_mul_tau μ h).const_mul _).add
    (((integrable_square_tau μ h h4).sub (integrable_tau μ h)).const_mul _)

private theorem integral_gaussianWeight (μ : ProbabilityMeasure ℝ)
    (h : StandardizedLaw μ) (h4 : Integrable (fun x : ℝ => x ^ 4) (μ : Measure ℝ))
    (n : ℕ) (H : ℝ) :
    (∫ t : ℝ, gaussianWeight μ n H t) =
      Real.sqrt n * (gamma μ / 2) + (H / Real.sqrt n) / 2 * (fourthMoment μ / 3 - 1) := by
  have hA : Integrable (fun t : ℝ => Real.sqrt n * (t * tau μ t)) :=
    (integrable_mul_tau μ h).const_mul _
  have hsub : Integrable (fun t : ℝ => t ^ 2 * tau μ t - tau μ t) :=
    (integrable_square_tau μ h h4).sub (integrable_tau μ h)
  have hB : Integrable (fun t : ℝ => (H / Real.sqrt n) / 2 * (t ^ 2 * tau μ t - tau μ t)) :=
    hsub.const_mul _
  unfold gaussianWeight
  rw [integral_add hA hB, integral_const_mul, integral_const_mul,
    integral_sub (integrable_square_tau μ h h4) (integrable_tau μ h),
    integral_mul_tau μ h, integral_square_tau μ h h4, integral_tau μ h]
  rfl

private lemma weight_identity (μ : ProbabilityMeasure ℝ) (n : ℕ) (H C : ℝ) :
    (fun t : ℝ => tau μ t * ContactPolynomial.majorant μ n H C t) =
      (fun t : ℝ => (MixtureSum.iidSumLaw (μ : Measure ℝ) n).real (Iic H) * tau μ t -
        (GaussianTools.phi (H / Real.sqrt n) / n) * gaussianWeight μ n H t +
        C / ((n : ℝ) * Real.sqrt n) * polynomialWeight μ t) := by
  funext t
  unfold ContactPolynomial.majorant gaussianWeight polynomialWeight ContactVariation.momentSlope
  ring

theorem integrable_tau_majorant (μ : ProbabilityMeasure ℝ)
    (h : StandardizedLaw μ) (h4 : Integrable (fun x : ℝ => x ^ 4) (μ : Measure ℝ))
    (h5 : Integrable (fun x : ℝ => |x| ^ 5) (μ : Measure ℝ)) (n : ℕ) (H C : ℝ) :
    Integrable (fun t : ℝ => tau μ t * ContactPolynomial.majorant μ n H C t) := by
  rw [weight_identity]
  exact (((integrable_tau μ h).const_mul _).sub
    ((integrable_gaussianWeight μ h h4 n H).const_mul _)).add
    ((integrable_polynomialWeight μ h h4 h5).const_mul _)

theorem integral_tau_majorant (μ : ProbabilityMeasure ℝ)
    (h : StandardizedLaw μ) (h4 : Integrable (fun x : ℝ => x ^ 4) (μ : Measure ℝ))
    (h5 : Integrable (fun x : ℝ => |x| ^ 5) (μ : Measure ℝ)) (n : ℕ) (H C : ℝ) :
    (∫ t : ℝ, tau μ t * ContactPolynomial.majorant μ n H C t) =
      (MixtureSum.iidSumLaw (μ : Measure ℝ) n).real (Iic H) -
        (GaussianTools.phi (H / Real.sqrt n) / n) *
          (Real.sqrt n * (gamma μ / 2) + (H / Real.sqrt n) / 2 * (fourthMoment μ / 3 - 1)) +
        C / ((n : ℝ) * Real.sqrt n) * Kq μ := by
  have hA : Integrable (fun t : ℝ =>
      (MixtureSum.iidSumLaw (μ : Measure ℝ) n).real (Iic H) * tau μ t) :=
    (integrable_tau μ h).const_mul _
  have hB : Integrable (fun t : ℝ => (GaussianTools.phi (H / Real.sqrt n) / n) *
      gaussianWeight μ n H t) := (integrable_gaussianWeight μ h h4 n H).const_mul _
  have hC : Integrable (fun t : ℝ => C / ((n : ℝ) * Real.sqrt n) * polynomialWeight μ t) :=
    (integrable_polynomialWeight μ h h4 h5).const_mul _
  have hAB : Integrable (fun t : ℝ =>
      (MixtureSum.iidSumLaw (μ : Measure ℝ) n).real (Iic H) * tau μ t -
      (GaussianTools.phi (H / Real.sqrt n) / n) * gaussianWeight μ n H t) := hA.sub hB
  have hPoly : (∫ t : ℝ, polynomialWeight μ t) = Kq μ := by
    rw [← integral_polynomialWeight μ h h4 h5]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun t => by
      change polynomialWeight μ t = tau μ t * ContactVariation.momentSlope μ t
      unfold polynomialWeight ContactVariation.momentSlope
      ring
  rw [weight_identity, integral_add hAB hC, integral_sub hA hB,
    integral_const_mul, integral_const_mul, integral_const_mul,
    integral_tau μ h, integral_gaussianWeight μ h h4 n H, hPoly]
  ring

end BerryEsseen.ContactZeroBiasMoment

#print axioms BerryEsseen.ContactZeroBiasMoment.integral_polynomialWeight
#print axioms BerryEsseen.ContactZeroBiasMoment.integrable_tau_majorant
#print axioms BerryEsseen.ContactZeroBiasMoment.integral_tau_majorant
