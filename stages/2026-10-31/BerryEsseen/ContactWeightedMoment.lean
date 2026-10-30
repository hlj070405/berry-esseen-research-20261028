module

public import BerryEsseen.ContactPolynomial
public import BerryEsseen.ZeroBias

@[expose] public section

/-! 2026-10-28: the actual X-weighted contact moment for the conserved
resource. Fourth-moment integrability is explicit; no free replacement
moment or differentiability of a probability distribution is assumed. -/

noncomputable section

open MeasureTheory Set

namespace BerryEsseen.ContactWeightedMoment

def signedFourthMoment (μ : ProbabilityMeasure ℝ) : ℝ :=
  ∫ x : ℝ, x * |x| ^ 3 ∂(μ : Measure ℝ)

def K1 (μ : ProbabilityMeasure ℝ) : ℝ :=
  signedFourthMoment μ - 3 * SignedMoment.signedSecondMoment μ -
    (3 / 2 : ℝ) * thirdAbsoluteMoment μ * ZeroBias.gamma μ

theorem integrable_signedFourth (μ : ProbabilityMeasure ℝ)
    (h4 : Integrable (fun x : ℝ => x ^ 4) (μ : Measure ℝ)) :
    Integrable (fun x : ℝ => x * |x| ^ 3) (μ : Measure ℝ) := by
  apply (integrable_norm_iff (by fun_prop)).mp
  convert h4 using 1
  funext x
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_abs]
  calc
    |x| * |x| ^ 3 = (|x| ^ 2) ^ 2 := by ring
    _ = (x ^ 2) ^ 2 := by rw [sq_abs]
    _ = x ^ 4 := by ring

theorem integrable_weighted_momentSlope (μ : ProbabilityMeasure ℝ)
    (h : StandardizedLaw μ) (h4 : Integrable (fun x : ℝ => x ^ 4) (μ : Measure ℝ)) :
    Integrable (fun x : ℝ => x * ContactVariation.momentSlope μ x) (μ : Measure ℝ) := by
  have hi := (((integrable_signedFourth μ h4).sub
    ((ZeroBias.integrable_signed_cube μ h).const_mul ((3 / 2 : ℝ) * thirdAbsoluteMoment μ))).sub
    (h.integrable_square.const_mul (3 * SignedMoment.signedSecondMoment μ))).add
    (h.integrable_mean.const_mul (thirdAbsoluteMoment μ / 2))
  convert hi using 1
  funext x
  simp only [Pi.add_apply, Pi.sub_apply]
  unfold ContactVariation.momentSlope
  ring

theorem integral_weighted_momentSlope (μ : ProbabilityMeasure ℝ)
    (h : StandardizedLaw μ) (h4 : Integrable (fun x : ℝ => x ^ 4) (μ : Measure ℝ)) :
    (∫ x : ℝ, x * ContactVariation.momentSlope μ x ∂(μ : Measure ℝ)) = K1 μ := by
  have hA := integrable_signedFourth μ h4
  have hB := (ZeroBias.integrable_signed_cube μ h).const_mul
    ((3 / 2 : ℝ) * thirdAbsoluteMoment μ)
  have hC := h.integrable_square.const_mul (3 * SignedMoment.signedSecondMoment μ)
  have hD := h.integrable_mean.const_mul (thirdAbsoluteMoment μ / 2)
  have hAB : Integrable (fun x : ℝ => x * |x| ^ 3 -
      (3 / 2 : ℝ) * thirdAbsoluteMoment μ * x ^ 3) (μ : Measure ℝ) := hA.sub hB
  have hABC : Integrable (fun x : ℝ => x * |x| ^ 3 -
      (3 / 2 : ℝ) * thirdAbsoluteMoment μ * x ^ 3 -
      3 * SignedMoment.signedSecondMoment μ * x ^ 2) (μ : Measure ℝ) := hAB.sub hC
  have heq : (fun x : ℝ => x * ContactVariation.momentSlope μ x) =
      (fun x : ℝ => (x * |x| ^ 3 -
        (3 / 2 : ℝ) * thirdAbsoluteMoment μ * x ^ 3) -
        3 * SignedMoment.signedSecondMoment μ * x ^ 2 + thirdAbsoluteMoment μ / 2 * x) := by
    funext x
    unfold ContactVariation.momentSlope
    ring
  rw [heq, integral_add hABC hD,
    integral_sub hAB hC, integral_sub hA hB,
    integral_const_mul, integral_const_mul, integral_const_mul,
    h.second_moment_one, h.mean_zero]
  unfold K1 signedFourthMoment ZeroBias.gamma
  ring

private def weightedGaussianPart (n : ℕ) (H x : ℝ) : ℝ :=
  Real.sqrt n * x ^ 2 + (H / Real.sqrt n) / 2 * (x ^ 3 - x)

private theorem integrable_weightedGaussianPart (μ : ProbabilityMeasure ℝ)
    (h : StandardizedLaw μ) (n : ℕ) (H : ℝ) :
    Integrable (weightedGaussianPart n H) (μ : Measure ℝ) :=
  (h.integrable_square.const_mul _).add
    (((ZeroBias.integrable_signed_cube μ h).sub h.integrable_mean).const_mul _)

private theorem integral_weightedGaussianPart (μ : ProbabilityMeasure ℝ)
    (h : StandardizedLaw μ) (n : ℕ) (H : ℝ) :
    (∫ x : ℝ, weightedGaussianPart n H x ∂(μ : Measure ℝ)) =
      Real.sqrt n + (H / Real.sqrt n) / 2 * ZeroBias.gamma μ := by
  have hA : Integrable (fun x : ℝ => Real.sqrt n * x ^ 2) (μ : Measure ℝ) :=
    h.integrable_square.const_mul _
  have hsub : Integrable (fun x : ℝ => x ^ 3 - x) (μ : Measure ℝ) :=
    (ZeroBias.integrable_signed_cube μ h).sub h.integrable_mean
  have hB : Integrable (fun x : ℝ => (H / Real.sqrt n) / 2 * (x ^ 3 - x))
      (μ : Measure ℝ) := hsub.const_mul _
  unfold weightedGaussianPart
  rw [integral_add hA hB,
    integral_const_mul, integral_const_mul,
    integral_sub (ZeroBias.integrable_signed_cube μ h) h.integrable_mean,
    h.second_moment_one, h.mean_zero]
  unfold ZeroBias.gamma
  ring

theorem integrable_weighted_majorant (μ : ProbabilityMeasure ℝ)
    (h : StandardizedLaw μ) (h4 : Integrable (fun x : ℝ => x ^ 4) (μ : Measure ℝ))
    (n : ℕ) (H C : ℝ) :
    Integrable (fun x : ℝ => x * ContactPolynomial.majorant μ n H C x) (μ : Measure ℝ) := by
  have hi := ((h.integrable_mean.const_mul
    ((MixtureSum.iidSumLaw (μ : Measure ℝ) n).real (Iic H))).sub
    ((integrable_weightedGaussianPart μ h n H).const_mul
      (GaussianTools.phi (H / Real.sqrt n) / n))).add
    ((integrable_weighted_momentSlope μ h h4).const_mul (C / ((n : ℝ) * Real.sqrt n)))
  convert hi using 1
  funext x
  simp only [Pi.add_apply, Pi.sub_apply]
  unfold ContactPolynomial.majorant weightedGaussianPart
  ring

theorem integral_weighted_majorant (μ : ProbabilityMeasure ℝ)
    (h : StandardizedLaw μ) (h4 : Integrable (fun x : ℝ => x ^ 4) (μ : Measure ℝ))
    (n : ℕ) (H C : ℝ) :
    (∫ x : ℝ, x * ContactPolynomial.majorant μ n H C x ∂(μ : Measure ℝ)) =
      -(GaussianTools.phi (H / Real.sqrt n) / n) *
        (Real.sqrt n + (H / Real.sqrt n) / 2 * ZeroBias.gamma μ) +
        C / ((n : ℝ) * Real.sqrt n) * K1 μ := by
  have hA := h.integrable_mean.const_mul
    ((MixtureSum.iidSumLaw (μ : Measure ℝ) n).real (Iic H))
  have hB := (integrable_weightedGaussianPart μ h n H).const_mul
    (GaussianTools.phi (H / Real.sqrt n) / n)
  have hC := (integrable_weighted_momentSlope μ h h4).const_mul
    (C / ((n : ℝ) * Real.sqrt n))
  have hAB : Integrable (fun x : ℝ =>
      (MixtureSum.iidSumLaw (μ : Measure ℝ) n).real (Iic H) * x -
      (GaussianTools.phi (H / Real.sqrt n) / n) * weightedGaussianPart n H x)
      (μ : Measure ℝ) := hA.sub hB
  have heq : (fun x : ℝ => x * ContactPolynomial.majorant μ n H C x) =
      (fun x : ℝ => (MixtureSum.iidSumLaw (μ : Measure ℝ) n).real (Iic H) * x -
        (GaussianTools.phi (H / Real.sqrt n) / n) * weightedGaussianPart n H x +
        (C / ((n : ℝ) * Real.sqrt n)) * (x * ContactVariation.momentSlope μ x)) := by
    funext x
    unfold ContactPolynomial.majorant weightedGaussianPart
    ring
  rw [heq, integral_add hAB hC, integral_sub hA hB,
    integral_const_mul, integral_const_mul, integral_const_mul,
    h.mean_zero, integral_weightedGaussianPart μ h n H,
    integral_weighted_momentSlope μ h h4]
  ring

theorem integrable_weighted_closedTail (μ : ProbabilityMeasure ℝ)
    (h : StandardizedLaw μ) (h4 : Integrable (fun x : ℝ => x ^ 4) (μ : Measure ℝ))
    (n : ℕ) (hn : 0 < n) (H C : ℝ)
    (hm : ContactVariation.PositiveClosedMaximum μ n H C) :
    Integrable (fun x : ℝ => x *
      (ContactPolynomial.predecessorTailLaw μ n H : Measure ℝ).real (Ici x)) (μ : Measure ℝ) := by
  apply (integrable_weighted_majorant μ h h4 n H C).congr
  filter_upwards [ContactPolynomial.majorant_eq_closedTail_ae μ h n hn H C hm] with x hx
  rw [hx]

theorem integral_weighted_closedTail (μ : ProbabilityMeasure ℝ)
    (h : StandardizedLaw μ) (h4 : Integrable (fun x : ℝ => x ^ 4) (μ : Measure ℝ))
    (n : ℕ) (hn : 0 < n) (H C : ℝ)
    (hm : ContactVariation.PositiveClosedMaximum μ n H C) :
    (∫ x : ℝ, x * (ContactPolynomial.predecessorTailLaw μ n H : Measure ℝ).real
      (Ici x) ∂(μ : Measure ℝ)) =
      -(GaussianTools.phi (H / Real.sqrt n) / n) *
        (Real.sqrt n + (H / Real.sqrt n) / 2 * ZeroBias.gamma μ) +
        C / ((n : ℝ) * Real.sqrt n) * K1 μ := by
  rw [← integral_weighted_majorant μ h h4 n H C]
  apply integral_congr_ae
  filter_upwards [ContactPolynomial.majorant_eq_closedTail_ae μ h n hn H C hm] with x hx
  rw [hx]

end BerryEsseen.ContactWeightedMoment

#print axioms BerryEsseen.ContactWeightedMoment.integrable_signedFourth
#print axioms BerryEsseen.ContactWeightedMoment.integral_weighted_momentSlope
#print axioms BerryEsseen.ContactWeightedMoment.integrable_weighted_majorant
#print axioms BerryEsseen.ContactWeightedMoment.integral_weighted_majorant
#print axioms BerryEsseen.ContactWeightedMoment.integrable_weighted_closedTail
#print axioms BerryEsseen.ContactWeightedMoment.integral_weighted_closedTail
