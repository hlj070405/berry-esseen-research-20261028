module

public import BerryEsseen.ContactWeightedMoment
public import BerryEsseen.ContactZeroBiasMoment
public import BerryEsseen.ContactGapSum
public import BerryEsseen.ConservedPutMoment

@[expose] public section

/-! 2026-10-28: the exact conserved resource of the original law and its
actual positive closed maximum. Both evaluations of the same integrable
zero-bias contact gap are connected to the literal Fourier remainder.
The bounded-support corollary uses an incoming support bound; it does not
acquire support from its own conclusion. -/

noncomputable section

open MeasureTheory Set

namespace BerryEsseen.ConservedResource

open GaussianTools ZeroBias ContactWeightedMoment ContactZeroBiasMoment
open GapDefect ContactGapSum ContactGapResource ContactPolynomial

/-- The common actual integral, with the same original law, maximum,
predecessor law and contact majorant in both evaluations. -/
def actualI (μ : ProbabilityMeasure ℝ) (n : ℕ) (H C : ℝ) : ℝ :=
  ∫ t : ℝ, ContactGapResource.integrand μ n H C t

def P0 (μ : ProbabilityMeasure ℝ) (n : ℕ) (H C : ℝ) : ℝ :=
  H ^ 2 * (C * thirdAbsoluteMoment μ + gamma μ * phi (H / Real.sqrt n) / 2) -
    H * (C * K1 μ + phi (H / Real.sqrt n) * (fourthMoment μ - 3) / 6) + C * Kq μ

def gapCorrection (μ : ProbabilityMeasure ℝ) (n : ℕ) (H C : ℝ) : ℝ :=
  (3 / 2 : ℝ) * C * SignedMoment.signedSecondMoment μ * actualJ μ +
    (H * phi (H / Real.sqrt n) + 3 * C * thirdAbsoluteMoment μ) * actualJ1 μ -
      3 * C * actualJ2 μ

/-- The literal raw remainder in loc:raw. All moments and gap resources
are the previously defined actual quantities of this same μ. -/
def raw (μ : ProbabilityMeasure ℝ) (n : ℕ) (H C : ℝ) : ℝ :=
  C * ((3 / 2 : ℝ) * SignedMoment.signedSecondMoment μ * actualJ μ +
    3 * thirdAbsoluteMoment μ * actualJ1 μ - 3 * actualJ2 μ - Kq μ) +
    H * (C * K1 μ + phi (H / Real.sqrt n) * (actualJ1 μ + (fourthMoment μ - 3) / 6)) -
    H ^ 2 * (C * thirdAbsoluteMoment μ + gamma μ * phi (H / Real.sqrt n) / 2) +
    FourierRemainder.value μ n H

theorem raw_eq_gapCorrection_sub_P0 (μ : ProbabilityMeasure ℝ) (n : ℕ) (H C : ℝ) :
    raw μ n H C = gapCorrection μ n H C - P0 μ n H C + FourierRemainder.value μ n H := by
  unfold raw gapCorrection P0
  ring

private theorem integrand_eq_difference (μ : ProbabilityMeasure ℝ) (n : ℕ) (H C : ℝ) :
    ContactGapResource.integrand μ n H C =
      (fun t : ℝ => tau μ t * majorant μ n H C t -
        tau μ t * (predecessorTailLaw μ n H : Measure ℝ).real (Ici t)) := by
  funext t
  unfold ContactGapResource.integrand GapIntegration.closedTail
  ring

/-- Each part is L1 before the actual integral is separated. -/
theorem integrable_actual_integrand (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (h4 : Integrable (fun x : ℝ => x ^ 4) (μ : Measure ℝ))
    (h5 : Integrable (fun x : ℝ => |x| ^ 5) (μ : Measure ℝ)) (n : ℕ) (H C : ℝ) :
    Integrable (ContactGapResource.integrand μ n H C) := by
  rw [integrand_eq_difference]
  exact (ContactZeroBiasMoment.integrable_tau_majorant μ hμ h4 h5 n H C).sub
    (ZeroBiasClosedTail.integrable_tau_closedTail μ (predecessorTailLaw μ n H) hμ)

theorem actualI_eq_difference (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (h4 : Integrable (fun x : ℝ => x ^ 4) (μ : Measure ℝ))
    (h5 : Integrable (fun x : ℝ => |x| ^ 5) (μ : Measure ℝ)) (n : ℕ) (H C : ℝ) :
    actualI μ n H C = (∫ t : ℝ, tau μ t * majorant μ n H C t) -
      ∫ t : ℝ, tau μ t * (predecessorTailLaw μ n H : Measure ℝ).real (Ici t) := by
  unfold actualI
  rw [integrand_eq_difference]
  exact integral_sub (ContactZeroBiasMoment.integrable_tau_majorant μ hμ h4 h5 n H C)
    (ZeroBiasClosedTail.integrable_tau_closedTail μ (predecessorTailLaw μ n H) hμ)

/-- The actual second evaluation, using contact weighted by X, the true
Gaussian and iid put-square moments, and the original Fourier remainder. -/
theorem second_evaluation (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (h4 : Integrable (fun x : ℝ => x ^ 4) (μ : Measure ℝ))
    (h5 : Integrable (fun x : ℝ => |x| ^ 5) (μ : Measure ℝ))
    (n : ℕ) (hn : 0 < n) (H C : ℝ)
    (hm : ContactVariation.PositiveClosedMaximum μ n H C) :
    actualI μ n H C = C * thirdAbsoluteMoment μ / Real.sqrt n -
      phi (H / Real.sqrt n) * gamma μ / (6 * Real.sqrt n) +
      (P0 μ n H C - FourierRemainder.value μ n H) / ((n : ℝ) * Real.sqrt n) := by
  have hn0 : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
  have hs0 : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)).ne'
  have hs2 : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
  have htail := ZeroBiasClosedTail.tau_predecessor_closedTail_identity μ hμ n hn H
  change (∫ t : ℝ, tau μ t * (predecessorTailLaw μ n H : Measure ℝ).real (Ici t)) =
    -(1 / (n : ℝ)) * (∫ s : ℝ, s * ConservedPutMoment.put H s
      ∂MixtureSum.iidSumLaw (μ : Measure ℝ) n) at htail
  have hF : (MixtureSum.iidSumLaw (μ : Measure ℝ) n).real (Iic H) =
      Phi (H / Real.sqrt n) + C * thirdAbsoluteMoment μ / Real.sqrt n := by
    linarith only [hm.attainment]
  rw [actualI_eq_difference μ hμ h4 h5 n H C,
    ContactZeroBiasMoment.integral_tau_majorant μ hμ h4 h5 n H C,
    htail,
    ConservedPutMoment.iid_marked_put_identity μ hμ n hn H,
    ContactWeightedMoment.integral_weighted_closedTail μ hμ h4 n hn H C hm,
    ConservedPutMoment.iid_put_square_formula μ hμ n hn H, hF]
  unfold P0
  generalize hs : Real.sqrt (n : ℝ) = s at *
  rw [← hs2]
  field_simp [hs0] <;> ring

/-- The first evaluation is the proved full-space sum over the genuine
convergent family of actual support gaps. -/
theorem first_evaluation (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (R : ℝ) (hR : 0 ≤ R) (hbound : (μ : Measure ℝ).support ⊆ Icc (-R) R)
    (n : ℕ) (hn : 0 < n) (H C : ℝ)
    (hm : ContactVariation.PositiveClosedMaximum μ n H C) :
    actualI μ n H C = phi (H / Real.sqrt n) / (2 * Real.sqrt n) * actualJ μ +
      gapCorrection μ n H C / ((n : ℝ) * Real.sqrt n) - actualL μ n H :=
  ContactGapSum.first_resource_identity μ hμ R hR hbound n hn H C hm

/-- Equating the two genuine evaluations produces the original balanced
resource identity, before the defect and Gaussian phase are expanded. -/
theorem balanced_identity_of_moments (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (h4 : Integrable (fun x : ℝ => x ^ 4) (μ : Measure ℝ))
    (h5 : Integrable (fun x : ℝ => |x| ^ 5) (μ : Measure ℝ))
    (R : ℝ) (hR : 0 ≤ R) (hbound : (μ : Measure ℝ).support ⊆ Icc (-R) R)
    (n : ℕ) (hn : 0 < n) (H C : ℝ)
    (hm : ContactVariation.PositiveClosedMaximum μ n H C) :
    C * thirdAbsoluteMoment μ + Real.sqrt n * actualL μ n H =
      phi (H / Real.sqrt n) * (gamma μ + 3 * actualJ μ) / 6 + raw μ n H C / n := by
  have hfirst := first_evaluation μ hμ R hR hbound n hn H C hm
  have hsecond := second_evaluation μ hμ h4 h5 n hn H C hm
  have he := hfirst.symm.trans hsecond
  have hn0 : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
  have hs0 : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)).ne'
  have hs2 : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
  rw [raw_eq_gapCorrection_sub_P0]
  generalize hs : Real.sqrt (n : ℝ) = s at *
  rw [← hs2] at he ⊢
  field_simp [hs0] at he ⊢
  nlinarith only [he]

theorem gaussian_phase_density (n : ℕ) (hn : 0 < n) (H : ℝ) :
    phi (H / Real.sqrt n) = phi 0 * Real.exp (-(H ^ 2 / (2 * (n : ℝ)))) := by
  have hn0 : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
  have harg : (H / Real.sqrt n) ^ 2 / 2 = H ^ 2 / (2 * (n : ℝ)) := by
    rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
    field_simp
  rw [GaussianPrices.phi_eq_phi_zero_mul_exp, harg]

theorem esseenConstant_eq_phi_zero : esseenConstant = (3 + Real.sqrt 10) * phi 0 / 6 := by
  rw [esseenConstant, GaussianPrices.phi_zero_eq]
  have hs : Real.sqrt (2 * Real.pi) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  field_simp [hs] <;> ring

/-- The original weighted phase/defect conserved identity, with the exact
raw remainder and the same actual physical defect of μ. -/
theorem conserved_identity_of_moments (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (h4 : Integrable (fun x : ℝ => x ^ 4) (μ : Measure ℝ))
    (h5 : Integrable (fun x : ℝ => |x| ^ 5) (μ : Measure ℝ))
    (R : ℝ) (hR : 0 ≤ R) (hbound : (μ : Measure ℝ).support ⊆ Icc (-R) R)
    (n : ℕ) (hn : 0 < n) (H C : ℝ)
    (hm : ContactVariation.PositiveClosedMaximum μ n H C) :
    (n : ℝ) * (C - esseenConstant) * thirdAbsoluteMoment μ +
      (n : ℝ) * esseenConstant * thirdAbsoluteMoment μ *
        (1 - Real.exp (-(H ^ 2 / (2 * (n : ℝ))))) +
      (n : ℝ) * phi 0 * Real.exp (-(H ^ 2 / (2 * (n : ℝ)))) * actualPhysicalDefect μ / 6 +
      (n : ℝ) * Real.sqrt n * actualL μ n H = raw μ n H C := by
  have hb := balanced_identity_of_moments μ hμ h4 h5 R hR hbound n hn H C hm
  rw [gaussian_phase_density n hn H] at hb
  have hD : gamma μ + 3 * actualJ μ =
      (3 + Real.sqrt 10) * thirdAbsoluteMoment μ - actualPhysicalDefect μ := by
    unfold actualPhysicalDefect
    ring
  rw [hD] at hb
  have hmultiply := congrArg (fun z : ℝ => (n : ℝ) * z) hb
  have hn0 : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
  have hcancel : (n : ℝ) * (raw μ n H C / n) = raw μ n H C := by field_simp
  simp only [mul_add, hcancel] at hmultiply
  rw [esseenConstant_eq_phi_zero]
  nlinarith only [hmultiply]

/-- An incoming bound on the original support supplies all required higher
absolute moments under that same original measure. -/
theorem integrable_abs_pow_of_bounded_support (μ : ProbabilityMeasure ℝ)
    (R : ℝ) (hbound : (μ : Measure ℝ).support ⊆ Icc (-R) R) (k : ℕ) :
    Integrable (fun x : ℝ => |x| ^ k) (μ : Measure ℝ) := by
  have hm : AEStronglyMeasurable (fun x : ℝ => |x| ^ k) (μ : Measure ℝ) := by fun_prop
  apply (integrable_const (R ^ k)).mono' hm
  filter_upwards [(μ : Measure ℝ).support_mem_ae] with x hx
  have hxR : |x| ≤ R := abs_le.mpr (hbound hx)
  change abs (|x| ^ k) ≤ R ^ k
  rw [abs_of_nonneg (pow_nonneg (abs_nonneg x) k)]
  exact pow_le_pow_left₀ (abs_nonneg x) hxR k

theorem integrable_pow_of_bounded_support (μ : ProbabilityMeasure ℝ)
    (R : ℝ) (hbound : (μ : Measure ℝ).support ⊆ Icc (-R) R) (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k) (μ : Measure ℝ) := by
  have hm : AEStronglyMeasurable (fun x : ℝ => x ^ k) (μ : Measure ℝ) := by fun_prop
  apply (integrable_norm_iff hm).mp
  simpa only [Real.norm_eq_abs, abs_pow] using integrable_abs_pow_of_bounded_support μ R hbound k

/-- Bounded support is an already acquired input, so this corollary adds
no independent fourth/fifth-moment assumptions and has no support cycle. -/
theorem balanced_identity (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (R : ℝ) (hR : 0 ≤ R) (hbound : (μ : Measure ℝ).support ⊆ Icc (-R) R)
    (n : ℕ) (hn : 0 < n) (H C : ℝ)
    (hm : ContactVariation.PositiveClosedMaximum μ n H C) :
    C * thirdAbsoluteMoment μ + Real.sqrt n * actualL μ n H =
      phi (H / Real.sqrt n) * (gamma μ + 3 * actualJ μ) / 6 + raw μ n H C / n :=
  balanced_identity_of_moments μ hμ (integrable_pow_of_bounded_support μ R hbound 4)
    (integrable_abs_pow_of_bounded_support μ R hbound 5) R hR hbound n hn H C hm

/-- The complete actual loc:conserved--loc:raw identity on the original
positive-maximum domain with an incoming original support bound. -/
theorem conserved_identity (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (R : ℝ) (hR : 0 ≤ R) (hbound : (μ : Measure ℝ).support ⊆ Icc (-R) R)
    (n : ℕ) (hn : 0 < n) (H C : ℝ)
    (hm : ContactVariation.PositiveClosedMaximum μ n H C) :
    (n : ℝ) * (C - esseenConstant) * thirdAbsoluteMoment μ +
      (n : ℝ) * esseenConstant * thirdAbsoluteMoment μ *
        (1 - Real.exp (-(H ^ 2 / (2 * (n : ℝ))))) +
      (n : ℝ) * phi 0 * Real.exp (-(H ^ 2 / (2 * (n : ℝ)))) * actualPhysicalDefect μ / 6 +
      (n : ℝ) * Real.sqrt n * actualL μ n H = raw μ n H C :=
  conserved_identity_of_moments μ hμ (integrable_pow_of_bounded_support μ R hbound 4)
    (integrable_abs_pow_of_bounded_support μ R hbound 5) R hR hbound n hn H C hm

end BerryEsseen.ConservedResource

#print axioms BerryEsseen.ConservedResource.integrable_actual_integrand
#print axioms BerryEsseen.ConservedResource.second_evaluation
#print axioms BerryEsseen.ConservedResource.balanced_identity_of_moments
#print axioms BerryEsseen.ConservedResource.conserved_identity_of_moments
#print axioms BerryEsseen.ConservedResource.balanced_identity
#print axioms BerryEsseen.ConservedResource.conserved_identity
