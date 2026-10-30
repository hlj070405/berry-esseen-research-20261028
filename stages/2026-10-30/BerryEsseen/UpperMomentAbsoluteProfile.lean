module

public import BerryEsseen.UpperMomentSpectralCells
public import BerryEsseen.SmallBetaRayEndpoint

@[expose] public section

/-! 2026-10-30: the absolute CDF price in rational spectral coordinates.
The common sqrt(s) is removed from all four integrands before numerical
cell evaluation. Only the final sqrt(n)/rho normalization needs a root.
The identity and actual-law client do not assume any numerical rows. -/

noncomputable section

open MeasureTheory Set

namespace BerryEsseen.UpperMomentAbsoluteProfile

open RaySpectralCurvature (spectralKernelWeight spectralCorrectionWeight)

def first (U : ℝ) (G : ℝ → ℝ) (V s v : ℝ) : ℝ :=
  spectralKernelWeight V v * UpperMomentSpectralCells.R U G s v

def second (G : ℝ → ℝ) (V s v : ℝ) : ℝ :=
  spectralKernelWeight V v * Real.exp (s * G v)

def third (V s v : ℝ) : ℝ :=
  spectralCorrectionWeight V v * Real.exp (-s * v ^ 2 / 2)

def fourth (s v : ℝ) : ℝ := Real.exp (-s * v ^ 2 / 2) / v

def profile (U : ℝ) (G : ℝ → ℝ) (A V s : ℝ) : ℝ :=
  (2 / V) * (∫ v in Ioc 0 A, first U G V s v) +
  (2 / V) * (∫ v in Ioc A V, second G V s v) +
  (2 / V) * (∫ v in Ioc 0 A, third V s v) +
  (1 / Real.pi) * (∫ v in Ioi A, fourth s v)

lemma powerExp_half (s r : ℝ) (hs : 0 < s) :
    RaySpectralCurvature.powerExp (1 / 2) r s =
      Real.sqrt s * Real.exp (-s * r) := by
  rw [RaySpectralCurvature.powerExp_eq_rpow _ _ _ hs, Real.sqrt_eq_rpow]

theorem first_eq (U : ℝ) (G : ℝ → ℝ) (V s v : ℝ) (hs : 0 < s) :
    UpperMomentSpectrumPrice.firstSpectralIntegrand U G V s v =
      Real.sqrt s * first U G V s v := by
  rw [UpperMomentSpectrumPrice.firstSpectralIntegrand,
    UpperMomentSpectralCells.firstSlice_eq_sqrt_mul_R U G s v hs]
  unfold first
  ring

theorem second_eq (G : ℝ → ℝ) (V s v : ℝ) (hs : 0 < s) :
    FixedSpectrumPrice.secondSpectralIntegrand G V s v =
      Real.sqrt s * second G V s v := by
  rw [FixedSpectrumPrice.secondSpectralIntegrand, powerExp_half s _ hs]
  unfold second
  rw [show -s * -G v = s * G v by ring]
  ring

theorem third_eq (V s v : ℝ) (hs : 0 < s) :
    RaySpectralCurvature.thirdSpectralIntegrand V s v =
      Real.sqrt s * third V s v := by
  rw [RaySpectralCurvature.thirdSpectralIntegrand, powerExp_half s _ hs]
  unfold third
  rw [show -s * (v ^ 2 / 2) = -s * v ^ 2 / 2 by ring]
  ring

theorem fourth_eq (s v : ℝ) (hs : 0 < s) :
    RaySpectralCurvature.fourthSpectralIntegrand s v =
      Real.sqrt s * fourth s v := by
  rw [RaySpectralCurvature.fourthSpectralIntegrand, powerExp_half s _ hs]
  unfold fourth
  rw [show -s * (v ^ 2 / 2) = -s * v ^ 2 / 2 by ring]
  ring

theorem spectral_profile_eq (U : ℝ) (G : ℝ → ℝ) (A V s : ℝ) (hs : 0 < s) :
    UpperMomentSpectrumPrice.spectralProfile U G A V s =
      Real.sqrt s * profile U G A V s := by
  unfold UpperMomentSpectrumPrice.spectralProfile profile
  simp_rw [first_eq U G V s _ hs, second_eq G V s _ hs,
    third_eq V s _ hs, fourth_eq s _ hs]
  rw [integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul]
  ring

structure ProfileIntegrable (U : ℝ) (G : ℝ → ℝ) (A V s : ℝ) : Prop where
  first : IntegrableOn (first U G V s) (Ioc 0 A)
  second : IntegrableOn (second G V s) (Ioc A V)
  third : IntegrableOn (third V s) (Ioc 0 A)
  fourth : IntegrableOn (fourth s) (Ioi A)

private lemma integrableOn_unscale {f : ℝ → ℝ} {S : Set ℝ} {c : ℝ} (hc : c ≠ 0)
    (h : IntegrableOn (fun v => c * f v) S) : IntegrableOn f S :=
  (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hc) f).mp h

/-- All four absolute integrands are genuinely integrable. The nonzero
common scalar is removed from previously established integrable objects. -/
theorem profileIntegrable (U : ℝ) (hU : 0 < U) (G : ℝ → ℝ) (hG : Continuous G)
    (hG0 : ∀ v, G v ≤ 0) (A V s : ℝ) (hA : 0 < A) (hAV : A ≤ V)
    (hs : 0 < s) (hds : UpperMomentSpectrumPrice.d U ≤ s) :
    ProfileIntegrable U G A V s := by
  have hOld := UpperMomentSpectrumPrice.profileIntegrable U hU G hG hG0 A V s hA hAV hs hds
  have hr : Real.sqrt s ≠ 0 := (Real.sqrt_pos.mpr hs).ne'
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply integrableOn_unscale hr
    have he : UpperMomentSpectrumPrice.firstSpectralIntegrand U G V s =
        (fun v => Real.sqrt s * first U G V s v) := funext (fun v => first_eq U G V s v hs)
    rw [← he]
    exact hOld.first
  · apply integrableOn_unscale hr
    have he : FixedSpectrumPrice.secondSpectralIntegrand G V s =
        (fun v => Real.sqrt s * second G V s v) := funext (fun v => second_eq G V s v hs)
    rw [← he]
    exact hOld.second
  · apply integrableOn_unscale hr
    have he : RaySpectralCurvature.thirdSpectralIntegrand V s =
        (fun v => Real.sqrt s * third V s v) := funext (fun v => third_eq V s v hs)
    rw [← he]
    exact hOld.third
  · apply integrableOn_unscale hr
    have he : RaySpectralCurvature.fourthSpectralIntegrand s =
        (fun v => Real.sqrt s * fourth s v) := funext (fun v => fourth_eq s v hs)
    rw [← he]
    exact hOld.fourth

theorem betaScale_mul_sqrt_sScale (U : ℝ) (n : ℕ) (hU : 0 < U) (hn : 0 < n) :
    UpperMomentDamping.betaScale U n * Real.sqrt (UpperMomentDamping.sScale U n) = 1 := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hr : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnR
  unfold UpperMomentDamping.betaScale UpperMomentDamping.sScale
  rw [Real.sqrt_div hnR.le, Real.sqrt_sq hU.le]
  field_simp [hU.ne', hr.ne']

/-- The true closed CDF of the same arbitrary standardized law is paid
by this absolute profile. There is no actual-moment lower bound. -/
theorem actual_cdf_le (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (U : ℝ) (hU : 0 < U) (hρ : thirdAbsoluteMoment μ ≤ U) (n : ℕ) (hn : 0 < n)
    (A V : ℝ) (hA : 0 < A) (hAV : A ≤ V) (x : ℝ) :
    |(normalizedIidSumLaw μ n).real (Iic x) - GaussianTools.Phi x| ≤
      profile U (UpperMomentDamping.G U U) A V (UpperMomentDamping.sScale U n) := by
  have hs : 0 < UpperMomentDamping.sScale U n :=
    div_pos (Nat.cast_pos.mpr hn) (sq_pos_of_pos hU)
  have hh := UpperMomentSpectrumPrice.normalized_actual_cdf_le_scale_spectralProfile
    μ h U hU hρ n hn A V hA hAV x
  rw [spectral_profile_eq U _ A V _ hs, ← mul_assoc,
    betaScale_mul_sqrt_sScale U n hU hn, one_mul] at hh
  exact hh

/-- The infinite fourth term is controlled analytically; no truncation
or finite array is substituted for its genuine integral. -/
theorem fourth_integral_le (s A : ℝ) (hs : 0 < s) (hA : 0 < A) :
    (1 / Real.pi) * (∫ v in Ioi A, fourth s v) ≤
      Real.exp (-s * A ^ 2 / 2) / (Real.pi * s * A ^ 2) := by
  have ht := SmallBetaRayEndpoint.gaussian_reciprocal_tail_le (s / 2) A
    (by positivity) hA
  have he : (fun v : ℝ => Real.exp (-(s / 2) * v ^ 2) / v) = fourth s := by
    funext v
    unfold fourth
    congr 2
    ring
  rw [he] at ht
  have hc := mul_le_mul_of_nonneg_left ht
    (by positivity : (0 : ℝ) ≤ 1 / Real.pi)
  convert hc using 1; ring_nf

end BerryEsseen.UpperMomentAbsoluteProfile

#print axioms BerryEsseen.UpperMomentAbsoluteProfile.spectral_profile_eq
#print axioms BerryEsseen.UpperMomentAbsoluteProfile.profileIntegrable
#print axioms BerryEsseen.UpperMomentAbsoluteProfile.actual_cdf_le
#print axioms BerryEsseen.UpperMomentAbsoluteProfile.fourth_integral_le
