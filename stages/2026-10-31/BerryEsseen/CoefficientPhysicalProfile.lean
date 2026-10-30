module

public import BerryEsseen.CoefficientRaySpectral

@[expose] public section

/-! 2026-10-29: the coefficient-ray four-term price in physical frequency
t.  The change v=beta*t is exact for each integrand, including zero and
the Prawitz band endpoint.  In particular, the assigned value K(1) is
preserved, and no endpoint replacement of the kernel is used.
The third term uses the dimensionless principal correction K(t/U)-i/(2*pi*t/U).
No numerical endpoint bound or new CDF constant is asserted. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped Interval

namespace BerryEsseen.CoefficientPhysicalProfile

open HighMomentRayDamping
open Causalean.Stat.CLT.BerryEsseen (prawitzKernel)
open RaySpectralCurvature (spectralKernelWeight spectralCorrectionWeight
  thirdSpectralIntegrand fourthSpectralIntegrand powerExp_half_scale powerExp_half_gaussian_scale)

def firstIntegrand (N : ℕ) (c β U t : ℝ) : ℝ :=
  ‖prawitzKernel (t / U)‖ * CoefficientRayPrice.coarsePrice N c β t

def secondIntegrand (c β U t : ℝ) : ℝ :=
  ‖prawitzKernel (t / U)‖ * CoefficientRayPrice.envelope c β t

def thirdIntegrand (U t : ℝ) : ℝ :=
  ‖prawitzKernel (t / U) - Complex.I / ((2 * Real.pi * (t / U) : ℝ) : ℂ)‖ *
    Real.exp (-(t ^ 2 / 2))

def fourthIntegrand (t : ℝ) : ℝ := Real.exp (-(t ^ 2 / 2)) / t

def physicalProfile (N : ℕ) (c β U0 U : ℝ) : ℝ :=
  (2 / U) * (∫ t in (0 : ℝ)..U0, firstIntegrand N c β U t) +
  (2 / (U * β)) * (∫ t in U0..U, secondIntegrand c β U t) +
  (2 / (U * β)) * (∫ t in (0 : ℝ)..U0, thirdIntegrand U t) +
  (1 / (Real.pi * β)) * (∫ t in Ioi U0, fourthIntegrand t)

private lemma frequency_ratio (β V v : ℝ) (hβ : 0 < β) :
    (v / β) / (V / β) = v / V := by field_simp [hβ.ne']

/-- Pointwise equality, with the actual values at v=0 and v=V retained. -/
theorem firstIntegrand_scale (N : ℕ) (hN : 0 < N) (c β V v : ℝ) (hβ : 0 < β) :
    firstIntegrand N c β (V / β) (v / β) =
      CoefficientRaySpectral.firstSpectralIntegrand N c V (1 / β ^ 2) v := by
  unfold firstIntegrand CoefficientRaySpectral.firstSpectralIntegrand
    CoefficientRaySpectral.coarseSpectralSlice spectralKernelWeight
  rw [frequency_ratio β V v hβ, CoefficientRaySpectral.coarsePrice_spectral_eq N hN c β v hβ]

theorem secondIntegrand_scale (c β V v : ℝ) (hβ : 0 < β) :
    secondIntegrand c β (V / β) (v / β) =
      β * CoefficientRaySpectral.secondSpectralIntegrand c V (1 / β ^ 2) v := by
  unfold secondIntegrand CoefficientRaySpectral.secondSpectralIntegrand spectralKernelWeight
  rw [frequency_ratio β V v hβ, CoefficientRaySpectral.envelope_spectral_eq c β v hβ,
    powerExp_half_scale β _ hβ]
  have he : -(1 / β ^ 2) * (-CoefficientRaySpectral.spectralExponent c v) =
      (1 / β ^ 2) * CoefficientRaySpectral.spectralExponent c v := by ring
  rw [he]
  field_simp [hβ.ne']

theorem thirdIntegrand_scale (β V v : ℝ) (hβ : 0 < β) :
    thirdIntegrand (V / β) (v / β) = β * thirdSpectralIntegrand V (1 / β ^ 2) v := by
  unfold thirdIntegrand thirdSpectralIntegrand spectralCorrectionWeight
  rw [frequency_ratio β V v hβ, powerExp_half_gaussian_scale β v hβ]
  field_simp [hβ.ne']

theorem fourthIntegrand_scale (β v : ℝ) (hβ : 0 < β) :
    fourthIntegrand (v / β) = β ^ 2 * fourthSpectralIntegrand (1 / β ^ 2) v := by
  unfold fourthIntegrand fourthSpectralIntegrand
  rw [powerExp_half_gaussian_scale β v hβ]
  by_cases hv : v = 0
  · simp [hv]
  · field_simp [hβ.ne', hv]

private lemma intervalIntegral_div_scale (f : ℝ → ℝ) (β a b : ℝ) (hβ : 0 < β) :
    (∫ t in a / β..b / β, f t) = (1 / β) * ∫ v in a..b, f (v / β) := by
  have hh := intervalIntegral.integral_comp_div (a := a) (b := b) f hβ.ne'
  simp only [smul_eq_mul] at hh
  rw [hh]
  field_simp [hβ.ne']

private lemma tailIntegral_div_scale (f : ℝ → ℝ) (β A : ℝ) (hβ : 0 < β) :
    (∫ t in Ioi (A / β), f t) = (1 / β) * ∫ v in Ioi A, f (v / β) := by
  simpa only [div_eq_mul_inv, one_mul, mul_one, smul_eq_mul, mul_comm] using
    (integral_comp_mul_left_Ioi' f A (one_div_pos.mpr hβ)).symm

/-- Exact four-term identity for the same coefficient, including the
unbounded Gaussian tail and the full Prawitz kernel at both endpoints. -/
theorem physicalProfile_scale_eq_spectral (N : ℕ) (hN : 0 < N) (c β A V : ℝ)
    (hβ : 0 < β) (hA : 0 < A) (hAV : A ≤ V) :
    physicalProfile N c β (A / β) (V / β) =
      CoefficientRaySpectral.spectralProfile N c A V (1 / β ^ 2) := by
  have hV : 0 < V := hA.trans_le hAV
  have h1 := intervalIntegral_div_scale (firstIntegrand N c β (V / β)) β 0 A hβ
  have h2 := intervalIntegral_div_scale (secondIntegrand c β (V / β)) β A V hβ
  have h3 := intervalIntegral_div_scale (thirdIntegrand (V / β)) β 0 A hβ
  have h4 := tailIntegral_div_scale fourthIntegrand β A hβ
  simp only [zero_div] at h1 h3
  unfold physicalProfile
  rw [h1, h2, h3, h4]
  simp_rw [firstIntegrand_scale N hN c β V _ hβ, secondIntegrand_scale c β V _ hβ,
    thirdIntegrand_scale β V _ hβ, fourthIntegrand_scale β _ hβ]
  simp only [integral_const_mul,
    intervalIntegral.integral_of_le hA.le, intervalIntegral.integral_of_le hAV]
  unfold CoefficientRaySpectral.spectralProfile
  field_simp [hβ.ne', hV.ne', Real.pi_ne_zero]

private lemma intervalIntegrable_of_div_comp (f : ℝ → ℝ) (β a b : ℝ) (hβ : 0 < β)
    (hf : IntervalIntegrable (fun v => f (v / β)) volume a b) :
    IntervalIntegrable f volume (a / β) (b / β) := by
  have hh := hf.comp_mul_left (c := β)
  simpa only [mul_div_cancel_left₀ _ hβ.ne'] using hh

private lemma integrableOn_Ioi_of_div_comp (f : ℝ → ℝ) (β A : ℝ) (hβ : 0 < β)
    (hf : IntegrableOn (fun v => f (v / β)) (Ioi A)) :
    IntegrableOn f (Ioi (A / β)) := by
  have hc : IntegrableOn (fun v => f ((1 / β) * v)) (Ioi A) := by
    simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm] using hf
  have hh := (integrableOn_Ioi_comp_mul_left_iff f A (one_div_pos.mpr hβ)).mp hc
  simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm] using hh

/-- All four physical integrals are genuinely integrable, by transport
from the already proved spectral integrability. -/
theorem four_integrands_integrable (N : ℕ) (hN : 0 < N) (c β A V : ℝ)
    (hβ : 0 < β) (hA : 0 < A) (hAV : A ≤ V) :
    IntervalIntegrable (firstIntegrand N c β (V / β)) volume 0 (A / β) ∧
      IntervalIntegrable (secondIntegrand c β (V / β)) volume (A / β) (V / β) ∧
      IntervalIntegrable (thirdIntegrand (V / β)) volume 0 (A / β) ∧
      IntegrableOn fourthIntegrand (Ioi (A / β)) := by
  have hI := CoefficientRaySpectral.profileIntegrable N hN c A V (1 / β ^ 2) hA hAV (by positivity)
  have h1 := (intervalIntegrable_iff_integrableOn_Ioc_of_le hA.le).mpr hI.first
  have h2 := (intervalIntegrable_iff_integrableOn_Ioc_of_le hAV).mpr hI.second
  have h3 := (intervalIntegrable_iff_integrableOn_Ioc_of_le hA.le).mpr hI.third
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hc : IntervalIntegrable (fun v => firstIntegrand N c β (V / β) (v / β)) volume 0 A := by
      simpa only [firstIntegrand_scale N hN c β V _ hβ] using h1
    have hh := intervalIntegrable_of_div_comp (firstIntegrand N c β (V / β)) β 0 A hβ hc
    simpa only [zero_div] using hh
  · apply intervalIntegrable_of_div_comp (secondIntegrand c β (V / β)) β A V hβ
    simpa only [secondIntegrand_scale c β V _ hβ] using h2.const_mul β
  · have hc : IntervalIntegrable (fun v => thirdIntegrand (V / β) (v / β)) volume 0 A := by
      simpa only [thirdIntegrand_scale β V _ hβ] using h3.const_mul β
    have hh := intervalIntegrable_of_div_comp (thirdIntegrand (V / β)) β 0 A hβ hc
    simpa only [zero_div] using hh
  · apply integrableOn_Ioi_of_div_comp fourthIntegrand β A hβ
    apply (hI.fourth.const_mul (β ^ 2)).congr
    filter_upwards [] with v
    exact (fourthIntegrand_scale β v hβ).symm

theorem normalized_actual_cdf_le_beta_physicalProfile (μ : ProbabilityMeasure ℝ)
    (h : StandardizedLaw μ) (n N : ℕ) (hN : 0 < N) (hNn : N ≤ n)
    (hρ : rho0 ≤ thirdAbsoluteMoment μ) (c : ℝ)
    (hC : thirdAbsoluteMoment μ + 1 ≤ c * thirdAbsoluteMoment μ)
    (A V : ℝ) (hA : 0 < A) (hAV : A ≤ V) (x : ℝ) :
    |(normalizedIidSumLaw μ n).real (Iic x) - GaussianTools.Phi x| ≤
      beta μ n * physicalProfile N c (beta μ n) (A / beta μ n) (V / beta μ n) := by
  have hβ := CoarseHighMomentRayPrice.beta_pos μ n (lt_of_lt_of_le hN hNn) hρ
  rw [physicalProfile_scale_eq_spectral N hN c (beta μ n) A V hβ hA hAV]
  exact CoefficientRaySpectral.normalized_actual_cdf_le_beta_spectralProfile
    μ h n N hN hNn hρ c hC A V hA hAV x

end BerryEsseen.CoefficientPhysicalProfile

#print axioms BerryEsseen.CoefficientPhysicalProfile.physicalProfile_scale_eq_spectral
#print axioms BerryEsseen.CoefficientPhysicalProfile.four_integrands_integrable
#print axioms BerryEsseen.CoefficientPhysicalProfile.normalized_actual_cdf_le_beta_physicalProfile
