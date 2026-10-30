module

public import BerryEsseen.Standardization
public import BerryEsseen.PerturbationCDF
public import BerryEsseen.GaussianTools
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

@[expose] public section

noncomputable section

namespace BerryEsseen.ContactVariation

open MeasureTheory Filter Set
open scoped Topology

/-- A positive closed global upper bound and its actual attainment.
This condition does not assert that such a maximizer exists. -/
structure PositiveClosedMaximum (μ : ProbabilityMeasure ℝ) (n : ℕ) (H C : ℝ) : Prop where
  global_upper : ∀ (ν : ProbabilityMeasure ℝ), StandardizedLaw ν → ∀ y : ℝ,
    (normalizedIidSumLaw ν n).real (Iic y) - GaussianTools.Phi y ≤
      C * thirdAbsoluteMoment ν / Real.sqrt n
  attainment : (MixtureSum.iidSumLaw (μ : Measure ℝ) n).real (Iic H) -
    GaussianTools.Phi (H / Real.sqrt n) = C * thirdAbsoluteMoment μ / Real.sqrt n

def scale (x ε : ℝ) : ℝ := Real.sqrt (PerturbationMoment.varianceFormula x ε)

def threshold (n : ℕ) (H x ε : ℝ) : ℝ :=
  (H / Real.sqrt n - (Real.sqrt n * x) * ε) / scale x ε

def normalizedThird (μ : ProbabilityMeasure ℝ) (x ε : ℝ) : ℝ :=
  PerturbationMoment.centeredMomentFormula μ x ε / scale x ε ^ 3

def momentSlope (μ : ProbabilityMeasure ℝ) (x : ℝ) : ℝ :=
  |x| ^ 3 - (3 / 2 : ℝ) * thirdAbsoluteMoment μ * x ^ 2 -
    3 * SignedMoment.signedSecondMoment μ * x + thirdAbsoluteMoment μ / 2

def D (μ : ProbabilityMeasure ℝ) (n : ℕ) (H C x : ℝ) : ℝ :=
  (n : ℝ) * ((MixtureSum.iidSumLaw (μ : Measure ℝ) (n - 1)).real (Iic (H - x)) -
      (MixtureSum.iidSumLaw (μ : Measure ℝ) n).real (Iic H)) +
    GaussianTools.phi (H / Real.sqrt n) *
      (Real.sqrt n * x + (H / Real.sqrt n) / 2 * (x ^ 2 - 1)) -
    (C / Real.sqrt n) * momentSlope μ x

/-- The extension is analytic only as a proof tool; probability identities
below are restricted to the genuine nonnegative mixture weights. -/
def J (μ : ProbabilityMeasure ℝ) (n : ℕ) (H C x ε : ℝ) : ℝ :=
  PerturbationCDF.cdfPolynomial μ x H n ε - GaussianTools.Phi (threshold n H x ε) -
    (C / Real.sqrt n) * normalizedThird μ x ε

@[simp] theorem scale_zero (x : ℝ) : scale x 0 = 1 := by
  simp [scale, PerturbationMoment.varianceFormula]

@[simp] theorem threshold_zero (n : ℕ) (H x : ℝ) : threshold n H x 0 = H / Real.sqrt n := by
  simp [threshold]

@[simp] theorem normalizedThird_zero (μ : ProbabilityMeasure ℝ) (x : ℝ) :
    normalizedThird μ x 0 = thirdAbsoluteMoment μ := by
  simp [normalizedThird, PerturbationMoment.centeredMomentFormula, thirdAbsoluteMoment]

theorem hasDerivAt_scale (x : ℝ) :
    HasDerivAt (scale x) ((x ^ 2 - 1) / 2) 0 := by
  have hd := (PerturbationMoment.hasDerivAt_varianceFormula x).sqrt
    (by simp [PerturbationMoment.varianceFormula])
  convert hd using 1
  · funext ε
    rfl
  · simp [PerturbationMoment.varianceFormula]

theorem hasDerivAt_threshold (n : ℕ) (H x : ℝ) :
    HasDerivAt (threshold n H x)
      (-(Real.sqrt n * x + (H / Real.sqrt n) / 2 * (x ^ 2 - 1))) 0 := by
  have hnum := (hasDerivAt_const (0 : ℝ) (H / Real.sqrt n)).sub
    ((hasDerivAt_id 0).const_mul (Real.sqrt n * x))
  have hd := hnum.div (hasDerivAt_scale x) (by simp)
  convert hd using 1
  · funext ε
    rfl
  · simp
    ring

theorem hasDerivAt_normalizedThird (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (x : ℝ) :
    HasDerivAt (normalizedThird μ x) (momentSlope μ x) 0 := by
  have hd := (PerturbationMoment.hasDerivAt_centeredMomentFormula μ h x).div
    ((hasDerivAt_scale x).fun_pow 3) (by simp)
  convert hd using 1
  · funext ε
    rfl
  · simp [momentSlope, PerturbationMoment.centeredMomentFormula, thirdAbsoluteMoment]
    ring

/-- The derivative uses the actual Gaussian CDF and the already proved
common-marginal convolution and central-moment variations. -/
theorem hasDerivAt_J (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (hn : 0 < n) (H C x : ℝ) : HasDerivAt (J μ n H C x) (D μ n H C x) 0 := by
  have hg := (GaussianTools.hasDerivAt_Phi (threshold n H x 0)).comp 0
    (hasDerivAt_threshold n H x)
  have hm := (hasDerivAt_normalizedThird μ h x).const_mul (C / Real.sqrt n)
  have hd := ((PerturbationCDF.hasDerivAt_cdfPolynomial μ x H n hn).sub hg).sub hm
  convert hd using 1
  · funext ε
    rfl
  · simp [D]
    ring

theorem threshold_eq_original (n : ℕ) (hn : 0 < n) (H x ε : ℝ)
    (hs : scale x ε ≠ 0) :
    threshold n H x ε =
      (H - (n : ℝ) * (ε * x)) / (scale x ε * Real.sqrt n) := by
  have hn0 : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn))
  have hn2 := congrArg (fun a : ℝ => a * (ε * x)) (Real.sq_sqrt (Nat.cast_nonneg n))
  unfold threshold
  field_simp [hs, hn0]
  nlinarith

theorem cdfPolynomial_zero (μ : ProbabilityMeasure ℝ) (n : ℕ) (H x : ℝ) :
    PerturbationCDF.cdfPolynomial μ x H n 0 =
      (MixtureSum.iidSumLaw (μ : Measure ℝ) n).real (Iic H) := by
  have heq := (PerturbationCDF.actualCDF_eq_polynomial μ x H 0 n
    (by norm_num) (by norm_num)).symm
  simpa [PerturbationCDF.actualCDF, PerturbationMoment.mixtureMeasure] using heq

theorem J_zero (μ : ProbabilityMeasure ℝ) (n : ℕ) (H C x : ℝ)
    (hm : PositiveClosedMaximum μ n H C) : J μ n H C x 0 = 0 := by
  unfold J
  rw [cdfPolynomial_zero, threshold_zero, normalizedThird_zero, hm.attainment]
  ring

/-- The global standardized bound applies to the actual perturbed marginal,
at the same fixed threshold in original coordinates. -/
theorem J_nonpos (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (hn : 0 < n) (H C x ε : ℝ) (hm : PositiveClosedMaximum μ n H C)
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) : J μ n H C x ε ≤ 0 := by
  let ν := Standardization.standardized
    (PerturbationMoment.mixtureLaw μ x ε hε0 (le_of_lt hε1))
  have hν : StandardizedLaw ν := Standardization.perturbation_standardizedLaw μ h x ε hε0 hε1
  have hbound := hm.global_upper ν hν
    ((H - (n : ℝ) * (ε * x)) /
      (Real.sqrt (PerturbationMoment.varianceFormula x ε) * Real.sqrt n))
  have hcdf := Standardization.perturbation_iidSum_closedCDF μ h x ε hε0 hε1 n hn H
  have hthird := Standardization.perturbation_thirdAbsoluteMoment μ h x ε hε0 hε1
  change (normalizedIidSumLaw ν n).real _ - _ ≤ C * thirdAbsoluteMoment ν / Real.sqrt n at hbound
  rw [← hcdf, hthird] at hbound
  have hv : 0 < PerturbationMoment.varianceFormula x ε := by
    unfold PerturbationMoment.varianceFormula
    exact mul_pos (sub_pos.mpr hε1) (by nlinarith [mul_nonneg hε0 (sq_nonneg x)])
  have hs : scale x ε ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hv)
  change PerturbationCDF.actualCDF μ x H n ε -
    GaussianTools.Phi ((H - (n : ℝ) * (ε * x)) / (scale x ε * Real.sqrt n)) ≤
      C * normalizedThird μ x ε / Real.sqrt n at hbound
  rw [PerturbationCDF.actualCDF_eq_polynomial μ x H ε n hε0 (le_of_lt hε1),
    ← threshold_eq_original n hn H x ε hs] at hbound
  have hcost : C * normalizedThird μ x ε / Real.sqrt n =
      (C / Real.sqrt n) * normalizedThird μ x ε := by ring
  rw [hcost] at hbound
  unfold J
  linarith

theorem eventually_J_nonpos (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (hn : 0 < n) (H C x : ℝ) (hm : PositiveClosedMaximum μ n H C) :
    ∀ᶠ ε in 𝓝[Set.Ici (0 : ℝ)] 0, J μ n H C x ε ≤ 0 := by
  have hlt0 : ∀ᶠ ε : ℝ in 𝓝 (0 : ℝ), ε < 1 := Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)
  have hlt : ∀ᶠ ε : ℝ in 𝓝[Set.Ici (0 : ℝ)] 0, ε < 1 :=
    hlt0.filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hlt] with ε hε0 hε1
  exact J_nonpos μ h n hn H C x ε hm hε0 hε1

/-- The genuine first-variation contact inequality. Existence of the
global maximizing law is a separate mathematical problem. -/
theorem D_nonpos (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (hn : 0 < n) (H C : ℝ) (hm : PositiveClosedMaximum μ n H C) (x : ℝ) :
    D μ n H C x ≤ 0 := by
  have hmax : IsLocalMaxOn (J μ n H C x) (Ici (0 : ℝ)) 0 := by
    change ∀ᶠ ε in 𝓝[Ici (0 : ℝ)] 0, J μ n H C x ε ≤ J μ n H C x 0
    rw [J_zero μ n H C x hm]
    exact eventually_J_nonpos μ h n hn H C x hm
  have ht : (1 : ℝ) ∈ posTangentConeAt (Ici (0 : ℝ)) 0 := by
    rw [one_mem_posTangentConeAt_iff_mem_closure]
    simp [inter_eq_left.mpr Ioi_subset_Ici_self, closure_Ioi]
  have hd := hmax.hasFDerivWithinAt_nonpos
    (hasDerivAt_J μ h n hn H C x).hasFDerivAt.hasFDerivWithinAt ht
  simpa using hd

end BerryEsseen.ContactVariation

#print axioms BerryEsseen.ContactVariation.hasDerivAt_normalizedThird
#print axioms BerryEsseen.ContactVariation.hasDerivAt_J
#print axioms BerryEsseen.ContactVariation.J_nonpos
#print axioms BerryEsseen.ContactVariation.D_nonpos
