module

public import BerryEsseen.IidSmoothingPrice
public import BerryEsseen.ThirdMomentRegion
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

/-! 2026-10-29: the complete two-cap sine primitive used by the finite-n
closed-rho-box certificates.  Both caps are retained at their actual cut
points, and the original directed integrals are split at those points.
The same-law comparison uses only the actual third absolute moment <= R.
No numerical interval value or finite-n CDF constant is asserted here. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped Interval

namespace BerryEsseen.FiniteRhoSinePrice

def firstKernel (R v : ℝ) : ℝ := 2 * Real.sin (min (R * v / 2) (Real.pi / 2))

def secondKernel (v : ℝ) : ℝ := v * Real.sin (min v (Real.pi / 2))

def kernel (R v : ℝ) : ℝ := firstKernel R v + secondKernel v

def H (R t : ℝ) : ℝ := ∫ v in (0 : ℝ)..t, kernel R v

def firstCut (R t : ℝ) : ℝ := min t (Real.pi / R)

def secondCut (t : ℝ) : ℝ := min t (Real.pi / 2)

def closedForm (R t : ℝ) : ℝ :=
  8 * Real.sin (R * firstCut R t / 4) ^ 2 / R + 2 * (t - firstCut R t) +
    Real.sin (secondCut t) - secondCut t * Real.cos (secondCut t) +
    (t ^ 2 - secondCut t ^ 2) / 2

lemma continuous_firstKernel (R : ℝ) : Continuous (firstKernel R) := by
  unfold firstKernel
  fun_prop

lemma continuous_secondKernel : Continuous secondKernel := by
  unfold secondKernel
  fun_prop

lemma continuous_kernel (R : ℝ) : Continuous (kernel R) :=
  (continuous_firstKernel R).add continuous_secondKernel

lemma continuous_H (R : ℝ) : Continuous (H R) :=
  intervalIntegral.continuous_primitive (fun a b => (continuous_kernel R).intervalIntegrable a b) 0

lemma firstCut_nonneg (R t : ℝ) (hR : 0 < R) (ht : 0 ≤ t) : 0 ≤ firstCut R t :=
  le_min ht (div_nonneg Real.pi_pos.le hR.le)

lemma secondCut_nonneg (t : ℝ) (ht : 0 ≤ t) : 0 ≤ secondCut t :=
  le_min ht (by positivity)

/-- The first uncapped prefix is computed using Mathlib's sine integral,
then written as a squared sine exactly as in the interval program. -/
lemma integral_first_uncapped (R u : ℝ) (hR : 0 < R) :
    (∫ v in (0 : ℝ)..u, 2 * Real.sin (R * v / 2)) =
      8 * Real.sin (R * u / 4) ^ 2 / R := by
  have hhalf : R / 2 ≠ 0 := by positivity
  have hc : Real.cos ((R / 2) * u) = 1 - 2 * Real.sin (R * u / 4) ^ 2 := by
    rw [show (R / 2) * u = 2 * (R * u / 4) by ring, Real.cos_two_mul_eq_one_sub]
  calc
    _ = 2 * ∫ v in (0 : ℝ)..u, Real.sin ((R / 2) * v) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro v _
      dsimp only
      rw [show R * v / 2 = (R / 2) * v by ring]
    _ = 2 * ((R / 2)⁻¹ * (1 - Real.cos ((R / 2) * u))) := by
      rw [intervalIntegral.integral_comp_mul_left Real.sin hhalf, integral_sin]
      simp only [mul_zero, Real.cos_zero, smul_eq_mul]
    _ = _ := by rw [hc]; field_simp [hR.ne']; ring

private lemma secondPrefix_hasDerivAt (v : ℝ) :
    HasDerivAt (fun x : ℝ => Real.sin x - x * Real.cos x) (v * Real.sin v) v := by
  have hd : HasDerivAt (fun x : ℝ => Real.sin x - x * Real.cos x)
      (Real.cos v - (Real.cos v + v * (-Real.sin v))) v := by
    simpa only [id_eq, one_mul] using
      (Real.hasDerivAt_sin v).fun_sub ((hasDerivAt_id v).fun_mul (Real.hasDerivAt_cos v))
  convert hd using 1
  ring

lemma integral_second_uncapped (u : ℝ) :
    (∫ v in (0 : ℝ)..u, v * Real.sin v) = Real.sin u - u * Real.cos u := by
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun v _ => secondPrefix_hasDerivAt v)
    ((by fun_prop : Continuous (fun v : ℝ => v * Real.sin v)).intervalIntegrable 0 u)
  simpa only [Real.sin_zero, zero_mul, sub_zero] using hh

theorem integral_firstKernel_eq (R t : ℝ) (hR : 0 < R) (ht : 0 ≤ t) :
    (∫ v in (0 : ℝ)..t, firstKernel R v) =
      8 * Real.sin (R * firstCut R t / 4) ^ 2 / R + 2 * (t - firstCut R t) := by
  let z := firstCut R t
  have hz0 : 0 ≤ z := firstCut_nonneg R t hR ht
  have hzt : z ≤ t := min_le_left _ _
  have hzc : z ≤ Real.pi / R := min_le_right _ _
  have hp : (∫ v in (0 : ℝ)..z, firstKernel R v) =
      8 * Real.sin (R * z / 4) ^ 2 / R := by
    rw [← integral_first_uncapped R z hR]
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le hz0] at hv
    have hvc : v ≤ Real.pi / R := hv.2.trans hzc
    have hh := (le_div_iff₀ hR).mp hvc
    have harg : R * v / 2 ≤ Real.pi / 2 := by nlinarith only [hh]
    rw [firstKernel, min_eq_left harg]
  have htail : (∫ v in z..t, firstKernel R v) = 2 * (t - z) := by
    by_cases htc : t ≤ Real.pi / R
    · have hz : z = t := min_eq_left htc
      rw [hz]
      simp
    · have hct : Real.pi / R ≤ t := (lt_of_not_ge htc).le
      have hz : z = Real.pi / R := min_eq_right hct
      calc
        _ = ∫ v in z..t, (2 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro v hv
          rw [uIcc_of_le hzt] at hv
          have hcv : Real.pi / R ≤ v := hz ▸ hv.1
          have hh := (div_le_iff₀ hR).mp hcv
          have harg : Real.pi / 2 ≤ R * v / 2 := by nlinarith only [hh]
          rw [firstKernel, min_eq_right harg, Real.sin_pi_div_two, mul_one]
        _ = _ := by rw [intervalIntegral.integral_const]; simp only [smul_eq_mul]; ring
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    ((continuous_firstKernel R).intervalIntegrable 0 z)
    ((continuous_firstKernel R).intervalIntegrable z t)
  change (∫ v in (0 : ℝ)..t, firstKernel R v) = 8 * Real.sin (R * z / 4) ^ 2 / R + 2 * (t - z)
  rw [← hsplit, hp, htail]

theorem integral_secondKernel_eq (t : ℝ) (ht : 0 ≤ t) :
    (∫ v in (0 : ℝ)..t, secondKernel v) =
      Real.sin (secondCut t) - secondCut t * Real.cos (secondCut t) +
        (t ^ 2 - secondCut t ^ 2) / 2 := by
  let w := secondCut t
  have hw0 : 0 ≤ w := secondCut_nonneg t ht
  have hwt : w ≤ t := min_le_left _ _
  have hwc : w ≤ Real.pi / 2 := min_le_right _ _
  have hp : (∫ v in (0 : ℝ)..w, secondKernel v) = Real.sin w - w * Real.cos w := by
    rw [← integral_second_uncapped w]
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le hw0] at hv
    rw [secondKernel, min_eq_left (hv.2.trans hwc)]
  have htail : (∫ v in w..t, secondKernel v) = (t ^ 2 - w ^ 2) / 2 := by
    by_cases htc : t ≤ Real.pi / 2
    · have hw : w = t := min_eq_left htc
      rw [hw]
      simp
    · have hct : Real.pi / 2 ≤ t := (lt_of_not_ge htc).le
      have hw : w = Real.pi / 2 := min_eq_right hct
      calc
        _ = ∫ v in w..t, v := by
          apply intervalIntegral.integral_congr
          intro v hv
          rw [uIcc_of_le hwt] at hv
          have hcv : Real.pi / 2 ≤ v := hw ▸ hv.1
          rw [secondKernel, min_eq_right hcv, Real.sin_pi_div_two, mul_one]
        _ = _ := integral_id
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (continuous_secondKernel.intervalIntegrable 0 w) (continuous_secondKernel.intervalIntegrable w t)
  change (∫ v in (0 : ℝ)..t, secondKernel v) = Real.sin w - w * Real.cos w + (t ^ 2 - w ^ 2) / 2
  rw [← hsplit, hp, htail]

/-- Exact full double-cap elementary primitive, including both seams. -/
theorem H_eq_closedForm (R t : ℝ) (hR : 0 < R) (ht : 0 ≤ t) : H R t = closedForm R t := by
  unfold H kernel closedForm
  rw [intervalIntegral.integral_add ((continuous_firstKernel R).intervalIntegrable 0 t)
    (continuous_secondKernel.intervalIntegrable 0 t), integral_firstKernel_eq R t hR ht,
    integral_secondKernel_eq t ht]
  ring

/-- The quantities intersected with [0,infinity) by h_complete really are
nonnegative at the exact capped endpoints. -/
theorem closedForm_parts_nonneg (R t : ℝ) (ht : 0 ≤ t) :
    0 ≤ t - firstCut R t ∧
      0 ≤ Real.sin (secondCut t) - secondCut t * Real.cos (secondCut t) ∧
      0 ≤ t ^ 2 - secondCut t ^ 2 := by
  have hw0 := secondCut_nonneg t ht
  have hwt : secondCut t ≤ t := min_le_left _ _
  have hwc : secondCut t ≤ Real.pi / 2 := min_le_right _ _
  refine ⟨sub_nonneg.mpr (min_le_left _ _), ?_, by nlinarith⟩
  rw [← integral_second_uncapped (secondCut t)]
  apply intervalIntegral.integral_nonneg hw0
  intro v hv
  have hsin : 0 ≤ Real.sin v := Real.sin_nonneg_of_nonneg_of_le_pi hv.1
    (hv.2.trans (hwc.trans (by linarith [Real.pi_pos])))
  exact mul_nonneg hv.1 hsin

theorem closedForm_nonneg (R t : ℝ) (hR : 0 < R) (ht : 0 ≤ t) : 0 ≤ closedForm R t := by
  obtain ⟨hz, hp, hw⟩ := closedForm_parts_nonneg R t ht
  have hfirst : 0 ≤ 8 * Real.sin (R * firstCut R t / 4) ^ 2 / R := by positivity
  unfold closedForm
  linarith only [hz, hp, hw, hfirst]

theorem H_nonneg (R t : ℝ) (hR : 0 < R) (ht : 0 ≤ t) : 0 ≤ H R t := by
  rw [H_eq_closedForm R t hR ht]
  exact closedForm_nonneg R t hR ht

lemma sineKernelPrice_le_kernel (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (R v : ℝ) (hρ : thirdAbsoluteMoment μ ≤ R) (hv : 0 ≤ v) :
    SquareBiasSine.sineKernelPrice μ v ≤ kernel R v := by
  have hρ0 : 0 ≤ thirdAbsoluteMoment μ := (by norm_num : (0 : ℝ) ≤ 1).trans
    (ThirdMomentRegion.one_le_third μ h)
  have hleft : 0 ≤ min (thirdAbsoluteMoment μ * v / 2) (Real.pi / 2) :=
    le_min (by positivity) (by positivity)
  have harg : min (thirdAbsoluteMoment μ * v / 2) (Real.pi / 2) ≤
      min (R * v / 2) (Real.pi / 2) := by
    apply min_le_min _ le_rfl
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hρ hv) (by norm_num)
  have hs := Real.sin_le_sin_of_le_of_le_pi_div_two
    (show -(Real.pi / 2) ≤ min (thirdAbsoluteMoment μ * v / 2) (Real.pi / 2) by
      linarith [Real.pi_pos]) (min_le_right (R * v / 2) (Real.pi / 2)) harg
  unfold SquareBiasSine.sineKernelPrice kernel firstKernel secondKernel
  rw [abs_of_nonneg hv]
  linarith only [hs]

theorem sinePrimitive_le_H (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (R t : ℝ) (hρ : thirdAbsoluteMoment μ ≤ R) (ht : 0 ≤ t) :
    IidSmoothingPrice.sinePrimitive μ t ≤ H R t := by
  unfold IidSmoothingPrice.sinePrimitive H
  exact intervalIntegral.integral_mono_on ht
    ((SquareBiasSine.continuous_sineKernelPrice μ).intervalIntegrable 0 t)
    ((continuous_kernel R).intervalIntegrable 0 t)
    (fun v hv => sineKernelPrice_le_kernel μ h R v hρ hv.1)

theorem sinePrimitive_le_closedForm (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (R t : ℝ) (hR : 0 < R) (hρ : thirdAbsoluteMoment μ ≤ R) (ht : 0 ≤ t) :
    IidSmoothingPrice.sinePrimitive μ t ≤ closedForm R t := by
  rw [← H_eq_closedForm R t hR ht]
  exact sinePrimitive_le_H μ h R t hρ ht

theorem gamma_sq_le_root_at_R (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (R : ℝ) (hR : 0 ≤ R) (hρ : thirdAbsoluteMoment μ ≤ R) :
    ZeroBias.gamma μ ^ 2 ≤ (R ^ 2 - 4 + R * Real.sqrt (R ^ 2 + 8)) / 2 := by
  have hρ0 : 0 ≤ thirdAbsoluteMoment μ := (by norm_num : (0 : ℝ) ≤ 1).trans
    (ThirdMomentRegion.one_le_third μ h)
  have hs := pow_le_pow_left₀ hρ0 hρ 2
  have hm := mul_le_mul_of_nonneg_right hs (by positivity : 0 ≤ ZeroBias.gamma μ ^ 2 + 4)
  exact ThirdMomentRegion.square_le_root_of_region _ R hR
    ((ThirdMomentRegion.signed_third_region μ h).trans hm)

theorem abs_gamma_le_root_at_R (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (R : ℝ) (hR : 0 ≤ R) (hρ : thirdAbsoluteMoment μ ≤ R) :
    |ZeroBias.gamma μ| ≤ Real.sqrt ((R ^ 2 - 4 + R * Real.sqrt (R ^ 2 + 8)) / 2) :=
  Real.abs_le_sqrt (gamma_sq_le_root_at_R μ h R hR hρ)

end BerryEsseen.FiniteRhoSinePrice

#print axioms BerryEsseen.FiniteRhoSinePrice.H_eq_closedForm
#print axioms BerryEsseen.FiniteRhoSinePrice.closedForm_parts_nonneg
#print axioms BerryEsseen.FiniteRhoSinePrice.sinePrimitive_le_closedForm
#print axioms BerryEsseen.FiniteRhoSinePrice.gamma_sq_le_root_at_R
#print axioms BerryEsseen.FiniteRhoSinePrice.abs_gamma_le_root_at_R
