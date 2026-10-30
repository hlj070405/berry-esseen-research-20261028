module

public import BerryEsseen.GaussianContactApplication
public import BerryEsseen.SignedMoment
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

/-! 2026-10-28: one-item real-CDF Gaussian replacement and heat smoothing.
The law's own third absolute moment prices the item replacement; variance
smoothing is controlled separately by the Gaussian third Hermite factor. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators MeasureTheory Interval
open BerryEsseen.GaussianTools BerryEsseen.GaussianPrices BerryEsseen.GaussianPeano
open BerryEsseen.GaussianPeanoRepresentation BerryEsseen.GaussianContactApplication

namespace BerryEsseen.GaussianEntry

lemma hermite3_certificate (y : ℝ) :
    (64 : ℝ) / 25 * (1 + y + y ^ 2 / 2 + y ^ 3 / 6 + y ^ 4 / 24) - y * (3 - y) ^ 2 =
      (8 : ℝ) / 75 * y ^ 2 * (y - 3) ^ 2 + y ^ 3 / 15 +
      6 * (y - 1 / 2) ^ 2 + (8 : ℝ) / 25 * (y - 11 / 16) ^ 2 + 727 / 800 := by ring

lemma hermite3_polynomial (y : ℝ) (hy : 0 ≤ y) :
    y * (3 - y) ^ 2 ≤ (64 : ℝ) / 25 * Real.exp y := by
  have hsum := Real.sum_le_exp_of_nonneg hy 5
  have hseries : (∑ k ∈ Finset.range 5, y ^ k / (k.factorial : ℝ)) =
      1 + y + y ^ 2 / 2 + y ^ 3 / 6 + y ^ 4 / 24 := by
    norm_num [Finset.sum_range_succ]
  rw [hseries] at hsum
  have hnon : 0 ≤ (64 : ℝ) / 25 *
      (1 + y + y ^ 2 / 2 + y ^ 3 / 6 + y ^ 4 / 24) - y * (3 - y) ^ 2 := by
    rw [hermite3_certificate]
    positivity
  nlinarith [hsum]

lemma phi_sq_mul_exp (r : ℝ) : phi r ^ 2 * Real.exp (r ^ 2) = phi 0 ^ 2 := by
  have he : Real.exp (r ^ 2 / 2) ^ 2 = Real.exp (r ^ 2) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [phi_eq_phi_zero_div_exp r, div_pow, he]
  exact div_mul_cancel₀ _ (Real.exp_ne_zero _)

/-- A global rational bound for the actual third Gaussian density derivative. -/
theorem hermite3_bound (r : ℝ) : |r * (3 - r ^ 2) * phi r| ≤ (16 : ℝ) / 25 := by
  have hp := hermite3_polynomial (r ^ 2) (sq_nonneg r)
  have hmul := mul_le_mul_of_nonneg_right hp (sq_nonneg (phi r))
  have hphi := phi_sq_mul_exp r
  have hzero : phi 0 ^ 2 ≤ ((2 : ℝ) / 5) ^ 2 :=
    (sq_le_sq₀ (phi_nonneg 0) (by norm_num)).mpr phi_zero_lt_2_5.le
  have hs : (r * (3 - r ^ 2) * phi r) ^ 2 ≤ ((16 : ℝ) / 25) ^ 2 := by
    nlinarith [hmul, hphi, hzero]
  exact (sq_le_sq₀ (abs_nonneg _) (by norm_num)).mp (by simpa only [sq_abs] using hs)

lemma rho_ge_one (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) : 1 ≤ thirdAbsoluteMoment μ := by
  have ha := SignedMoment.firstAbsoluteMoment_pos μ h
  have hb := SignedMoment.first_sq_add_signed_sq_le_one μ h
  have hp := SignedMoment.first_mul_third_ge_one_add_signed_sq μ h
  have har : SignedMoment.firstAbsoluteMoment μ ≤ 1 := by
    apply (sq_le_sq₀ ha.le (by norm_num : (0 : ℝ) ≤ 1)).mp
    nlinarith [sq_nonneg (SignedMoment.signedSecondMoment μ)]
  have hr : 0 ≤ thirdAbsoluteMoment μ := integral_nonneg fun x => pow_nonneg (abs_nonneg x) 3
  have hprod := mul_le_mul_of_nonneg_right har hr
  nlinarith [sq_nonneg (SignedMoment.signedSecondMoment μ)]

lemma integrable_quadratic_standardized (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (A B C : ℝ) : Integrable (quadratic A B C) (μ : Measure ℝ) := by
  have hAB : Integrable (fun u : ℝ => A + B * u) (μ : Measure ℝ) :=
    (integrable_const _).add (h.integrable_mean.const_mul _)
  exact hAB.add (h.integrable_square.const_mul C)

lemma integral_quadratic_standardized (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (A B C : ℝ) : (∫ u, quadratic A B C u ∂(μ : Measure ℝ)) = A + C := by
  have hA : Integrable (fun _ : ℝ => A) (μ : Measure ℝ) := integrable_const _
  have hB : Integrable (fun u : ℝ => B * u) (μ : Measure ℝ) := h.integrable_mean.const_mul _
  have hC : Integrable (fun u : ℝ => C * u ^ 2) (μ : Measure ℝ) := h.integrable_square.const_mul _
  have hAB : Integrable (fun u : ℝ => A + B * u) (μ : Measure ℝ) := hA.add hB
  simp only [quadratic]
  rw [integral_add hAB hC, integral_add hA hB, integral_const_mul, integral_const_mul,
    h.mean_zero, h.second_moment_one]
  simp

lemma continuous_remainder_two (g : ℝ → ℝ) (hg : ContDiff ℝ 3 g) : Continuous (remainder 2 g) := by
  have heq : remainder 2 g = (fun u : ℝ => g u - quadratic (g 0) (deriv g 0) (iteratedDeriv 2 g 0 / 2) u) := by
    ext u
    linarith [remainder_identity_two g hg u]
  rw [heq]
  apply hg.continuous.sub
  unfold quadratic
  fun_prop

lemma integrable_remainder_standardized (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (g : ℝ → ℝ) (hg : ContDiff ℝ 3 g) (M : ℝ) (hbound : ∀ u, |iteratedDeriv 3 g u| ≤ M) :
    Integrable (remainder 2 g) (μ : Measure ℝ) := by
  have hdom : Integrable (fun u : ℝ => M / 6 * |u| ^ 3) (μ : Measure ℝ) := h.integrable_cube.const_mul _
  apply hdom.mono' (continuous_remainder_two g hg).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun u => by
    rw [Real.norm_eq_abs]
    convert abs_remainder_two_le g hg M hbound u using 1
    ring

/-- The original law alone prices its second-order Taylor error; there is no added Gaussian third moment. -/
theorem standardized_taylor_bound (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (g : ℝ → ℝ) (hg : ContDiff ℝ 3 g) (M : ℝ) (hbound : ∀ u, |iteratedDeriv 3 g u| ≤ M) :
    Integrable g (μ : Measure ℝ) ∧
      |(∫ u, g u ∂(μ : Measure ℝ)) - g 0 - iteratedDeriv 2 g 0 / 2| ≤ M * thirdAbsoluteMoment μ / 6 := by
  have hR := integrable_remainder_standardized μ h g hg M hbound
  have hP := integrable_quadratic_standardized μ h (g 0) (deriv g 0) (iteratedDeriv 2 g 0 / 2)
  have hEq : g = (fun u : ℝ => quadratic (g 0) (deriv g 0) (iteratedDeriv 2 g 0 / 2) u + remainder 2 g u) :=
    funext (remainder_identity_two g hg)
  constructor
  · rw [hEq]
    exact hP.add hR
  have hInt : (∫ u, g u ∂(μ : Measure ℝ)) = g 0 + iteratedDeriv 2 g 0 / 2 +
      ∫ u, remainder 2 g u ∂(μ : Measure ℝ) := by
    calc
      _ = ∫ u, quadratic (g 0) (deriv g 0) (iteratedDeriv 2 g 0 / 2) u + remainder 2 g u ∂(μ : Measure ℝ) :=
        integral_congr_ae (Filter.Eventually.of_forall (remainder_identity_two g hg))
      _ = _ := by rw [integral_add hP hR, integral_quadratic_standardized μ h]
  have hMono : (∫ u, ‖remainder 2 g u‖ ∂(μ : Measure ℝ)) ≤
      ∫ u, M / 6 * |u| ^ 3 ∂(μ : Measure ℝ) := by
    apply integral_mono hR.norm (h.integrable_cube.const_mul _)
    intro u
    dsimp only
    rw [Real.norm_eq_abs]
    convert abs_remainder_two_le g hg M hbound u using 1
    ring
  rw [integral_const_mul] at hMono
  change (∫ u, ‖remainder 2 g u‖ ∂(μ : Measure ℝ)) ≤ M / 6 * thirdAbsoluteMoment μ at hMono
  rw [hInt]
  have hEqAbs : |g 0 + iteratedDeriv 2 g 0 / 2 + (∫ u, remainder 2 g u ∂(μ : Measure ℝ)) -
      g 0 - iteratedDeriv 2 g 0 / 2| = |∫ u, remainder 2 g u ∂(μ : Measure ℝ)| := by congr 1; ring
  rw [hEqAbs]
  have hNorm := norm_integral_le_integral_norm (f := remainder 2 g) (μ := (μ : Measure ℝ))
  rw [Real.norm_eq_abs] at hNorm
  nlinarith [hMono, hNorm]

end BerryEsseen.GaussianEntry

#print axioms BerryEsseen.GaussianEntry.hermite3_bound
#print axioms BerryEsseen.GaussianEntry.standardized_taylor_bound

namespace BerryEsseen.GaussianEntry

/-- The original closed Gaussian CDF as a function of its positive variance. -/
def heatCDF (H s : ℝ) : ℝ := Phi (H / Real.sqrt s)
def heatArgument (H s : ℝ) : ℝ := H / Real.sqrt s
def heatSlope (H s : ℝ) : ℝ := -(heatArgument H s * phi (heatArgument H s)) / (2 * s)
def heatSecond (H s : ℝ) : ℝ :=
  (heatArgument H s * (3 - heatArgument H s ^ 2) * phi (heatArgument H s)) / (4 * s ^ 2)

lemma hasDerivAt_heatArgument (H s : ℝ) (hs : 0 < s) :
    HasDerivAt (heatArgument H) (-heatArgument H s / (2 * s)) s := by
  have h := (hasDerivAt_const s H).fun_div (Real.hasDerivAt_sqrt (ne_of_gt hs))
    (ne_of_gt (Real.sqrt_pos.mpr hs))
  convert h using 1
  · rfl
  · simp only [heatArgument]
    rw [Real.sq_sqrt hs.le]
    field_simp [ne_of_gt hs, ne_of_gt (Real.sqrt_pos.mpr hs)]; ring

lemma hasDerivAt_heatCDF (H s : ℝ) (hs : 0 < s) : HasDerivAt (heatCDF H) (heatSlope H s) s := by
  have h := (hasDerivAt_Phi (heatArgument H s)).comp s (hasDerivAt_heatArgument H s hs)
  convert h using 1
  · rfl
  · simp only [heatSlope]
    ring

/-- The heat variance derivative is differentiated on the whole positive half-line. -/
lemma hasDerivAt_heatSlope (H s : ℝ) (hs : 0 < s) : HasDerivAt (heatSlope H) (heatSecond H s) s := by
  have ha := hasDerivAt_heatArgument H s hs
  have h := ((ha.fun_mul ((hasDerivAt_phi (heatArgument H s)).comp s ha)).fun_neg).fun_div
    ((hasDerivAt_id' s).const_mul (2 : ℝ)) (by positivity)
  convert h using 1
  · rfl
  · simp only [heatSecond, Function.comp_apply]
    field_simp [ne_of_gt hs]; ring

lemma abs_heatSecond_le (H v s : ℝ) (hv : 0 < v) (hvs : v ≤ s) :
    |heatSecond H s| ≤ (4 : ℝ) / (25 * v ^ 2) := by
  have hs : 0 < s := lt_of_lt_of_le hv hvs
  have hsq : v ^ 2 ≤ s ^ 2 := (sq_le_sq₀ hv.le hs.le).mpr hvs
  rw [heatSecond, abs_div, abs_of_pos (by positivity : 0 < 4 * s ^ 2)]
  calc
    |heatArgument H s * (3 - heatArgument H s ^ 2) * phi (heatArgument H s)| / (4 * s ^ 2) ≤
        ((16 : ℝ) / 25) / (4 * s ^ 2) :=
      div_le_div_of_nonneg_right (hermite3_bound _) (by positivity)
    _ = (4 : ℝ) / (25 * s ^ 2) := by ring
    _ ≤ (4 : ℝ) / (25 * v ^ 2) := by
      apply (div_le_div_iff₀ (by positivity : 0 < 25 * s ^ 2) (by positivity : 0 < 25 * v ^ 2)).mpr
      nlinarith [hsq]

lemma heatSlope_increment_bound (H v : ℝ) (hv : 0 < v) :
    ∀ s ∈ Icc v (v + 1), |heatSlope H s - heatSlope H v| ≤
      ((4 : ℝ) / (25 * v ^ 2)) * (s - v) := by
  have h := norm_image_sub_le_of_norm_deriv_le_segment'
    (a := v) (b := v + 1) (f := heatSlope H) (f' := heatSecond H)
    (fun s hs => (hasDerivAt_heatSlope H s (lt_of_lt_of_le hv hs.1)).hasDerivWithinAt)
    (fun s hs => by
      rw [Real.norm_eq_abs]
      exact abs_heatSecond_le H v s hv hs.1)
  simpa only [Real.norm_eq_abs] using h

/-- The exact half-factor heat-smoothing error, proved by an actual FTC integral. -/
theorem heat_taylor_bound (H v : ℝ) (hv : 0 < v) :
    |heatCDF H (v + 1) - heatCDF H v - heatSlope H v| ≤ (2 : ℝ) / (25 * v ^ 2) := by
  have hab : v ≤ v + 1 := by linarith
  have hcont : ContinuousOn (heatSlope H) (uIcc v (v + 1)) := by
    rw [uIcc_of_le hab]
    intro s hs
    exact (hasDerivAt_heatSlope H s (lt_of_lt_of_le hv hs.1)).continuousAt.continuousWithinAt
  have hint : IntervalIntegrable (heatSlope H) volume v (v + 1) := hcont.intervalIntegrable
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := v) (b := v + 1) (fun s hs => hasDerivAt_heatCDF H s (by
      rw [uIcc_of_le hab] at hs
      exact lt_of_lt_of_le hv hs.1)) hint
  have heq : heatCDF H (v + 1) - heatCDF H v - heatSlope H v =
      ∫ s in v..(v + 1), heatSlope H s - heatSlope H v := by
    rw [intervalIntegral.integral_sub hint intervalIntegrable_const, hFTC, intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    ring
  let C : ℝ := 4 / (25 * v ^ 2)
  have hwcont : Continuous (fun s : ℝ => C * (s - v)) := by fun_prop
  have hw : (∫ s in v..(v + 1), C * (s - v)) = C / 2 := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hasDerivAt_shift_square v s)
        ((continuous_id.sub continuous_const).intervalIntegrable v (v + 1))]
    ring
  calc
    |heatCDF H (v + 1) - heatCDF H v - heatSlope H v| =
        ‖∫ s in v..(v + 1), heatSlope H s - heatSlope H v‖ := by rw [heq, Real.norm_eq_abs]
    _ ≤ ∫ s in v..(v + 1), C * (s - v) := by
      apply intervalIntegral.norm_integral_le_of_norm_le hab ?_ (hwcont.intervalIntegrable v (v + 1))
      exact Filter.Eventually.of_forall fun s hs => by
        rw [Real.norm_eq_abs]
        exact heatSlope_increment_bound H v hv s ⟨hs.1.le, hs.2⟩
    _ = (2 : ℝ) / (25 * v ^ 2) := by rw [hw]; dsimp [C]; ring

end BerryEsseen.GaussianEntry

#print axioms BerryEsseen.GaussianEntry.hasDerivAt_heatSlope
#print axioms BerryEsseen.GaussianEntry.heat_taylor_bound

namespace BerryEsseen.GaussianEntry

/-- One Gaussian replacement item, using the original closed CDF. -/
def gaussianStep (v H u : ℝ) : ℝ := Phi ((H - u) / Real.sqrt v)

lemma contDiff_gaussianStep (v H : ℝ) : ContDiff ℝ 3 (gaussianStep v H) := by
  have ha : ContDiff ℝ 3 (fun u : ℝ => (H - u) / Real.sqrt v) := by fun_prop
  exact contDiff_Phi_three.comp ha

lemma gaussianStep_eq_test_div (v H : ℝ) (hv : 1 ≤ v) :
    gaussianStep v H = (fun u : ℝ => testFunction (v + 1) H u / ((v + 1) * Real.sqrt (v + 1))) := by
  have hn : 0 < v + 1 := by linarith
  have hA : (v + 1) * Real.sqrt (v + 1) ≠ 0 :=
    ne_of_gt (mul_pos hn (Real.sqrt_pos.mpr hn))
  ext u
  simp only [gaussianStep, testFunction]
  rw [show v + 1 - 1 = v by ring, mul_div_cancel_left₀ _ hA]

lemma gaussianStep_third_bound (v H u : ℝ) (hv : 1 ≤ v) :
    |iteratedDeriv 3 (gaussianStep v H) u| ≤ phi 0 / (v * Real.sqrt v) := by
  have hv0 : 0 < v := by linarith
  have hn : 0 < v + 1 := by linarith
  have hA : 0 < (v + 1) * Real.sqrt (v + 1) := mul_pos hn (Real.sqrt_pos.mpr hn)
  rw [gaussianStep_eq_test_div v H hv, iteratedDeriv_div_const, abs_div, abs_of_pos hA]
  calc
    |iteratedDeriv 3 (testFunction (v + 1) H) u| / ((v + 1) * Real.sqrt (v + 1)) ≤
        (thirdScale (v + 1) * phi 0) / ((v + 1) * Real.sqrt (v + 1)) :=
      div_le_div_of_nonneg_right (abs_thirdDeriv_le (v + 1) H u (by linarith)) hA.le
    _ = _ := by
      simp only [thirdScale]
      rw [show v + 1 - 1 = v by ring]
      field_simp [ne_of_gt hA, ne_of_gt hv0, ne_of_gt (Real.sqrt_pos.mpr hv0)]

lemma gaussianStep_second_half (v H : ℝ) (hv : 1 ≤ v) :
    iteratedDeriv 2 (gaussianStep v H) 0 / 2 = heatSlope H v := by
  have hv0 : 0 < v := by linarith
  have hn : 0 < v + 1 := by linarith
  have hA : (v + 1) * Real.sqrt (v + 1) ≠ 0 :=
    ne_of_gt (mul_pos hn (Real.sqrt_pos.mpr hn))
  rw [gaussianStep_eq_test_div v H hv, iteratedDeriv_div_const, secondDeriv_testFunction]
  simp only [curvature, argument, heatSlope, heatArgument, sub_zero]
  rw [show v + 1 - 1 = v by ring, Real.sq_sqrt hv0.le]
  field_simp [hA, ne_of_gt hv0, ne_of_gt (Real.sqrt_pos.mpr hv0)]

/-- The one-law Taylor price uses exactly its rho, and includes actual integrability. -/
theorem item_taylor_bound (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (v H : ℝ) (hv : 1 ≤ v) :
    Integrable (gaussianStep v H) (μ : Measure ℝ) ∧
      |(∫ u, gaussianStep v H u ∂(μ : Measure ℝ)) - heatCDF H v - heatSlope H v| ≤
        thirdAbsoluteMoment μ / (15 * (v * Real.sqrt v)) := by
  have hv0 : 0 < v := by linarith
  have hb : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv0
  have hr : 0 ≤ thirdAbsoluteMoment μ := (rho_ge_one μ h).trans' (by norm_num)
  have ht := standardized_taylor_bound μ h (gaussianStep v H) (contDiff_gaussianStep v H)
    (phi 0 / (v * Real.sqrt v)) (fun u => gaussianStep_third_bound v H u hv)
  refine ⟨ht.1, ?_⟩
  have hz : gaussianStep v H 0 = heatCDF H v := by simp [gaussianStep, heatCDF]
  rw [hz, gaussianStep_second_half v H hv] at ht
  calc
    |(∫ u, gaussianStep v H u ∂(μ : Measure ℝ)) - heatCDF H v - heatSlope H v| ≤
        (phi 0 / (v * Real.sqrt v)) * thirdAbsoluteMoment μ / 6 := ht.2
    _ = (thirdAbsoluteMoment μ / (6 * (v * Real.sqrt v))) * phi 0 := by
      field_simp [ne_of_gt hv0, ne_of_gt hb]
    _ ≤ (thirdAbsoluteMoment μ / (6 * (v * Real.sqrt v))) * ((2 : ℝ) / 5) :=
      mul_le_mul_of_nonneg_left phi_zero_lt_2_5.le (div_nonneg hr (by positivity))
    _ = _ := by field_simp [ne_of_gt hv0, ne_of_gt hb]; ring

/-- Separate item and variance Taylor errors give the original Gaussian entry constants. -/
theorem smoothing_error (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (v H : ℝ) (hv : 1 ≤ v) :
    (∫ u, gaussianStep v H u ∂(μ : Measure ℝ)) - heatCDF H (v + 1) ≤
      thirdAbsoluteMoment μ / (15 * (v * Real.sqrt v)) +
        2 * thirdAbsoluteMoment μ / (25 * v ^ 2) := by
  have hv0 : 0 < v := by linarith
  have hi := (abs_le.mp (item_taylor_bound μ h v H hv).2).2
  have hh := (abs_le.mp (heat_taylor_bound H v hv0)).1
  have hr := rho_ge_one μ h
  have hcost : (2 : ℝ) / (25 * v ^ 2) ≤ 2 * thirdAbsoluteMoment μ / (25 * v ^ 2) :=
    div_le_div_of_nonneg_right (by linarith) (by positivity)
  linarith

/-- Closed translated predecessor CDFs are genuinely integrable, with no atom restriction. -/
lemma integrable_translated_cdf (μ ν : ProbabilityMeasure ℝ) (H : ℝ) :
    Integrable (fun u : ℝ => (ν : Measure ℝ).real (Iic (H - u))) (μ : Measure ℝ) := by
  let S : Set (ℝ × ℝ) := {p | p.1 + p.2 ≤ H}
  have hS : MeasurableSet S := measurableSet_le (measurable_fst.add measurable_snd) measurable_const
  have hi : Integrable (S.indicator (fun _ : ℝ × ℝ => (1 : ℝ)))
      ((μ : Measure ℝ).prod (ν : Measure ℝ)) := (integrable_const 1).indicator hS
  apply hi.integral_prod_left.congr
  filter_upwards with u
  rw [← integral_indicator_one (μ := (ν : Measure ℝ)) (s := Iic (H - u)) measurableSet_Iic]
  apply integral_congr_ae
  filter_upwards with w
  by_cases hw : w ≤ H - u
  · have hsum : u + w ≤ H := by linarith
    simp [S, hw, hsum]
  · have hsum : ¬u + w ≤ H := by linarith
    simp [S, hw, hsum]

/-- Law-level one-item replacement for a genuine convolution of probability measures.
The predecessor hypothesis is the positive closed-CDF upper comparison at every threshold. -/
theorem one_item_gaussian_entry (μ ν : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (v H Cprev : ℝ) (hv : 1 ≤ v)
    (hprev : ∀ y : ℝ, (ν : Measure ℝ).real (Iic y) ≤
      Phi (y / Real.sqrt v) + Cprev * thirdAbsoluteMoment μ / Real.sqrt v) :
    ((μ : Measure ℝ) ∗ (ν : Measure ℝ)).real (Iic H) - Phi (H / Real.sqrt (v + 1)) ≤
      Cprev * thirdAbsoluteMoment μ / Real.sqrt v +
      thirdAbsoluteMoment μ / (15 * (v * Real.sqrt v)) +
      2 * thirdAbsoluteMoment μ / (25 * v ^ 2) := by
  let cost := Cprev * thirdAbsoluteMoment μ / Real.sqrt v
  have hs := (item_taylor_bound μ h v H hv).1
  have hCDF : ((μ : Measure ℝ) ∗ (ν : Measure ℝ)).real (Iic H) ≤
      (∫ u, gaussianStep v H u ∂(μ : Measure ℝ)) + cost := by
    rw [cdf_conv]
    calc
      (∫ u, (ν : Measure ℝ).real (Iic (H - u)) ∂(μ : Measure ℝ)) ≤
          ∫ u, gaussianStep v H u + cost ∂(μ : Measure ℝ) := by
        apply integral_mono (integrable_translated_cdf μ ν H) (hs.add (integrable_const cost))
        intro u
        exact hprev (H - u)
      _ = _ := by
        rw [integral_add hs (integrable_const cost)]
        simp only [integral_const, probReal_univ, one_smul]
  have he := smoothing_error μ h v H hv
  dsimp only [heatCDF] at he
  dsimp only [cost] at hCDF
  linarith

/-- The same law-level entry at the actual index, with v=n-1 retained explicitly. -/
theorem gaussian_entry (μ ν : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n H Cprev : ℝ) (hn : 2 ≤ n)
    (hprev : ∀ y : ℝ, (ν : Measure ℝ).real (Iic y) ≤
      Phi (y / Real.sqrt (n - 1)) + Cprev * thirdAbsoluteMoment μ / Real.sqrt (n - 1)) :
    ((μ : Measure ℝ) ∗ (ν : Measure ℝ)).real (Iic H) - Phi (H / Real.sqrt n) ≤
      Cprev * thirdAbsoluteMoment μ / Real.sqrt (n - 1) +
      thirdAbsoluteMoment μ / (15 * ((n - 1) * Real.sqrt (n - 1))) +
      2 * thirdAbsoluteMoment μ / (25 * (n - 1) ^ 2) := by
  have hentry := one_item_gaussian_entry μ ν h (n - 1) H Cprev (by linarith) hprev
  simpa only [sub_add_cancel] using hentry

end BerryEsseen.GaussianEntry

#print axioms BerryEsseen.GaussianEntry.item_taylor_bound
#print axioms BerryEsseen.GaussianEntry.smoothing_error
#print axioms BerryEsseen.GaussianEntry.integrable_translated_cdf
#print axioms BerryEsseen.GaussianEntry.gaussian_entry
