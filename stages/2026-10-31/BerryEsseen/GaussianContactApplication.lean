module

public import BerryEsseen.GaussianPeanoRepresentation
public import BerryEsseen.GaussianPrices
public import Mathlib.MeasureTheory.Group.IntegralConvolution

@[expose] public section

/-! 2026-10-28: the real Gaussian Hermite contact application. All expectations
are against Target's standard Gaussian and all CDF values use the frozen Phi. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology MeasureTheory
open BerryEsseen.GaussianTools BerryEsseen.GaussianMills BerryEsseen.GaussianPrices
open BerryEsseen.GaussianPeano BerryEsseen.GaussianPeanoRepresentation

namespace BerryEsseen.GaussianContactApplication

def squareVariance (b : ℝ) : NNReal := ⟨b ^ 2, sq_nonneg b⟩

lemma gaussian_cdf_scale (b H : ℝ) (hb : 0 < b) :
    (gaussianReal 0 (squareVariance b)).real (Iic H) = Phi (H / b) := by
  have hmap : standardGaussian.map (fun u : ℝ => b * u) = gaussianReal 0 (squareVariance b) := by
    have h := gaussianReal_map_const_mul (μ := 0) (v := 1) b
    have hv : (NNReal.mk (b ^ 2) (sq_nonneg b) * 1 : NNReal) = squareVariance b := by
      apply NNReal.coe_injective
      simp [squareVariance]
      rfl
    rw [mul_zero, hv] at h
    exact h
  have hpre : (fun u : ℝ => b * u) ⁻¹' Iic H = Iic (H / b) := by
    ext u
    simp only [Set.mem_preimage, Set.mem_Iic]
    constructor
    · intro h
      exact (le_div_iff₀ hb).mpr (by simpa only [mul_comm] using h)
    · intro h
      simpa only [mul_comm] using (le_div_iff₀ hb).mp h
  change ((gaussianReal 0 (squareVariance b)) (Iic H)).toReal =
    (standardGaussian (Iic (H / b))).toReal
  rw [← hmap, Measure.map_apply (by fun_prop) measurableSet_Iic, hpre]

/-- The closed CDF of an actual convolution is the integral of the translated closed CDF. -/
lemma cdf_conv (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (H : ℝ) :
    (μ ∗ ν).real (Iic H) = ∫ u, ν.real (Iic (H - u)) ∂μ := by
  let f : ℝ → ℝ := (Iic H).indicator (fun _ => (1 : ℝ))
  have hi : Integrable f (μ ∗ ν) := (integrable_const 1).indicator measurableSet_Iic
  have h := integral_conv hi
  calc
    (μ ∗ ν).real (Iic H) = ∫ u, ∫ v, f (u + v) ∂ν ∂μ := by
      rw [← integral_indicator_one measurableSet_Iic]
      exact h
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with u
      rw [← integral_indicator_one (μ := ν) (s := Iic (H - u)) measurableSet_Iic]
      apply integral_congr_ae
      filter_upwards with v
      by_cases hv : v ≤ H - u
      · have hsum : u + v ≤ H := by linarith
        simp [f, hv, hsum]
      · have hsum : ¬u + v ≤ H := by linarith
        simp [f, hv, hsum]

/-- The actual Gaussian convolution CDF identity, for every real n>=2 and every H. -/
theorem expectation_Phi_affine (n H : ℝ) (hn : 2 ≤ n) :
    expectation (fun u : ℝ => Phi ((H - u) / Real.sqrt (n - 1))) = Phi (H / Real.sqrt n) := by
  have hd : 0 < n - 1 := by linarith
  have hn0 : 0 < n := by linarith
  have hb : 0 < Real.sqrt (n - 1) := Real.sqrt_pos.mpr hd
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  let v : NNReal := ⟨n - 1, hd.le⟩
  have hbvar : squareVariance (Real.sqrt (n - 1)) = v := by
    apply NNReal.coe_injective
    change Real.sqrt (n - 1) ^ 2 = n - 1
    exact Real.sq_sqrt hd.le
  have hconv : standardGaussian ∗ gaussianReal 0 v = gaussianReal 0 (squareVariance (Real.sqrt n)) := by
    rw [standardGaussian, gaussianReal_conv_gaussianReal, zero_add]
    congr 1
    apply NNReal.coe_injective
    change 1 + (n - 1) = Real.sqrt n ^ 2
    rw [Real.sq_sqrt hn0.le]
    ring
  calc
    expectation (fun u : ℝ => Phi ((H - u) / Real.sqrt (n - 1))) =
        ∫ u, (gaussianReal 0 v).real (Iic (H - u)) ∂standardGaussian := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun u => by
        dsimp only
        rw [← hbvar, gaussian_cdf_scale _ _ hb]
    _ = (standardGaussian ∗ gaussianReal 0 v).real (Iic H) := (cdf_conv _ _ H).symm
    _ = Phi (H / Real.sqrt n) := by rw [hconv, gaussian_cdf_scale _ _ hs]

/-- The Gaussian test function; n*sqrt n is the real version of n^(3/2). -/
def testFunction (n H u : ℝ) : ℝ := n * Real.sqrt n * Phi ((H - u) / Real.sqrt (n - 1))

theorem expectation_testFunction (n H : ℝ) (hn : 2 ≤ n) :
    expectation (testFunction n H) = n * Real.sqrt n * Phi (H / Real.sqrt n) := by
  change (∫ u, (n * Real.sqrt n) * Phi ((H - u) / Real.sqrt (n - 1)) ∂standardGaussian) = _
  rw [integral_const_mul]
  change n * Real.sqrt n * expectation (fun u : ℝ => Phi ((H - u) / Real.sqrt (n - 1))) = _
  rw [expectation_Phi_affine n H hn]

end BerryEsseen.GaussianContactApplication

#print axioms BerryEsseen.GaussianContactApplication.expectation_Phi_affine
#print axioms BerryEsseen.GaussianContactApplication.expectation_testFunction

namespace BerryEsseen.GaussianContactApplication

def argument (n H u : ℝ) : ℝ := (H - u) / Real.sqrt (n - 1)
def slope (n H u : ℝ) : ℝ :=
  -(n * Real.sqrt n / Real.sqrt (n - 1)) * phi (argument n H u)
def curvature (n H u : ℝ) : ℝ :=
  -(n * Real.sqrt n / Real.sqrt (n - 1) ^ 2) * (argument n H u * phi (argument n H u))
def thirdDerivative (n H u : ℝ) : ℝ :=
  (n * Real.sqrt n / Real.sqrt (n - 1) ^ 3) * ((1 - argument n H u ^ 2) * phi (argument n H u))
def thirdScale (n : ℝ) : ℝ := n * Real.sqrt n / ((n - 1) * Real.sqrt (n - 1))

lemma hasDerivAt_argument (n H u : ℝ) :
    HasDerivAt (argument n H) (-1 / Real.sqrt (n - 1)) u := by
  change HasDerivAt (fun v : ℝ => (H - v) / Real.sqrt (n - 1)) _ u
  convert ((hasDerivAt_const u H).fun_sub (hasDerivAt_id' u)).div_const (Real.sqrt (n - 1)) using 1
  ring

lemma hasDerivAt_testFunction (n H u : ℝ) : HasDerivAt (testFunction n H) (slope n H u) u := by
  have h := ((hasDerivAt_Phi (argument n H u)).comp u (hasDerivAt_argument n H u)).const_mul (n * Real.sqrt n)
  convert h using 1
  · rfl
  · simp only [slope]
    ring

lemma deriv_testFunction (n H : ℝ) : deriv (testFunction n H) = slope n H :=
  funext (fun u => (hasDerivAt_testFunction n H u).deriv)

lemma hasDerivAt_slope (n H u : ℝ) : HasDerivAt (slope n H) (curvature n H u) u := by
  have h := ((hasDerivAt_phi (argument n H u)).comp u (hasDerivAt_argument n H u)).const_mul
    (-(n * Real.sqrt n / Real.sqrt (n - 1)))
  convert h using 1
  · rfl
  · simp only [curvature, div_eq_mul_inv]
    ring

lemma deriv_slope (n H : ℝ) : deriv (slope n H) = curvature n H :=
  funext (fun u => (hasDerivAt_slope n H u).deriv)

lemma hasDerivAt_curvature (n H u : ℝ) : HasDerivAt (curvature n H) (thirdDerivative n H u) u := by
  have h := ((hasDerivAt_argument n H u).fun_mul
    ((hasDerivAt_phi (argument n H u)).comp u (hasDerivAt_argument n H u))).const_mul
      (-(n * Real.sqrt n / Real.sqrt (n - 1) ^ 2))
  convert h using 1
  · rfl
  · simp only [thirdDerivative, Function.comp_apply, div_eq_mul_inv]
    ring

lemma secondDeriv_testFunction (n H : ℝ) : iteratedDeriv 2 (testFunction n H) = curvature n H := by
  rw [show (2 : ℕ) = 1 + 1 by rfl, iteratedDeriv_succ, iteratedDeriv_one, deriv_testFunction]
  exact deriv_slope n H

lemma thirdDeriv_testFunction (n H : ℝ) : iteratedDeriv 3 (testFunction n H) = thirdDerivative n H := by
  rw [show (3 : ℕ) = 2 + 1 by rfl, iteratedDeriv_succ, secondDeriv_testFunction]
  exact funext (fun u => (hasDerivAt_curvature n H u).deriv)

lemma contDiff_phi (k : ℕ) : ContDiff ℝ k phi := by
  change ContDiff ℝ k (gaussianPDFReal 0 1)
  unfold gaussianPDFReal
  fun_prop

lemma contDiff_Phi_three : ContDiff ℝ 3 Phi := by
  apply (contDiff_succ_iff_deriv (n := 2)).mpr
  refine ⟨fun u => (hasDerivAt_Phi u).differentiableAt, by simp, ?_⟩
  have hd : deriv Phi = phi := funext deriv_Phi
  rw [hd]
  exact contDiff_phi 2

/-- The Gaussian CDF test function has exactly the C3 regularity required by Peano. -/
theorem contDiff_testFunction (n H : ℝ) : ContDiff ℝ 3 (testFunction n H) := by
  have ha : ContDiff ℝ 3 (argument n H) := by unfold argument; fun_prop
  change ContDiff ℝ 3 (fun u : ℝ => (n * Real.sqrt n) * Phi (argument n H u))
  exact contDiff_const.mul (contDiff_Phi_three.comp ha)

/-- The Hermite factor is bounded on the entire real line, not on a support restriction. -/
theorem hermite_factor_bound (r : ℝ) : |(1 - r ^ 2) * phi r| ≤ phi 0 := by
  have hu : 0 ≤ r ^ 2 / 2 := div_nonneg (sq_nonneg r) (by norm_num)
  have hlow := Real.quadratic_le_exp_of_nonneg hu
  have hone : 1 ≤ Real.exp (r ^ 2 / 2) := Real.one_le_exp_iff.mpr hu
  have habs : |1 - r ^ 2| ≤ Real.exp (r ^ 2 / 2) := by
    apply abs_le.mpr
    constructor
    · nlinarith [sq_nonneg (r ^ 2 / 2 - 1)]
    · nlinarith [sq_nonneg r]
  rw [abs_mul, abs_of_nonneg (phi_nonneg r), phi_eq_phi_zero_div_exp r]
  calc
    |1 - r ^ 2| * (phi 0 / Real.exp (r ^ 2 / 2)) ≤
        Real.exp (r ^ 2 / 2) * (phi 0 / Real.exp (r ^ 2 / 2)) :=
      mul_le_mul_of_nonneg_right habs (div_nonneg (phi_nonneg 0) (Real.exp_pos _).le)
    _ = phi 0 := by rw [← mul_div_assoc, mul_div_cancel_left₀ _ (Real.exp_ne_zero _)]

lemma thirdScale_pos (n : ℝ) (hn : 2 ≤ n) : 0 < thirdScale n := by
  have hn0 : 0 < n := by linarith
  have hd : 0 < n - 1 := by linarith
  exact div_pos (mul_pos hn0 (Real.sqrt_pos.mpr hn0)) (mul_pos hd (Real.sqrt_pos.mpr hd))

lemma thirdScale_sq (n : ℝ) (hn : 2 ≤ n) : thirdScale n ^ 2 = (n / (n - 1)) ^ 3 := by
  have hn0 : 0 ≤ n := by linarith
  have hd : 0 < n - 1 := by linarith
  simp only [thirdScale, div_pow, mul_pow, Real.sq_sqrt hn0, Real.sq_sqrt hd.le]
  field_simp [ne_of_gt hd]

lemma thirdScale_lt_213_200 (n : ℝ) (hn : 25 ≤ n) : thirdScale n < (213 : ℝ) / 200 := by
  have hn2 : 2 ≤ n := by linarith
  have hd : 0 < n - 1 := by linarith
  have hratio : n / (n - 1) ≤ (25 : ℝ) / 24 := by
    apply (div_le_iff₀ hd).mpr
    nlinarith
  have hpow := pow_le_pow_left₀ (div_nonneg (show 0 ≤ n by linarith) hd.le) hratio 3
  have hs : thirdScale n ^ 2 < ((213 : ℝ) / 200) ^ 2 := by
    rw [thirdScale_sq n hn2]
    exact hpow.trans_lt (by norm_num)
  exact (sq_lt_sq₀ (thirdScale_pos n hn2).le (by norm_num)).mp hs

/-- The native third derivative is the manuscript's exact scaled Hermite factor. -/
theorem thirdDeriv_formula (n H u : ℝ) (hn : 2 ≤ n) :
    iteratedDeriv 3 (testFunction n H) u =
      thirdScale n * ((1 - argument n H u ^ 2) * phi (argument n H u)) := by
  have hd : 0 ≤ n - 1 := by linarith
  have hb3 : Real.sqrt (n - 1) ^ 3 = (n - 1) * Real.sqrt (n - 1) := by
    calc
      Real.sqrt (n - 1) ^ 3 = Real.sqrt (n - 1) ^ 2 * Real.sqrt (n - 1) := by ring
      _ = _ := by rw [Real.sq_sqrt hd]
  rw [thirdDeriv_testFunction]
  simp only [thirdDerivative, thirdScale, hb3]

lemma abs_thirdDeriv_le (n H u : ℝ) (hn : 2 ≤ n) :
    |iteratedDeriv 3 (testFunction n H) u| ≤ thirdScale n * phi 0 := by
  rw [thirdDeriv_formula n H u hn, abs_mul, abs_of_pos (thirdScale_pos n hn)]
  exact mul_le_mul_of_nonneg_left (hermite_factor_bound _) (thirdScale_pos n hn).le

/-- A strict rational derivative price valid for every H and n>=25. -/
theorem abs_thirdDeriv_lt_213_500 (n H u : ℝ) (hn : 25 ≤ n) :
    |iteratedDeriv 3 (testFunction n H) u| < (213 : ℝ) / 500 := by
  have hn2 : 2 ≤ n := by linarith
  calc
    |iteratedDeriv 3 (testFunction n H) u| ≤ thirdScale n * phi 0 := abs_thirdDeriv_le n H u hn2
    _ < thirdScale n * ((2 : ℝ) / 5) :=
      mul_lt_mul_of_pos_left phi_zero_lt_2_5 (thirdScale_pos n hn2)
    _ ≤ ((213 : ℝ) / 200) * ((2 : ℝ) / 5) :=
      mul_le_mul_of_nonneg_right (thirdScale_lt_213_200 n hn).le (by norm_num)
    _ = (213 : ℝ) / 500 := by norm_num

end BerryEsseen.GaussianContactApplication

#print axioms BerryEsseen.GaussianContactApplication.contDiff_testFunction
#print axioms BerryEsseen.GaussianContactApplication.thirdDeriv_formula
#print axioms BerryEsseen.GaussianContactApplication.hermite_factor_bound
#print axioms BerryEsseen.GaussianContactApplication.abs_thirdDeriv_lt_213_500

namespace BerryEsseen.GaussianContactApplication

lemma integral_mul_phi_zero : (∫ u : ℝ, u * phi u) = 0 := by
  have h := expectation_id
  rw [expectation_eq_density] at h
  simpa only [mul_comm] using h

lemma integrable_scaled_phi (a : ℝ) (ha : 0 < a) : Integrable (fun u : ℝ => phi (a * u)) :=
  integrable_phi.comp_mul_left' (ne_of_gt ha)

lemma integrable_scaled_mul_phi (a : ℝ) (ha : 0 < a) :
    Integrable (fun u : ℝ => u * phi (a * u)) := by
  convert (integrable_mul_phi.comp_mul_left' (ne_of_gt ha)).div_const a using 1
  ext u
  field_simp [ne_of_gt ha]

lemma integrable_phi_affine (a m : ℝ) (ha : 0 < a) :
    Integrable (fun u : ℝ => phi (a * (u - m))) :=
  (integrable_scaled_phi a ha).comp_sub_right m

lemma integrable_mul_phi_affine (a m : ℝ) (ha : 0 < a) :
    Integrable (fun u : ℝ => u * phi (a * (u - m))) := by
  have hc : Integrable (fun u : ℝ => (u + m) * phi (a * u)) := by
    convert (integrable_scaled_mul_phi a ha).add ((integrable_scaled_phi a ha).const_mul m) using 1
    ext u
    simp only [Pi.add_apply]
    ring
  simpa only [sub_add_cancel] using hc.comp_sub_right m

lemma integral_phi_affine (a m : ℝ) (ha : 0 < a) :
    (∫ u : ℝ, phi (a * (u - m))) = 1 / a := by
  rw [integral_sub_right_eq_self (fun u : ℝ => phi (a * u)) m,
    Measure.integral_comp_mul_left phi a, integral_phi]
  simp only [smul_eq_mul, mul_one, abs_of_pos (inv_pos.mpr ha), one_div]

lemma integral_scaled_mul_phi_zero (a : ℝ) (ha : 0 < a) :
    (∫ u : ℝ, u * phi (a * u)) = 0 := by
  have h := Measure.integral_comp_mul_left (fun u : ℝ => u * phi u) a
  rw [integral_mul_phi_zero, smul_zero] at h
  change (∫ u : ℝ, (a * u) * phi (a * u)) = 0 at h
  have heq : (fun u : ℝ => (a * u) * phi (a * u)) = (fun u : ℝ => a * (u * phi (a * u))) := by
    ext u
    ring
  rw [heq, integral_const_mul] at h
  exact (mul_eq_zero.mp h).resolve_left (ne_of_gt ha)

lemma integral_mul_phi_affine (a m : ℝ) (ha : 0 < a) :
    (∫ u : ℝ, u * phi (a * (u - m))) = m / a := by
  have hshift := integral_sub_right_eq_self (μ := volume) (fun u : ℝ => (u + m) * phi (a * u)) m
  have hzero : (∫ u : ℝ, phi (a * u)) = 1 / a := by
    simpa only [sub_zero] using integral_phi_affine a 0 ha
  have heq : (fun u : ℝ => (u + m) * phi (a * u)) =
      (fun u : ℝ => u * phi (a * u) + m * phi (a * u)) := by ext u; ring
  calc
    (∫ u : ℝ, u * phi (a * (u - m))) = ∫ u : ℝ, (u + m) * phi (a * u) := by
      simpa only [sub_add_cancel] using hshift
    _ = _ := by
      rw [heq, integral_add (integrable_scaled_mul_phi a ha) ((integrable_scaled_phi a ha).const_mul m),
        integral_const_mul, integral_scaled_mul_phi_zero a ha, hzero]
      ring

/-- The product of two actual standard Gaussian densities is completed to a translated scaled density. -/
lemma density_product (n H u : ℝ) (hn : 2 ≤ n) :
    phi u * phi (argument n H u) = phi (H / Real.sqrt n) *
      phi ((Real.sqrt n / Real.sqrt (n - 1)) * (u - H / n)) := by
  have hn0 : 0 < n := by linarith
  have hd : 0 < n - 1 := by linarith
  have hq : u ^ 2 + argument n H u ^ 2 = (H / Real.sqrt n) ^ 2 +
      ((Real.sqrt n / Real.sqrt (n - 1)) * (u - H / n)) ^ 2 := by
    simp only [argument, div_pow, mul_pow, Real.sq_sqrt hn0.le, Real.sq_sqrt hd.le]
    field_simp [ne_of_gt hn0, ne_of_gt hd]
    ring
  have he : Real.exp (-(u ^ 2) / 2) * Real.exp (-(argument n H u ^ 2) / 2) =
      Real.exp (-((H / Real.sqrt n) ^ 2) / 2) *
        Real.exp (-(((Real.sqrt n / Real.sqrt (n - 1)) * (u - H / n)) ^ 2) / 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    nlinarith [hq]
  let k := (Real.sqrt (2 * Real.pi))⁻¹
  calc
    phi u * phi (argument n H u) = k ^ 2 *
        (Real.exp (-(u ^ 2) / 2) * Real.exp (-(argument n H u ^ 2) / 2)) := by
      rw [phi_formula, phi_formula]
      dsimp [k]
      ring
    _ = k ^ 2 * (Real.exp (-((H / Real.sqrt n) ^ 2) / 2) *
        Real.exp (-(((Real.sqrt n / Real.sqrt (n - 1)) * (u - H / n)) ^ 2) / 2)) := by rw [he]
    _ = _ := by
      rw [phi_formula, phi_formula]
      dsimp [k]
      ring

lemma expectation_phi_argument (n H : ℝ) (hn : 2 ≤ n) :
    expectation (fun u : ℝ => phi (argument n H u)) =
      (Real.sqrt (n - 1) / Real.sqrt n) * phi (H / Real.sqrt n) := by
  have hn0 : 0 < n := by linarith
  have hd : 0 < n - 1 := by linarith
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hb : 0 < Real.sqrt (n - 1) := Real.sqrt_pos.mpr hd
  have ha : 0 < Real.sqrt n / Real.sqrt (n - 1) := div_pos hs hb
  rw [expectation_eq_density]
  have heq : (fun u : ℝ => phi u * phi (argument n H u)) =
      (fun u : ℝ => phi (H / Real.sqrt n) *
        phi ((Real.sqrt n / Real.sqrt (n - 1)) * (u - H / n))) :=
    funext (fun u => density_product n H u hn)
  rw [heq, integral_const_mul, integral_phi_affine _ _ ha]
  field_simp [ne_of_gt hs, ne_of_gt hb]

lemma expectation_argument_phi_argument (n H : ℝ) (hn : 2 ≤ n) :
    expectation (fun u : ℝ => argument n H u * phi (argument n H u)) =
      (H * (n - 1) / (n * Real.sqrt n)) * phi (H / Real.sqrt n) := by
  have hn0 : 0 < n := by linarith
  have hd : 0 < n - 1 := by linarith
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hb : 0 < Real.sqrt (n - 1) := Real.sqrt_pos.mpr hd
  have ha : 0 < Real.sqrt n / Real.sqrt (n - 1) := div_pos hs hb
  let a := Real.sqrt n / Real.sqrt (n - 1)
  let m := H / n
  have hwa := integrable_phi_affine a m ha
  have hwm := integrable_mul_phi_affine a m ha
  have heq : (fun u : ℝ => phi u * (argument n H u * phi (argument n H u))) =
      (fun u : ℝ => phi (H / Real.sqrt n) * ((H - u) / Real.sqrt (n - 1) * phi (a * (u - m)))) := by
    ext u
    calc
      phi u * (argument n H u * phi (argument n H u)) =
          argument n H u * (phi u * phi (argument n H u)) := by ring
      _ = argument n H u * (phi (H / Real.sqrt n) * phi (a * (u - m))) := by
        rw [density_product n H u hn]
      _ = _ := by dsimp [argument]; ring
  rw [expectation_eq_density, heq, integral_const_mul]
  have hlin : (fun u : ℝ => (H - u) / Real.sqrt (n - 1) * phi (a * (u - m))) =
      (fun u : ℝ => (H / Real.sqrt (n - 1)) * phi (a * (u - m)) -
        (1 / Real.sqrt (n - 1)) * (u * phi (a * (u - m)))) := by ext u; ring
  rw [hlin, integral_sub (hwa.const_mul _) (hwm.const_mul _), integral_const_mul, integral_const_mul,
    integral_phi_affine a m ha, integral_mul_phi_affine a m ha]
  dsimp [a, m]
  field_simp [ne_of_gt hs, ne_of_gt hb, ne_of_gt hn0]

/-- First native derivative expectation, evaluated under the actual standard Gaussian. -/
theorem expectation_deriv_testFunction (n H : ℝ) (hn : 2 ≤ n) :
    expectation (deriv (testFunction n H)) = -n * phi (H / Real.sqrt n) := by
  have hn0 : 0 < n := by linarith
  have hd : 0 < n - 1 := by linarith
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hb : 0 < Real.sqrt (n - 1) := Real.sqrt_pos.mpr hd
  rw [deriv_testFunction]
  change (∫ u, -(n * Real.sqrt n / Real.sqrt (n - 1)) * phi (argument n H u) ∂standardGaussian) = _
  rw [integral_const_mul]
  change -(n * Real.sqrt n / Real.sqrt (n - 1)) * expectation (fun u : ℝ => phi (argument n H u)) = _
  rw [expectation_phi_argument n H hn]
  field_simp [ne_of_gt hs, ne_of_gt hb]

/-- Second native derivative expectation, with no restriction on H. -/
theorem expectation_secondDeriv_testFunction (n H : ℝ) (hn : 2 ≤ n) :
    expectation (iteratedDeriv 2 (testFunction n H)) = -H * phi (H / Real.sqrt n) := by
  have hn0 : 0 < n := by linarith
  have hd : 0 < n - 1 := by linarith
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hb : 0 < Real.sqrt (n - 1) := Real.sqrt_pos.mpr hd
  rw [secondDeriv_testFunction]
  change (∫ u, -(n * Real.sqrt n / Real.sqrt (n - 1) ^ 2) *
    (argument n H u * phi (argument n H u)) ∂standardGaussian) = _
  rw [integral_const_mul]
  change -(n * Real.sqrt n / Real.sqrt (n - 1) ^ 2) *
    expectation (fun u : ℝ => argument n H u * phi (argument n H u)) = _
  rw [expectation_argument_phi_argument n H hn, Real.sq_sqrt hd.le]
  field_simp [ne_of_gt hs, ne_of_gt hd, ne_of_gt hn0]

/-- All three real Gaussian expectations in the projected contact functional are finite. -/
theorem integrable_testFunction_jets (n H : ℝ) (hn : 2 ≤ n) :
    Integrable (testFunction n H) standardGaussian ∧
    Integrable (deriv (testFunction n H)) standardGaussian ∧
    Integrable (iteratedDeriv 2 (testFunction n H)) standardGaussian :=
  gaussian_integrable_of_bounded_third (testFunction n H) (contDiff_testFunction n H)
    (thirdScale n * phi 0) (fun u => abs_thirdDeriv_le n H u hn)

/-- The exact Gaussian Hermite contact term from the manuscript. -/
def hermiteProjection (n H x : ℝ) : ℝ :=
  n * Real.sqrt n * (Phi ((H - x) / Real.sqrt (n - 1)) - Phi (H / Real.sqrt n)) +
    n * x * phi (H / Real.sqrt n) + H / 2 * (x ^ 2 - 1) * phi (H / Real.sqrt n)

theorem contact_testFunction_eq_hermiteProjection (n H x : ℝ) (hn : 2 ≤ n) :
    contact x (testFunction n H) = hermiteProjection n H x := by
  rw [contact, expectation_testFunction n H hn, expectation_deriv_testFunction n H hn,
    expectation_secondDeriv_testFunction n H hn]
  simp only [testFunction, hermiteProjection]
  ring

end BerryEsseen.GaussianContactApplication

#print axioms BerryEsseen.GaussianContactApplication.expectation_deriv_testFunction
#print axioms BerryEsseen.GaussianContactApplication.expectation_secondDeriv_testFunction
#print axioms BerryEsseen.GaussianContactApplication.integrable_testFunction_jets
#print axioms BerryEsseen.GaussianContactApplication.contact_testFunction_eq_hermiteProjection
