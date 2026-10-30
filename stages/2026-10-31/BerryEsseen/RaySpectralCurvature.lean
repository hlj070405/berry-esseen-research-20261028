module

public import BerryEsseen.CoarseHighMomentRayPrice
public import BerryEsseen.PowerExponentialEndpoint
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

@[expose] public section

/-! 2026-10-29: fixed spectral coordinates for the actual coarse high-moment
price.  The change of variables is s = beta^(-2), v = beta*t.

The minimum of the cubic damping exponents depends only on v.  The loss in
these coordinates is d(s) = min(rho0^(-2), s/N).  On each side of its single
switch, the positive integrand is a sum of kernels s^r exp(-s*R), with
r = 1/2, 3/2, or 5/2.  The exact kernel curvature is bounded below by
-r/s^2 times the kernel.  No numerical endpoint certificate or all-beta
Berry--Esseen constant is asserted in this module.

Analytic endpoint check: K(v/V) = O(1/v) at zero, whereas the inner coarse
forcing is O(w^2).  Thus the integrated first-term integrand is O(v^2).
The principal correction K(v/V)-iV/(2*pi*v) is bounded by 1/2 in 0<v<=V.  On every
compact s interval inside (0,infinity), the first two parameter derivatives
retain those local bounds.  In the unbounded fourth term, they are bounded
by a polynomial in v times exp(-a*v^2/2), with a>0.  These facts justify
differentiation under the four integrals in ordinary analysis.  The final
formal profile bound instead integrates a common pointwise logarithmic
endpoint inequality, and therefore requires no under-integral derivative. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Interval Topology

namespace BerryEsseen.RaySpectralCurvature

open HighMomentRayDamping

/-- Logarithmic representation avoids any convention for real powers at zero.
For positive s this is exactly s^r exp(-s*R). -/
def powerExp (r R s : ℝ) : ℝ := Real.exp (r * Real.log s - s * R)

lemma powerExp_eq_rpow (r R s : ℝ) (hs : 0 < s) :
    powerExp r R s = s ^ r * Real.exp (-s * R) := by
  rw [powerExp, sub_eq_add_neg, Real.exp_add, Real.rpow_def_of_pos hs]
  rw [mul_comm r (Real.log s), neg_mul]

lemma powerExp_pos (r R s : ℝ) : 0 < powerExp r R s := Real.exp_pos _

lemma hasDerivAt_powerExp (r R s : ℝ) (hs : s ≠ 0) :
    HasDerivAt (powerExp r R) (powerExp r R s * (r / s - R)) s := by
  unfold powerExp
  simpa only [Pi.sub_apply, id_eq, div_eq_mul_inv, one_mul] using
    (((Real.hasDerivAt_log hs).const_mul r).sub
      ((hasDerivAt_id s).mul_const R)).exp

lemma hasDerivAt_powerExp_slope (r R s : ℝ) (hs : s ≠ 0) :
    HasDerivAt (fun x => powerExp r R x * (r / x - R))
      (powerExp r R s * ((r / s - R) ^ 2 - r / s ^ 2)) s := by
  have hq : HasDerivAt (fun x : ℝ => r / x - R) (-r / s ^ 2) s := by
    convert (((hasDerivAt_const s r).div (hasDerivAt_id s) hs).sub_const R) using 1 <;>
      simp
  convert (hasDerivAt_powerExp r R s hs).mul hq using 1
  ring

theorem deriv_deriv_powerExp (r R s : ℝ) (hs : 0 < s) :
    deriv (deriv (powerExp r R)) s =
      powerExp r R s * ((r / s - R) ^ 2 - r / s ^ 2) := by
  have heq : deriv (powerExp r R) =ᶠ[𝓝 s]
      (fun x => powerExp r R x * (r / x - R)) := by
    filter_upwards [eventually_ne_nhds hs.ne'] with x hx
    exact (hasDerivAt_powerExp r R x hx).deriv
  rw [heq.deriv_eq]
  exact (hasDerivAt_powerExp_slope r R s hs.ne').deriv

/-- The curvature estimate does not require R to be nonnegative. -/
theorem powerExp_curvature (r R s : ℝ) (hs : 0 < s) :
    -(r / s ^ 2) * powerExp r R s ≤ deriv (deriv (powerExp r R)) s := by
  rw [deriv_deriv_powerExp r R s hs]
  have h := mul_nonneg (powerExp_pos r R s).le (sq_nonneg (r / s - R))
  nlinarith only [h]

theorem weighted_powerExp_curvature (c r R s : ℝ) (hc : 0 ≤ c) (hs : 0 < s) :
    -(r / s ^ 2) * (c * powerExp r R s) ≤
      c * (powerExp r R s * ((r / s - R) ^ 2 - r / s ^ 2)) := by
  have h := mul_le_mul_of_nonneg_left (powerExp_curvature r R s hs) hc
  rw [deriv_deriv_powerExp r R s hs] at h
  nlinarith only [h]

theorem weighted_powerExp_curvature_of_le (c r rmax R s : ℝ)
    (hc : 0 ≤ c) (hs : 0 < s) (hr : r ≤ rmax) :
    -(rmax / s ^ 2) * (c * powerExp r R s) ≤
      c * (powerExp r R s * ((r / s - R) ^ 2 - r / s ^ 2)) := by
  have hdiv := div_le_div_of_nonneg_right hr (sq_nonneg s)
  have hmul := mul_le_mul_of_nonneg_right (neg_le_neg hdiv)
    (mul_nonneg hc (powerExp_pos r R s).le)
  exact hmul.trans (weighted_powerExp_curvature c r R s hc hs)

/-- Curvature can be integrated against any positive weights once both
integrands are integrable.  This is an inequality between the two integrals;
identifying the right integral with an actual profile's second derivative
still requires dominated differentiation. -/
theorem integral_powerExp_curvature {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (c r R : α → ℝ) (rmax s : ℝ) (hs : 0 < s)
    (hc : ∀ᵐ x ∂μ, 0 ≤ c x) (hr : ∀ᵐ x ∂μ, r x ≤ rmax)
    (h0 : Integrable (fun x => c x * powerExp (r x) (R x) s) μ)
    (h2 : Integrable (fun x => c x * (powerExp (r x) (R x) s *
      ((r x / s - R x) ^ 2 - r x / s ^ 2))) μ) :
    -(rmax / s ^ 2) * (∫ x, c x * powerExp (r x) (R x) s ∂μ) ≤
      ∫ x, c x * (powerExp (r x) (R x) s *
        ((r x / s - R x) ^ 2 - r x / s ^ 2)) ∂μ := by
  have hh : ∀ᵐ x ∂μ,
      -(rmax / s ^ 2) * (c x * powerExp (r x) (R x) s) ≤
        c x * (powerExp (r x) (R x) s *
          ((r x / s - R x) ^ 2 - r x / s ^ 2)) := by
    filter_upwards [hc, hr] with x hcx hrx
    exact weighted_powerExp_curvature_of_le (c x) (r x) rmax (R x) s hcx hs hrx
  have hi := integral_mono_ae (h0.const_mul (-(rmax / s ^ 2))) h2 hh
  simpa only [integral_const_mul] using hi

/-- The minimum is taken before multiplication by s; its switch locations
in v consequently do not move with beta. -/
def spectralExponent (v : ℝ) : ℝ :=
  min 0 (min (exponent (1 / 2) (1 / 10) 1 v)
    (min (exponent ClassicalCosineCubic.a ClassicalCosineCubic.b 1 v)
      (exponent ClassicalRationalCosine.a ClassicalRationalCosine.b 1 v)))

def spectralLoss (N : ℕ) (s : ℝ) : ℝ := min (1 / rho0 ^ 2) (s / (N : ℝ))

lemma spectralExponent_nonpos (v : ℝ) : spectralExponent v ≤ 0 := min_le_left _ _

lemma continuous_spectralExponent : Continuous spectralExponent := by
  unfold spectralExponent exponent
  fun_prop

private lemma exp_min (x y : ℝ) : Real.exp (min x y) = min (Real.exp x) (Real.exp y) := by
  rcases le_total x y with h | h
  · rw [min_eq_left h, min_eq_left (Real.exp_le_exp.mpr h)]
  · rw [min_eq_right h, min_eq_right (Real.exp_le_exp.mpr h)]

private lemma exponent_scale (a b β v : ℝ) (hβ : 0 < β) :
    exponent a b β (v / β) = (1 / β ^ 2) * exponent a b 1 v := by
  unfold exponent
  rw [abs_div, abs_of_pos hβ, div_pow, div_pow]
  field_simp [hβ.ne']

lemma spectralLoss_eq_scaled_loss (N : ℕ) (β : ℝ) (hβ : 0 < β) :
    spectralLoss N (1 / β ^ 2) = (1 / β ^ 2) * loss N β := by
  unfold spectralLoss loss
  rw [mul_min_of_nonneg _ _ (by positivity : 0 ≤ 1 / β ^ 2)]
  congr 1 <;> field_simp [hβ.ne', rho0_pos.ne']

theorem envelope_spectral_eq (β v : ℝ) (hβ : 0 < β) :
    envelope β (v / β) = Real.exp ((1 / β ^ 2) * spectralExponent v) := by
  unfold envelope spectralExponent
  rw [mul_min_of_nonneg _ _ (by positivity : 0 ≤ 1 / β ^ 2), mul_zero,
    mul_min_of_nonneg _ _ (by positivity : 0 ≤ 1 / β ^ 2),
    mul_min_of_nonneg _ _ (by positivity : 0 ≤ 1 / β ^ 2)]
  simp only [exp_min, Real.exp_zero]
  rw [exponent_scale _ _ _ _ hβ, exponent_scale _ _ _ _ hβ,
    exponent_scale _ _ _ _ hβ]

theorem lossEnvelope_spectral_eq (N : ℕ) (hN : 0 < N) (β v : ℝ) (hβ : 0 < β) :
    lossEnvelope N β (v / β) =
      Real.exp (((1 / β ^ 2) - spectralLoss N (1 / β ^ 2)) * spectralExponent v) := by
  have he : 0 ≤ 1 - loss N β := sub_nonneg.mpr (loss_le_one N hN β)
  have hs : 0 ≤ (1 - loss N β) * (1 / β ^ 2) := mul_nonneg he (by positivity)
  rw [spectralLoss_eq_scaled_loss N β hβ]
  have hid : (1 / β ^ 2 - 1 / β ^ 2 * loss N β) = (1 - loss N β) * (1 / β ^ 2) := by ring
  rw [hid]
  unfold lossEnvelope spectralExponent
  rw [mul_min_of_nonneg _ _ hs, mul_zero, mul_min_of_nonneg _ _ hs,
    mul_min_of_nonneg _ _ hs]
  simp only [exp_min, Real.exp_zero]
  rw [exponent_scale _ _ _ _ hβ, exponent_scale _ _ _ _ hβ,
    exponent_scale _ _ _ _ hβ]
  simp only [mul_assoc]

lemma spectralLoss_eq_const (N : ℕ) (hN : 0 < N) (s : ℝ)
    (hs : (N : ℝ) / rho0 ^ 2 ≤ s) : spectralLoss N s = 1 / rho0 ^ 2 := by
  apply min_eq_left
  apply (le_div_iff₀ (Nat.cast_pos.mpr hN)).mpr
  convert hs using 1 <;> ring

lemma spectralLoss_eq_linear (N : ℕ) (hN : 0 < N) (s : ℝ)
    (hs : s ≤ (N : ℝ) / rho0 ^ 2) : spectralLoss N s = s / (N : ℝ) := by
  apply min_eq_right
  apply (div_le_iff₀ (Nat.cast_pos.mpr hN)).mpr
  convert hs using 1 <;> ring

def spectralRate (v w : ℝ) : ℝ := (v ^ 2 - w ^ 2) / 2 - spectralExponent w

def linearSpectralRate (N : ℕ) (v w : ℝ) : ℝ :=
  (v ^ 2 - w ^ 2) / 2 - (1 - 1 / (N : ℝ)) * spectralExponent w

/-- This is the complete inner coarse-price integrand in fixed coordinates,
including the Jacobian. -/
def coarseSpectralCore (N : ℕ) (s v w : ℝ) : ℝ :=
  s ^ (3 / 2 : ℝ) *
    Real.exp (-s * spectralRate v w - spectralLoss N s * spectralExponent w) *
    (w ^ 2 / 2 + spectralLoss N s * w ^ 3 / 3)

lemma spectralRate_nonneg (v w : ℝ) (hw : 0 ≤ w) (hwv : w ≤ v) :
    0 ≤ spectralRate v w := by
  have hg := spectralExponent_nonpos w
  unfold spectralRate
  nlinarith

lemma linearSpectralRate_nonneg (N : ℕ) (hN : 0 < N) (v w : ℝ)
    (hw : 0 ≤ w) (hwv : w ≤ v) : 0 ≤ linearSpectralRate N v w := by
  have h1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hc : 0 ≤ 1 - 1 / (N : ℝ) := by
    have := (div_le_one hNp).mpr h1
    linarith
  have hg := mul_nonpos_of_nonneg_of_nonpos hc (spectralExponent_nonpos w)
  unfold linearSpectralRate
  nlinarith

/-- The frozen-loss branch is one positive weighted r=3/2 kernel. -/
theorem coarseSpectralCore_const (N : ℕ) (hN : 0 < N) (s v w : ℝ) (hs : 0 < s)
    (hbranch : (N : ℝ) / rho0 ^ 2 ≤ s) :
    coarseSpectralCore N s v w =
      (Real.exp (-(1 / rho0 ^ 2) * spectralExponent w) *
        (w ^ 2 / 2 + (1 / rho0 ^ 2) * w ^ 3 / 3)) *
      powerExp (3 / 2) (spectralRate v w) s := by
  rw [coarseSpectralCore, spectralLoss_eq_const N hN s hbranch,
    powerExp_eq_rpow _ _ _ hs]
  rw [sub_eq_add_neg, Real.exp_add]
  ring

/-- The linear-loss branch is exactly the sum of r=3/2 and r=5/2 kernels. -/
theorem coarseSpectralCore_linear (N : ℕ) (hN : 0 < N) (s v w : ℝ) (hs : 0 < s)
    (hbranch : s ≤ (N : ℝ) / rho0 ^ 2) :
    coarseSpectralCore N s v w =
      (w ^ 2 / 2) * powerExp (3 / 2) (linearSpectralRate N v w) s +
      (w ^ 3 / (3 * (N : ℝ))) * powerExp (5 / 2) (linearSpectralRate N v w) s := by
  rw [coarseSpectralCore, spectralLoss_eq_linear N hN s hbranch,
    powerExp_eq_rpow _ _ _ hs, powerExp_eq_rpow _ _ _ hs]
  have he : -s * spectralRate v w - s / (N : ℝ) * spectralExponent w =
      -s * linearSpectralRate N v w := by
    unfold spectralRate linearSpectralRate
    ring
  rw [he]
  have hp : s ^ (5 / 2 : ℝ) = s ^ (3 / 2 : ℝ) * s := by
    convert Real.rpow_add_one hs.ne' (3 / 2) using 1 <;> norm_num
  rw [hp]
  ring

lemma constCoreWeight_nonneg (w : ℝ) (hw : 0 ≤ w) :
    0 ≤ Real.exp (-(1 / rho0 ^ 2) * spectralExponent w) *
      (w ^ 2 / 2 + (1 / rho0 ^ 2) * w ^ 3 / 3) := by positivity

lemma linearCoreWeights_nonneg (N : ℕ) (w : ℝ) (hw : 0 ≤ w) :
    0 ≤ w ^ 2 / 2 ∧ 0 ≤ w ^ 3 / (3 * (N : ℝ)) := by constructor <;> positivity

private lemma scaled_three_halves (β : ℝ) (hβ : 0 < β) :
    (1 / β ^ 2) ^ (3 / 2 : ℝ) = 1 / β ^ 3 := by
  have hsqrt : (1 / β ^ 2) ^ (1 / 2 : ℝ) = 1 / β := by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_div (by positivity), Real.sqrt_one,
      Real.sqrt_sq_eq_abs, abs_of_pos hβ]
  have h := Real.rpow_mul_natCast (by positivity : 0 ≤ 1 / β ^ 2) (1 / 2) 3
  norm_num only [Nat.cast_ofNat] at h
  convert h.trans (by rw [hsqrt, div_pow, one_pow]) using 1 <;> norm_num

private lemma lambda_spectral (N : ℕ) (β : ℝ) (hβ : 0 < β) :
    CoarseHighMomentRayPrice.lambda N β = β * spectralLoss N (1 / β ^ 2) := by
  rw [spectralLoss_eq_scaled_loss N β hβ,
    ← CoarseHighMomentRayPrice.loss_div_eq_lambda N β hβ]
  field_simp [hβ.ne']

/-- Exact connection to the existing coarse price, before any kernel weight
or Prawitz integration is added. -/
theorem coarsePrice_spectral_eq (N : ℕ) (hN : 0 < N) (β v : ℝ) (hβ : 0 < β) :
    CoarseHighMomentRayPrice.coarsePrice N β (v / β) =
      ∫ w in (0 : ℝ)..v, coarseSpectralCore N (1 / β ^ 2) v w := by
  have hsub := intervalIntegral.integral_comp_div (a := (0 : ℝ)) (b := v)
    (CoarseHighMomentRayPrice.coarseIntegrand N β) hβ.ne'
  simp only [zero_div, smul_eq_mul] at hsub
  have hchange : (∫ u in (0 : ℝ)..v / β, CoarseHighMomentRayPrice.coarseIntegrand N β u) =
      (1 / β) * ∫ w in (0 : ℝ)..v,
        CoarseHighMomentRayPrice.coarseIntegrand N β (w / β) := by
    rw [hsub]
    field_simp [hβ.ne']
  unfold CoarseHighMomentRayPrice.coarsePrice
  rw [hchange]
  rw [← mul_assoc, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro w _
  unfold CoarseHighMomentRayPrice.coarseIntegrand coarseSpectralCore
  dsimp only
  rw [lossEnvelope_spectral_eq N hN β w hβ, lambda_spectral N β hβ,
    scaled_three_halves β hβ]
  have he : Real.exp (-((v / β) ^ 2 / 2)) * Real.exp ((w / β) ^ 2 / 2) *
      Real.exp ((1 / β ^ 2 - spectralLoss N (1 / β ^ 2)) * spectralExponent w) =
      Real.exp (-(1 / β ^ 2) * spectralRate v w -
        spectralLoss N (1 / β ^ 2) * spectralExponent w) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    unfold spectralRate
    field_simp [hβ.ne'] <;> ring
  calc
    _ = (1 / β ^ 3) *
        (Real.exp (-((v / β) ^ 2 / 2)) * Real.exp ((w / β) ^ 2 / 2) *
          Real.exp ((1 / β ^ 2 - spectralLoss N (1 / β ^ 2)) * spectralExponent w)) *
        (w ^ 2 / 2 + spectralLoss N (1 / β ^ 2) * w ^ 3 / 3) := by
      field_simp [hβ.ne'] <;> ring
    _ = _ := by rw [he]

/-- A common endpoint factor and common interpolation weights, uniform in
the real exponential rate.  This interface lets the scalar interpolation
theorem feed all four actual spectral terms. -/
def KernelEndpointBound (a b s E l r rmax : ℝ) : Prop :=
  ∀ p R : ℝ, 0 ≤ p → p ≤ rmax →
    powerExp p R s ≤ E * (l * powerExp p R a + r * powerExp p R b)

lemma coarseSpectralCore_nonneg (N : ℕ) (s v w : ℝ) (hs : 0 ≤ s) (hw : 0 ≤ w) :
    0 ≤ coarseSpectralCore N s v w := by
  unfold coarseSpectralCore spectralLoss
  positivity

lemma continuous_coarseSpectralCore (N : ℕ) (s v : ℝ) :
    Continuous (coarseSpectralCore N s v) := by
  unfold coarseSpectralCore spectralRate spectralExponent exponent
  fun_prop

theorem coarseSpectralCore_endpoint_const (N : ℕ) (hN : 0 < N)
    (a b s E l r v w : ℝ) (ha : 0 < a) (hb : 0 < b) (hs : 0 < s) (hw : 0 ≤ w)
    (hba : (N : ℝ) / rho0 ^ 2 ≤ a) (hbb : (N : ℝ) / rho0 ^ 2 ≤ b)
    (hbs : (N : ℝ) / rho0 ^ 2 ≤ s) (hk : KernelEndpointBound a b s E l r (3 / 2)) :
    coarseSpectralCore N s v w ≤
      E * (l * coarseSpectralCore N a v w + r * coarseSpectralCore N b v w) := by
  rw [coarseSpectralCore_const N hN s v w hs hbs,
    coarseSpectralCore_const N hN a v w ha hba,
    coarseSpectralCore_const N hN b v w hb hbb]
  have hh := mul_le_mul_of_nonneg_left
    (hk (3 / 2) (spectralRate v w) (by norm_num) le_rfl)
    (constCoreWeight_nonneg w hw)
  convert hh using 1 <;> ring

theorem coarseSpectralCore_endpoint_linear (N : ℕ) (hN : 0 < N)
    (a b s E l r v w : ℝ) (ha : 0 < a) (hb : 0 < b) (hs : 0 < s) (hw : 0 ≤ w)
    (hba : a ≤ (N : ℝ) / rho0 ^ 2) (hbb : b ≤ (N : ℝ) / rho0 ^ 2)
    (hbs : s ≤ (N : ℝ) / rho0 ^ 2) (hk : KernelEndpointBound a b s E l r (5 / 2)) :
    coarseSpectralCore N s v w ≤
      E * (l * coarseSpectralCore N a v w + r * coarseSpectralCore N b v w) := by
  rw [coarseSpectralCore_linear N hN s v w hs hbs,
    coarseSpectralCore_linear N hN a v w ha hba,
    coarseSpectralCore_linear N hN b v w hb hbb]
  obtain ⟨hc1, hc2⟩ := linearCoreWeights_nonneg N w hw
  have hh1 := mul_le_mul_of_nonneg_left
    (hk (3 / 2) (linearSpectralRate N v w) (by norm_num) (by norm_num)) hc1
  have hh2 := mul_le_mul_of_nonneg_left
    (hk (5 / 2) (linearSpectralRate N v w) (by norm_num) le_rfl) hc2
  convert add_le_add hh1 hh2 using 1 <;> ring

def coarseSpectralSlice (N : ℕ) (s v : ℝ) : ℝ :=
  ∫ w in (0 : ℝ)..v, coarseSpectralCore N s v w

lemma coarseSpectralSlice_nonneg (N : ℕ) (s v : ℝ) (hs : 0 ≤ s) (hv : 0 ≤ v) :
    0 ≤ coarseSpectralSlice N s v := by
  apply intervalIntegral.integral_nonneg hv
  intro w hw
  exact coarseSpectralCore_nonneg N s v w hs hw.1

theorem coarseSpectralSlice_endpoint (N : ℕ) (a b s E l r v : ℝ) (hv : 0 ≤ v)
    (hc : ∀ w, 0 ≤ w → w ≤ v → coarseSpectralCore N s v w ≤
      E * (l * coarseSpectralCore N a v w + r * coarseSpectralCore N b v w)) :
    coarseSpectralSlice N s v ≤
      E * (l * coarseSpectralSlice N a v + r * coarseSpectralSlice N b v) := by
  have hca := continuous_coarseSpectralCore N a v
  have hcb := continuous_coarseSpectralCore N b v
  have hcs := continuous_coarseSpectralCore N s v
  have hcd := ((hca.const_mul l).add (hcb.const_mul r)).const_mul E
  have hh := intervalIntegral.integral_mono_on (μ := volume) hv (hcs.intervalIntegrable 0 v)
    (hcd.intervalIntegrable 0 v)
    (fun w hw => hc w hw.1 hw.2)
  unfold coarseSpectralSlice
  convert hh using 1
  simp only [Pi.add_apply]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add ((hca.const_mul l).intervalIntegrable 0 v)
      ((hcb.const_mul r).intervalIntegrable 0 v),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

open Causalean.Stat.CLT.BerryEsseen (prawitzKernel)

def spectralKernelWeight (V v : ℝ) : ℝ := ‖prawitzKernel (v / V)‖

def spectralCorrectionWeight (V v : ℝ) : ℝ :=
  ‖prawitzKernel (v / V) - Complex.I / ((2 * Real.pi * (v / V) : ℝ) : ℂ)‖

def firstSpectralIntegrand (N : ℕ) (V s v : ℝ) : ℝ :=
  spectralKernelWeight V v * coarseSpectralSlice N s v

def secondSpectralIntegrand (V s v : ℝ) : ℝ :=
  spectralKernelWeight V v * powerExp (1 / 2) (-spectralExponent v) s

def thirdSpectralIntegrand (V s v : ℝ) : ℝ :=
  spectralCorrectionWeight V v * powerExp (1 / 2) (v ^ 2 / 2) s

def fourthSpectralIntegrand (s v : ℝ) : ℝ := powerExp (1 / 2) (v ^ 2 / 2) s / v

/-- The four-term normalized coarse Prawitz profile in fixed spectral
coordinates.  For 0<A<V, the finite set integrals equal the corresponding
ordered interval integrals. -/
def spectralProfile (N : ℕ) (A V s : ℝ) : ℝ :=
  (2 / V) * (∫ v in Ioc 0 A, firstSpectralIntegrand N V s v) +
  (2 / V) * (∫ v in Ioc A V, secondSpectralIntegrand V s v) +
  (2 / V) * (∫ v in Ioc 0 A, thirdSpectralIntegrand V s v) +
  (1 / Real.pi) * (∫ v in Ioi A, fourthSpectralIntegrand s v)

/-- Plain integrability of the four actual profile terms at an endpoint.
There is no derivative hypothesis. -/
structure ProfileIntegrable (N : ℕ) (A V s : ℝ) : Prop where
  first : IntegrableOn (firstSpectralIntegrand N V s) (Ioc 0 A)
  second : IntegrableOn (secondSpectralIntegrand V s) (Ioc A V)
  third : IntegrableOn (thirdSpectralIntegrand V s) (Ioc 0 A)
  fourth : IntegrableOn (fourthSpectralIntegrand s) (Ioi A)

lemma continuous_coarseSpectralSlice (N : ℕ) (hN : 0 < N) (s : ℝ) (hs : 0 < s) :
    Continuous (coarseSpectralSlice N s) := by
  let β : ℝ := 1 / Real.sqrt s
  have hβ : 0 < β := div_pos zero_lt_one (Real.sqrt_pos.mpr hs)
  have hid : 1 / β ^ 2 = s := by
    dsimp [β]
    rw [div_pow, one_pow, one_div_div, Real.sq_sqrt hs.le, div_one]
  have heq : coarseSpectralSlice N s =
      (fun v : ℝ => CoarseHighMomentRayPrice.coarsePrice N β (v / β)) := by
    funext v
    rw [coarsePrice_spectral_eq N hN β v hβ, hid]
    rfl
  rw [heq]
  exact (CoarseHighMomentRayPrice.continuous_coarsePrice N β).comp (by fun_prop)

private lemma measurable_prawitzKernel : Measurable prawitzKernel := by
  have hs : Measurable Real.sign := by
    unfold Real.sign
    exact Measurable.ite measurableSet_Iio measurable_const
      (Measurable.ite measurableSet_Ioi measurable_const measurable_const)
  unfold prawitzKernel
  apply Measurable.ite
  · exact (measurableSet_eq_fun measurable_id measurable_const).union
      (measurableSet_lt measurable_const continuous_abs.measurable)
  · fun_prop
  · fun_prop

lemma measurable_firstSpectralIntegrand (N : ℕ) (hN : 0 < N) (V s : ℝ) (hs : 0 < s) :
    Measurable (firstSpectralIntegrand N V s) := by
  exact ((measurable_prawitzKernel.comp (by fun_prop)).norm).mul
    (continuous_coarseSpectralSlice N hN s hs).measurable

lemma measurable_secondSpectralIntegrand (V s : ℝ) :
    Measurable (secondSpectralIntegrand V s) := by
  have hscaled : Measurable (fun v : ℝ => prawitzKernel (v / V)) :=
    measurable_prawitzKernel.comp (by fun_prop)
  unfold secondSpectralIntegrand spectralKernelWeight powerExp spectralExponent exponent
  fun_prop

lemma measurable_thirdSpectralIntegrand (V s : ℝ) :
    Measurable (thirdSpectralIntegrand V s) := by
  have hscaled : Measurable (fun v : ℝ => prawitzKernel (v / V)) :=
    measurable_prawitzKernel.comp (by fun_prop)
  unfold thirdSpectralIntegrand spectralCorrectionWeight powerExp
  fun_prop

lemma measurable_fourthSpectralIntegrand (s : ℝ) :
    Measurable (fourthSpectralIntegrand s) := by
  unfold fourthSpectralIntegrand powerExp
  fun_prop

/-- Positive domination by two integrable endpoints gives both middle
integrability and the required integral inequality. -/
private theorem integral_endpoint_mixture {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f fa fb : α → ℝ) (E l r : ℝ)
    (hf : AEStronglyMeasurable f μ) (ha : Integrable fa μ) (hb : Integrable fb μ)
    (hn : ∀ᵐ x ∂μ, 0 ≤ f x)
    (hle : ∀ᵐ x ∂μ, f x ≤ E * (l * fa x + r * fb x)) :
    Integrable f μ ∧ (∫ x, f x ∂μ) ≤ E * (l * (∫ x, fa x ∂μ) + r * (∫ x, fb x ∂μ)) := by
  have hd : Integrable (fun x => E * (l * fa x + r * fb x)) μ :=
    ((ha.const_mul l).add (hb.const_mul r)).const_mul E
  have hi : Integrable f μ := hd.mono' hf (by
    filter_upwards [hn, hle] with x hnx hlex
    simpa only [Real.norm_eq_abs, abs_of_nonneg hnx] using hlex)
  refine ⟨hi, ?_⟩
  have hh := integral_mono_ae hi hd hle
  simpa only [integral_const_mul,
    integral_add (ha.const_mul l) (hb.const_mul r)] using hh

/-- The full actual spectral profile inherits a common kernel endpoint
factor.  Only plain endpoint integrability is required; middle
integrability is proved by positive endpoint domination. -/
theorem spectralProfile_endpoint_of_core (N : ℕ) (hN : 0 < N)
    (A V a b s E l r : ℝ) (hA : 0 < A) (hV : 0 < V) (hs : 0 < s)
    (haI : ProfileIntegrable N A V a) (hbI : ProfileIntegrable N A V b)
    (hc : ∀ v w : ℝ, 0 ≤ v → 0 ≤ w → w ≤ v →
      coarseSpectralCore N s v w ≤
        E * (l * coarseSpectralCore N a v w + r * coarseSpectralCore N b v w))
    (hk : ∀ R : ℝ, powerExp (1 / 2) R s ≤
      E * (l * powerExp (1 / 2) R a + r * powerExp (1 / 2) R b)) :
    ProfileIntegrable N A V s ∧
      spectralProfile N A V s ≤ E * (l * spectralProfile N A V a + r * spectralProfile N A V b) := by
  have h1 := integral_endpoint_mixture (volume.restrict (Ioc 0 A))
    (firstSpectralIntegrand N V s) (firstSpectralIntegrand N V a)
    (firstSpectralIntegrand N V b) E l r
    (measurable_firstSpectralIntegrand N hN V s hs).aestronglyMeasurable
    haI.first hbI.first (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
      exact mul_nonneg (norm_nonneg _) (coarseSpectralSlice_nonneg N s v hs.le hv.1.le)) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
      have hslice := coarseSpectralSlice_endpoint N a b s E l r v hv.1.le
        (fun w hw hwv => hc v w hv.1.le hw hwv)
      have hh := mul_le_mul_of_nonneg_left hslice (norm_nonneg (prawitzKernel (v / V)))
      unfold firstSpectralIntegrand spectralKernelWeight
      convert hh using 1 <;> ring)
  have h2 := integral_endpoint_mixture (volume.restrict (Ioc A V))
    (secondSpectralIntegrand V s) (secondSpectralIntegrand V a)
    (secondSpectralIntegrand V b) E l r
    (measurable_secondSpectralIntegrand V s).aestronglyMeasurable
    haI.second hbI.second (ae_of_all _ (fun v =>
      mul_nonneg (norm_nonneg _) (powerExp_pos _ _ _).le)) (ae_of_all _ (fun v => by
        have hh := mul_le_mul_of_nonneg_left (hk (-spectralExponent v))
          (norm_nonneg (prawitzKernel (v / V)))
        unfold secondSpectralIntegrand spectralKernelWeight
        convert hh using 1 <;> ring))
  have h3 := integral_endpoint_mixture (volume.restrict (Ioc 0 A))
    (thirdSpectralIntegrand V s) (thirdSpectralIntegrand V a)
    (thirdSpectralIntegrand V b) E l r
    (measurable_thirdSpectralIntegrand V s).aestronglyMeasurable
    haI.third hbI.third (ae_of_all _ (fun v =>
      mul_nonneg (norm_nonneg _) (powerExp_pos _ _ _).le)) (ae_of_all _ (fun v => by
        have hh := mul_le_mul_of_nonneg_left (hk (v ^ 2 / 2))
          (norm_nonneg (prawitzKernel (v / V) -
            Complex.I / ((2 * Real.pi * (v / V) : ℝ) : ℂ)))
        unfold thirdSpectralIntegrand spectralCorrectionWeight
        convert hh using 1 <;> ring))
  have h4 := integral_endpoint_mixture (volume.restrict (Ioi A))
    (fourthSpectralIntegrand s) (fourthSpectralIntegrand a)
    (fourthSpectralIntegrand b) E l r
    (measurable_fourthSpectralIntegrand s).aestronglyMeasurable
    haI.fourth hbI.fourth (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      exact div_nonneg (powerExp_pos _ _ _).le (hA.trans hv).le) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      have hh := div_le_div_of_nonneg_right (hk (v ^ 2 / 2)) (hA.trans hv).le
      unfold fourthSpectralIntegrand
      convert hh using 1 <;> ring)
  refine ⟨⟨h1.1, h2.1, h3.1, h4.1⟩, ?_⟩
  have h1' := mul_le_mul_of_nonneg_left h1.2 (by positivity : 0 ≤ 2 / V)
  have h2' := mul_le_mul_of_nonneg_left h2.2 (by positivity : 0 ≤ 2 / V)
  have h3' := mul_le_mul_of_nonneg_left h3.2 (by positivity : 0 ≤ 2 / V)
  have h4' := mul_le_mul_of_nonneg_left h4.2 (by positivity : 0 ≤ 1 / Real.pi)
  convert add_le_add (add_le_add (add_le_add h1' h2') h3') h4' using 1 <;>
    unfold spectralProfile <;> ring

theorem spectralProfile_endpoint_const (N : ℕ) (hN : 0 < N)
    (A V a b s E l r : ℝ) (hA : 0 < A) (hV : 0 < V)
    (ha : 0 < a) (hb : 0 < b) (hs : 0 < s)
    (hba : (N : ℝ) / rho0 ^ 2 ≤ a) (hbb : (N : ℝ) / rho0 ^ 2 ≤ b)
    (hbs : (N : ℝ) / rho0 ^ 2 ≤ s)
    (haI : ProfileIntegrable N A V a) (hbI : ProfileIntegrable N A V b)
    (hk : KernelEndpointBound a b s E l r (3 / 2)) :
    ProfileIntegrable N A V s ∧
      spectralProfile N A V s ≤ E * (l * spectralProfile N A V a + r * spectralProfile N A V b) := by
  apply spectralProfile_endpoint_of_core N hN A V a b s E l r hA hV hs haI hbI
  · intro v w _ hw _
    exact coarseSpectralCore_endpoint_const N hN a b s E l r v w ha hb hs hw hba hbb hbs hk
  · intro R
    exact hk (1 / 2) R (by norm_num) (by norm_num)

theorem spectralProfile_endpoint_linear (N : ℕ) (hN : 0 < N)
    (A V a b s E l r : ℝ) (hA : 0 < A) (hV : 0 < V)
    (ha : 0 < a) (hb : 0 < b) (hs : 0 < s)
    (hba : a ≤ (N : ℝ) / rho0 ^ 2) (hbb : b ≤ (N : ℝ) / rho0 ^ 2)
    (hbs : s ≤ (N : ℝ) / rho0 ^ 2)
    (haI : ProfileIntegrable N A V a) (hbI : ProfileIntegrable N A V b)
    (hk : KernelEndpointBound a b s E l r (5 / 2)) :
    ProfileIntegrable N A V s ∧
      spectralProfile N A V s ≤ E * (l * spectralProfile N A V a + r * spectralProfile N A V b) := by
  apply spectralProfile_endpoint_of_core N hN A V a b s E l r hA hV hs haI hbI
  · intro v w _ hw _
    exact coarseSpectralCore_endpoint_linear N hN a b s E l r v w ha hb hs hw hba hbb hbs hk
  · intro R
    exact hk (1 / 2) R (by norm_num) (by norm_num)

lemma spectralLoss_nonneg (N : ℕ) (s : ℝ) (hs : 0 ≤ s) : 0 ≤ spectralLoss N s := by
  unfold spectralLoss
  positivity

lemma spectralLoss_le_self (N : ℕ) (hN : 0 < N) (s : ℝ) (hs : 0 ≤ s) :
    spectralLoss N s ≤ s := by
  have h1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  exact (min_le_right _ _).trans (div_le_self hs h1)

def sliceCoefficient (N : ℕ) (A s : ℝ) : ℝ :=
  s ^ (3 / 2 : ℝ) * (1 / 2 + spectralLoss N s * A / 3)

lemma sliceCoefficient_nonneg (N : ℕ) (A s : ℝ) (hA : 0 ≤ A) (hs : 0 ≤ s) :
    0 ≤ sliceCoefficient N A s := by
  unfold sliceCoefficient
  have hd := spectralLoss_nonneg N s hs
  positivity

lemma coarseSpectralCore_le_quadratic (N : ℕ) (hN : 0 < N) (A s v w : ℝ)
    (hs : 0 ≤ s) (hw : 0 ≤ w) (hwv : w ≤ v) (hvA : v ≤ A) :
    coarseSpectralCore N s v w ≤ sliceCoefficient N A s * w ^ 2 := by
  have hd := spectralLoss_nonneg N s hs
  have hds := spectralLoss_le_self N hN s hs
  have hvw : 0 ≤ v ^ 2 - w ^ 2 := by nlinarith
  have hg := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hds) (spectralExponent_nonpos w)
  have harg : -s * spectralRate v w - spectralLoss N s * spectralExponent w ≤ 0 := by
    unfold spectralRate
    have hh := mul_nonneg hs hvw
    nlinarith only [hh, hg]
  have he := Real.exp_le_one_iff.mpr harg
  have hpw : w ^ 3 ≤ A * w ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right (hwv.trans hvA) (sq_nonneg w)
    nlinarith only [hh]
  have hp := mul_le_mul_of_nonneg_left hpw hd
  have hpow : 0 ≤ s ^ (3 / 2 : ℝ) := Real.rpow_nonneg hs _
  have hp' := mul_le_mul_of_nonneg_left hp hpow
  unfold coarseSpectralCore sliceCoefficient
  calc
    _ ≤ s ^ (3 / 2 : ℝ) * 1 * (w ^ 2 / 2 + spectralLoss N s * w ^ 3 / 3) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he hpow) (by positivity)
    _ ≤ _ := by nlinarith only [hp']

lemma coarseSpectralSlice_le_cubic (N : ℕ) (hN : 0 < N) (A s v : ℝ)
    (hs : 0 ≤ s) (hv : 0 ≤ v) (hvA : v ≤ A) :
    coarseSpectralSlice N s v ≤ sliceCoefficient N A s * v ^ 3 / 3 := by
  have hc := continuous_coarseSpectralCore N s v
  have hp : Continuous (fun w : ℝ => sliceCoefficient N A s * w ^ 2) := by fun_prop
  have hh := intervalIntegral.integral_mono_on (μ := volume) hv
    (hc.intervalIntegrable 0 v) (hp.intervalIntegrable 0 v)
    (fun w hw => coarseSpectralCore_le_quadratic N hN A s v w hs hw.1 hw.2 hvA)
  unfold coarseSpectralSlice
  convert hh using 1
  rw [intervalIntegral.integral_const_mul, integral_pow]
  norm_num
  ring

lemma spectralKernelWeight_le (V v : ℝ) (hV : 0 < V) (hv : 0 < v) (hband : v ≤ V) :
    spectralKernelWeight V v ≤ V / (2 * Real.pi) / v + 1 / 2 := by
  have harg := div_pos hv hV
  have hb := Causalean.Stat.CLT.BerryEsseen.prawitzKernel_norm_le (v / V)
    (by simpa only [abs_of_pos harg] using harg)
    (by rw [abs_of_pos harg]; exact (div_le_one hV).mpr hband)
  unfold spectralKernelWeight
  rw [abs_of_pos harg] at hb
  convert hb using 1
  field_simp

lemma spectralCorrectionWeight_le (V v : ℝ) (hV : 0 < V) (hv : 0 < v) (hband : v ≤ V) :
    spectralCorrectionWeight V v ≤ 1 / 2 := by
  have harg := div_pos hv hV
  exact Causalean.Stat.CLT.BerryEsseen.prawitzKernel_principal_correction_norm_le (v / V)
    (by simpa only [abs_of_pos harg] using harg)
    (by rw [abs_of_pos harg]; exact (div_le_one hV).mpr hband)

theorem profileIntegrable (N : ℕ) (hN : 0 < N) (A V s : ℝ)
    (hA : 0 < A) (hAV : A ≤ V) (hs : 0 < s) : ProfileIntegrable N A V s := by
  have hV : 0 < V := hA.trans_le hAV
  have hkmeas : Measurable (spectralKernelWeight V) :=
    (measurable_prawitzKernel.comp (by fun_prop)).norm
  have hcmeas : Measurable (spectralCorrectionWeight V) := by
    have hscaled : Measurable (fun v : ℝ => prawitzKernel (v / V)) :=
      measurable_prawitzKernel.comp (by fun_prop)
    unfold spectralCorrectionWeight
    fun_prop
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hp : Continuous (fun v : ℝ =>
        (sliceCoefficient N A s / 3) * (V / (2 * Real.pi) * v ^ 2 + v ^ 3 / 2)) := by fun_prop
    apply (hp.intervalIntegrable 0 A).1.mono'
      (measurable_firstSpectralIntegrand N hN V s hs).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    have hn := mul_nonneg (norm_nonneg (prawitzKernel (v / V)))
      (coarseSpectralSlice_nonneg N s v hs.le hv.1.le)
    unfold firstSpectralIntegrand spectralKernelWeight
    rw [Real.norm_eq_abs, abs_of_nonneg hn]
    have hh := mul_le_mul (spectralKernelWeight_le V v hV hv.1 (hv.2.trans hAV))
      (coarseSpectralSlice_le_cubic N hN A s v hs.le hv.1.le hv.2)
      (coarseSpectralSlice_nonneg N s v hs.le hv.1.le) (by
        have hvpos : 0 < v := hv.1
        positivity)
    calc
      _ ≤ (V / (2 * Real.pi) / v + 1 / 2) * (sliceCoefficient N A s * v ^ 3 / 3) := by
        simpa only [spectralKernelWeight] using hh
      _ = _ := by field_simp [hv.1.ne']
  · have hkI : IntegrableOn (spectralKernelWeight V) (Ioc A V) := by
      apply (intervalIntegrable_const (c := V / (2 * Real.pi) / A + 1 / 2)
        (a := A) (b := V) (μ := volume)).1.mono' hkmeas.aestronglyMeasurable
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
      rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ spectralKernelWeight V v from norm_nonneg _)]
      exact (spectralKernelWeight_le V v hV (hA.trans hv.1) hv.2).trans (by
        gcongr
        exact hv.1.le)
    have hp : Continuous (fun v : ℝ => powerExp (1 / 2) (-spectralExponent v) s) := by
      unfold powerExp spectralExponent exponent
      fun_prop
    exact hkI.mul_continuousOn_of_subset hp.continuousOn measurableSet_Ioc isCompact_Icc Ioc_subset_Icc_self
  · have hcI : IntegrableOn (spectralCorrectionWeight V) (Ioc 0 A) := by
      apply (intervalIntegrable_const (c := (1 / 2 : ℝ))
        (a := 0) (b := A) (μ := volume)).1.mono' hcmeas.aestronglyMeasurable
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
      rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ spectralCorrectionWeight V v from norm_nonneg _)]
      exact spectralCorrectionWeight_le V v hV hv.1 (hv.2.trans hAV)
    have hp : Continuous (fun v : ℝ => powerExp (1 / 2) (v ^ 2 / 2) s) := by
      unfold powerExp
      fun_prop
    exact hcI.mul_continuousOn_of_subset hp.continuousOn measurableSet_Ioc isCompact_Icc Ioc_subset_Icc_self
  · have hg : Integrable (fun v : ℝ => powerExp (1 / 2) (v ^ 2 / 2) s) volume := by
      have hh := (integrable_exp_neg_mul_sq (b := (s / 2)) (by positivity : 0 < s / 2)).const_mul
        (Real.exp ((1 / 2) * Real.log s))
      convert hh using 1
      funext v
      unfold powerExp
      rw [sub_eq_add_neg, Real.exp_add]
      congr 1
      congr 1
      ring
    apply (hg.div_const A).integrableOn.mono'
      (measurable_fourthSpectralIntegrand s).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    unfold fourthSpectralIntegrand
    rw [Real.norm_eq_abs, abs_of_pos (div_pos (powerExp_pos _ _ _) (hA.trans hv))]
    exact div_le_div_of_nonneg_left (powerExp_pos _ _ _).le hA hv.le

theorem kernelEndpointBound_log_chord (a b s rmax : ℝ) (ha : 0 < a)
    (hab : a < b) (hs : s ∈ Icc a b) :
    KernelEndpointBound a b s (Real.exp (rmax * ((b - a) ^ 2 / (8 * a ^ 2))))
      ((b - s) / (b - a)) ((s - a) / (b - a)) rmax := by
  intro p R hp0 hpr
  rw [powerExp_eq_rpow _ _ _ (ha.trans_le hs.1), powerExp_eq_rpow _ _ _ ha,
    powerExp_eq_rpow _ _ _ (ha.trans hab)]
  simpa only [mul_comm s R, mul_comm a R, mul_comm b R, neg_mul, mul_neg] using
    PowerExponentialEndpoint.powerExp_le_endpoint_mixture a b s p R rmax ha hab hs hp0 hpr

/-- The complete frozen-loss spectral profile is controlled by two
endpoints, with a quadratic relative-width factor and no profile derivative
or integrability assumptions. -/
theorem spectralProfile_le_const_endpoint_mixture (N : ℕ) (hN : 0 < N)
    (A V a b s : ℝ) (hA : 0 < A) (hAV : A ≤ V) (ha : 0 < a) (hab : a < b)
    (hs : s ∈ Icc a b) (hbranch : (N : ℝ) / rho0 ^ 2 ≤ a) :
    spectralProfile N A V s ≤ Real.exp ((3 / 2) * ((b - a) ^ 2 / (8 * a ^ 2))) *
      (((b - s) / (b - a)) * spectralProfile N A V a +
        ((s - a) / (b - a)) * spectralProfile N A V b) := by
  exact (spectralProfile_endpoint_const N hN A V a b s _ _ _ hA (hA.trans_le hAV)
    ha (ha.trans hab) (ha.trans_le hs.1) hbranch (hbranch.trans hab.le)
    (hbranch.trans hs.1) (profileIntegrable N hN A V a hA hAV ha)
    (profileIntegrable N hN A V b hA hAV (ha.trans hab))
    (kernelEndpointBound_log_chord a b s (3 / 2) ha hab hs)).2

/-- The complete linear-loss spectral profile has the same endpoint
control, with rmax=5/2 because the cubic forcing contributes one extra s. -/
theorem spectralProfile_le_linear_endpoint_mixture (N : ℕ) (hN : 0 < N)
    (A V a b s : ℝ) (hA : 0 < A) (hAV : A ≤ V) (ha : 0 < a) (hab : a < b)
    (hs : s ∈ Icc a b) (hbranch : b ≤ (N : ℝ) / rho0 ^ 2) :
    spectralProfile N A V s ≤ Real.exp ((5 / 2) * ((b - a) ^ 2 / (8 * a ^ 2))) *
      (((b - s) / (b - a)) * spectralProfile N A V a +
        ((s - a) / (b - a)) * spectralProfile N A V b) := by
  exact (spectralProfile_endpoint_linear N hN A V a b s _ _ _ hA (hA.trans_le hAV)
    ha (ha.trans hab) (ha.trans_le hs.1) (hab.le.trans hbranch) hbranch
    (hs.2.trans hbranch) (profileIntegrable N hN A V a hA hAV ha)
    (profileIntegrable N hN A V b hA hAV (ha.trans hab))
    (kernelEndpointBound_log_chord a b s (5 / 2) ha hab hs)).2

private lemma endpoint_mixture_le_max (a b s x y : ℝ) (hab : a < b) (hs : s ∈ Icc a b) :
    ((b - s) / (b - a)) * x + ((s - a) / (b - a)) * y ≤ max x y := by
  have hl : 0 ≤ (b - s) / (b - a) := div_nonneg (sub_nonneg.mpr hs.2) (sub_pos.mpr hab).le
  have hr : 0 ≤ (s - a) / (b - a) := div_nonneg (sub_nonneg.mpr hs.1) (sub_pos.mpr hab).le
  calc
    _ ≤ ((b - s) / (b - a)) * max x y + ((s - a) / (b - a)) * max x y :=
      add_le_add (mul_le_mul_of_nonneg_left (le_max_left x y) hl)
        (mul_le_mul_of_nonneg_left (le_max_right x y) hr)
    _ = _ := by field_simp [(sub_pos.mpr hab).ne']; ring

theorem spectralProfile_le_const_endpoint_max (N : ℕ) (hN : 0 < N)
    (A V a b s : ℝ) (hA : 0 < A) (hAV : A ≤ V) (ha : 0 < a) (hab : a < b)
    (hs : s ∈ Icc a b) (hbranch : (N : ℝ) / rho0 ^ 2 ≤ a) :
    spectralProfile N A V s ≤ Real.exp ((3 / 2) * ((b - a) ^ 2 / (8 * a ^ 2))) *
      max (spectralProfile N A V a) (spectralProfile N A V b) := by
  apply (spectralProfile_le_const_endpoint_mixture N hN A V a b s hA hAV ha hab hs hbranch).trans
  exact mul_le_mul_of_nonneg_left (endpoint_mixture_le_max a b s _ _ hab hs) (Real.exp_pos _).le

theorem spectralProfile_le_linear_endpoint_max (N : ℕ) (hN : 0 < N)
    (A V a b s : ℝ) (hA : 0 < A) (hAV : A ≤ V) (ha : 0 < a) (hab : a < b)
    (hs : s ∈ Icc a b) (hbranch : b ≤ (N : ℝ) / rho0 ^ 2) :
    spectralProfile N A V s ≤ Real.exp ((5 / 2) * ((b - a) ^ 2 / (8 * a ^ 2))) *
      max (spectralProfile N A V a) (spectralProfile N A V b) := by
  apply (spectralProfile_le_linear_endpoint_mixture N hN A V a b s hA hAV ha hab hs hbranch).trans
  exact mul_le_mul_of_nonneg_left (endpoint_mixture_le_max a b s _ _ hab hs) (Real.exp_pos _).le

lemma scaled_one_half (β : ℝ) (hβ : 0 < β) :
    (1 / β ^ 2) ^ (1 / 2 : ℝ) = 1 / β := by
  rw [← Real.sqrt_eq_rpow, Real.sqrt_div (by positivity), Real.sqrt_one,
    Real.sqrt_sq_eq_abs, abs_of_pos hβ]

lemma powerExp_half_gaussian_scale (β v : ℝ) (hβ : 0 < β) :
    powerExp (1 / 2) (v ^ 2 / 2) (1 / β ^ 2) =
      Real.exp (-((v / β) ^ 2 / 2)) / β := by
  rw [powerExp_eq_rpow _ _ _ (by positivity), scaled_one_half β hβ]
  have he : -(1 / β ^ 2) * (v ^ 2 / 2) = -((v / β) ^ 2 / 2) := by
    field_simp [hβ.ne'] <;> ring
  rw [he]
  ring

lemma powerExp_half_scale (β R : ℝ) (hβ : 0 < β) :
    powerExp (1 / 2) R (1 / β ^ 2) = Real.exp (-(1 / β ^ 2) * R) / β := by
  rw [powerExp_eq_rpow _ _ _ (by positivity), scaled_one_half β hβ]
  ring

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

private lemma scaledCorrection_eq (β V v : ℝ) (hβ : 0 < β) (hV : 0 < V) :
    ‖prawitzKernel ((v / β) / (V / β)) / ((V / β : ℝ) : ℂ) -
      Complex.I / ((2 * Real.pi * (v / β) : ℝ) : ℂ)‖ =
      (β / V) * spectralCorrectionWeight V v := by
  have harg : (v / β) / (V / β) = v / V := by field_simp [hβ.ne']
  rw [harg]
  by_cases hv : v = 0
  · subst v
    simp [spectralCorrectionWeight, prawitzKernel]
  · have hβc : (β : ℂ) ≠ 0 := by exact_mod_cast hβ.ne'
    have hVc : (V : ℂ) ≠ 0 := by exact_mod_cast hV.ne'
    have hvc : (v : ℂ) ≠ 0 := by exact_mod_cast hv
    have hpc : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have he : prawitzKernel (v / V) / ((V / β : ℝ) : ℂ) -
        Complex.I / ((2 * Real.pi * (v / β) : ℝ) : ℂ) =
        ((β / V : ℝ) : ℂ) *
          (prawitzKernel (v / V) - Complex.I / ((2 * Real.pi * (v / V) : ℝ) : ℂ)) := by
      push_cast
      field_simp [hβc, hVc, hvc, hpc] <;> ring
    rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos hβ hV)]
    rfl

def actualFirstSpectralIntegrand (μ : ProbabilityMeasure ℝ) (n : ℕ) (β V v : ℝ) : ℝ :=
  spectralKernelWeight V v *
    (‖charFun (μ : Measure ℝ) ((v / β) / Real.sqrt n) ^ n -
      (Real.exp (-((v / β) ^ 2 / 2)) : ℂ)‖ / β)

def actualSecondSpectralIntegrand (μ : ProbabilityMeasure ℝ) (n : ℕ) (β V v : ℝ) : ℝ :=
  spectralKernelWeight V v * (‖charFun (μ : Measure ℝ) ((v / β) / Real.sqrt n) ^ n‖ / β)

def actualSpectralProfile (μ : ProbabilityMeasure ℝ) (n : ℕ) (β A V : ℝ) : ℝ :=
  (2 / V) * (∫ v in Ioc 0 A, actualFirstSpectralIntegrand μ n β V v) +
  (2 / V) * (∫ v in Ioc A V, actualSecondSpectralIntegrand μ n β V v) +
  (2 / V) * (∫ v in Ioc 0 A, thirdSpectralIntegrand V (1 / β ^ 2) v) +
  (1 / Real.pi) * (∫ v in Ioi A, fourthSpectralIntegrand (1 / β ^ 2) v)

/-- Exact scaling of all four terms of the original-law Prawitz envelope,
including its complex principal correction and infinite Gaussian tail. -/
theorem normalizedEnvelope_div_beta_eq_actualSpectralProfile (μ : ProbabilityMeasure ℝ)
    (n : ℕ) (β A V : ℝ) (hβ : 0 < β) (hA : 0 < A) (hAV : A ≤ V) :
    PrawitzSmoothing.normalizedEnvelope μ n (A / β) (V / β) / β =
      actualSpectralProfile μ n β A V := by
  have hV : 0 < V := hA.trans_le hAV
  let f1 : ℝ → ℝ := fun t => ‖prawitzKernel (t / (V / β))‖ *
    ‖charFun (μ : Measure ℝ) (t / Real.sqrt n) ^ n - (Real.exp (-(t ^ 2 / 2)) : ℂ)‖
  let f2 : ℝ → ℝ := fun t => ‖prawitzKernel (t / (V / β))‖ *
    ‖charFun (μ : Measure ℝ) (t / Real.sqrt n) ^ n‖
  let f3 : ℝ → ℝ := fun t =>
    ‖prawitzKernel (t / (V / β)) / ((V / β : ℝ) : ℂ) -
      Complex.I / ((2 * Real.pi * t : ℝ) : ℂ)‖ * Real.exp (-(t ^ 2 / 2))
  let f4 : ℝ → ℝ := fun t => Real.exp (-(t ^ 2 / 2)) / t
  have harg (v : ℝ) : (v / β) / (V / β) = v / V := by field_simp [hβ.ne']
  have hf1 (v : ℝ) : f1 (v / β) = β * actualFirstSpectralIntegrand μ n β V v := by
    dsimp [f1, actualFirstSpectralIntegrand, spectralKernelWeight]
    rw [harg]
    field_simp [hβ.ne']
  have hf2 (v : ℝ) : f2 (v / β) = β * actualSecondSpectralIntegrand μ n β V v := by
    dsimp [f2, actualSecondSpectralIntegrand, spectralKernelWeight]
    rw [harg]
    field_simp [hβ.ne']
  have hf3 (v : ℝ) : f3 (v / β) = (β ^ 2 / V) * thirdSpectralIntegrand V (1 / β ^ 2) v := by
    dsimp [f3, thirdSpectralIntegrand]
    rw [scaledCorrection_eq β V v hβ hV, powerExp_half_gaussian_scale β v hβ]
    field_simp [hβ.ne', hV.ne'] <;> ring
  have hf4 (v : ℝ) : f4 (v / β) = β ^ 2 * fourthSpectralIntegrand (1 / β ^ 2) v := by
    dsimp [f4, fourthSpectralIntegrand]
    rw [powerExp_half_gaussian_scale β v hβ]
    by_cases hv : v = 0
    · simp [hv]
    · field_simp [hβ.ne', hv] <;> ring
  have hI1 : (∫ t in (0 : ℝ)..A / β, f1 t) =
      ∫ v in (0 : ℝ)..A, actualFirstSpectralIntegrand μ n β V v := by
    have hh := intervalIntegral_div_scale f1 β 0 A hβ
    simp only [zero_div] at hh
    rw [hh]
    simp_rw [hf1]
    rw [intervalIntegral.integral_const_mul]
    field_simp [hβ.ne']
  have hI2 : (∫ t in A / β..V / β, f2 t) =
      ∫ v in A..V, actualSecondSpectralIntegrand μ n β V v := by
    rw [intervalIntegral_div_scale f2 β A V hβ]
    simp_rw [hf2]
    rw [intervalIntegral.integral_const_mul]
    field_simp [hβ.ne']
  have hI3 : (∫ t in (0 : ℝ)..A / β, f3 t) =
      (β / V) * ∫ v in (0 : ℝ)..A, thirdSpectralIntegrand V (1 / β ^ 2) v := by
    have hh := intervalIntegral_div_scale f3 β 0 A hβ
    simp only [zero_div] at hh
    rw [hh]
    simp_rw [hf3]
    rw [intervalIntegral.integral_const_mul]
    field_simp [hβ.ne', hV.ne']
  have hI4 : (∫ t in Ioi (A / β), f4 t) =
      β * ∫ v in Ioi A, fourthSpectralIntegrand (1 / β ^ 2) v := by
    rw [tailIntegral_div_scale f4 β A hβ]
    simp_rw [hf4]
    rw [integral_const_mul]
    field_simp [hβ.ne']
  change ((2 / (V / β)) * (∫ t in (0 : ℝ)..A / β, f1 t) +
    (2 / (V / β)) * (∫ t in A / β..V / β, f2 t) +
    2 * (∫ t in (0 : ℝ)..A / β, f3 t) +
    (1 / Real.pi) * (∫ t in Ioi (A / β), f4 t)) / β = _
  rw [hI1, hI2, hI3, hI4]
  simp only [intervalIntegral.integral_of_le hA.le, intervalIntegral.integral_of_le hAV]
  unfold actualSpectralProfile
  field_simp [hβ.ne', hV.ne', Real.pi_ne_zero]

/-- The profile still bounds the same original iid law: its first term
uses the proved coarse CF discrepancy, and its second uses the proved
same-law damping envelope.  Both actual spectral integrands are proved
integrable by domination before comparing their integrals. -/
theorem actualSpectralProfile_le_spectralProfile (μ : ProbabilityMeasure ℝ)
    (h : StandardizedLaw μ) (n N : ℕ) (hN : 0 < N) (hNn : N ≤ n)
    (hρ : rho0 ≤ thirdAbsoluteMoment μ) (A V : ℝ) (hA : 0 < A) (hAV : A ≤ V) :
    actualSpectralProfile μ n (beta μ n) A V ≤
      spectralProfile N A V (1 / beta μ n ^ 2) := by
  let β := beta μ n
  have hn : 0 < n := lt_of_lt_of_le hN hNn
  have hβ : 0 < β := CoarseHighMomentRayPrice.beta_pos μ n hn hρ
  have hV : 0 < V := hA.trans_le hAV
  have hI := profileIntegrable N hN A V (1 / β ^ 2) hA hAV (by positivity)
  have h1point (v : ℝ) (hv : 0 ≤ v) : actualFirstSpectralIntegrand μ n β V v ≤
      firstSpectralIntegrand N V (1 / β ^ 2) v := by
    have hh := CoarseHighMomentRayPrice.normalized_power_error_div_beta_le_coarsePrice
      μ h n N hN hNn hρ (v / β) (div_nonneg hv hβ.le)
    rw [coarsePrice_spectral_eq N hN β v hβ] at hh
    exact mul_le_mul_of_nonneg_left hh (norm_nonneg (prawitzKernel (v / V)))
  have h2point (v : ℝ) : actualSecondSpectralIntegrand μ n β V v ≤
      secondSpectralIntegrand V (1 / β ^ 2) v := by
    have hh := div_le_div_of_nonneg_right
      (normalized_power_le_envelope μ h n hn hρ (v / β)) hβ.le
    rw [envelope_spectral_eq β v hβ] at hh
    have he : powerExp (1 / 2) (-spectralExponent v) (1 / β ^ 2) =
        Real.exp ((1 / β ^ 2) * spectralExponent v) / β := by
      rw [powerExp_half_scale β _ hβ]
      congr 2 <;> ring
    unfold actualSecondSpectralIntegrand secondSpectralIntegrand
    rw [he, norm_pow]
    exact mul_le_mul_of_nonneg_left hh (norm_nonneg (prawitzKernel (v / V)))
  have hscaled : Measurable (fun v : ℝ => prawitzKernel (v / V)) :=
    measurable_prawitzKernel.comp (by fun_prop)
  have h1meas : Measurable (actualFirstSpectralIntegrand μ n β V) := by
    unfold actualFirstSpectralIntegrand spectralKernelWeight
    fun_prop
  have h2meas : Measurable (actualSecondSpectralIntegrand μ n β V) := by
    unfold actualSecondSpectralIntegrand spectralKernelWeight
    fun_prop
  have h1n (v : ℝ) : 0 ≤ actualFirstSpectralIntegrand μ n β V v := by
    unfold actualFirstSpectralIntegrand spectralKernelWeight
    positivity
  have h2n (v : ℝ) : 0 ≤ actualSecondSpectralIntegrand μ n β V v := by
    unfold actualSecondSpectralIntegrand spectralKernelWeight
    positivity
  have h1I : IntegrableOn (actualFirstSpectralIntegrand μ n β V) (Ioc 0 A) := by
    apply hI.first.mono' h1meas.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    simpa only [Real.norm_eq_abs, abs_of_nonneg (h1n v)] using h1point v hv.1.le
  have h2I : IntegrableOn (actualSecondSpectralIntegrand μ n β V) (Ioc A V) := by
    apply hI.second.mono' h2meas.aestronglyMeasurable
    exact ae_of_all _ (fun v => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (h2n v)] using h2point v)
  have h1int := integral_mono_ae h1I hI.first (by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    exact h1point v hv.1.le)
  have h2int := integral_mono_ae h2I hI.second (ae_of_all _ h2point)
  have h1mul := mul_le_mul_of_nonneg_left h1int (by positivity : 0 ≤ 2 / V)
  have h2mul := mul_le_mul_of_nonneg_left h2int (by positivity : 0 ≤ 2 / V)
  change actualSpectralProfile μ n β A V ≤ spectralProfile N A V (1 / β ^ 2)
  unfold actualSpectralProfile spectralProfile
  linarith only [h1mul, h2mul]

/-- Formal CDF transfer for the actual original iid law in the fixed
spectral coordinates used by the endpoint interpolation theorem. -/
theorem normalized_actual_cdf_le_beta_spectralProfile (μ : ProbabilityMeasure ℝ)
    (h : StandardizedLaw μ) (n N : ℕ) (hN : 0 < N) (hNn : N ≤ n)
    (hρ : rho0 ≤ thirdAbsoluteMoment μ) (A V : ℝ) (hA : 0 < A) (hAV : A ≤ V) (x : ℝ) :
    |(normalizedIidSumLaw μ n).real (Iic x) - GaussianTools.Phi x| ≤
      beta μ n * spectralProfile N A V (1 / beta μ n ^ 2) := by
  have hn : 0 < n := lt_of_lt_of_le hN hNn
  have hβ : 0 < beta μ n := CoarseHighMomentRayPrice.beta_pos μ n hn hρ
  have hh := div_le_div_of_nonneg_right
    (PrawitzSmoothing.normalized_actual_cdf_le μ h n hn (A / beta μ n) (V / beta μ n)
      (div_pos hA hβ) (div_le_div_of_nonneg_right hAV hβ.le) x) hβ.le
  rw [normalizedEnvelope_div_beta_eq_actualSpectralProfile μ n (beta μ n) A V hβ hA hAV] at hh
  have hm := hh.trans (actualSpectralProfile_le_spectralProfile μ h n N hN hNn hρ A V hA hAV)
  have hc := (div_le_iff₀ hβ).mp hm
  simpa only [mul_comm] using hc

theorem normalized_actual_cdf_le_const_endpoints (μ : ProbabilityMeasure ℝ)
    (h : StandardizedLaw μ) (n N : ℕ) (hN : 0 < N) (hNn : N ≤ n)
    (hρ : rho0 ≤ thirdAbsoluteMoment μ) (A V a b : ℝ) (hA : 0 < A) (hAV : A ≤ V)
    (ha : 0 < a) (hab : a < b) (hs : 1 / beta μ n ^ 2 ∈ Icc a b)
    (hbranch : (N : ℝ) / rho0 ^ 2 ≤ a) (x : ℝ) :
    |(normalizedIidSumLaw μ n).real (Iic x) - GaussianTools.Phi x| ≤
      beta μ n * (Real.exp ((3 / 2) * ((b - a) ^ 2 / (8 * a ^ 2))) *
        max (spectralProfile N A V a) (spectralProfile N A V b)) := by
  apply (normalized_actual_cdf_le_beta_spectralProfile μ h n N hN hNn hρ A V hA hAV x).trans
  have hβ := CoarseHighMomentRayPrice.beta_pos μ n (lt_of_lt_of_le hN hNn) hρ
  exact mul_le_mul_of_nonneg_left
    (spectralProfile_le_const_endpoint_max N hN A V a b (1 / beta μ n ^ 2)
      hA hAV ha hab hs hbranch) hβ.le

theorem normalized_actual_cdf_le_linear_endpoints (μ : ProbabilityMeasure ℝ)
    (h : StandardizedLaw μ) (n N : ℕ) (hN : 0 < N) (hNn : N ≤ n)
    (hρ : rho0 ≤ thirdAbsoluteMoment μ) (A V a b : ℝ) (hA : 0 < A) (hAV : A ≤ V)
    (ha : 0 < a) (hab : a < b) (hs : 1 / beta μ n ^ 2 ∈ Icc a b)
    (hbranch : b ≤ (N : ℝ) / rho0 ^ 2) (x : ℝ) :
    |(normalizedIidSumLaw μ n).real (Iic x) - GaussianTools.Phi x| ≤
      beta μ n * (Real.exp ((5 / 2) * ((b - a) ^ 2 / (8 * a ^ 2))) *
        max (spectralProfile N A V a) (spectralProfile N A V b)) := by
  apply (normalized_actual_cdf_le_beta_spectralProfile μ h n N hN hNn hρ A V hA hAV x).trans
  have hβ := CoarseHighMomentRayPrice.beta_pos μ n (lt_of_lt_of_le hN hNn) hρ
  exact mul_le_mul_of_nonneg_left
    (spectralProfile_le_linear_endpoint_max N hN A V a b (1 / beta μ n ^ 2)
      hA hAV ha hab hs hbranch) hβ.le

end BerryEsseen.RaySpectralCurvature

#print axioms BerryEsseen.RaySpectralCurvature.powerExp_curvature
#print axioms BerryEsseen.RaySpectralCurvature.envelope_spectral_eq
#print axioms BerryEsseen.RaySpectralCurvature.lossEnvelope_spectral_eq
#print axioms BerryEsseen.RaySpectralCurvature.coarseSpectralCore_const
#print axioms BerryEsseen.RaySpectralCurvature.coarseSpectralCore_linear
#print axioms BerryEsseen.RaySpectralCurvature.coarsePrice_spectral_eq
#print axioms BerryEsseen.RaySpectralCurvature.spectralProfile_endpoint_const
#print axioms BerryEsseen.RaySpectralCurvature.spectralProfile_endpoint_linear
#print axioms BerryEsseen.RaySpectralCurvature.profileIntegrable
#print axioms BerryEsseen.RaySpectralCurvature.spectralProfile_le_const_endpoint_max
#print axioms BerryEsseen.RaySpectralCurvature.spectralProfile_le_linear_endpoint_max
#print axioms BerryEsseen.RaySpectralCurvature.normalizedEnvelope_div_beta_eq_actualSpectralProfile
#print axioms BerryEsseen.RaySpectralCurvature.normalized_actual_cdf_le_beta_spectralProfile
#print axioms BerryEsseen.RaySpectralCurvature.normalized_actual_cdf_le_const_endpoints
#print axioms BerryEsseen.RaySpectralCurvature.normalized_actual_cdf_le_linear_endpoints
