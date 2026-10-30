module

public import BerryEsseen.RaySpectralCurvature
public import BerryEsseen.CoefficientRayPrice

@[expose] public section

/-! 2026-10-29: keep the moment coefficient c fixed on each spectral node.
The spectral exponent changes with c, while the loss, its switch, the
power-exponential kernels, Prawitz weights, Gaussian terms and logarithmic
endpoint interpolation are reused from RaySpectralCurvature.

The analytic profile is defined for every real c.  Its actual-law CDF
theorems require the genuine coefficient inequality rho+1 <= c*rho; the
node wrappers derive that inequality from n>=N and the upper s endpoint.
No numerical endpoint value or all-ray numerical constant is asserted. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Interval Topology

namespace BerryEsseen.CoefficientRaySpectral

open HighMomentRayDamping
open RaySpectralCurvature (powerExp powerExp_eq_rpow powerExp_half_scale scaled_one_half
  spectralLoss spectralLoss_eq_scaled_loss spectralLoss_eq_const spectralLoss_eq_linear
  spectralLoss_nonneg spectralLoss_le_self spectralKernelWeight spectralCorrectionWeight
  spectralKernelWeight_le thirdSpectralIntegrand fourthSpectralIntegrand sliceCoefficient
  linearCoreWeights_nonneg KernelEndpointBound kernelEndpointBound_log_chord
  actualFirstSpectralIntegrand actualSecondSpectralIntegrand actualSpectralProfile
  normalizedEnvelope_div_beta_eq_actualSpectralProfile)
open Causalean.Stat.CLT.BerryEsseen (prawitzKernel)

def spectralExponent (c v : ℝ) : ℝ :=
  min 0 (min (CoefficientRayPrice.exponent c (1 / 2) (1 / 10) 1 v)
    (min (CoefficientRayPrice.exponent c ClassicalCosineCubic.a ClassicalCosineCubic.b 1 v)
      (CoefficientRayPrice.exponent c ClassicalRationalCosine.a ClassicalRationalCosine.b 1 v)))

lemma spectralExponent_nonpos (c v : ℝ) : spectralExponent c v ≤ 0 := min_le_left _ _

lemma continuous_spectralExponent (c : ℝ) : Continuous (spectralExponent c) := by
  unfold spectralExponent CoefficientRayPrice.exponent
  fun_prop

private lemma exp_min (x y : ℝ) : Real.exp (min x y) = min (Real.exp x) (Real.exp y) := by
  rcases le_total x y with h | h
  · rw [min_eq_left h, min_eq_left (Real.exp_le_exp.mpr h)]
  · rw [min_eq_right h, min_eq_right (Real.exp_le_exp.mpr h)]

private lemma exponent_scale (c a b β v : ℝ) (hβ : 0 < β) :
    CoefficientRayPrice.exponent c a b β (v / β) =
      (1 / β ^ 2) * CoefficientRayPrice.exponent c a b 1 v := by
  unfold CoefficientRayPrice.exponent
  rw [abs_div, abs_of_pos hβ, div_pow, div_pow]
  field_simp [hβ.ne']

theorem envelope_spectral_eq (c β v : ℝ) (hβ : 0 < β) :
    CoefficientRayPrice.envelope c β (v / β) = Real.exp ((1 / β ^ 2) * spectralExponent c v) := by
  unfold CoefficientRayPrice.envelope spectralExponent
  rw [mul_min_of_nonneg _ _ (by positivity : 0 ≤ 1 / β ^ 2), mul_zero,
    mul_min_of_nonneg _ _ (by positivity : 0 ≤ 1 / β ^ 2),
    mul_min_of_nonneg _ _ (by positivity : 0 ≤ 1 / β ^ 2)]
  simp only [exp_min, Real.exp_zero]
  rw [exponent_scale _ _ _ _ _ hβ, exponent_scale _ _ _ _ _ hβ,
    exponent_scale _ _ _ _ _ hβ]

theorem lossEnvelope_spectral_eq (N : ℕ) (hN : 0 < N) (c β v : ℝ) (hβ : 0 < β) :
    CoefficientRayPrice.lossEnvelope N c β (v / β) =
      Real.exp (((1 / β ^ 2) - spectralLoss N (1 / β ^ 2)) * spectralExponent c v) := by
  have he : 0 ≤ 1 - loss N β := sub_nonneg.mpr (loss_le_one N hN β)
  have hs : 0 ≤ (1 - loss N β) * (1 / β ^ 2) := mul_nonneg he (by positivity)
  rw [spectralLoss_eq_scaled_loss N β hβ]
  have hid : (1 / β ^ 2 - 1 / β ^ 2 * loss N β) = (1 - loss N β) * (1 / β ^ 2) := by ring
  rw [hid]
  unfold CoefficientRayPrice.lossEnvelope spectralExponent
  rw [mul_min_of_nonneg _ _ hs, mul_zero, mul_min_of_nonneg _ _ hs, mul_min_of_nonneg _ _ hs]
  simp only [exp_min, Real.exp_zero]
  rw [exponent_scale _ _ _ _ _ hβ, exponent_scale _ _ _ _ _ hβ,
    exponent_scale _ _ _ _ _ hβ]
  simp only [mul_assoc]

def spectralRate (c v w : ℝ) : ℝ := (v ^ 2 - w ^ 2) / 2 - spectralExponent c w

def linearSpectralRate (N : ℕ) (c v w : ℝ) : ℝ :=
  (v ^ 2 - w ^ 2) / 2 - (1 - 1 / (N : ℝ)) * spectralExponent c w

def coarseSpectralCore (N : ℕ) (c s v w : ℝ) : ℝ :=
  s ^ (3 / 2 : ℝ) *
    Real.exp (-s * spectralRate c v w - spectralLoss N s * spectralExponent c w) *
    (w ^ 2 / 2 + spectralLoss N s * w ^ 3 / 3)

theorem coarseSpectralCore_const (N : ℕ) (hN : 0 < N) (c s v w : ℝ) (hs : 0 < s)
    (hbranch : (N : ℝ) / rho0 ^ 2 ≤ s) :
    coarseSpectralCore N c s v w =
      (Real.exp (-(1 / rho0 ^ 2) * spectralExponent c w) *
        (w ^ 2 / 2 + (1 / rho0 ^ 2) * w ^ 3 / 3)) *
      powerExp (3 / 2) (spectralRate c v w) s := by
  rw [coarseSpectralCore, spectralLoss_eq_const N hN s hbranch, powerExp_eq_rpow _ _ _ hs]
  rw [sub_eq_add_neg, Real.exp_add]
  ring

theorem coarseSpectralCore_linear (N : ℕ) (hN : 0 < N) (c s v w : ℝ) (hs : 0 < s)
    (hbranch : s ≤ (N : ℝ) / rho0 ^ 2) :
    coarseSpectralCore N c s v w =
      (w ^ 2 / 2) * powerExp (3 / 2) (linearSpectralRate N c v w) s +
      (w ^ 3 / (3 * (N : ℝ))) * powerExp (5 / 2) (linearSpectralRate N c v w) s := by
  rw [coarseSpectralCore, spectralLoss_eq_linear N hN s hbranch,
    powerExp_eq_rpow _ _ _ hs, powerExp_eq_rpow _ _ _ hs]
  have he : -s * spectralRate c v w - s / (N : ℝ) * spectralExponent c w =
      -s * linearSpectralRate N c v w := by unfold spectralRate linearSpectralRate; ring
  rw [he]
  have hp : s ^ (5 / 2 : ℝ) = s ^ (3 / 2 : ℝ) * s := by
    convert Real.rpow_add_one hs.ne' (3 / 2) using 1 <;> norm_num
  rw [hp]
  ring

private lemma scaled_three_halves (β : ℝ) (hβ : 0 < β) :
    (1 / β ^ 2) ^ (3 / 2 : ℝ) = 1 / β ^ 3 := by
  have hh := Real.rpow_mul_natCast (by positivity : 0 ≤ 1 / β ^ 2) (1 / 2) 3
  norm_num only [Nat.cast_ofNat] at hh
  convert hh.trans (by rw [scaled_one_half β hβ, div_pow, one_pow]) using 1 <;> norm_num

private lemma lambda_spectral (N : ℕ) (β : ℝ) (hβ : 0 < β) :
    CoarseHighMomentRayPrice.lambda N β = β * spectralLoss N (1 / β ^ 2) := by
  rw [spectralLoss_eq_scaled_loss N β hβ, ← CoarseHighMomentRayPrice.loss_div_eq_lambda N β hβ]
  field_simp [hβ.ne']

theorem coarsePrice_spectral_eq (N : ℕ) (hN : 0 < N) (c β v : ℝ) (hβ : 0 < β) :
    CoefficientRayPrice.coarsePrice N c β (v / β) =
      ∫ w in (0 : ℝ)..v, coarseSpectralCore N c (1 / β ^ 2) v w := by
  have hsub := intervalIntegral.integral_comp_div (a := (0 : ℝ)) (b := v)
    (CoefficientRayPrice.coarseIntegrand N c β) hβ.ne'
  simp only [zero_div, smul_eq_mul] at hsub
  have hchange : (∫ u in (0 : ℝ)..v / β, CoefficientRayPrice.coarseIntegrand N c β u) =
      (1 / β) * ∫ w in (0 : ℝ)..v, CoefficientRayPrice.coarseIntegrand N c β (w / β) := by
    rw [hsub]
    field_simp [hβ.ne']
  unfold CoefficientRayPrice.coarsePrice
  rw [hchange, ← mul_assoc, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro w _
  unfold CoefficientRayPrice.coarseIntegrand coarseSpectralCore
  dsimp only
  rw [lossEnvelope_spectral_eq N hN c β w hβ, lambda_spectral N β hβ, scaled_three_halves β hβ]
  have he : Real.exp (-((v / β) ^ 2 / 2)) * Real.exp ((w / β) ^ 2 / 2) *
      Real.exp ((1 / β ^ 2 - spectralLoss N (1 / β ^ 2)) * spectralExponent c w) =
      Real.exp (-(1 / β ^ 2) * spectralRate c v w -
        spectralLoss N (1 / β ^ 2) * spectralExponent c w) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    unfold spectralRate
    field_simp [hβ.ne'] <;> ring
  calc
    _ = (1 / β ^ 3) *
        (Real.exp (-((v / β) ^ 2 / 2)) * Real.exp ((w / β) ^ 2 / 2) *
          Real.exp ((1 / β ^ 2 - spectralLoss N (1 / β ^ 2)) * spectralExponent c w)) *
        (w ^ 2 / 2 + spectralLoss N (1 / β ^ 2) * w ^ 3 / 3) := by field_simp [hβ.ne']
    _ = _ := by rw [he]

def coarseSpectralSlice (N : ℕ) (c s v : ℝ) : ℝ := ∫ w in (0 : ℝ)..v, coarseSpectralCore N c s v w

def firstSpectralIntegrand (N : ℕ) (c V s v : ℝ) : ℝ :=
  spectralKernelWeight V v * coarseSpectralSlice N c s v

def secondSpectralIntegrand (c V s v : ℝ) : ℝ :=
  spectralKernelWeight V v * powerExp (1 / 2) (-spectralExponent c v) s

def spectralProfile (N : ℕ) (c A V s : ℝ) : ℝ :=
  (2 / V) * (∫ v in Ioc 0 A, firstSpectralIntegrand N c V s v) +
  (2 / V) * (∫ v in Ioc A V, secondSpectralIntegrand c V s v) +
  (2 / V) * (∫ v in Ioc 0 A, thirdSpectralIntegrand V s v) +
  (1 / Real.pi) * (∫ v in Ioi A, fourthSpectralIntegrand s v)

structure ProfileIntegrable (N : ℕ) (c A V s : ℝ) : Prop where
  first : IntegrableOn (firstSpectralIntegrand N c V s) (Ioc 0 A)
  second : IntegrableOn (secondSpectralIntegrand c V s) (Ioc A V)
  third : IntegrableOn (thirdSpectralIntegrand V s) (Ioc 0 A)
  fourth : IntegrableOn (fourthSpectralIntegrand s) (Ioi A)

lemma coarseSpectralCore_nonneg (N : ℕ) (c s v w : ℝ) (hs : 0 ≤ s) (hw : 0 ≤ w) :
    0 ≤ coarseSpectralCore N c s v w := by
  unfold coarseSpectralCore spectralLoss
  positivity

lemma continuous_coarseSpectralCore (N : ℕ) (c s v : ℝ) : Continuous (coarseSpectralCore N c s v) := by
  unfold coarseSpectralCore spectralRate spectralExponent CoefficientRayPrice.exponent
  fun_prop

lemma coarseSpectralSlice_nonneg (N : ℕ) (c s v : ℝ) (hs : 0 ≤ s) (hv : 0 ≤ v) :
    0 ≤ coarseSpectralSlice N c s v := by
  apply intervalIntegral.integral_nonneg hv
  intro w hw
  exact coarseSpectralCore_nonneg N c s v w hs hw.1

lemma continuous_coarseSpectralSlice (N : ℕ) (hN : 0 < N) (c s : ℝ) (hs : 0 < s) :
    Continuous (coarseSpectralSlice N c s) := by
  let β : ℝ := 1 / Real.sqrt s
  have hβ : 0 < β := div_pos zero_lt_one (Real.sqrt_pos.mpr hs)
  have hid : 1 / β ^ 2 = s := by
    dsimp [β]
    rw [div_pow, one_pow, one_div_div, Real.sq_sqrt hs.le, div_one]
  have heq : coarseSpectralSlice N c s =
      (fun v : ℝ => CoefficientRayPrice.coarsePrice N c β (v / β)) := by
    funext v
    rw [coarsePrice_spectral_eq N hN c β v hβ, hid]
    rfl
  rw [heq]
  exact (CoefficientRayPrice.continuous_coarsePrice N c β).comp (by fun_prop)

private lemma measurable_spectralKernelWeight (V : ℝ) : Measurable (spectralKernelWeight V) := by
  have heq : spectralKernelWeight V = RaySpectralCurvature.secondSpectralIntegrand V 0 := by
    funext v
    simp only [RaySpectralCurvature.secondSpectralIntegrand, powerExp, Real.log_zero,
      mul_zero, zero_mul, sub_zero, Real.exp_zero, mul_one]
  rw [heq]
  exact RaySpectralCurvature.measurable_secondSpectralIntegrand V 0

lemma measurable_firstSpectralIntegrand (N : ℕ) (hN : 0 < N) (c V s : ℝ) (hs : 0 < s) :
    Measurable (firstSpectralIntegrand N c V s) :=
  (measurable_spectralKernelWeight V).mul (continuous_coarseSpectralSlice N hN c s hs).measurable

lemma measurable_secondSpectralIntegrand (c V s : ℝ) : Measurable (secondSpectralIntegrand c V s) := by
  have hk := measurable_spectralKernelWeight V
  unfold secondSpectralIntegrand powerExp spectralExponent CoefficientRayPrice.exponent
  fun_prop

/-- The singular-cell majorant does not depend on c: g_c<=0 and s-d>=0
make the complete coarse exponential at most one. -/
lemma coarseSpectralCore_le_quadratic (N : ℕ) (hN : 0 < N) (c A s v w : ℝ)
    (hs : 0 ≤ s) (hw : 0 ≤ w) (hwv : w ≤ v) (hvA : v ≤ A) :
    coarseSpectralCore N c s v w ≤ sliceCoefficient N A s * w ^ 2 := by
  have hd := spectralLoss_nonneg N s hs
  have hds := spectralLoss_le_self N hN s hs
  have hvw : 0 ≤ v ^ 2 - w ^ 2 := by nlinarith
  have hg := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hds) (spectralExponent_nonpos c w)
  have harg : -s * spectralRate c v w - spectralLoss N s * spectralExponent c w ≤ 0 := by
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

lemma coarseSpectralSlice_le_cubic (N : ℕ) (hN : 0 < N) (c A s v : ℝ)
    (hs : 0 ≤ s) (hv : 0 ≤ v) (hvA : v ≤ A) :
    coarseSpectralSlice N c s v ≤ sliceCoefficient N A s * v ^ 3 / 3 := by
  have hc := continuous_coarseSpectralCore N c s v
  have hp : Continuous (fun w : ℝ => sliceCoefficient N A s * w ^ 2) := by fun_prop
  have hh := intervalIntegral.integral_mono_on (μ := volume) hv
    (hc.intervalIntegrable 0 v) (hp.intervalIntegrable 0 v)
    (fun w hw => coarseSpectralCore_le_quadratic N hN c A s v w hs hw.1 hw.2 hvA)
  unfold coarseSpectralSlice
  convert hh using 1
  rw [intervalIntegral.integral_const_mul, integral_pow]
  norm_num
  ring

theorem profileIntegrable (N : ℕ) (hN : 0 < N) (c A V s : ℝ)
    (hA : 0 < A) (hAV : A ≤ V) (hs : 0 < s) : ProfileIntegrable N c A V s := by
  have hV : 0 < V := hA.trans_le hAV
  have hOld := RaySpectralCurvature.profileIntegrable N hN A V s hA hAV hs
  refine ⟨?_, ?_, hOld.third, hOld.fourth⟩
  · have hp : Continuous (fun v : ℝ =>
        (sliceCoefficient N A s / 3) * (V / (2 * Real.pi) * v ^ 2 + v ^ 3 / 2)) := by fun_prop
    apply (hp.intervalIntegrable 0 A).1.mono'
      (measurable_firstSpectralIntegrand N hN c V s hs).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    have hn := mul_nonneg (norm_nonneg (prawitzKernel (v / V)))
      (coarseSpectralSlice_nonneg N c s v hs.le hv.1.le)
    unfold firstSpectralIntegrand spectralKernelWeight
    rw [Real.norm_eq_abs, abs_of_nonneg hn]
    have hh := mul_le_mul (spectralKernelWeight_le V v hV hv.1 (hv.2.trans hAV))
      (coarseSpectralSlice_le_cubic N hN c A s v hs.le hv.1.le hv.2)
      (coarseSpectralSlice_nonneg N c s v hs.le hv.1.le) (by
        have hvpos : 0 < v := hv.1
        positivity)
    calc
      _ ≤ (V / (2 * Real.pi) / v + 1 / 2) * (sliceCoefficient N A s * v ^ 3 / 3) := by
        simpa only [spectralKernelWeight] using hh
      _ = _ := by field_simp [hv.1.ne']
  · have hkI : IntegrableOn (spectralKernelWeight V) (Ioc A V) := by
      apply (intervalIntegrable_const (c := V / (2 * Real.pi) / A + 1 / 2)
        (a := A) (b := V) (μ := volume)).1.mono' (measurable_spectralKernelWeight V).aestronglyMeasurable
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
      rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ spectralKernelWeight V v from norm_nonneg _)]
      exact (spectralKernelWeight_le V v hV (hA.trans hv.1) hv.2).trans (by gcongr; exact hv.1.le)
    have hp : Continuous (fun v : ℝ => powerExp (1 / 2) (-spectralExponent c v) s) := by
      unfold powerExp spectralExponent CoefficientRayPrice.exponent
      fun_prop
    exact hkI.mul_continuousOn_of_subset hp.continuousOn measurableSet_Ioc isCompact_Icc Ioc_subset_Icc_self

theorem coarseSpectralCore_endpoint_const (N : ℕ) (hN : 0 < N)
    (c a b s E l r v w : ℝ) (ha : 0 < a) (hb : 0 < b) (hs : 0 < s) (hw : 0 ≤ w)
    (hba : (N : ℝ) / rho0 ^ 2 ≤ a) (hbb : (N : ℝ) / rho0 ^ 2 ≤ b)
    (hbs : (N : ℝ) / rho0 ^ 2 ≤ s) (hk : KernelEndpointBound a b s E l r (3 / 2)) :
    coarseSpectralCore N c s v w ≤
      E * (l * coarseSpectralCore N c a v w + r * coarseSpectralCore N c b v w) := by
  rw [coarseSpectralCore_const N hN c s v w hs hbs,
    coarseSpectralCore_const N hN c a v w ha hba, coarseSpectralCore_const N hN c b v w hb hbb]
  have hc : 0 ≤ Real.exp (-(1 / rho0 ^ 2) * spectralExponent c w) *
      (w ^ 2 / 2 + (1 / rho0 ^ 2) * w ^ 3 / 3) := by positivity
  have hh := mul_le_mul_of_nonneg_left
    (hk (3 / 2) (spectralRate c v w) (by norm_num) le_rfl) hc
  convert hh using 1 <;> ring

theorem coarseSpectralCore_endpoint_linear (N : ℕ) (hN : 0 < N)
    (c a b s E l r v w : ℝ) (ha : 0 < a) (hb : 0 < b) (hs : 0 < s) (hw : 0 ≤ w)
    (hba : a ≤ (N : ℝ) / rho0 ^ 2) (hbb : b ≤ (N : ℝ) / rho0 ^ 2)
    (hbs : s ≤ (N : ℝ) / rho0 ^ 2) (hk : KernelEndpointBound a b s E l r (5 / 2)) :
    coarseSpectralCore N c s v w ≤
      E * (l * coarseSpectralCore N c a v w + r * coarseSpectralCore N c b v w) := by
  rw [coarseSpectralCore_linear N hN c s v w hs hbs,
    coarseSpectralCore_linear N hN c a v w ha hba, coarseSpectralCore_linear N hN c b v w hb hbb]
  obtain ⟨hc1, hc2⟩ := linearCoreWeights_nonneg N w hw
  have hh1 := mul_le_mul_of_nonneg_left
    (hk (3 / 2) (linearSpectralRate N c v w) (by norm_num) (by norm_num)) hc1
  have hh2 := mul_le_mul_of_nonneg_left
    (hk (5 / 2) (linearSpectralRate N c v w) (by norm_num) le_rfl) hc2
  convert add_le_add hh1 hh2 using 1 <;> ring

theorem coarseSpectralSlice_endpoint (N : ℕ) (c a b s E l r v : ℝ) (hv : 0 ≤ v)
    (hc : ∀ w, 0 ≤ w → w ≤ v → coarseSpectralCore N c s v w ≤
      E * (l * coarseSpectralCore N c a v w + r * coarseSpectralCore N c b v w)) :
    coarseSpectralSlice N c s v ≤
      E * (l * coarseSpectralSlice N c a v + r * coarseSpectralSlice N c b v) := by
  have hca := continuous_coarseSpectralCore N c a v
  have hcb := continuous_coarseSpectralCore N c b v
  have hcs := continuous_coarseSpectralCore N c s v
  have hcd := ((hca.const_mul l).add (hcb.const_mul r)).const_mul E
  have hh := intervalIntegral.integral_mono_on (μ := volume) hv (hcs.intervalIntegrable 0 v)
    (hcd.intervalIntegrable 0 v) (fun w hw => hc w hw.1 hw.2)
  unfold coarseSpectralSlice
  convert hh using 1
  simp only [Pi.add_apply]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add ((hca.const_mul l).intervalIntegrable 0 v)
      ((hcb.const_mul r).intervalIntegrable 0 v), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]

private theorem integral_endpoint_le {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f fa fb : α → ℝ) (E l r : ℝ)
    (hfs : Integrable f μ) (hfa : Integrable fa μ) (hfb : Integrable fb μ)
    (hle : ∀ᵐ x ∂μ, f x ≤ E * (l * fa x + r * fb x)) :
    (∫ x, f x ∂μ) ≤ E * (l * (∫ x, fa x ∂μ) + r * (∫ x, fb x ∂μ)) := by
  have hd : Integrable (fun x => E * (l * fa x + r * fb x)) μ :=
    ((hfa.const_mul l).add (hfb.const_mul r)).const_mul E
  have hh := integral_mono_ae hfs hd hle
  simpa only [integral_const_mul, integral_add (hfa.const_mul l) (hfb.const_mul r)] using hh

theorem spectralProfile_endpoint_of_core (N : ℕ) (hN : 0 < N)
    (c A V a b s E l r : ℝ) (hA : 0 < A) (hAV : A ≤ V)
    (ha : 0 < a) (hb : 0 < b) (hs : 0 < s)
    (hc : ∀ v w : ℝ, 0 ≤ v → 0 ≤ w → w ≤ v →
      coarseSpectralCore N c s v w ≤ E *
        (l * coarseSpectralCore N c a v w + r * coarseSpectralCore N c b v w))
    (hk : ∀ R : ℝ, powerExp (1 / 2) R s ≤
      E * (l * powerExp (1 / 2) R a + r * powerExp (1 / 2) R b)) :
    spectralProfile N c A V s ≤
      E * (l * spectralProfile N c A V a + r * spectralProfile N c A V b) := by
  have hV : 0 < V := hA.trans_le hAV
  have hIa := profileIntegrable N hN c A V a hA hAV ha
  have hIb := profileIntegrable N hN c A V b hA hAV hb
  have hIs := profileIntegrable N hN c A V s hA hAV hs
  have h1 := integral_endpoint_le (volume.restrict (Ioc 0 A))
    (firstSpectralIntegrand N c V s) (firstSpectralIntegrand N c V a)
    (firstSpectralIntegrand N c V b) E l r hIs.first hIa.first hIb.first (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
      have hslice := coarseSpectralSlice_endpoint N c a b s E l r v hv.1.le
        (fun w hw hwv => hc v w hv.1.le hw hwv)
      have hh := mul_le_mul_of_nonneg_left hslice (norm_nonneg (prawitzKernel (v / V)))
      unfold firstSpectralIntegrand spectralKernelWeight
      convert hh using 1 <;> ring)
  have h2 := integral_endpoint_le (volume.restrict (Ioc A V))
    (secondSpectralIntegrand c V s) (secondSpectralIntegrand c V a)
    (secondSpectralIntegrand c V b) E l r hIs.second hIa.second hIb.second (ae_of_all _ (fun v => by
      have hh := mul_le_mul_of_nonneg_left (hk (-spectralExponent c v))
        (norm_nonneg (prawitzKernel (v / V)))
      unfold secondSpectralIntegrand spectralKernelWeight
      convert hh using 1 <;> ring))
  have h3 := integral_endpoint_le (volume.restrict (Ioc 0 A))
    (thirdSpectralIntegrand V s) (thirdSpectralIntegrand V a)
    (thirdSpectralIntegrand V b) E l r hIs.third hIa.third hIb.third (ae_of_all _ (fun v => by
      have hh := mul_le_mul_of_nonneg_left (hk (v ^ 2 / 2))
        (norm_nonneg (prawitzKernel (v / V) -
          Complex.I / ((2 * Real.pi * (v / V) : ℝ) : ℂ)))
      unfold thirdSpectralIntegrand spectralCorrectionWeight
      convert hh using 1 <;> ring))
  have h4 := integral_endpoint_le (volume.restrict (Ioi A))
    (fourthSpectralIntegrand s) (fourthSpectralIntegrand a)
    (fourthSpectralIntegrand b) E l r hIs.fourth hIa.fourth hIb.fourth (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      have hh := div_le_div_of_nonneg_right (hk (v ^ 2 / 2)) (hA.trans hv).le
      unfold fourthSpectralIntegrand
      convert hh using 1 <;> ring)
  have h1' := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 2 / V)
  have h2' := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ 2 / V)
  have h3' := mul_le_mul_of_nonneg_left h3 (by positivity : 0 ≤ 2 / V)
  have h4' := mul_le_mul_of_nonneg_left h4 (by positivity : 0 ≤ 1 / Real.pi)
  convert add_le_add (add_le_add (add_le_add h1' h2') h3') h4' using 1 <;>
    unfold spectralProfile <;> ring

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
    (c A V a b s : ℝ) (hA : 0 < A) (hAV : A ≤ V) (ha : 0 < a) (hab : a < b)
    (hs : s ∈ Icc a b) (hbranch : (N : ℝ) / rho0 ^ 2 ≤ a) :
    spectralProfile N c A V s ≤ Real.exp ((3 / 2) * ((b - a) ^ 2 / (8 * a ^ 2))) *
      max (spectralProfile N c A V a) (spectralProfile N c A V b) := by
  have hk := kernelEndpointBound_log_chord a b s (3 / 2) ha hab hs
  have hm := spectralProfile_endpoint_of_core N hN c A V a b s _ _ _ hA hAV
    ha (ha.trans hab) (ha.trans_le hs.1)
    (fun v w _ hw _ => coarseSpectralCore_endpoint_const N hN c a b s _ _ _ v w
      ha (ha.trans hab) (ha.trans_le hs.1) hw hbranch (hbranch.trans hab.le)
      (hbranch.trans hs.1) hk) (fun R => hk (1 / 2) R (by norm_num) (by norm_num))
  apply hm.trans
  exact mul_le_mul_of_nonneg_left (endpoint_mixture_le_max a b s _ _ hab hs) (Real.exp_pos _).le

theorem spectralProfile_le_linear_endpoint_max (N : ℕ) (hN : 0 < N)
    (c A V a b s : ℝ) (hA : 0 < A) (hAV : A ≤ V) (ha : 0 < a) (hab : a < b)
    (hs : s ∈ Icc a b) (hbranch : b ≤ (N : ℝ) / rho0 ^ 2) :
    spectralProfile N c A V s ≤ Real.exp ((5 / 2) * ((b - a) ^ 2 / (8 * a ^ 2))) *
      max (spectralProfile N c A V a) (spectralProfile N c A V b) := by
  have hk := kernelEndpointBound_log_chord a b s (5 / 2) ha hab hs
  have hm := spectralProfile_endpoint_of_core N hN c A V a b s _ _ _ hA hAV
    ha (ha.trans hab) (ha.trans_le hs.1)
    (fun v w _ hw _ => coarseSpectralCore_endpoint_linear N hN c a b s _ _ _ v w
      ha (ha.trans hab) (ha.trans_le hs.1) hw (hab.le.trans hbranch) hbranch
      (hs.2.trans hbranch) hk) (fun R => hk (1 / 2) R (by norm_num) (by norm_num))
  apply hm.trans
  exact mul_le_mul_of_nonneg_left (endpoint_mixture_le_max a b s _ _ hab hs) (Real.exp_pos _).le

theorem actualSpectralProfile_le_spectralProfile (μ : ProbabilityMeasure ℝ)
    (h : StandardizedLaw μ) (n N : ℕ) (hN : 0 < N) (hNn : N ≤ n)
    (hρ : rho0 ≤ thirdAbsoluteMoment μ) (c : ℝ)
    (hC : thirdAbsoluteMoment μ + 1 ≤ c * thirdAbsoluteMoment μ)
    (A V : ℝ) (hA : 0 < A) (hAV : A ≤ V) :
    actualSpectralProfile μ n (beta μ n) A V ≤
      spectralProfile N c A V (1 / beta μ n ^ 2) := by
  let β := beta μ n
  have hn : 0 < n := lt_of_lt_of_le hN hNn
  have hβ : 0 < β := CoarseHighMomentRayPrice.beta_pos μ n hn hρ
  have hV : 0 < V := hA.trans_le hAV
  have hI := profileIntegrable N hN c A V (1 / β ^ 2) hA hAV (by positivity)
  have h1point (v : ℝ) (hv : 0 ≤ v) : actualFirstSpectralIntegrand μ n β V v ≤
      firstSpectralIntegrand N c V (1 / β ^ 2) v := by
    have hh := CoefficientRayPrice.normalized_power_error_div_beta_le_coarsePrice
      μ h n N hN hNn hρ c hC (v / β) (div_nonneg hv hβ.le)
    rw [coarsePrice_spectral_eq N hN c β v hβ] at hh
    exact mul_le_mul_of_nonneg_left hh (norm_nonneg (prawitzKernel (v / V)))
  have h2point (v : ℝ) : actualSecondSpectralIntegrand μ n β V v ≤
      secondSpectralIntegrand c V (1 / β ^ 2) v := by
    have hh := div_le_div_of_nonneg_right
      (CoefficientRayPrice.normalized_power_le_envelope μ h n hn c hC (v / β)) hβ.le
    rw [envelope_spectral_eq c β v hβ] at hh
    have he : powerExp (1 / 2) (-spectralExponent c v) (1 / β ^ 2) =
        Real.exp ((1 / β ^ 2) * spectralExponent c v) / β := by
      rw [powerExp_half_scale β _ hβ]
      congr 2 <;> ring
    unfold actualSecondSpectralIntegrand secondSpectralIntegrand
    rw [he, norm_pow]
    exact mul_le_mul_of_nonneg_left hh (norm_nonneg (prawitzKernel (v / V)))
  have hk := measurable_spectralKernelWeight V
  have h1meas : Measurable (actualFirstSpectralIntegrand μ n β V) := by
    unfold actualFirstSpectralIntegrand
    fun_prop
  have h2meas : Measurable (actualSecondSpectralIntegrand μ n β V) := by
    unfold actualSecondSpectralIntegrand
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
  change actualSpectralProfile μ n β A V ≤ spectralProfile N c A V (1 / β ^ 2)
  unfold actualSpectralProfile spectralProfile
  linarith only [h1mul, h2mul]

/-- The old exact four-term rescaling is coefficient-independent and is
reused here; the new coefficient enters only the genuine CF comparisons. -/
theorem normalized_actual_cdf_le_beta_spectralProfile (μ : ProbabilityMeasure ℝ)
    (h : StandardizedLaw μ) (n N : ℕ) (hN : 0 < N) (hNn : N ≤ n)
    (hρ : rho0 ≤ thirdAbsoluteMoment μ) (c : ℝ)
    (hC : thirdAbsoluteMoment μ + 1 ≤ c * thirdAbsoluteMoment μ)
    (A V : ℝ) (hA : 0 < A) (hAV : A ≤ V) (x : ℝ) :
    |(normalizedIidSumLaw μ n).real (Iic x) - GaussianTools.Phi x| ≤
      beta μ n * spectralProfile N c A V (1 / beta μ n ^ 2) := by
  have hn : 0 < n := lt_of_lt_of_le hN hNn
  have hβ : 0 < beta μ n := CoarseHighMomentRayPrice.beta_pos μ n hn hρ
  have hh := div_le_div_of_nonneg_right
    (PrawitzSmoothing.normalized_actual_cdf_le μ h n hn (A / beta μ n) (V / beta μ n)
      (div_pos hA hβ) (div_le_div_of_nonneg_right hAV hβ.le) x) hβ.le
  rw [normalizedEnvelope_div_beta_eq_actualSpectralProfile μ n (beta μ n) A V hβ hA hAV] at hh
  have hm := hh.trans (actualSpectralProfile_le_spectralProfile μ h n N hN hNn hρ c hC A V hA hAV)
  have hc := (div_le_iff₀ hβ).mp hm
  simpa only [mul_comm] using hc

/-- Exact canonical coefficient for a node whose upper spectral endpoint
is b.  Numerical endpoints may use any proved upper bound for this value. -/
def nodeCoefficient (N : ℕ) (b : ℝ) : ℝ :=
  min CoefficientRayPrice.oldCoefficient (1 + Real.sqrt (b / (N : ℝ)))

theorem normalized_actual_cdf_le_node_const_endpoints (μ : ProbabilityMeasure ℝ)
    (h : StandardizedLaw μ) (n N : ℕ) (hN : 0 < N) (hNn : N ≤ n)
    (hρ : rho0 ≤ thirdAbsoluteMoment μ) (c A V a b : ℝ)
    (hc : nodeCoefficient N b ≤ c) (hA : 0 < A) (hAV : A ≤ V)
    (ha : 0 < a) (hab : a < b) (hs : 1 / beta μ n ^ 2 ∈ Icc a b)
    (hbranch : (N : ℝ) / rho0 ^ 2 ≤ a) (x : ℝ) :
    |(normalizedIidSumLaw μ n).real (Iic x) - GaussianTools.Phi x| ≤
      beta μ n * (Real.exp ((3 / 2) * ((b - a) ^ 2 / (8 * a ^ 2))) *
        max (spectralProfile N c A V a) (spectralProfile N c A V b)) := by
  have hC := CoefficientRayPrice.node_coefficient_qualifies μ n N hN hNn hρ a b c ha hs.1 hs.2 hc
  apply (normalized_actual_cdf_le_beta_spectralProfile μ h n N hN hNn hρ c hC A V hA hAV x).trans
  have hβ := CoarseHighMomentRayPrice.beta_pos μ n (lt_of_lt_of_le hN hNn) hρ
  exact mul_le_mul_of_nonneg_left
    (spectralProfile_le_const_endpoint_max N hN c A V a b (1 / beta μ n ^ 2)
      hA hAV ha hab hs hbranch) hβ.le

theorem normalized_actual_cdf_le_node_linear_endpoints (μ : ProbabilityMeasure ℝ)
    (h : StandardizedLaw μ) (n N : ℕ) (hN : 0 < N) (hNn : N ≤ n)
    (hρ : rho0 ≤ thirdAbsoluteMoment μ) (c A V a b : ℝ)
    (hc : nodeCoefficient N b ≤ c) (hA : 0 < A) (hAV : A ≤ V)
    (ha : 0 < a) (hab : a < b) (hs : 1 / beta μ n ^ 2 ∈ Icc a b)
    (hbranch : b ≤ (N : ℝ) / rho0 ^ 2) (x : ℝ) :
    |(normalizedIidSumLaw μ n).real (Iic x) - GaussianTools.Phi x| ≤
      beta μ n * (Real.exp ((5 / 2) * ((b - a) ^ 2 / (8 * a ^ 2))) *
        max (spectralProfile N c A V a) (spectralProfile N c A V b)) := by
  have hC := CoefficientRayPrice.node_coefficient_qualifies μ n N hN hNn hρ a b c ha hs.1 hs.2 hc
  apply (normalized_actual_cdf_le_beta_spectralProfile μ h n N hN hNn hρ c hC A V hA hAV x).trans
  have hβ := CoarseHighMomentRayPrice.beta_pos μ n (lt_of_lt_of_le hN hNn) hρ
  exact mul_le_mul_of_nonneg_left
    (spectralProfile_le_linear_endpoint_max N hN c A V a b (1 / beta μ n ^ 2)
      hA hAV ha hab hs hbranch) hβ.le

theorem normalized_actual_cdf_le_canonical_node_const_endpoints (μ : ProbabilityMeasure ℝ)
    (h : StandardizedLaw μ) (n N : ℕ) (hN : 0 < N) (hNn : N ≤ n)
    (hρ : rho0 ≤ thirdAbsoluteMoment μ) (A V a b : ℝ) (hA : 0 < A) (hAV : A ≤ V)
    (ha : 0 < a) (hab : a < b) (hs : 1 / beta μ n ^ 2 ∈ Icc a b)
    (hbranch : (N : ℝ) / rho0 ^ 2 ≤ a) (x : ℝ) :
    |(normalizedIidSumLaw μ n).real (Iic x) - GaussianTools.Phi x| ≤
      beta μ n * (Real.exp ((3 / 2) * ((b - a) ^ 2 / (8 * a ^ 2))) *
        max (spectralProfile N (nodeCoefficient N b) A V a)
          (spectralProfile N (nodeCoefficient N b) A V b)) :=
  normalized_actual_cdf_le_node_const_endpoints μ h n N hN hNn hρ (nodeCoefficient N b) A V a b
    le_rfl hA hAV ha hab hs hbranch x

theorem normalized_actual_cdf_le_canonical_node_linear_endpoints (μ : ProbabilityMeasure ℝ)
    (h : StandardizedLaw μ) (n N : ℕ) (hN : 0 < N) (hNn : N ≤ n)
    (hρ : rho0 ≤ thirdAbsoluteMoment μ) (A V a b : ℝ) (hA : 0 < A) (hAV : A ≤ V)
    (ha : 0 < a) (hab : a < b) (hs : 1 / beta μ n ^ 2 ∈ Icc a b)
    (hbranch : b ≤ (N : ℝ) / rho0 ^ 2) (x : ℝ) :
    |(normalizedIidSumLaw μ n).real (Iic x) - GaussianTools.Phi x| ≤
      beta μ n * (Real.exp ((5 / 2) * ((b - a) ^ 2 / (8 * a ^ 2))) *
        max (spectralProfile N (nodeCoefficient N b) A V a)
          (spectralProfile N (nodeCoefficient N b) A V b)) :=
  normalized_actual_cdf_le_node_linear_endpoints μ h n N hN hNn hρ (nodeCoefficient N b) A V a b
    le_rfl hA hAV ha hab hs hbranch x

end BerryEsseen.CoefficientRaySpectral

#print axioms BerryEsseen.CoefficientRaySpectral.coarsePrice_spectral_eq
#print axioms BerryEsseen.CoefficientRaySpectral.profileIntegrable
#print axioms BerryEsseen.CoefficientRaySpectral.spectralProfile_le_const_endpoint_max
#print axioms BerryEsseen.CoefficientRaySpectral.spectralProfile_le_linear_endpoint_max
#print axioms BerryEsseen.CoefficientRaySpectral.normalized_actual_cdf_le_beta_spectralProfile
#print axioms BerryEsseen.CoefficientRaySpectral.normalized_actual_cdf_le_node_const_endpoints
#print axioms BerryEsseen.CoefficientRaySpectral.normalized_actual_cdf_le_node_linear_endpoints
#print axioms BerryEsseen.CoefficientRaySpectral.normalized_actual_cdf_le_canonical_node_const_endpoints
#print axioms BerryEsseen.CoefficientRaySpectral.normalized_actual_cdf_le_canonical_node_linear_endpoints
