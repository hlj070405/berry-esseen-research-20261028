module

public import BerryEsseen.SquareBiasSine
public import BerryEsseen.PrawitzSmoothing

@[expose] public section

/-! 2026-10-29: actual iid characteristic-function error from a single
integrating factor and the proved square-bias residual. No classical
numerical Berry--Esseen estimate or zero-bias distance is an input.
Frequencies are raw, matching PrawitzSmoothing.rawEnvelope. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology Interval

namespace BerryEsseen.IidSmoothingPrice

open SquareBiasFourier

def scaledFactor (n : ℕ) (t : ℝ) : ℂ :=
  (Real.exp ((n : ℝ) * (t ^ 2 / 2)) : ℂ)

def scaledGaussian (n : ℕ) (t : ℝ) : ℂ :=
  (Real.exp (-((n : ℝ) * (t ^ 2 / 2))) : ℂ)

def transformed (μ : ProbabilityMeasure ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  scaledFactor n t * charFun (μ : Measure ℝ) t ^ n

def residual (μ : ProbabilityMeasure ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  (n : ℂ) * scaledFactor n t * charFun (μ : Measure ℝ) t ^ (n - 1) * firstResidual μ t

lemma hasDerivAt_scaledFactor (n : ℕ) (t : ℝ) :
    HasDerivAt (scaledFactor n) ((n : ℂ) * (t : ℂ) * scaledFactor n t) t := by
  have hd := ((((hasDerivAt_id' t).fun_pow 2).div_const 2).const_mul (n : ℝ)).exp.ofReal_comp
  convert hd using 1
  · rfl
  · unfold scaledFactor
    push_cast
    ring

lemma continuous_scaledFactor (n : ℕ) : Continuous (scaledFactor n) := by
  unfold scaledFactor
  fun_prop

lemma scaledGaussian_mul_factor (n : ℕ) (t : ℝ) :
    scaledGaussian n t * scaledFactor n t = 1 := by
  unfold scaledGaussian scaledFactor
  rw [← Complex.ofReal_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, Complex.ofReal_one]

lemma norm_scaledFactor (n : ℕ) (t : ℝ) :
    ‖scaledFactor n t‖ = Real.exp ((n : ℝ) * (t ^ 2 / 2)) := by
  rw [scaledFactor, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

lemma norm_scaledGaussian (n : ℕ) (t : ℝ) :
    ‖scaledGaussian n t‖ = Real.exp (-((n : ℝ) * (t ^ 2 / 2))) := by
  rw [scaledGaussian, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

theorem hasDerivAt_transformed (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (hn : 0 < n) (t : ℝ) : HasDerivAt (transformed μ n) (residual μ n t) t := by
  have hp : charFun (μ : Measure ℝ) t ^ n =
      charFun (μ : Measure ℝ) t ^ (n - 1) * charFun (μ : Measure ℝ) t := by
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using
      (pow_succ (charFun (μ : Measure ℝ) t) (n - 1))
  have hd := (hasDerivAt_scaledFactor n t).mul ((hasDerivAt_cf μ h t).fun_pow n)
  convert hd using 1
  · rfl
  · unfold residual firstResidual
    rw [hp]
    ring

lemma continuous_residual (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (n : ℕ) :
    Continuous (residual μ n) := by
  exact (((continuous_const.mul (continuous_scaledFactor n)).mul
    (continuous_charFun.pow (n - 1))).mul (continuous_firstResidual μ h))

/-- The exact identity retains the true nth characteristic-function power.
In particular, n=1 and frequency zero require no limiting convention. -/
theorem single_integral_identity (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (hn : 0 < n) (t : ℝ) :
    charFun (μ : Measure ℝ) t ^ n - scaledGaussian n t =
      scaledGaussian n t * ∫ u in (0 : ℝ)..t, residual μ n u := by
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => hasDerivAt_transformed μ h n hn u) ((continuous_residual μ h n).intervalIntegrable 0 t)
  have hz : transformed μ n 0 = 1 := by simp [transformed, scaledFactor]
  rw [hz] at hFTC
  rw [hFTC]
  unfold transformed
  rw [mul_sub, ← mul_assoc, scaledGaussian_mul_factor, one_mul, mul_one]

def sinePrimitive (μ : ProbabilityMeasure ℝ) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, SquareBiasSine.sineKernelPrice μ s

lemma continuous_sinePrimitive (μ : ProbabilityMeasure ℝ) : Continuous (sinePrimitive μ) :=
  intervalIntegral.continuous_primitive
    (fun a b => (SquareBiasSine.continuous_sineKernelPrice μ).intervalIntegrable a b) 0

theorem norm_firstResidual_le_sinePrimitive (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (t : ℝ) (ht : 0 ≤ t) : ‖firstResidual μ t‖ ≤ sinePrimitive μ t := by
  rw [firstResidual_eq_integral μ h]
  apply (intervalIntegral.norm_integral_le_integral_norm ht).trans
  exact intervalIntegral.integral_mono_on ht
    ((continuous_kernel μ h).norm.intervalIntegrable 0 t)
    ((SquareBiasSine.continuous_sineKernelPrice μ).intervalIntegrable 0 t)
    (fun s _ => SquareBiasSine.norm_kernel_le_sine_price μ h s)

def priceIntegrand (μ : ProbabilityMeasure ℝ) (n : ℕ) (q : ℝ → ℝ) (u : ℝ) : ℝ :=
  (n : ℝ) * Real.exp ((n : ℝ) * (u ^ 2 / 2)) * q u ^ (n - 1) * sinePrimitive μ u

def rawSinePrice (μ : ProbabilityMeasure ℝ) (n : ℕ) (q : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (-((n : ℝ) * (t ^ 2 / 2))) * ∫ u in (0 : ℝ)..t, priceIntegrand μ n q u

lemma continuous_priceIntegrand (μ : ProbabilityMeasure ℝ) (n : ℕ) (q : ℝ → ℝ)
    (hq : Continuous q) : Continuous (priceIntegrand μ n q) := by
  exact (((continuous_const.mul (by fun_prop : Continuous
    (fun u : ℝ => Real.exp ((n : ℝ) * (u ^ 2 / 2))))).mul
      (hq.pow (n - 1))).mul (continuous_sinePrimitive μ))

/-- Any proved envelope for the same original CF may be inserted here.
The actual residual and all integrability are supplied by the standardized
finite-third-moment law, without support or fourth-moment assumptions. -/
theorem norm_iid_sub_gaussian_le (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (hn : 0 < n) (q : ℝ → ℝ) (hq : Continuous q) (t : ℝ) (ht : 0 ≤ t)
    (hbound : ∀ u ∈ Icc (0 : ℝ) t, ‖charFun (μ : Measure ℝ) u‖ ≤ q u) :
    ‖charFun (μ : Measure ℝ) t ^ n - scaledGaussian n t‖ ≤ rawSinePrice μ n q t := by
  rw [single_integral_identity μ h n hn t, norm_mul, norm_scaledGaussian]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  apply intervalIntegral.norm_integral_le_of_norm_le (f := residual μ n)
    (g := priceIntegrand μ n q) ht _ ((continuous_priceIntegrand μ n q hq).intervalIntegrable 0 t)
  exact Eventually.of_forall fun u hu => by
    have hu0 : 0 ≤ u := hu.1.le
    have hCF := hbound u ⟨hu0, hu.2⟩
    have hpow := pow_le_pow_left₀ (norm_nonneg _) hCF (n - 1)
    have hres := norm_firstResidual_le_sinePrimitive μ h u hu0
    unfold residual priceIntegrand
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_natCast, norm_scaledFactor, norm_pow]
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left hpow (by positivity)
    · exact hres
    · exact norm_nonneg _
    · exact mul_nonneg (by positivity) (pow_nonneg ((norm_nonneg _).trans hCF) _)

end BerryEsseen.IidSmoothingPrice

#print axioms BerryEsseen.IidSmoothingPrice.hasDerivAt_transformed
#print axioms BerryEsseen.IidSmoothingPrice.single_integral_identity
#print axioms BerryEsseen.IidSmoothingPrice.norm_firstResidual_le_sinePrimitive
#print axioms BerryEsseen.IidSmoothingPrice.norm_iid_sub_gaussian_le
