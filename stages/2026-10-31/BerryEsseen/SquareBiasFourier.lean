module

public import BerryEsseen.SquareBiasDistance
public import BerryEsseen.CharacteristicDerivative
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

@[expose] public section

/-! The actual square-bias differential bridge and the first twice-integrated
identity in I. Shevtsova, "A square bias transformation: properties and
applications", arXiv:1212.6775v4, Section 2. All characteristic functions
are those of the original measures, in radians. Continuity and interval
integrability precede each use of the fundamental theorem of calculus. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology Interval

namespace BerryEsseen.SquareBiasFourier

open SquareBias

lemma memLp_two (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    MemLp (fun x : ℝ => x) 2 (μ : Measure ℝ) :=
  (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).mpr h.integrable_square

theorem contDiff_cf_two (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    ContDiff ℝ 2 (charFun (μ : Measure ℝ)) := contDiff_charFun (n := 2) (memLp_two μ h)

theorem second_deriv_cf (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (t : ℝ) :
    deriv (deriv (charFun (μ : Measure ℝ))) t = -charFun (squareLaw μ h : Measure ℝ) t := by
  have hi := iteratedDeriv_charFun (n := 2) (t := t) (memLp_two μ h)
  have hd : iteratedDeriv 2 (charFun (μ : Measure ℝ)) =
      deriv (deriv (charFun (μ : Measure ℝ))) := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  rw [hd] at hi
  rw [charFun_apply_real, integral_squareLaw]
  simpa only [Complex.I_sq, neg_one_mul, Complex.real_smul, Complex.ofReal_pow] using hi

theorem hasDerivAt_cf (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (t : ℝ) :
    HasDerivAt (charFun (μ : Measure ℝ)) (deriv (charFun (μ : Measure ℝ)) t) t :=
  (((contDiff_cf_two μ h).differentiable (by norm_num)) t).hasDerivAt

theorem hasDerivAt_deriv_cf (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (t : ℝ) :
    HasDerivAt (deriv (charFun (μ : Measure ℝ))) (-charFun (squareLaw μ h : Measure ℝ) t) t :=
  ((contDiff_cf_two μ h).differentiable_deriv_two t).hasDerivAt.congr_deriv (second_deriv_cf μ h t)

theorem continuous_deriv_cf (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    Continuous (deriv (charFun (μ : Measure ℝ))) :=
  (contDiff_cf_two μ h).continuous_deriv (by norm_num)

theorem cf_zero (μ : ProbabilityMeasure ℝ) : charFun (μ : Measure ℝ) 0 = 1 := by simp

theorem deriv_cf_zero (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    deriv (charFun (μ : Measure ℝ)) 0 = 0 := by
  rw [CharacteristicDerivative.deriv_charFun_eq μ h.integrable_mean 0]
  unfold CharacteristicDerivative.weightedCF CharacteristicDerivative.oscillation
  simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one]
  have hc : (∫ x : ℝ, (x : ℂ) ∂(μ : Measure ℝ)) =
      ((∫ x : ℝ, x ∂(μ : Measure ℝ) : ℝ) : ℂ) :=
    integral_ofReal (𝕜 := ℂ) (f := fun x : ℝ => x)
  rw [hc, h.mean_zero]
  simp

def firstResidual (μ : ProbabilityMeasure ℝ) (t : ℝ) : ℂ :=
  deriv (charFun (μ : Measure ℝ)) t + (t : ℂ) * charFun (μ : Measure ℝ) t

def kernel (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (t : ℝ) : ℂ :=
  charFun (μ : Measure ℝ) t - charFun (squareLaw μ h : Measure ℝ) t +
    (t : ℂ) * deriv (charFun (μ : Measure ℝ)) t

theorem hasDerivAt_firstResidual (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (t : ℝ) :
    HasDerivAt (firstResidual μ) (kernel μ h t) t := by
  have hd := (hasDerivAt_deriv_cf μ h t).add
    (((hasDerivAt_id t).ofReal_comp).mul (hasDerivAt_cf μ h t))
  convert hd using 1
  · funext u
    rfl
  · simp only [kernel, id_eq, Complex.ofReal_one, one_mul]
    ring

theorem continuous_firstResidual (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    Continuous (firstResidual μ) :=
  (continuous_deriv_cf μ h).add (Complex.continuous_ofReal.mul continuous_charFun)

theorem continuous_kernel (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    Continuous (kernel μ h) :=
  (continuous_charFun.sub continuous_charFun).add
    (Complex.continuous_ofReal.mul (continuous_deriv_cf μ h))

theorem intervalIntegrable_kernel (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (a b : ℝ) :
    IntervalIntegrable (kernel μ h) volume a b := (continuous_kernel μ h).intervalIntegrable a b

theorem firstResidual_zero (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    firstResidual μ 0 = 0 := by simp only [firstResidual, deriv_cf_zero μ h, Complex.ofReal_zero, zero_mul, add_zero]

theorem firstResidual_eq_integral (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (t : ℝ) :
    firstResidual μ t = ∫ s in (0 : ℝ)..t, kernel μ h s := by
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => hasDerivAt_firstResidual μ h s) (intervalIntegrable_kernel μ h 0 t)
  simpa only [firstResidual_zero μ h, sub_zero] using hi.symm

def integratingFactor (t : ℝ) : ℂ := (Real.exp (t ^ 2 / 2) : ℂ)
def gaussianFactor (t : ℝ) : ℂ := (Real.exp (-(t ^ 2 / 2)) : ℂ)

lemma continuous_integratingFactor : Continuous integratingFactor := by unfold integratingFactor; fun_prop
lemma continuous_gaussianFactor : Continuous gaussianFactor := by unfold gaussianFactor; fun_prop

lemma gaussian_mul_integratingFactor (t : ℝ) : gaussianFactor t * integratingFactor t = 1 := by
  unfold gaussianFactor integratingFactor
  rw [← Complex.ofReal_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, Complex.ofReal_one]

lemma gaussianFactor_eq_actualCF (t : ℝ) : gaussianFactor t = charFun (gaussianReal 0 1) t := by
  rw [charFun_gaussianReal, gaussianFactor, Complex.ofReal_exp]
  congr 1
  push_cast
  ring

lemma hasDerivAt_integratingFactor (t : ℝ) :
    HasDerivAt integratingFactor ((t : ℂ) * integratingFactor t) t := by
  have hd : HasDerivAt (fun u : ℝ => Real.exp (u ^ 2 / 2)) (Real.exp (t ^ 2 / 2) * t) t := by
    have hs : HasDerivAt (fun u : ℝ => u ^ 2) (2 * t) t := by
      convert (hasDerivAt_id' t).fun_pow 2 using 1 <;> ring
    have hh : HasDerivAt (fun u : ℝ => u ^ 2 / 2) t t := by
      convert hs.div_const 2 using 1 <;> ring
    exact hh.exp
  unfold integratingFactor
  convert hd.ofReal_comp using 1
  push_cast
  ring

def transformedCF (μ : ProbabilityMeasure ℝ) (t : ℝ) : ℂ :=
  integratingFactor t * charFun (μ : Measure ℝ) t

def outerResidual (μ : ProbabilityMeasure ℝ) (t : ℝ) : ℂ :=
  integratingFactor t * firstResidual μ t

theorem hasDerivAt_transformedCF (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (t : ℝ) :
    HasDerivAt (transformedCF μ) (outerResidual μ t) t := by
  convert (hasDerivAt_integratingFactor t).mul (hasDerivAt_cf μ h t) using 1
  · funext u
    rfl
  · unfold outerResidual firstResidual
    ring

theorem continuous_outerResidual (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    Continuous (outerResidual μ) := continuous_integratingFactor.mul (continuous_firstResidual μ h)

theorem intervalIntegrable_outerResidual (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (a b : ℝ) : IntervalIntegrable (outerResidual μ) volume a b :=
  (continuous_outerResidual μ h).intervalIntegrable a b

def innerPrimitive (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (u : ℝ) : ℂ :=
  ∫ s in (0 : ℝ)..u, kernel μ h s

def doubleIntegrand (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (u : ℝ) : ℂ :=
  integratingFactor u * innerPrimitive μ h u

theorem continuous_innerPrimitive (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    Continuous (innerPrimitive μ h) :=
  intervalIntegral.continuous_primitive (intervalIntegrable_kernel μ h) 0

theorem continuous_doubleIntegrand (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    Continuous (doubleIntegrand μ h) :=
  continuous_integratingFactor.mul (continuous_innerPrimitive μ h)

theorem intervalIntegrable_doubleIntegrand (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (a b : ℝ) : IntervalIntegrable (doubleIntegrand μ h) volume a b :=
  (continuous_doubleIntegrand μ h).intervalIntegrable a b

theorem integral_outerResidual (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (t : ℝ) :
    (∫ u in (0 : ℝ)..t, outerResidual μ u) = transformedCF μ t - 1 := by
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => hasDerivAt_transformedCF μ h u) (intervalIntegrable_outerResidual μ h 0 t)
  have hz : transformedCF μ 0 = 1 := by simp [transformedCF, integratingFactor, cf_zero]
  simpa only [hz] using hi

/-- The genuine all-real twice-integrated square-bias identity. In
particular, negative t uses the actual oriented interval integrals. -/
theorem double_integral_identity (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (t : ℝ) :
    charFun (μ : Measure ℝ) t - (Real.exp (-(t ^ 2 / 2)) : ℂ) =
      (Real.exp (-(t ^ 2 / 2)) : ℂ) *
        ∫ u in (0 : ℝ)..t, (Real.exp (u ^ 2 / 2) : ℂ) *
          (∫ s in (0 : ℝ)..u, charFun (μ : Measure ℝ) s -
            charFun (squareLaw μ h : Measure ℝ) s + (s : ℂ) * deriv (charFun (μ : Measure ℝ)) s) := by
  change charFun (μ : Measure ℝ) t - gaussianFactor t =
    gaussianFactor t * ∫ u in (0 : ℝ)..t, doubleIntegrand μ h u
  calc
    _ = gaussianFactor t * (transformedCF μ t - 1) := by
      unfold transformedCF
      rw [mul_sub, ← mul_assoc, gaussian_mul_integratingFactor, one_mul, mul_one]
    _ = gaussianFactor t * ∫ u in (0 : ℝ)..t, outerResidual μ u := by
      rw [integral_outerResidual μ h t]
    _ = _ := by
      congr 1
      apply intervalIntegral.integral_congr
      intro u _
      unfold outerResidual doubleIntegrand innerPrimitive
      rw [firstResidual_eq_integral μ h u]

lemma norm_integratingFactor (t : ℝ) : ‖integratingFactor t‖ = Real.exp (t ^ 2 / 2) := by
  rw [integratingFactor, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

lemma norm_gaussianFactor (t : ℝ) : ‖gaussianFactor t‖ = Real.exp (-(t ^ 2 / 2)) := by
  rw [gaussianFactor, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

def normOuter (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (u : ℝ) : ℝ :=
  Real.exp (u ^ 2 / 2) * ∫ s in (0 : ℝ)..u, ‖kernel μ h s‖

def doubleNormPrice (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (t : ℝ) : ℝ :=
  Real.exp (-(t ^ 2 / 2)) * ∫ u in (0 : ℝ)..t, normOuter μ h u

theorem continuous_normOuter (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    Continuous (normOuter μ h) := by
  have hc : Continuous (fun u : ℝ => ∫ s in (0 : ℝ)..u, ‖kernel μ h s‖) :=
    intervalIntegral.continuous_primitive
      (fun a b => (continuous_kernel μ h).norm.intervalIntegrable a b) 0
  exact (by fun_prop : Continuous (fun u : ℝ => Real.exp (u ^ 2 / 2))).mul hc

/-- A nonnegative-frequency norm bound whose inner price is the norm
of the actual square-bias differential residual. -/
theorem norm_cf_sub_gaussian_le_actual_price (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (t : ℝ) (ht : 0 ≤ t) :
    ‖charFun (μ : Measure ℝ) t - charFun (gaussianReal 0 1) t‖ ≤ doubleNormPrice μ h t := by
  have hid : charFun (μ : Measure ℝ) t - gaussianFactor t =
      gaussianFactor t * ∫ u in (0 : ℝ)..t, doubleIntegrand μ h u := double_integral_identity μ h t
  rw [← gaussianFactor_eq_actualCF, hid, norm_mul, norm_gaussianFactor]
  unfold doubleNormPrice
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  apply intervalIntegral.norm_integral_le_of_norm_le (f := doubleIntegrand μ h) (g := normOuter μ h) ht
    _ ((continuous_normOuter μ h).intervalIntegrable 0 t)
  exact Eventually.of_forall fun u hu => by
    change ‖integratingFactor u * innerPrimitive μ h u‖ ≤
      Real.exp (u ^ 2 / 2) * ∫ s in (0 : ℝ)..u, ‖kernel μ h s‖
    rw [norm_mul, norm_integratingFactor]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    exact intervalIntegral.norm_integral_le_integral_norm hu.1.le

/-- This price uses the proved linear cross-law bound and the proved
sine bound on f'. It does not assume a sine upgrade of the cross-law bound. -/
def linearSinePrice (μ : ProbabilityMeasure ℝ) (s : ℝ) : ℝ :=
  thirdAbsoluteMoment μ * |s| + |s| * Real.sin (min |s| (Real.pi / 2))

theorem norm_kernel_le_linearSinePrice (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (s : ℝ) :
    ‖kernel μ h s‖ ≤ linearSinePrice μ s := by
  have hsq : ‖charFun (μ : Measure ℝ) s - charFun (squareLaw μ h : Measure ℝ) s‖ ≤
      thirdAbsoluteMoment μ * |s| := by
    rw [norm_sub_rev]
    exact SquareBiasDistance.charFun_squareLaw_sub_le μ h s
  have hd := CharacteristicDerivative.standardized_deriv_sine μ h s
  change ‖(charFun (μ : Measure ℝ) s - charFun (squareLaw μ h : Measure ℝ) s) +
      (s : ℂ) * deriv (charFun (μ : Measure ℝ)) s‖ ≤
    thirdAbsoluteMoment μ * |s| + |s| * Real.sin (min |s| (Real.pi / 2))
  calc
    _ ≤ ‖charFun (μ : Measure ℝ) s - charFun (squareLaw μ h : Measure ℝ) s‖ +
        ‖(s : ℂ) * deriv (charFun (μ : Measure ℝ)) s‖ := norm_add_le _ _
    _ ≤ _ := by
      apply add_le_add hsq
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left hd (abs_nonneg s)

lemma continuous_linearSinePrice (μ : ProbabilityMeasure ℝ) : Continuous (linearSinePrice μ) := by
  unfold linearSinePrice
  fun_prop

def linearSineOuter (μ : ProbabilityMeasure ℝ) (u : ℝ) : ℝ :=
  Real.exp (u ^ 2 / 2) * ∫ s in (0 : ℝ)..u, linearSinePrice μ s

def doubleLinearSinePrice (μ : ProbabilityMeasure ℝ) (t : ℝ) : ℝ :=
  Real.exp (-(t ^ 2 / 2)) * ∫ u in (0 : ℝ)..t, linearSineOuter μ u

lemma continuous_linearSineOuter (μ : ProbabilityMeasure ℝ) : Continuous (linearSineOuter μ) := by
  have hc : Continuous (fun u : ℝ => ∫ s in (0 : ℝ)..u, linearSinePrice μ s) :=
    intervalIntegral.continuous_primitive
      (fun a b => (continuous_linearSinePrice μ).intervalIntegrable a b) 0
  exact (by fun_prop : Continuous (fun u : ℝ => Real.exp (u ^ 2 / 2))).mul hc

theorem norm_cf_sub_gaussian_le_linear_sine_price (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (t : ℝ) (ht : 0 ≤ t) :
    ‖charFun (μ : Measure ℝ) t - charFun (gaussianReal 0 1) t‖ ≤ doubleLinearSinePrice μ t := by
  apply (norm_cf_sub_gaussian_le_actual_price μ h t ht).trans
  unfold doubleNormPrice doubleLinearSinePrice
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  apply intervalIntegral.integral_mono_on ht
    ((continuous_normOuter μ h).intervalIntegrable 0 t) ((continuous_linearSineOuter μ).intervalIntegrable 0 t)
  intro u hu
  change Real.exp (u ^ 2 / 2) * (∫ s in (0 : ℝ)..u, ‖kernel μ h s‖) ≤
    Real.exp (u ^ 2 / 2) * (∫ s in (0 : ℝ)..u, linearSinePrice μ s)
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  apply intervalIntegral.integral_mono_on hu.1
    ((continuous_kernel μ h).norm.intervalIntegrable 0 u) ((continuous_linearSinePrice μ).intervalIntegrable 0 u)
  exact fun s _ => norm_kernel_le_linearSinePrice μ h s

end BerryEsseen.SquareBiasFourier

#print axioms BerryEsseen.SquareBiasFourier.contDiff_cf_two
#print axioms BerryEsseen.SquareBiasFourier.second_deriv_cf
#print axioms BerryEsseen.SquareBiasFourier.deriv_cf_zero
#print axioms BerryEsseen.SquareBiasFourier.hasDerivAt_firstResidual
#print axioms BerryEsseen.SquareBiasFourier.intervalIntegrable_doubleIntegrand
#print axioms BerryEsseen.SquareBiasFourier.double_integral_identity
#print axioms BerryEsseen.SquareBiasFourier.norm_cf_sub_gaussian_le_actual_price
#print axioms BerryEsseen.SquareBiasFourier.norm_kernel_le_linearSinePrice
#print axioms BerryEsseen.SquareBiasFourier.norm_cf_sub_gaussian_le_linear_sine_price
