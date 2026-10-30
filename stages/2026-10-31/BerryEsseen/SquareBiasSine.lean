module

public import BerryEsseen.SquareBiasCoupling
public import BerryEsseen.CouplingSinePrice
public import BerryEsseen.SquareBiasFourier

@[expose] public section

/-! 2026-10-29: Shevtsova's sine cross-law price from the explicit common-part
coupling, then the corresponding actual double-integral CF error price.
The transport theorem is an existing result; no novelty is claimed here. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Interval

namespace BerryEsseen.SquareBiasSine

open SquareBias SquareBiasDistance SquareBiasFourier

theorem charFun_squareLaw_sub_le (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (t : ℝ) :
    ‖charFun (squareLaw μ h : Measure ℝ) t - charFun (μ : Measure ℝ) t‖ ≤
      2 * Real.sin (min (thirdAbsoluteMoment μ * |t| / 2) (Real.pi / 2)) := by
  letI := SquareBiasCoupling.coupling_isProbability μ h
  have hX : (∫ w : ℝ × ℝ, phase t w.1 ∂SquareBiasCoupling.coupling μ) =
      charFun (μ : Measure ℝ) t := by
    rw [← integral_map measurable_fst.aemeasurable (continuous_phase t).aestronglyMeasurable,
      SquareBiasCoupling.coupling_fst μ h, ← charFun_eq_integral_phase]
  have hY : (∫ w : ℝ × ℝ, phase t w.2 ∂SquareBiasCoupling.coupling μ) =
      charFun (squareLaw μ h : Measure ℝ) t := by
    rw [← integral_map measurable_snd.aemeasurable (continuous_phase t).aestronglyMeasurable,
      SquareBiasCoupling.coupling_snd μ h, ← charFun_eq_integral_phase]
  have hp := CouplingSinePrice.norm_integral_difference_le
    (SquareBiasCoupling.coupling μ) Prod.fst Prod.snd measurable_fst measurable_snd
    (SquareBiasCoupling.integrable_cost μ h) (thirdAbsoluteMoment μ) t
    (SquareBiasCoupling.cost_le_third μ h)
  rw [hX, hY, norm_sub_rev] at hp
  exact hp

def sineKernelPrice (μ : ProbabilityMeasure ℝ) (s : ℝ) : ℝ :=
  2 * Real.sin (min (thirdAbsoluteMoment μ * |s| / 2) (Real.pi / 2)) +
    |s| * Real.sin (min |s| (Real.pi / 2))

theorem norm_kernel_le_sine_price (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (s : ℝ) :
    ‖kernel μ h s‖ ≤ sineKernelPrice μ s := by
  have hsq := charFun_squareLaw_sub_le μ h s
  rw [norm_sub_rev] at hsq
  have hd := CharacteristicDerivative.standardized_deriv_sine μ h s
  change ‖(charFun (μ : Measure ℝ) s - charFun (squareLaw μ h : Measure ℝ) s) +
      (s : ℂ) * deriv (charFun (μ : Measure ℝ)) s‖ ≤ _
  apply (norm_add_le _ _).trans
  apply add_le_add hsq
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left hd (abs_nonneg s)

lemma continuous_sineKernelPrice (μ : ProbabilityMeasure ℝ) : Continuous (sineKernelPrice μ) := by
  unfold sineKernelPrice
  fun_prop

def sineOuter (μ : ProbabilityMeasure ℝ) (u : ℝ) : ℝ :=
  Real.exp (u ^ 2 / 2) * ∫ s in (0 : ℝ)..u, sineKernelPrice μ s

def doubleSinePrice (μ : ProbabilityMeasure ℝ) (t : ℝ) : ℝ :=
  Real.exp (-(t ^ 2 / 2)) * ∫ u in (0 : ℝ)..t, sineOuter μ u

lemma continuous_sineOuter (μ : ProbabilityMeasure ℝ) : Continuous (sineOuter μ) := by
  have hi : Continuous (fun u : ℝ => ∫ s in (0 : ℝ)..u, sineKernelPrice μ s) :=
    intervalIntegral.continuous_primitive
      (fun a b => (continuous_sineKernelPrice μ).intervalIntegrable a b) 0
  exact (by fun_prop : Continuous (fun u : ℝ => Real.exp (u ^ 2 / 2))).mul hi

/-- Both sine terms are now genuine same-law bounds. Only a nonnegative
frequency is required to compare the two oriented integrals as prices. -/
theorem norm_cf_sub_gaussian_le_sine_price (μ : ProbabilityMeasure ℝ)
    (h : StandardizedLaw μ) (t : ℝ) (ht : 0 ≤ t) :
    ‖charFun (μ : Measure ℝ) t - charFun (gaussianReal 0 1) t‖ ≤ doubleSinePrice μ t := by
  apply (norm_cf_sub_gaussian_le_actual_price μ h t ht).trans
  unfold doubleNormPrice doubleSinePrice
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  apply intervalIntegral.integral_mono_on ht
    ((continuous_normOuter μ h).intervalIntegrable 0 t) ((continuous_sineOuter μ).intervalIntegrable 0 t)
  intro u hu
  change Real.exp (u ^ 2 / 2) * (∫ s in (0 : ℝ)..u, ‖kernel μ h s‖) ≤
    Real.exp (u ^ 2 / 2) * (∫ s in (0 : ℝ)..u, sineKernelPrice μ s)
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  apply intervalIntegral.integral_mono_on hu.1
    ((continuous_kernel μ h).norm.intervalIntegrable 0 u)
    ((continuous_sineKernelPrice μ).intervalIntegrable 0 u)
  exact fun s _ => norm_kernel_le_sine_price μ h s

end BerryEsseen.SquareBiasSine

#print axioms BerryEsseen.SquareBiasSine.charFun_squareLaw_sub_le
#print axioms BerryEsseen.SquareBiasSine.norm_kernel_le_sine_price
#print axioms BerryEsseen.SquareBiasSine.norm_cf_sub_gaussian_le_sine_price
