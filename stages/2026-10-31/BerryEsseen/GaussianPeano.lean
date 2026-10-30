module

public import BerryEsseen.GaussianTools
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

@[expose] public section

/-! 2026-10-28: actual Gaussian contact functional, its Peano hinge kernel, and
quadratic annihilation. The general C3 Taylor/Fubini representation is a separate
stage; none of the hinge or expectation identities assumes that representation. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace BerryEsseen.GaussianPeano

open GaussianTools

abbrev standardGaussian : Measure ℝ := gaussianReal 0 1

def expectation (f : ℝ → ℝ) : ℝ := ∫ u, f u ∂standardGaussian

/-- The manuscript's actual functional, with native first and second derivatives. -/
def contact (x : ℝ) (g : ℝ → ℝ) : ℝ :=
  g x - expectation g - x * expectation (deriv g) -
    (x ^ 2 - 1) / 2 * expectation (iteratedDeriv 2 g)

/-- Exactly the kernel displayed in the manuscript, including its jump convention. -/
def kernel (x t : ℝ) : ℝ :=
  (x - t) ^ 2 / 2 * ((if t < x then 1 else 0) - (1 - Phi t)) + (t / 2 - x) * phi t

def hinge (t u : ℝ) : ℝ := max (u - t) 0 ^ 2 / 2
def hingeSlope (t u : ℝ) : ℝ := max (u - t) 0
def hingeCurvature (t u : ℝ) : ℝ := if t < u then 1 else 0

lemma expectation_eq_density (f : ℝ → ℝ) :
    expectation f = ∫ u, phi u * f u := by
  simpa only [expectation, standardGaussian, phi, smul_eq_mul] using
    (integral_gaussianReal_eq_integral_smul (μ := 0) (v := 1) (f := f) one_ne_zero)

lemma integrable_gaussian_iff (f : ℝ → ℝ) :
    Integrable f standardGaussian ↔ Integrable (fun u => f u * phi u) := by
  rw [standardGaussian, gaussianReal_of_var_ne_zero 0 (by norm_num : (1 : NNReal) ≠ 0)]
  simpa only [toReal_gaussianPDF, phi] using
    (integrable_withDensity_iff (g := f) (measurable_gaussianPDF 0 1)
      (Filter.Eventually.of_forall fun _ => gaussianPDF_lt_top))

lemma setIntegral_gaussian_eq_density (s : Set ℝ) (hs : MeasurableSet s) (f : ℝ → ℝ) :
    (∫ u in s, f u ∂standardGaussian) = ∫ u in s, phi u * f u := by
  rw [← integral_indicator hs]
  change expectation (s.indicator f) = _
  rw [expectation_eq_density, ← integral_indicator hs]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun u => by
    by_cases hu : u ∈ s <;> simp [hu]

lemma integrable_gaussian_pow (n : ℕ) : Integrable (fun u : ℝ => u ^ n) standardGaussian :=
  (integrable_gaussian_iff _).mpr (integrable_pow_mul_phi n)

lemma integrable_gaussian_id : Integrable (fun u : ℝ => u) standardGaussian := by
  simpa only [pow_one] using integrable_gaussian_pow 1

lemma expectation_id : expectation (fun u : ℝ => u) = 0 := integral_id_gaussianReal

lemma expectation_square : expectation (fun u : ℝ => u ^ 2) = 1 := by
  have h := variance_fun_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : NNReal))
  rw [variance_eq_integral (show AEMeasurable (fun u : ℝ => u) standardGaussian from
      measurable_id.aemeasurable), integral_id_gaussianReal] at h
  simpa only [sub_zero, NNReal.coe_one, expectation, standardGaussian] using h

lemma hinge_eq_indicator (t : ℝ) :
    hinge t = (Ioi t).indicator (fun u : ℝ => (u - t) ^ 2 / 2) := by
  ext u
  by_cases hu : t < u
  · simp [hinge, hu, max_eq_left (sub_nonneg.mpr hu.le)]
  · simp [hinge, hu, max_eq_right (sub_nonpos.mpr (le_of_not_gt hu))]

lemma hingeSlope_eq_indicator (t : ℝ) :
    hingeSlope t = (Ioi t).indicator (fun u : ℝ => u - t) := by
  ext u
  by_cases hu : t < u
  · simp [hingeSlope, hu, max_eq_left (sub_nonneg.mpr hu.le)]
  · simp [hingeSlope, hu, max_eq_right (sub_nonpos.mpr (le_of_not_gt hu))]

lemma hingeCurvature_eq_indicator (t : ℝ) :
    hingeCurvature t = (Ioi t).indicator (fun _ : ℝ => (1 : ℝ)) := by
  ext u
  simp [hingeCurvature, Set.indicator_apply]

lemma integrable_hinge (t : ℝ) : Integrable (hinge t) standardGaussian := by
  have hA : Integrable (fun u : ℝ => u ^ 2 - (2 * t) * u) standardGaussian :=
    (integrable_gaussian_pow 2).sub (integrable_gaussian_id.const_mul _)
  have hB : Integrable (fun u : ℝ => u ^ 2 - (2 * t) * u + t ^ 2) standardGaussian :=
    hA.add (integrable_const _)
  have hpoly : Integrable (fun u : ℝ => (u - t) ^ 2 / 2) standardGaussian := by
    convert hB.div_const 2 using 1
    ext u
    ring
  rw [hinge_eq_indicator]
  exact hpoly.indicator measurableSet_Ioi

lemma integrable_hingeSlope (t : ℝ) : Integrable (hingeSlope t) standardGaussian := by
  rw [hingeSlope_eq_indicator]
  exact (integrable_gaussian_id.sub (integrable_const t)).indicator measurableSet_Ioi

lemma integrable_hingeCurvature (t : ℝ) : Integrable (hingeCurvature t) standardGaussian := by
  rw [hingeCurvature_eq_indicator]
  exact (integrable_const 1).indicator measurableSet_Ioi

/-- The actual Gaussian expectation of the quadratic hinge. -/
theorem expectation_hinge (t : ℝ) :
    expectation (hinge t) = ((1 + t ^ 2) * (1 - Phi t) - t * phi t) / 2 := by
  rw [expectation, hinge_eq_indicator, integral_indicator measurableSet_Ioi,
    setIntegral_gaussian_eq_density (Ioi t) measurableSet_Ioi]
  have hi0 : IntegrableOn phi (Ioi t) := integrable_phi.integrableOn
  have hi1 : IntegrableOn (fun u : ℝ => u * phi u) (Ioi t) := integrable_mul_phi.integrableOn
  have hi2 : IntegrableOn (fun u : ℝ => u ^ 2 * phi u) (Ioi t) := integrable_sq_mul_phi.integrableOn
  have hA : IntegrableOn (fun u : ℝ => u ^ 2 * phi u - (2 * t) * (u * phi u)) (Ioi t) :=
    hi2.sub (hi1.const_mul _)
  have hfun : (fun u : ℝ => phi u * ((u - t) ^ 2 / 2)) =
      (fun u : ℝ => (u ^ 2 * phi u - (2 * t) * (u * phi u) + t ^ 2 * phi u) / 2) := by
    ext u
    ring
  rw [hfun, integral_div, integral_add hA (hi0.const_mul _),
    integral_sub hi2 (hi1.const_mul _), integral_const_mul, integral_const_mul,
    integral_sq_mul_phi_Ioi, integral_mul_phi_Ioi, integral_phi_Ioi]
  ring

/-- The actual Gaussian expectation of the first hinge derivative. -/
theorem expectation_hingeSlope (t : ℝ) :
    expectation (hingeSlope t) = phi t - t * (1 - Phi t) := by
  rw [expectation, hingeSlope_eq_indicator, integral_indicator measurableSet_Ioi,
    setIntegral_gaussian_eq_density (Ioi t) measurableSet_Ioi]
  have hfun : (fun u : ℝ => phi u * (u - t)) =
      (fun u : ℝ => u * phi u - t * phi u) := by ext u; ring
  rw [hfun, integral_sub integrable_mul_phi.integrableOn (integrable_phi.const_mul t).integrableOn,
    integral_const_mul, integral_mul_phi_Ioi, integral_phi_Ioi]

/-- The actual Gaussian expectation of the almost-everywhere second hinge derivative. -/
theorem expectation_hingeCurvature (t : ℝ) :
    expectation (hingeCurvature t) = 1 - Phi t := by
  rw [expectation, hingeCurvature_eq_indicator, integral_indicator measurableSet_Ioi,
    setIntegral_gaussian_eq_density (Ioi t) measurableSet_Ioi]
  simpa only [mul_one] using integral_phi_Ioi t

/-- The three actual Gaussian hinge moments give exactly the displayed Peano kernel. -/
theorem hinge_jet_eq_kernel (x t : ℝ) :
    hinge t x - expectation (hinge t) - x * expectation (hingeSlope t) -
      (x ^ 2 - 1) / 2 * expectation (hingeCurvature t) = kernel x t := by
  rw [expectation_hinge, expectation_hingeSlope, expectation_hingeCurvature]
  by_cases htx : t < x
  · simp only [hinge, kernel, ite_eq_left htx, max_eq_left (sub_nonneg.mpr htx.le)]
    ring
  · simp only [hinge, kernel, ite_eq_right htx, max_eq_right (sub_nonpos.mpr (le_of_not_gt htx))]
    ring

end BerryEsseen.GaussianPeano

#print axioms BerryEsseen.GaussianPeano.expectation_hinge
#print axioms BerryEsseen.GaussianPeano.hinge_jet_eq_kernel

namespace BerryEsseen.GaussianPeano

lemma hasDerivAt_shift_square (t u : ℝ) :
    HasDerivAt (fun v : ℝ => (v - t) ^ 2 / 2) (u - t) u := by
  convert (((hasDerivAt_id' u).sub_const t).fun_pow 2).div_const 2 using 1
  ring

lemma deriv_shift_square (t : ℝ) :
    deriv (fun v : ℝ => (v - t) ^ 2 / 2) = (fun u : ℝ => u - t) :=
  funext fun u => (hasDerivAt_shift_square t u).deriv

lemma hinge_eventuallyEq_poly (t u : ℝ) (htu : t < u) :
    hinge t =ᶠ[𝓝 u] (fun v : ℝ => (v - t) ^ 2 / 2) := by
  filter_upwards [Ioi_mem_nhds htu] with v hv
  simp only [hinge, max_eq_left (sub_nonneg.mpr (le_of_lt hv))]

lemma hinge_eventuallyEq_zero (t u : ℝ) (hut : u < t) :
    hinge t =ᶠ[𝓝 u] (fun _ : ℝ => (0 : ℝ)) := by
  filter_upwards [Iio_mem_nhds hut] with v hv
  simp [hinge, max_eq_right (sub_nonpos.mpr (le_of_lt hv))]

/-- Native first derivatives agree with the hinge slope off its sole knot. -/
lemma deriv_hinge_of_ne (t u : ℝ) (hu : u ≠ t) :
    deriv (hinge t) u = hingeSlope t u := by
  rcases lt_or_gt_of_ne hu with hut | htu
  · rw [(hinge_eventuallyEq_zero t u hut).deriv_eq, deriv_const]
    simp only [hingeSlope, max_eq_right (sub_nonpos.mpr hut.le)]
  · rw [(hinge_eventuallyEq_poly t u htu).deriv_eq, (hasDerivAt_shift_square t u).deriv]
    simp only [hingeSlope, max_eq_left (sub_nonneg.mpr htu.le)]

/-- Native second derivatives agree with the open-tail indicator off the knot. -/
lemma secondDeriv_hinge_of_ne (t u : ℝ) (hu : u ≠ t) :
    iteratedDeriv 2 (hinge t) u = hingeCurvature t u := by
  rw [show (2 : ℕ) = 1 + 1 by rfl, iteratedDeriv_succ, iteratedDeriv_one]
  rcases lt_or_gt_of_ne hu with hut | htu
  · rw [(hinge_eventuallyEq_zero t u hut).deriv.deriv_eq, deriv_const', deriv_const]
    simp [hingeCurvature, not_lt.mpr hut.le]
  · rw [(hinge_eventuallyEq_poly t u htu).deriv.deriv_eq, deriv_shift_square,
      ((hasDerivAt_id' u).sub_const t).deriv]
    simp [hingeCurvature, htu]

lemma deriv_hinge_ae (t : ℝ) : deriv (hinge t) =ᵐ[standardGaussian] hingeSlope t := by
  let : NullSingletonClass standardGaussian := nullSingletonClass_gaussianReal (by norm_num)
  filter_upwards [standardGaussian.ae_ne t] with u hu
  exact deriv_hinge_of_ne t u hu

lemma secondDeriv_hinge_ae (t : ℝ) :
    iteratedDeriv 2 (hinge t) =ᵐ[standardGaussian] hingeCurvature t := by
  let : NullSingletonClass standardGaussian := nullSingletonClass_gaussianReal (by norm_num)
  filter_upwards [standardGaussian.ae_ne t] with u hu
  exact secondDeriv_hinge_of_ne t u hu

lemma integrable_deriv_hinge (t : ℝ) : Integrable (deriv (hinge t)) standardGaussian :=
  (integrable_hingeSlope t).congr (deriv_hinge_ae t).symm

lemma integrable_secondDeriv_hinge (t : ℝ) :
    Integrable (iteratedDeriv 2 (hinge t)) standardGaussian :=
  (integrable_hingeCurvature t).congr (secondDeriv_hinge_ae t).symm

/-- The actual native-derivative contact functional applied to the hinge equals K. -/
theorem contact_hinge_eq_kernel (x t : ℝ) : contact x (hinge t) = kernel x t := by
  have h1 : expectation (deriv (hinge t)) = expectation (hingeSlope t) :=
    integral_congr_ae (deriv_hinge_ae t)
  have h2 : expectation (iteratedDeriv 2 (hinge t)) = expectation (hingeCurvature t) :=
    integral_congr_ae (secondDeriv_hinge_ae t)
  rw [contact, h1, h2]
  exact hinge_jet_eq_kernel x t

/-- A general quadratic polynomial, with all three coefficients free. -/
def quadratic (A B C u : ℝ) : ℝ := A + B * u + C * u ^ 2

lemma hasDerivAt_quadratic (A B C u : ℝ) :
    HasDerivAt (quadratic A B C) (B + 2 * C * u) u := by
  change HasDerivAt (fun v : ℝ => A + B * v + C * v ^ 2) (B + 2 * C * u) u
  convert ((hasDerivAt_const u A).fun_add ((hasDerivAt_id' u).const_mul B)).fun_add
    (((hasDerivAt_id' u).fun_pow 2).const_mul C) using 1
  ring

lemma deriv_quadratic (A B C : ℝ) :
    deriv (quadratic A B C) = (fun u : ℝ => B + 2 * C * u) :=
  funext fun u => (hasDerivAt_quadratic A B C u).deriv

lemma secondDeriv_quadratic (A B C : ℝ) :
    iteratedDeriv 2 (quadratic A B C) = (fun _ : ℝ => 2 * C) := by
  rw [show (2 : ℕ) = 1 + 1 by rfl, iteratedDeriv_succ, iteratedDeriv_one, deriv_quadratic]
  ext u
  simpa only [mul_one] using (((hasDerivAt_id' u).const_mul (2 * C)).const_add B).deriv

lemma integrable_quadratic (A B C : ℝ) : Integrable (quadratic A B C) standardGaussian := by
  have hAB : Integrable (fun u : ℝ => A + B * u) standardGaussian :=
    (integrable_const _).add (integrable_gaussian_id.const_mul _)
  exact hAB.add ((integrable_gaussian_pow 2).const_mul C)

lemma expectation_quadratic (A B C : ℝ) : expectation (quadratic A B C) = A + C := by
  have hA : Integrable (fun _ : ℝ => A) standardGaussian := integrable_const _
  have hB : Integrable (fun u : ℝ => B * u) standardGaussian := integrable_gaussian_id.const_mul _
  have hC : Integrable (fun u : ℝ => C * u ^ 2) standardGaussian :=
    (integrable_gaussian_pow 2).const_mul _
  have hAB : Integrable (fun u : ℝ => A + B * u) standardGaussian := hA.add hB
  simp only [expectation, quadratic]
  rw [integral_add hAB hC, integral_add hA hB, integral_const_mul, integral_const_mul]
  simp only [integral_const, probReal_univ, one_smul]
  change A + B * expectation (fun u : ℝ => u) + C * expectation (fun u : ℝ => u ^ 2) = A + C
  rw [expectation_id, expectation_square]
  ring

/-- The actual Gaussian contact functional annihilates every quadratic polynomial. -/
theorem contact_quadratic (x A B C : ℝ) : contact x (quadratic A B C) = 0 := by
  have hE1 : expectation (deriv (quadratic A B C)) = B := by
    rw [deriv_quadratic]
    have heq : (fun u : ℝ => B + 2 * C * u) = quadratic B (2 * C) 0 := by
      ext u
      simp [quadratic]
    rw [heq, expectation_quadratic]
    ring
  have hE2 : expectation (iteratedDeriv 2 (quadratic A B C)) = 2 * C := by
    rw [secondDeriv_quadratic]
    simp [expectation]
  rw [contact, expectation_quadratic, hE1, hE2, quadratic]
  ring

end BerryEsseen.GaussianPeano

#print axioms BerryEsseen.GaussianPeano.contact_hinge_eq_kernel
#print axioms BerryEsseen.GaussianPeano.contact_quadratic
