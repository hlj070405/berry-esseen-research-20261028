module

public import BerryEsseen.GaussianPeano
public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

/-! 2026-10-28: the global C3 Gaussian Peano representation, using actual
oriented Taylor kernels and absolutely integrable Gaussian/Lebesgue Fubini. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators Interval
open BerryEsseen.GaussianTools BerryEsseen.GaussianPeano

namespace BerryEsseen.GaussianPeanoRepresentation

open GaussianTools GaussianPeano

/-- Degree-n Taylor polynomial at zero, with global iterated derivatives. -/
def taylorPolynomial (n : ℕ) (g : ℝ → ℝ) (u : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), u ^ k / (k.factorial : ℝ) * iteratedDeriv k g 0

lemma taylorPolynomial_zero (n : ℕ) (g : ℝ → ℝ) : taylorPolynomial n g 0 = g 0 := by
  classical
  unfold taylorPolynomial
  rw [Finset.sum_eq_single 0]
  · simp [iteratedDeriv_zero]
  · intro k hk hk0
    simp [hk0]
  · simp

lemma taylorWithinEval_eq_global (n : ℕ) (g : ℝ → ℝ)
    (hg : ContDiff ℝ (n + 1 : ℕ) g) (u : ℝ) (hu : u ≠ 0) :
    taylorWithinEval g n (uIcc 0 u) 0 u = taylorPolynomial n g u := by
  classical
  have hs : UniqueDiffOn ℝ (uIcc 0 u) := uniqueDiffOn_uIcc (Ne.symm hu)
  rw [taylor_within_apply, taylorPolynomial]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hgk : ContDiff ℝ k g := hg.of_le (by exact_mod_cast Nat.le_succ_of_le hkn)
  rw [iteratedDerivWithin_eq_iteratedDeriv hs hgk.contDiffAt left_mem_uIcc]
  simp only [sub_zero, smul_eq_mul]
  ring

/-- Official integral Taylor remainder, with global derivatives and an arbitrary endpoint. -/
theorem taylor_global (n : ℕ) (g : ℝ → ℝ) (hg : ContDiff ℝ (n + 1 : ℕ) g) (u : ℝ) :
    g u - taylorPolynomial n g u =
      ∫ t in (0 : ℝ)..u, ((u - t) ^ n / (n.factorial : ℝ)) * iteratedDeriv (n + 1) g t := by
  by_cases hu : u = 0
  · subst u
    simp [taylorPolynomial_zero]
  have hs : UniqueDiffOn ℝ (uIcc 0 u) := uniqueDiffOn_uIcc (Ne.symm hu)
  have h := taylor_integral_remainder (n := n) (x₀ := (0 : ℝ)) (x := u) hg.contDiffOn
  rw [taylorWithinEval_eq_global n g hg u hu] at h
  calc
    g u - taylorPolynomial n g u =
        ∫ t in (0 : ℝ)..u, ((u - t) ^ n / (n.factorial : ℝ)) •
          iteratedDerivWithin (n + 1) g (uIcc 0 u) t := h
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro t ht
      dsimp only
      rw [iteratedDerivWithin_eq_iteratedDeriv hs hg.contDiffAt ht]
      rfl

/-- The Lebesgue kernel of an oriented integral from zero to u. -/
def orientedKernel (n : ℕ) (u t : ℝ) : ℝ :=
  if 0 ≤ u then (Ioc 0 u).indicator (fun t : ℝ => (u - t) ^ n / (n.factorial : ℝ)) t
  else -(Ioc u 0).indicator (fun t : ℝ => (u - t) ^ n / (n.factorial : ℝ)) t

lemma integral_orientedKernel (f : ℝ → ℝ) (n : ℕ) (u : ℝ) :
    (∫ t, f t * orientedKernel n u t) =
      ∫ t in (0 : ℝ)..u, ((u - t) ^ n / (n.factorial : ℝ)) * f t := by
  by_cases hu : 0 ≤ u
  · simp only [orientedKernel, ite_eq_left hu]
    have heq : (fun t : ℝ => f t * (Ioc 0 u).indicator
        (fun t : ℝ => (u - t) ^ n / (n.factorial : ℝ)) t) =
        (Ioc 0 u).indicator (fun t : ℝ => ((u - t) ^ n / (n.factorial : ℝ)) * f t) := by
      ext t
      by_cases ht : t ∈ Ioc 0 u <;> simp [ht, mul_comm]
    rw [heq, integral_indicator measurableSet_Ioc, intervalIntegral.integral_of_le hu]
  · simp only [orientedKernel, ite_eq_right hu]
    have heq : (fun t : ℝ => f t * -(Ioc u 0).indicator
        (fun t : ℝ => (u - t) ^ n / (n.factorial : ℝ)) t) =
        (fun t : ℝ => -((Ioc u 0).indicator
          (fun t : ℝ => ((u - t) ^ n / (n.factorial : ℝ)) * f t) t)) := by
      ext t
      by_cases ht : t ∈ Ioc u 0 <;> simp [ht, mul_comm]
    rw [heq, integral_neg, integral_indicator measurableSet_Ioc,
      intervalIntegral.integral_of_ge (le_of_not_ge hu)]

theorem taylor_oriented (n : ℕ) (g : ℝ → ℝ) (hg : ContDiff ℝ (n + 1 : ℕ) g) (u : ℝ) :
    g u = taylorPolynomial n g u + ∫ t, iteratedDeriv (n + 1) g t * orientedKernel n u t := by
  rw [integral_orientedKernel]
  linarith [taylor_global n g hg u]

end BerryEsseen.GaussianPeanoRepresentation

#print axioms BerryEsseen.GaussianPeanoRepresentation.taylor_global
#print axioms BerryEsseen.GaussianPeanoRepresentation.taylor_oriented

namespace BerryEsseen.GaussianPeanoRepresentation

lemma measurable_orientedKernel (n : ℕ) :
    Measurable (fun p : ℝ × ℝ => orientedKernel n p.1 p.2) := by
  unfold orientedKernel
  simp only [Set.indicator_apply, Set.mem_Ioc]
  apply Measurable.ite
  · measurability
  · exact Measurable.ite (by measurability) (by fun_prop) measurable_const
  · apply Measurable.neg
    exact Measurable.ite (by measurability) (by fun_prop) measurable_const

lemma norm_orientedKernel (f : ℝ → ℝ) (n : ℕ) (u t : ℝ) :
    ‖f t * orientedKernel n u t‖ =
      (uIoc 0 u).indicator (fun t : ℝ => ‖f t * ((u - t) ^ n / (n.factorial : ℝ))‖) t := by
  by_cases hu : 0 ≤ u
  · rw [orientedKernel, ite_eq_left hu, uIoc_of_le hu]
    by_cases ht : t ∈ Ioc 0 u <;> simp [ht]
  · rw [orientedKernel, ite_eq_right hu, uIoc_of_ge (le_of_not_ge hu)]
    by_cases ht : t ∈ Ioc u 0 <;> simp [ht, mul_neg]

lemma integrable_orientedKernel_section (f : ℝ → ℝ) (hfc : Continuous f) (n : ℕ) (u : ℝ) :
    Integrable (fun t : ℝ => f t * orientedKernel n u t) := by
  have hmeas : AEStronglyMeasurable (fun t : ℝ => f t * orientedKernel n u t) volume := by
    apply Measurable.aestronglyMeasurable
    exact hfc.measurable.mul ((measurable_orientedKernel n).comp (measurable_const.prodMk measurable_id))
  apply (integrable_norm_iff hmeas).mp
  have heq : (fun t : ℝ => ‖f t * orientedKernel n u t‖) =
      (uIoc 0 u).indicator (fun t : ℝ => ‖f t * ((u - t) ^ n / (n.factorial : ℝ))‖) :=
    funext (norm_orientedKernel f n u)
  rw [heq]
  apply (integrable_indicator_iff (show MeasurableSet (uIoc 0 u) from measurableSet_Ioc)).mpr
  have hc : Continuous (fun t : ℝ => f t * ((u - t) ^ n / (n.factorial : ℝ))) := by fun_prop
  exact (hc.intervalIntegrable 0 u).norm.def'

/-- The exact absolute Taylor price; this is the domination used for Fubini. -/
theorem integral_norm_orientedKernel_le (f : ℝ → ℝ) (hfc : Continuous f)
    (M : ℝ) (hbound : ∀ t, |f t| ≤ M) (n : ℕ) (u : ℝ) :
    (∫ t, ‖f t * orientedKernel n u t‖) ≤
      M * |u| ^ (n + 1) / ((n + 1).factorial : ℝ) := by
  have heq : (fun t : ℝ => ‖f t * orientedKernel n u t‖) =
      (uIoc 0 u).indicator (fun t : ℝ => ‖f t * ((u - t) ^ n / (n.factorial : ℝ))‖) :=
    funext (norm_orientedKernel f n u)
  rw [heq, integral_indicator (show MeasurableSet (uIoc 0 u) from measurableSet_Ioc)]
  have hfac : 0 < (n.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos n)
  have hc : Continuous (fun t : ℝ => f t * ((u - t) ^ n / (n.factorial : ℝ))) := by fun_prop
  have hwc : Continuous (fun t : ℝ => M / (n.factorial : ℝ) * |t - u| ^ n) := by fun_prop
  calc
    (∫ t in uIoc 0 u, ‖f t * ((u - t) ^ n / (n.factorial : ℝ))‖) ≤
        ∫ t in uIoc 0 u, M / (n.factorial : ℝ) * |t - u| ^ n := by
      apply integral_mono (hc.intervalIntegrable 0 u).norm.def' (hwc.intervalIntegrable 0 u).def'
      intro t
      dsimp only
      rw [Real.norm_eq_abs, abs_mul]
      calc
        |f t| * |(u - t) ^ n / (n.factorial : ℝ)| ≤
            M * |(u - t) ^ n / (n.factorial : ℝ)| :=
          mul_le_mul_of_nonneg_right (hbound t) (abs_nonneg _)
        _ = _ := by
          rw [abs_div, abs_pow, abs_of_pos hfac, abs_sub_comm]
          ring
    _ = (M / (n.factorial : ℝ)) * (|u| ^ (n + 1) / (n + 1)) := by
      rw [integral_const_mul, uIoc_comm 0 u, integral_pow_abs_sub_uIoc]
      simp only [zero_sub, abs_neg]
    _ = _ := by
      simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
        div_eq_mul_inv, mul_inv_rev]
      ring

/-- Absolute integrability on the actual Gaussian/Lebesgue product follows from the
Taylor price and actual Gaussian moments; it is not an additional hypothesis. -/
theorem integrable_prod_orientedKernel (f : ℝ → ℝ) (hfc : Continuous f)
    (M : ℝ) (hbound : ∀ t, |f t| ≤ M) (n : ℕ) :
    Integrable (fun p : ℝ × ℝ => f p.2 * orientedKernel n p.1 p.2)
      (standardGaussian.prod volume) := by
  have hsm : StronglyMeasurable (fun p : ℝ × ℝ => f p.2 * orientedKernel n p.1 p.2) :=
    ((hfc.measurable.comp measurable_snd).mul (measurable_orientedKernel n)).stronglyMeasurable
  apply (integrable_prod_iff hsm.aestronglyMeasurable).mpr
  refine ⟨Filter.Eventually.of_forall (integrable_orientedKernel_section f hfc n), ?_⟩
  have habspow : Integrable (fun u : ℝ => |u| ^ (n + 1)) standardGaussian := by
    simpa only [Real.norm_eq_abs, abs_pow] using (integrable_gaussian_pow (n + 1)).norm
  have hdom := (habspow.const_mul M).div_const ((n + 1).factorial : ℝ)
  have hinner : AEStronglyMeasurable
      (fun u : ℝ => ∫ t : ℝ, ‖f t * orientedKernel n u t‖) standardGaussian :=
    hsm.norm.integral_prod_right'.aestronglyMeasurable
  apply hdom.mono' hinner
  exact Filter.Eventually.of_forall fun u => by
    rw [Real.norm_of_nonneg (integral_nonneg fun t => norm_nonneg _)]
    exact integral_norm_orientedKernel_le f hfc M hbound n u

lemma integrable_oriented_remainder (f : ℝ → ℝ) (hfc : Continuous f)
    (M : ℝ) (hbound : ∀ t, |f t| ≤ M) (n : ℕ) :
    Integrable (fun u : ℝ => ∫ t, f t * orientedKernel n u t) standardGaussian :=
  (integrable_prod_orientedKernel f hfc M hbound n).integral_prod_left

lemma integrable_oriented_mean (f : ℝ → ℝ) (hfc : Continuous f)
    (M : ℝ) (hbound : ∀ t, |f t| ≤ M) (n : ℕ) :
    Integrable (fun t : ℝ => f t * expectation (fun u : ℝ => orientedKernel n u t)) := by
  simpa only [integral_const_mul, expectation] using
    (integrable_prod_orientedKernel f hfc M hbound n).integral_prod_right

/-- The needed Gaussian/Lebesgue interchange with its integrability discharged. -/
theorem fubini_orientedKernel (f : ℝ → ℝ) (hfc : Continuous f)
    (M : ℝ) (hbound : ∀ t, |f t| ≤ M) (n : ℕ) :
    (∫ u, (∫ t, f t * orientedKernel n u t) ∂standardGaussian) =
      ∫ t, f t * expectation (fun u : ℝ => orientedKernel n u t) := by
  have h := integral_integral_swap (μ := standardGaussian) (ν := volume)
    (f := fun u t : ℝ => f t * orientedKernel n u t)
    (integrable_prod_orientedKernel f hfc M hbound n)
  simpa only [integral_const_mul, expectation] using h

end BerryEsseen.GaussianPeanoRepresentation

#print axioms BerryEsseen.GaussianPeanoRepresentation.integral_norm_orientedKernel_le
#print axioms BerryEsseen.GaussianPeanoRepresentation.integrable_prod_orientedKernel
#print axioms BerryEsseen.GaussianPeanoRepresentation.fubini_orientedKernel

namespace BerryEsseen.GaussianPeanoRepresentation

lemma orientedKernel_of_pos_t (n : ℕ) (u t : ℝ) (ht : 0 < t) :
    orientedKernel n u t = if t ≤ u then (u - t) ^ n / (n.factorial : ℝ) else 0 := by
  by_cases hu : 0 ≤ u
  · simp [orientedKernel, hu, Set.indicator_apply, ht]
  · have htu : ¬t ≤ u := by linarith
    have ht0 : ¬t ≤ 0 := not_le.mpr ht
    simp [orientedKernel, hu, htu, ht0]

lemma orientedKernel_of_neg_t (n : ℕ) (u t : ℝ) (ht : t < 0) :
    orientedKernel n u t = if u < t then -((u - t) ^ n / (n.factorial : ℝ)) else 0 := by
  by_cases hu : 0 ≤ u
  · have hut : ¬u < t := by linarith
    simp [orientedKernel, hu, hut, not_lt.mpr ht.le]
  · by_cases hut : u < t <;> simp [orientedKernel, hu, hut, ht.le]

def anchor2 (t u : ℝ) : ℝ :=
  hinge t u - quadratic (hinge t 0) (hingeSlope t 0) (hingeCurvature t 0 / 2) u

def anchor1 (t u : ℝ) : ℝ :=
  hingeSlope t u - quadratic (hingeSlope t 0) (hingeCurvature t 0) 0 u

def anchor0 (t u : ℝ) : ℝ := hingeCurvature t u - hingeCurvature t 0

lemma orientedKernel_two (u t : ℝ) (ht : t ≠ 0) : orientedKernel 2 u t = anchor2 t u := by
  rcases lt_or_gt_of_ne ht with ht | ht
  · rw [orientedKernel_of_neg_t 2 u t ht]
    have hz : max (-t) 0 = -t := max_eq_left (neg_nonneg.mpr ht.le)
    by_cases hut : u < t
    · have hu : max (u - t) 0 = 0 := max_eq_right (sub_nonpos.mpr hut.le)
      norm_num [anchor2, quadratic, hinge, hingeSlope, hingeCurvature, ht, hut, hu, hz]; ring
    · have hu : max (u - t) 0 = u - t := max_eq_left (sub_nonneg.mpr (le_of_not_gt hut))
      norm_num [anchor2, quadratic, hinge, hingeSlope, hingeCurvature, ht, hut, hu, hz]; ring
  · rw [orientedKernel_of_pos_t 2 u t ht]
    have hz : max (-t) 0 = 0 := max_eq_right (neg_nonpos.mpr ht.le)
    have ht0 : ¬t < 0 := not_lt.mpr ht.le
    by_cases htu : t ≤ u
    · have hu : max (u - t) 0 = u - t := max_eq_left (sub_nonneg.mpr htu)
      norm_num [anchor2, quadratic, hinge, hingeSlope, hingeCurvature, ht0, htu, hu, hz]
    · have hu : max (u - t) 0 = 0 := max_eq_right (sub_nonpos.mpr (le_of_not_ge htu))
      norm_num [anchor2, quadratic, hinge, hingeSlope, hingeCurvature, ht0, htu, hu, hz]

lemma orientedKernel_one (u t : ℝ) (ht : t ≠ 0) : orientedKernel 1 u t = anchor1 t u := by
  rcases lt_or_gt_of_ne ht with ht | ht
  · rw [orientedKernel_of_neg_t 1 u t ht]
    have hz : max (-t) 0 = -t := max_eq_left (neg_nonneg.mpr ht.le)
    by_cases hut : u < t
    · have hu : max (u - t) 0 = 0 := max_eq_right (sub_nonpos.mpr hut.le)
      norm_num [anchor1, quadratic, hingeSlope, hingeCurvature, ht, hut, hu, hz]; ring
    · have hu : max (u - t) 0 = u - t := max_eq_left (sub_nonneg.mpr (le_of_not_gt hut))
      norm_num [anchor1, quadratic, hingeSlope, hingeCurvature, ht, hut, hu, hz]; ring
  · rw [orientedKernel_of_pos_t 1 u t ht]
    have hz : max (-t) 0 = 0 := max_eq_right (neg_nonpos.mpr ht.le)
    have ht0 : ¬t < 0 := not_lt.mpr ht.le
    by_cases htu : t ≤ u
    · have hu : max (u - t) 0 = u - t := max_eq_left (sub_nonneg.mpr htu)
      norm_num [anchor1, quadratic, hingeSlope, hingeCurvature, ht0, htu, hu, hz]
    · have hu : max (u - t) 0 = 0 := max_eq_right (sub_nonpos.mpr (le_of_not_ge htu))
      norm_num [anchor1, quadratic, hingeSlope, hingeCurvature, ht0, htu, hu, hz]

lemma orientedKernel_zero (u t : ℝ) (ht : t ≠ 0) (hut : u ≠ t) :
    orientedKernel 0 u t = anchor0 t u := by
  rcases lt_or_gt_of_ne ht with ht | ht
  · rw [orientedKernel_of_neg_t 0 u t ht]
    rcases lt_or_gt_of_ne hut with hut | htu
    · have htu : ¬t < u := not_lt.mpr hut.le
      simp [anchor0, hingeCurvature, ht, hut, htu]
    · have hut : ¬u < t := not_lt.mpr htu.le
      simp [anchor0, hingeCurvature, ht, hut, htu]
  · rw [orientedKernel_of_pos_t 0 u t ht]
    have ht0 : ¬t < 0 := not_lt.mpr ht.le
    rcases lt_or_gt_of_ne hut with hut | htu
    · have htu : ¬t < u := not_lt.mpr hut.le
      have htle : ¬t ≤ u := not_le.mpr hut
      simp [anchor0, hingeCurvature, ht0, htu, htle]
    · simp [anchor0, hingeCurvature, ht0, htu, htu.le]

lemma expectation_orientedKernel_two (t : ℝ) (ht : t ≠ 0) :
    expectation (fun u : ℝ => orientedKernel 2 u t) =
      expectation (hinge t) - (hinge t 0 + hingeCurvature t 0 / 2) := by
  have heq : (fun u : ℝ => orientedKernel 2 u t) = anchor2 t :=
    funext fun u => orientedKernel_two u t ht
  rw [heq]
  change expectation (fun u : ℝ => hinge t u -
    quadratic (hinge t 0) (hingeSlope t 0) (hingeCurvature t 0 / 2) u) = _
  rw [expectation, integral_sub (integrable_hinge t) (integrable_quadratic _ _ _)]
  change expectation (hinge t) - expectation (quadratic _ _ _) = _
  rw [expectation_quadratic]

lemma expectation_orientedKernel_one (t : ℝ) (ht : t ≠ 0) :
    expectation (fun u : ℝ => orientedKernel 1 u t) =
      expectation (hingeSlope t) - hingeSlope t 0 := by
  have heq : (fun u : ℝ => orientedKernel 1 u t) = anchor1 t :=
    funext fun u => orientedKernel_one u t ht
  rw [heq]
  change expectation (fun u : ℝ => hingeSlope t u - quadratic (hingeSlope t 0) (hingeCurvature t 0) 0 u) = _
  rw [expectation, integral_sub (integrable_hingeSlope t) (integrable_quadratic _ _ _)]
  change expectation (hingeSlope t) - expectation (quadratic _ _ _) = _
  rw [expectation_quadratic]
  ring

lemma expectation_orientedKernel_zero (t : ℝ) (ht : t ≠ 0) :
    expectation (fun u : ℝ => orientedKernel 0 u t) =
      expectation (hingeCurvature t) - hingeCurvature t 0 := by
  let : NullSingletonClass standardGaussian := nullSingletonClass_gaussianReal (by norm_num)
  have heq : (fun u : ℝ => orientedKernel 0 u t) =ᵐ[standardGaussian] anchor0 t := by
    filter_upwards [standardGaussian.ae_ne t] with u hut
    exact orientedKernel_zero u t ht hut
  rw [expectation, integral_congr_ae heq]
  change (∫ u, hingeCurvature t u - hingeCurvature t 0 ∂standardGaussian) = _
  rw [integral_sub (integrable_hingeCurvature t) (integrable_const _)]
  simp only [integral_const, probReal_univ, one_smul]
  rfl

/-- The oriented Taylor/Fubini kernels combine to exactly the frozen manuscript kernel. -/
theorem kernel_eq_orientedKernels (x t : ℝ) (ht : t ≠ 0) :
    kernel x t = orientedKernel 2 x t - expectation (fun u : ℝ => orientedKernel 2 u t) -
      x * expectation (fun u : ℝ => orientedKernel 1 u t) -
      (x ^ 2 - 1) / 2 * expectation (fun u : ℝ => orientedKernel 0 u t) := by
  rw [orientedKernel_two x t ht, expectation_orientedKernel_two t ht,
    expectation_orientedKernel_one t ht, expectation_orientedKernel_zero t ht,
    ← hinge_jet_eq_kernel x t]
  simp only [anchor2, quadratic]
  ring

end BerryEsseen.GaussianPeanoRepresentation

#print axioms BerryEsseen.GaussianPeanoRepresentation.kernel_eq_orientedKernels

namespace BerryEsseen.GaussianPeanoRepresentation

lemma taylorPolynomial_degree_zero (g : ℝ → ℝ) (u : ℝ) : taylorPolynomial 0 g u = g 0 := by
  simp [taylorPolynomial, iteratedDeriv_zero]

lemma taylorPolynomial_degree_one (g : ℝ → ℝ) (u : ℝ) :
    taylorPolynomial 1 g u = quadratic (g 0) (deriv g 0) 0 u := by
  norm_num [taylorPolynomial, Finset.sum_range_succ, iteratedDeriv_zero, iteratedDeriv_one, quadratic]; ring

lemma taylorPolynomial_degree_two (g : ℝ → ℝ) (u : ℝ) :
    taylorPolynomial 2 g u = quadratic (g 0) (deriv g 0) (iteratedDeriv 2 g 0 / 2) u := by
  norm_num [taylorPolynomial, Finset.sum_range_succ, iteratedDeriv_zero, iteratedDeriv_one, quadratic]; ring

def remainder (n : ℕ) (g : ℝ → ℝ) (u : ℝ) : ℝ :=
  ∫ t, iteratedDeriv 3 g t * orientedKernel n u t

lemma remainder_identity_two (g : ℝ → ℝ) (hg : ContDiff ℝ 3 g) (u : ℝ) :
    g u = quadratic (g 0) (deriv g 0) (iteratedDeriv 2 g 0 / 2) u + remainder 2 g u := by
  simpa only [taylorPolynomial_degree_two, remainder] using taylor_oriented 2 g hg u

lemma remainder_identity_one (g : ℝ → ℝ) (hg : ContDiff ℝ 3 g) (u : ℝ) :
    deriv g u = quadratic (deriv g 0) (iteratedDeriv 2 g 0) 0 u + remainder 1 g u := by
  have hgd : ContDiff ℝ 2 (deriv g) := hg.deriv'
  have h := taylor_oriented 1 (deriv g) hgd u
  have hsecond : deriv (deriv g) = iteratedDeriv 2 g := by
    rw [show (2 : ℕ) = 1 + 1 by rfl, iteratedDeriv_succ, iteratedDeriv_one]
  rw [taylorPolynomial_degree_one, hsecond, ← iteratedDeriv_succ' (n := 2) (f := g)] at h
  exact h

lemma remainder_identity_zero (g : ℝ → ℝ) (hg : ContDiff ℝ 3 g) (u : ℝ) :
    iteratedDeriv 2 g u = iteratedDeriv 2 g 0 + remainder 0 g u := by
  have hgd : ContDiff ℝ 1 (iteratedDeriv 2 g) :=
    (contDiff_nat_succ_iff_contDiff_one_iteratedDeriv (n := 2)).mp hg |>.2
  have h := taylor_oriented 0 (iteratedDeriv 2 g) hgd u
  rw [taylorPolynomial_degree_zero, iteratedDeriv_one, ← iteratedDeriv_succ (n := 2) (f := g)] at h
  exact h

lemma integrable_remainder (g : ℝ → ℝ) (hg : ContDiff ℝ 3 g) (M : ℝ)
    (hbound : ∀ t, |iteratedDeriv 3 g t| ≤ M) (n : ℕ) :
    Integrable (remainder n g) standardGaussian :=
  integrable_oriented_remainder (iteratedDeriv 3 g) (hg.continuous_iteratedDeriv 3 (by norm_num))
    M hbound n

/-- The three actual Gaussian expectations required by contact are finite under precisely C3
and the bounded third derivative hypothesis. -/
theorem gaussian_integrable_of_bounded_third (g : ℝ → ℝ) (hg : ContDiff ℝ 3 g) (M : ℝ)
    (hbound : ∀ t, |iteratedDeriv 3 g t| ≤ M) :
    Integrable g standardGaussian ∧ Integrable (deriv g) standardGaussian ∧
      Integrable (iteratedDeriv 2 g) standardGaussian := by
  constructor
  · have heq : g = (fun u : ℝ => quadratic (g 0) (deriv g 0) (iteratedDeriv 2 g 0 / 2) u + remainder 2 g u) :=
      funext (remainder_identity_two g hg)
    rw [heq]
    exact (integrable_quadratic _ _ _).add (integrable_remainder g hg M hbound 2)
  constructor
  · have heq : deriv g = (fun u : ℝ => quadratic (deriv g 0) (iteratedDeriv 2 g 0) 0 u + remainder 1 g u) :=
      funext (remainder_identity_one g hg)
    rw [heq]
    exact (integrable_quadratic _ _ _).add (integrable_remainder g hg M hbound 1)
  · have heq : iteratedDeriv 2 g = (fun u : ℝ => iteratedDeriv 2 g 0 + remainder 0 g u) :=
      funext (remainder_identity_zero g hg)
    rw [heq]
    exact (integrable_const _).add (integrable_remainder g hg M hbound 0)

lemma expectation_remainder_two (g : ℝ → ℝ) (hg : ContDiff ℝ 3 g) (M : ℝ)
    (hbound : ∀ t, |iteratedDeriv 3 g t| ≤ M) :
    expectation g = (g 0 + iteratedDeriv 2 g 0 / 2) + expectation (remainder 2 g) := by
  calc
    expectation g = expectation (fun u : ℝ =>
        quadratic (g 0) (deriv g 0) (iteratedDeriv 2 g 0 / 2) u + remainder 2 g u) :=
      congrArg expectation (funext (remainder_identity_two g hg))
    _ = expectation (quadratic _ _ _) + expectation (remainder 2 g) :=
      integral_add (integrable_quadratic _ _ _) (integrable_remainder g hg M hbound 2)
    _ = _ := by rw [expectation_quadratic]

lemma expectation_remainder_one (g : ℝ → ℝ) (hg : ContDiff ℝ 3 g) (M : ℝ)
    (hbound : ∀ t, |iteratedDeriv 3 g t| ≤ M) :
    expectation (deriv g) = deriv g 0 + expectation (remainder 1 g) := by
  calc
    expectation (deriv g) = expectation (fun u : ℝ =>
        quadratic (deriv g 0) (iteratedDeriv 2 g 0) 0 u + remainder 1 g u) :=
      congrArg expectation (funext (remainder_identity_one g hg))
    _ = expectation (quadratic _ _ _) + expectation (remainder 1 g) :=
      integral_add (integrable_quadratic _ _ _) (integrable_remainder g hg M hbound 1)
    _ = _ := by rw [expectation_quadratic]; ring

lemma expectation_remainder_zero (g : ℝ → ℝ) (hg : ContDiff ℝ 3 g) (M : ℝ)
    (hbound : ∀ t, |iteratedDeriv 3 g t| ≤ M) :
    expectation (iteratedDeriv 2 g) = iteratedDeriv 2 g 0 + expectation (remainder 0 g) := by
  calc
    expectation (iteratedDeriv 2 g) = expectation (fun u : ℝ => iteratedDeriv 2 g 0 + remainder 0 g u) :=
      congrArg expectation (funext (remainder_identity_zero g hg))
    _ = _ := by
      rw [expectation, integral_add (integrable_const _) (integrable_remainder g hg M hbound 0)]
      simp only [integral_const, probReal_univ, one_smul]
      rfl

/-- All polynomial Taylor contributions cancel in the original contact functional. -/
lemma contact_eq_remainders (g : ℝ → ℝ) (hg : ContDiff ℝ 3 g) (M : ℝ)
    (hbound : ∀ t, |iteratedDeriv 3 g t| ≤ M) (x : ℝ) :
    contact x g = remainder 2 g x - expectation (remainder 2 g) -
      x * expectation (remainder 1 g) - (x ^ 2 - 1) / 2 * expectation (remainder 0 g) := by
  rw [contact, expectation_remainder_two g hg M hbound, expectation_remainder_one g hg M hbound,
    expectation_remainder_zero g hg M hbound, remainder_identity_two g hg x]
  simp only [quadratic]
  ring

def combinedIntegrand (f : ℝ → ℝ) (x t : ℝ) : ℝ :=
  f t * orientedKernel 2 x t - f t * expectation (fun u : ℝ => orientedKernel 2 u t) -
    x * (f t * expectation (fun u : ℝ => orientedKernel 1 u t)) -
    (x ^ 2 - 1) / 2 * (f t * expectation (fun u : ℝ => orientedKernel 0 u t))

lemma integrable_combinedIntegrand (f : ℝ → ℝ) (hfc : Continuous f) (M : ℝ)
    (hbound : ∀ t, |f t| ≤ M) (x : ℝ) : Integrable (combinedIntegrand f x) := by
  have hAB : Integrable (fun t : ℝ => f t * orientedKernel 2 x t -
      f t * expectation (fun u : ℝ => orientedKernel 2 u t)) :=
    (integrable_orientedKernel_section f hfc 2 x).sub (integrable_oriented_mean f hfc M hbound 2)
  exact (hAB.sub ((integrable_oriented_mean f hfc M hbound 1).const_mul x)).sub
    ((integrable_oriented_mean f hfc M hbound 0).const_mul ((x ^ 2 - 1) / 2))

lemma combinedIntegrand_ae_kernel (f : ℝ → ℝ) (x : ℝ) :
    combinedIntegrand f x =ᵐ[volume] (fun t : ℝ => f t * kernel x t) := by
  filter_upwards [volume.ae_ne (0 : ℝ)] with t ht
  dsimp only [combinedIntegrand]
  rw [kernel_eq_orientedKernels x t ht]
  ring

/-- The Lebesgue integrand in the Peano representation is actually integrable. -/
theorem integrable_third_mul_kernel (g : ℝ → ℝ) (hg : ContDiff ℝ 3 g) (M : ℝ)
    (hbound : ∀ t, |iteratedDeriv 3 g t| ≤ M) (x : ℝ) :
    Integrable (fun t : ℝ => iteratedDeriv 3 g t * kernel x t) :=
  (integrable_combinedIntegrand (iteratedDeriv 3 g) (hg.continuous_iteratedDeriv 3 (by norm_num))
    M hbound x).congr (combinedIntegrand_ae_kernel (iteratedDeriv 3 g) x)

lemma integral_combinedIntegrand (f : ℝ → ℝ) (hfc : Continuous f) (M : ℝ)
    (hbound : ∀ t, |f t| ≤ M) (x : ℝ) :
    (∫ t, combinedIntegrand f x t) = (∫ t, f t * orientedKernel 2 x t) -
      (∫ u, (∫ t, f t * orientedKernel 2 u t) ∂standardGaussian) -
      x * (∫ u, (∫ t, f t * orientedKernel 1 u t) ∂standardGaussian) -
      (x ^ 2 - 1) / 2 * (∫ u, (∫ t, f t * orientedKernel 0 u t) ∂standardGaussian) := by
  have hA := integrable_orientedKernel_section f hfc 2 x
  have hB := integrable_oriented_mean f hfc M hbound 2
  have hC := (integrable_oriented_mean f hfc M hbound 1).const_mul x
  have hD := (integrable_oriented_mean f hfc M hbound 0).const_mul ((x ^ 2 - 1) / 2)
  have hAB : Integrable (fun t : ℝ => f t * orientedKernel 2 x t -
      f t * expectation (fun u : ℝ => orientedKernel 2 u t)) := hA.sub hB
  have hABC : Integrable (fun t : ℝ => f t * orientedKernel 2 x t -
      f t * expectation (fun u : ℝ => orientedKernel 2 u t) -
      x * (f t * expectation (fun u : ℝ => orientedKernel 1 u t))) := hAB.sub hC
  simp only [combinedIntegrand]
  rw [integral_sub hABC hD, integral_sub hAB hC, integral_sub hA hB,
    integral_const_mul, integral_const_mul,
    ← fubini_orientedKernel f hfc M hbound 2,
    ← fubini_orientedKernel f hfc M hbound 1,
    ← fubini_orientedKernel f hfc M hbound 0]

/-- The manuscript's full Peano representation for a global C3 function with bounded
third derivative, with actual Gaussian expectations and an actual Lebesgue integral. -/
theorem contact_eq_integral_third_mul_kernel (g : ℝ → ℝ) (hg : ContDiff ℝ 3 g) (M : ℝ)
    (hbound : ∀ t, |iteratedDeriv 3 g t| ≤ M) (x : ℝ) :
    contact x g = ∫ t, iteratedDeriv 3 g t * kernel x t := by
  have hfc := hg.continuous_iteratedDeriv 3 (by norm_num)
  calc
    contact x g = remainder 2 g x - expectation (remainder 2 g) -
        x * expectation (remainder 1 g) - (x ^ 2 - 1) / 2 * expectation (remainder 0 g) :=
      contact_eq_remainders g hg M hbound x
    _ = ∫ t, combinedIntegrand (iteratedDeriv 3 g) x t := by
      simpa only [remainder, expectation] using
        (integral_combinedIntegrand (iteratedDeriv 3 g) hfc M hbound x).symm
    _ = _ := integral_congr_ae (combinedIntegrand_ae_kernel (iteratedDeriv 3 g) x)

end BerryEsseen.GaussianPeanoRepresentation

#print axioms BerryEsseen.GaussianPeanoRepresentation.gaussian_integrable_of_bounded_third
#print axioms BerryEsseen.GaussianPeanoRepresentation.integrable_third_mul_kernel
#print axioms BerryEsseen.GaussianPeanoRepresentation.contact_eq_integral_third_mul_kernel


namespace BerryEsseen.GaussianPeanoRepresentation

/-- Actual remainder values have the same sharp factorial domination as their absolute integrals. -/
theorem abs_remainder_le (g : ℝ → ℝ) (hg : ContDiff ℝ 3 g) (M : ℝ)
    (hbound : ∀ t, |iteratedDeriv 3 g t| ≤ M) (n : ℕ) (u : ℝ) :
    |remainder n g u| ≤ M * |u| ^ (n + 1) / ((n + 1).factorial : ℝ) := by
  calc
    |remainder n g u| = ‖remainder n g u‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ t, ‖iteratedDeriv 3 g t * orientedKernel n u t‖ := norm_integral_le_integral_norm _
    _ ≤ _ := integral_norm_orientedKernel_le (iteratedDeriv 3 g)
      (hg.continuous_iteratedDeriv 3 (by norm_num)) M hbound n u

lemma abs_remainder_two_le (g : ℝ → ℝ) (hg : ContDiff ℝ 3 g) (M : ℝ)
    (hbound : ∀ t, |iteratedDeriv 3 g t| ≤ M) (u : ℝ) :
    |remainder 2 g u| ≤ M * |u| ^ 3 / 6 := by
  simpa only [show ((2 + 1).factorial : ℝ) = 6 by norm_num] using
    abs_remainder_le g hg M hbound 2 u

lemma abs_remainder_one_le (g : ℝ → ℝ) (hg : ContDiff ℝ 3 g) (M : ℝ)
    (hbound : ∀ t, |iteratedDeriv 3 g t| ≤ M) (u : ℝ) :
    |remainder 1 g u| ≤ M * |u| ^ 2 / 2 := by
  simpa only [show ((1 + 1).factorial : ℝ) = 2 by norm_num] using
    abs_remainder_le g hg M hbound 1 u

lemma abs_remainder_zero_le (g : ℝ → ℝ) (hg : ContDiff ℝ 3 g) (M : ℝ)
    (hbound : ∀ t, |iteratedDeriv 3 g t| ≤ M) (u : ℝ) :
    |remainder 0 g u| ≤ M * |u| := by
  simpa only [show ((0 + 1).factorial : ℝ) = 1 by norm_num, Nat.zero_add, pow_one, div_one] using
    abs_remainder_le g hg M hbound 0 u

/-- The frozen kernel itself is Lebesgue integrable, by the same Fubini domination. -/
theorem integrable_kernel (x : ℝ) : Integrable (kernel x) := by
  have h := (integrable_combinedIntegrand (fun _ : ℝ => (1 : ℝ)) continuous_const 1
    (by intro t; norm_num) x).congr
      (combinedIntegrand_ae_kernel (fun _ : ℝ => (1 : ℝ)) x)
  simpa only [one_mul] using h

end BerryEsseen.GaussianPeanoRepresentation

#print axioms BerryEsseen.GaussianPeanoRepresentation.abs_remainder_two_le
#print axioms BerryEsseen.GaussianPeanoRepresentation.abs_remainder_one_le
#print axioms BerryEsseen.GaussianPeanoRepresentation.abs_remainder_zero_le
#print axioms BerryEsseen.GaussianPeanoRepresentation.integrable_kernel
