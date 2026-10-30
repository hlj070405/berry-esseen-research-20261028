module

public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

@[expose] public section

/-! 2026-10-28: Rational Gaussian tail with its actual improper integral.
The proof differentiates an explicit upper primitive; its nonnegative remainder
also proves absolute integrability of the original integrand. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace BerryEsseen.RationalGaussianTail

def denominator (x : ℝ) : ℝ := x ^ 2 + 4 * x + 2

def Lambda (x : ℝ) : ℝ := (x + 2) / denominator x

lemma denominator_pos (x : ℝ) (hx : 0 ≤ x) : 0 < denominator x := by
  unfold denominator
  positivity

lemma Lambda_nonneg (x : ℝ) (hx : 0 ≤ x) : 0 ≤ Lambda x := by
  exact div_nonneg (by linarith) (denominator_pos x hx).le

lemma Lambda_le_one (x : ℝ) (hx : 0 ≤ x) : Lambda x ≤ 1 := by
  unfold Lambda
  apply (div_le_one₀ (denominator_pos x hx)).mpr
  unfold denominator
  nlinarith

lemma hasDerivAt_Lambda (x : ℝ) (hx : 0 ≤ x) :
    HasDerivAt Lambda (-(x ^ 2 + 4 * x + 6) / denominator x ^ 2) x := by
  have hD : HasDerivAt denominator (2 * x + 4) x := by
    convert (((hasDerivAt_id' x).pow 2).add ((hasDerivAt_id' x).const_mul 4)).add_const 2 using 1
    · ext y
      simp only [denominator, Pi.pow_apply, Pi.add_apply]
    · ring
  have h := ((hasDerivAt_id' x).add_const 2).div hD (ne_of_gt (denominator_pos x hx))
  convert h using 1
  · rfl
  · unfold denominator
    ring

/-- The proposed upper primitive at Gaussian rate c. -/
def barrier (c t : ℝ) : ℝ := Real.exp (-c * t ^ 2) / (2 * t ^ 2) * Lambda (c * t ^ 2)

/-- The derivative's exact positive price, including the discarded rational remainder. -/
def derivativePrice (c t : ℝ) : ℝ :=
  Real.exp (-c * t ^ 2) / t ^ 3 +
    4 * c * Real.exp (-c * t ^ 2) / (t * denominator (c * t ^ 2) ^ 2)

lemma hasDerivAt_barrier (c t : ℝ) (hc : 0 < c) (ht : 0 < t) :
    HasDerivAt (barrier c) (-derivativePrice c t) t := by
  have hct : 0 ≤ c * t ^ 2 := mul_nonneg hc.le (sq_nonneg t)
  have hinner : HasDerivAt (fun t : ℝ => c * t ^ 2) (2 * c * t) t := by
    convert ((hasDerivAt_id' t).pow 2).const_mul c using 1
    ring
  have hexp := hinner.neg.exp
  have hden : HasDerivAt (fun t : ℝ => 2 * t ^ 2) (4 * t) t := by
    convert ((hasDerivAt_id' t).pow 2).const_mul 2 using 1
    ring
  have h := (hexp.div hden (by positivity)).mul ((hasDerivAt_Lambda _ hct).comp t hinner)
  convert h using 1
  · ext y
    simp only [barrier, Pi.mul_apply, Pi.div_apply, Pi.neg_apply, Function.comp_apply, neg_mul]
  · dsimp only [derivativePrice, Lambda, Pi.mul_apply, Pi.div_apply, Pi.neg_apply,
      Function.comp_apply]
    simp only [neg_mul]
    field_simp [ne_of_gt ht, ne_of_gt (denominator_pos _ hct)]
    unfold denominator
    ring

lemma derivativePrice_nonneg (c t : ℝ) (hc : 0 < c) (ht : 0 < t) :
    0 ≤ derivativePrice c t := by
  unfold derivativePrice
  positivity

lemma integrand_le_derivativePrice (c t : ℝ) (hc : 0 < c) (ht : 0 < t) :
    Real.exp (-c * t ^ 2) / t ^ 3 ≤ derivativePrice c t := by
  unfold derivativePrice
  have h : 0 ≤ 4 * c * Real.exp (-c * t ^ 2) /
      (t * denominator (c * t ^ 2) ^ 2) := by positivity
  linarith

lemma tendsto_barrier_atTop (c : ℝ) (hc : 0 < c) :
    Tendsto (barrier c) atTop (𝓝 0) := by
  have hlim : Tendsto (fun t : ℝ => 1 / (2 * t ^ 2)) atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop (Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2) (tendsto_pow_atTop (by norm_num)))
  apply squeeze_zero' _ _ hlim
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    unfold barrier
    exact mul_nonneg (by positivity) (Lambda_nonneg _ (by positivity))
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have he : Real.exp (-c * t ^ 2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg hc.le (sq_nonneg t)])
    have hl := Lambda_le_one (c * t ^ 2) (by positivity)
    unfold barrier
    calc
      _ ≤ (1 / (2 * t ^ 2)) * 1 := mul_le_mul (div_le_div_of_nonneg_right he (by positivity)) hl
        (Lambda_nonneg _ (by positivity)) (by positivity)
      _ = _ := mul_one _

lemma integrableOn_derivativePrice (c b : ℝ) (hc : 0 < c) (hb : 0 < b) :
    IntegrableOn (derivativePrice c) (Ioi b) := by
  have h := integrableOn_Ioi_deriv_of_nonpos'
    (fun t ht => hasDerivAt_barrier c t hc (hb.trans_le ht))
    (fun t ht => neg_nonpos.mpr (derivativePrice_nonneg c t hc (hb.trans ht)))
    (tendsto_barrier_atTop c hc)
  exact h.neg.congr (by filter_upwards [] with t; simp)

/-- Absolute integrability of the exact singular Gaussian tail, away from zero. -/
theorem integrableOn_gaussian_inv_cube (c b : ℝ) (hc : 0 < c) (hb : 0 < b) :
    IntegrableOn (fun t : ℝ => Real.exp (-c * t ^ 2) / t ^ 3) (Ioi b) := by
  have hm : Measurable (fun t : ℝ => Real.exp (-c * t ^ 2) / t ^ 3) :=
    (Real.continuous_exp.comp (continuous_const.mul (continuous_id.pow 2))).measurable.div
      (continuous_id.pow 3).measurable
  apply (integrableOn_derivativePrice c b hc hb).mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 < t := hb.trans ht
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ Real.exp (-c * t ^ 2) / t ^ 3)]
  exact integrand_le_derivativePrice c t hc (hb.trans ht)

lemma integral_derivativePrice (c b : ℝ) (hc : 0 < c) (hb : 0 < b) :
    (∫ t in Ioi b, derivativePrice c t) = barrier c b := by
  have h := integral_Ioi_of_hasDerivAt_of_nonpos'
    (fun t ht => hasDerivAt_barrier c t hc (hb.trans_le ht))
    (fun t ht => neg_nonpos.mpr (derivativePrice_nonneg c t hc (hb.trans ht)))
    (tendsto_barrier_atTop c hc)
  rw [integral_neg] at h
  linarith

/-- The rational Gaussian-tail estimate with no unproved change of variables. -/
theorem gaussian_inv_cube_tail (c b : ℝ) (hc : 0 < c) (hb : 0 < b) :
    (∫ t in Ioi b, Real.exp (-c * t ^ 2) / t ^ 3) ≤
      Real.exp (-c * b ^ 2) / (2 * b ^ 2) * Lambda (c * b ^ 2) := by
  calc
    _ ≤ ∫ t in Ioi b, derivativePrice c t := by
      apply integral_mono_ae (integrableOn_gaussian_inv_cube c b hc hb)
        (integrableOn_derivativePrice c b hc hb)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact integrand_le_derivativePrice c t hc (hb.trans ht)
    _ = _ := integral_derivativePrice c b hc hb

/-- The manuscript's original j,k,b coefficient, with x=j*k*b². -/
theorem rational_gaussian_tail (j k b : ℝ) (hj : 0 < j) (hk : 0 < k) (hb : 0 < b) :
    Real.sqrt j * (∫ t in Ioi b, Real.exp (-j * k * t ^ 2) / t ^ 3) ≤
      Real.sqrt j * Real.exp (-(j * k * b ^ 2)) / (2 * b ^ 2) * Lambda (j * k * b ^ 2) := by
  have h := mul_le_mul_of_nonneg_left (gaussian_inv_cube_tail (j * k) b (mul_pos hj hk) hb)
    (Real.sqrt_nonneg j)
  convert h using 1 <;> simp only [neg_mul]
  ring

end BerryEsseen.RationalGaussianTail

#print axioms BerryEsseen.RationalGaussianTail.integrableOn_gaussian_inv_cube
#print axioms BerryEsseen.RationalGaussianTail.gaussian_inv_cube_tail
#print axioms BerryEsseen.RationalGaussianTail.rational_gaussian_tail








