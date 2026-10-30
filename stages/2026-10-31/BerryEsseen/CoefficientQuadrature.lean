module

public import BerryEsseen.CoefficientPriceCells
public import BerryEsseen.SmallBetaRayEndpoint

@[expose] public section

/-! 2026-10-29: finite-cell integration and the actual coarse price's
analytic first cell. Open-cell inequalities suffice, so the exceptional
totalized Prawitz endpoints are not silently included in a numerical bound.
No numerical cell array or final endpoint value is assumed to be certified. -/

noncomputable section

open MeasureTheory Set
open scoped Interval BigOperators

namespace BerryEsseen.CoefficientQuadrature

open CoefficientRayPrice
open Causalean.Stat.CLT.BerryEsseen (prawitzKernel)

/-- The sum is an exact partition of the original real integral. Each
cell bound is required throughout its open interior, not just at samples. -/
theorem integral_le_cell_sum (f : ℝ → ℝ) (a B : ℕ → ℝ) (m : ℕ)
    (horder : ∀ j < m, a j ≤ a (j + 1))
    (hint : ∀ j < m, IntervalIntegrable f volume (a j) (a (j + 1)))
    (hbound : ∀ j < m, ∀ t ∈ Ioo (a j) (a (j + 1)), f t ≤ B j) :
    (∫ t in a 0..a m, f t) ≤ ∑ j ∈ Finset.range m, (a (j + 1) - a j) * B j := by
  rw [← intervalIntegral.sum_integral_adjacent_intervals hint]
  apply Finset.sum_le_sum
  intro j hj
  have hjm := Finset.mem_range.mp hj
  have hh := intervalIntegral.integral_mono_on_of_le_Ioo (horder j hjm) (hint j hjm)
    (intervalIntegrable_const (c := B j) (a := a j) (b := a (j + 1)) (μ := volume))
    (hbound j hjm)
  simpa only [intervalIntegral.integral_const, smul_eq_mul] using hh

private lemma forcingPolynomial_integral (l b : ℝ) :
    (∫ t in (0 : ℝ)..b, t ^ 2 / 2 + l * t ^ 3 / 3) = b ^ 3 / 6 + l * b ^ 4 / 12 := by
  have h2 : IntervalIntegrable (fun t : ℝ => (1 / 2 : ℝ) * t ^ 2) volume 0 b :=
    (by fun_prop : Continuous (fun t : ℝ => (1 / 2 : ℝ) * t ^ 2)).intervalIntegrable 0 b
  have h3 : IntervalIntegrable (fun t : ℝ => (l / 3) * t ^ 3) volume 0 b :=
    (by fun_prop : Continuous (fun t : ℝ => (l / 3) * t ^ 3)).intervalIntegrable 0 b
  have heq : (fun t : ℝ => t ^ 2 / 2 + l * t ^ 3 / 3) =
      (fun t : ℝ => (1 / 2 : ℝ) * t ^ 2 + (l / 3) * t ^ 3) := by
    funext t
    ring
  rw [heq, intervalIntegral.integral_add h2 h3]
  simp only [intervalIntegral.integral_const_mul, integral_pow]
  norm_num
  ring

theorem coarsePrice_le_first_polynomial (N : ℕ) (hN : 0 < N) (c β t : ℝ)
    (hβ : 0 < β) (ht : 0 ≤ t) :
    coarsePrice N c β t ≤ t ^ 3 / 6 + CoarseHighMomentRayPrice.lambda N β * t ^ 4 / 12 := by
  have hl := CoefficientPriceCells.lambda_nonneg N hN β hβ
  have hI : IntervalIntegrable (fun u : ℝ => Real.exp (-((t ^ 2 - u ^ 2) / 2)) *
      (lossEnvelope N c β u * (u ^ 2 / 2 + CoarseHighMomentRayPrice.lambda N β * u ^ 3 / 3)))
      volume 0 t := by
    apply Continuous.intervalIntegrable
    exact (by fun_prop : Continuous (fun u : ℝ => Real.exp (-((t ^ 2 - u ^ 2) / 2)))).mul
      ((continuous_lossEnvelope N c β).mul (by fun_prop))
  have hP : IntervalIntegrable (fun u : ℝ => u ^ 2 / 2 +
      CoarseHighMomentRayPrice.lambda N β * u ^ 3 / 3) volume 0 t :=
    (by fun_prop : Continuous (fun u : ℝ => u ^ 2 / 2 +
      CoarseHighMomentRayPrice.lambda N β * u ^ 3 / 3)).intervalIntegrable 0 t
  have hh := intervalIntegral.integral_mono_on ht hI hP (fun u hu => by
    have hu0 : 0 ≤ u := hu.1
    have hs := pow_le_pow_left₀ hu.1 hu.2 2
    have he : Real.exp (-((t ^ 2 - u ^ 2) / 2)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by linarith only [hs])
    have hL : lossEnvelope N c β u ≤ 1 := min_le_left _ _
    have hp : 0 ≤ u ^ 2 / 2 + CoarseHighMomentRayPrice.lambda N β * u ^ 3 / 3 := by positivity
    have hm := mul_le_mul he hL (lossEnvelope_nonneg N c β u) (by norm_num : (0 : ℝ) ≤ 1)
    have hmul := mul_le_mul_of_nonneg_right hm hp
    simpa only [one_mul, mul_assoc] using hmul)
  rw [forcingPolynomial_integral] at hh
  rw [CoefficientPriceCells.coarsePrice_split N c β 0 t]
  simpa only [coarsePrice, intervalIntegral.integral_same, mul_zero, add_zero, zero_add] using hh

def firstCellMajorant (l U t : ℝ) : ℝ :=
  (1 / (6 * Real.pi)) * t ^ 2 + (1 / (6 * U) + l / (12 * Real.pi)) * t ^ 3 +
    (l / (12 * U)) * t ^ 4

theorem scaled_first_integrand_le (N : ℕ) (hN : 0 < N) (c β U t : ℝ)
    (hβ : 0 < β) (hU : 0 < U) (ht : 0 < t) (htU : t ≤ U) :
    (2 / U) * (‖prawitzKernel (t / U)‖ * coarsePrice N c β t) ≤
      firstCellMajorant (CoarseHighMomentRayPrice.lambda N β) U t := by
  have hk := SmallBetaRayEndpoint.scaled_kernel_le U t hU ht htU
  have hp := coarsePrice_le_first_polynomial N hN c β t hβ ht.le
  have hp0 := CoefficientPriceCells.coarsePrice_nonneg N hN c β t hβ ht.le
  have hbound0 : 0 ≤ 1 / (Real.pi * t) + 1 / U := by positivity
  have hh := mul_le_mul hk hp hp0 hbound0
  calc
    _ = ((2 / U) * ‖prawitzKernel (t / U)‖) * coarsePrice N c β t := by ring
    _ ≤ _ := hh
    _ = firstCellMajorant (CoarseHighMomentRayPrice.lambda N β) U t := by
      unfold firstCellMajorant
      field_simp [hU.ne', ht.ne', Real.pi_ne_zero]
      ring

lemma measurable_kernel : Measurable prawitzKernel := by
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

/-- Measurability and the polynomial bound acquire genuine integrability
at the singular endpoint; no default-zero integral branch is used later. -/
theorem first_integrand_intervalIntegrable (N : ℕ) (hN : 0 < N) (c β b U : ℝ)
    (hβ : 0 < β) (hb : 0 < b) (hbU : b ≤ U) :
    IntervalIntegrable (fun t : ℝ => ‖prawitzKernel (t / U)‖ * coarsePrice N c β t)
      volume 0 b := by
  have hU := hb.trans_le hbU
  let f : ℝ → ℝ := fun t => (2 / U) * (‖prawitzKernel (t / U)‖ * coarsePrice N c β t)
  have hmeas : Measurable f :=
    measurable_const.mul (((measurable_kernel.comp (by fun_prop)).norm).mul
      (continuous_coarsePrice N c β).measurable)
  have hc : Continuous (firstCellMajorant (CoarseHighMomentRayPrice.lambda N β) U) := by
    unfold firstCellMajorant
    fun_prop
  have hdom : IntegrableOn (firstCellMajorant (CoarseHighMomentRayPrice.lambda N β) U)
      (Ioc (0 : ℝ) b) volume :=
    hc.integrableOn_Icc.mono_set (Ioc_subset_Icc_self (a := (0 : ℝ)) (b := b))
  have hf : IntegrableOn f (Ioc (0 : ℝ) b) := by
    apply hdom.mono' hmeas.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hnn : 0 ≤ f t := mul_nonneg (by positivity)
      (mul_nonneg (norm_nonneg _) (CoefficientPriceCells.coarsePrice_nonneg N hN c β t hβ ht.1.le))
    simpa only [Real.norm_eq_abs, abs_of_nonneg hnn] using
      scaled_first_integrand_le N hN c β U t hβ hU ht.1 (ht.2.trans hbU)
  have hi : IntervalIntegrable f volume 0 b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hb.le).mpr hf
  have hr := hi.const_mul (U / 2)
  convert hr using 1
  funext t
  dsimp [f]
  field_simp [hU.ne']

private lemma firstCellMajorant_integral (l U b : ℝ) :
    (∫ t in (0 : ℝ)..b, firstCellMajorant l U t) =
      b ^ 4 / (24 * U) + l * b ^ 5 / (60 * U) +
        b ^ 3 / (18 * Real.pi) + l * b ^ 4 / (48 * Real.pi) := by
  have h2 : IntervalIntegrable (fun t : ℝ => (1 / (6 * Real.pi)) * t ^ 2) volume 0 b :=
    (by fun_prop : Continuous (fun t : ℝ => (1 / (6 * Real.pi)) * t ^ 2)).intervalIntegrable 0 b
  have h3 : IntervalIntegrable (fun t : ℝ => (1 / (6 * U) + l / (12 * Real.pi)) * t ^ 3) volume 0 b :=
    (by fun_prop : Continuous (fun t : ℝ => (1 / (6 * U) + l / (12 * Real.pi)) * t ^ 3)).intervalIntegrable 0 b
  have h4 : IntervalIntegrable (fun t : ℝ => (l / (12 * U)) * t ^ 4) volume 0 b :=
    (by fun_prop : Continuous (fun t : ℝ => (l / (12 * U)) * t ^ 4)).intervalIntegrable 0 b
  unfold firstCellMajorant
  rw [intervalIntegral.integral_add (h2.add h3) h4, intervalIntegral.integral_add h2 h3]
  simp only [intervalIntegral.integral_const_mul, integral_pow]
  norm_num
  ring

/-- The same first-cell polynomial used by the external endpoint evaluator,
now bounding the actual defining coarse-price integral for every N,c,beta. -/
theorem first_cell_le (N : ℕ) (hN : 0 < N) (c β b U : ℝ) (hβ : 0 < β)
    (hb : 0 < b) (hbU : b ≤ U) :
    (2 / U) * (∫ t in (0 : ℝ)..b, ‖prawitzKernel (t / U)‖ * coarsePrice N c β t) ≤
      b ^ 4 / (24 * U) + CoarseHighMomentRayPrice.lambda N β * b ^ 5 / (60 * U) +
        b ^ 3 / (18 * Real.pi) + CoarseHighMomentRayPrice.lambda N β * b ^ 4 / (48 * Real.pi) := by
  have hU := hb.trans_le hbU
  have hi := (first_integrand_intervalIntegrable N hN c β b U hβ hb hbU).const_mul (2 / U)
  have hc : Continuous (firstCellMajorant (CoarseHighMomentRayPrice.lambda N β) U) := by
    unfold firstCellMajorant
    fun_prop
  have hm := intervalIntegral.integral_mono_on_of_le_Ioo hb.le hi (hc.intervalIntegrable 0 b)
    (fun t ht => scaled_first_integrand_le N hN c β U t hβ hU ht.1 (ht.2.le.trans hbU))
  rw [intervalIntegral.integral_const_mul] at hm
  exact hm.trans_eq (firstCellMajorant_integral _ U b)

end BerryEsseen.CoefficientQuadrature

#print axioms BerryEsseen.CoefficientQuadrature.integral_le_cell_sum
#print axioms BerryEsseen.CoefficientQuadrature.coarsePrice_le_first_polynomial
#print axioms BerryEsseen.CoefficientQuadrature.first_integrand_intervalIntegrable
#print axioms BerryEsseen.CoefficientQuadrature.first_cell_le
