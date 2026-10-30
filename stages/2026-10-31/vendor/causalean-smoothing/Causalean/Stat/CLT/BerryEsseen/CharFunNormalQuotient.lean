module
public import Mathlib.Probability.CentralLimitTheorem
-- 2026-10-29: extracted verbatim from BerryEsseenSmoothing.lean,
-- original lines 27-89; original Apache-2.0 source in upstream/.
public section
namespace Causalean.Stat.CLT.BerryEsseen
open MeasureTheory ProbabilityTheory
theorem charFun_normal_quotient_intervalIntegrable
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hfirst : Integrable (fun y : ℝ => y) μ)
    (T : ℝ) :
    IntervalIntegrable
      (fun t : ℝ =>
        ‖charFun μ t - charFun (gaussianReal 0 1) t‖ / |t|)
      volume (-T) T := by
  have hchar (ν : Measure ℝ) [IsProbabilityMeasure ν]
      (hν : Integrable (fun y : ℝ => y) ν) (t : ℝ) :
      ‖charFun ν t - 1‖ ≤ |t| * ∫ y, |y| ∂ν := by
    have he : Integrable (fun y : ℝ => Complex.exp ((t * y : ℝ) * Complex.I)) ν := by
      apply Integrable.of_bound (by fun_prop) 1
      filter_upwards [] with y
      simpa [mul_comm] using (Complex.norm_exp_I_mul_ofReal (t * y)).le
    have hEq : charFun ν t - 1 =
        ∫ y, (Complex.exp ((t * y : ℝ) * Complex.I) - 1) ∂ν := by
      rw [charFun_apply_real]
      simp only [← Complex.ofReal_mul]
      rw [integral_sub he (integrable_const 1)]
      simp
    rw [hEq]
    calc
      ‖∫ y, (Complex.exp ((t * y : ℝ) * Complex.I) - 1) ∂ν‖ ≤
          ∫ y, |t| * |y| ∂ν := by
        apply norm_integral_le_of_norm_le (hν.norm.const_mul |t|)
        filter_upwards [] with y
        have hp := Real.norm_exp_I_mul_ofReal_sub_one_le (x := t * y)
        simpa [Real.norm_eq_abs, abs_mul, mul_comm] using hp
      _ = |t| * ∫ y, |y| ∂ν := by rw [integral_const_mul]
  have hg : Integrable (fun y : ℝ => y) (gaussianReal 0 1) := by
    exact memLp_one_iff_integrable.mp
      (ProbabilityTheory.memLp_id_gaussianReal (μ := 0) (v := 1) 1)
  have hbound : ∀ t : ℝ, t ≠ 0 →
      ‖charFun μ t - charFun (gaussianReal 0 1) t‖ / |t| ≤
        (∫ y, |y| ∂μ) + (∫ y, |y| ∂(gaussianReal 0 1)) := by
    intro t ht
    have htpos : 0 < |t| := abs_pos.mpr ht
    have hμ := hchar μ hfirst t
    have hγ := hchar (gaussianReal 0 1) hg t
    have htri : ‖charFun μ t - charFun (gaussianReal 0 1) t‖ ≤
        ‖charFun μ t - 1‖ + ‖charFun (gaussianReal 0 1) t - 1‖ := by
      convert norm_sub_le (charFun μ t - 1) (charFun (gaussianReal 0 1) t - 1) using 1
      ring_nf
    apply (div_le_iff₀ htpos).2
    nlinarith
  have hmeas : Measurable (fun t : ℝ =>
      ‖charFun μ t - charFun (gaussianReal 0 1) t‖ / |t|) := by
    fun_prop
  apply (intervalIntegrable_iff).2
  apply IntegrableOn.of_bound (by rw [Real.volume_uIoc]; exact ENNReal.ofReal_lt_top)
    hmeas.aestronglyMeasurable
    ((∫ y, |y| ∂μ) + (∫ y, |y| ∂(gaussianReal 0 1)))
  filter_upwards [] with t
  by_cases ht : t = 0
  · subst t
    simp only [charFun_zero, probReal_univ, Complex.ofReal_one, sub_self,
      norm_zero, abs_zero, div_zero]
    exact add_nonneg (integral_nonneg (fun y => abs_nonneg y))
      (integral_nonneg (fun y => abs_nonneg y))
  · simpa [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (norm_nonneg _) (abs_nonneg t))]
      using hbound t ht

end Causalean.Stat.CLT.BerryEsseen
