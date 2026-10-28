module

public import BerryEsseen.MomentBudget

@[expose] public section

/-! 2026-10-28: normalization and allocation interfaces for the actual residual
mixture. Absolute-cubic integrability is obtained from the integrable signed
cubics by taking norms, so normalization itself needs no group sign condition.
The sign assumptions remain necessary for the cubic expansion in MomentBudget. -/

noncomputable section

open MeasureTheory

namespace BerryEsseen.MomentBudget

/-- The actual mixture has a finite absolute third moment. The residual laws may
be arbitrary real probability laws; neither finite support nor a sign is needed. -/
theorem actual_abs_cube_integrable (μ0 μ1 : ProbabilityMeasure ℝ)
    (h0 : CenteredResidualLaw μ0) (h1 : CenteredResidualLaw μ1)
    (p c : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Integrable (fun x : ℝ => |x| ^ 3)
      (residualMixtureLaw μ0 μ1 p c hp0 hp1 : Measure ℝ) := by
  have hshift0 : Integrable (fun u : ℝ => (u - p) ^ 3) (μ0 : Measure ℝ) := by
    simpa only [sub_eq_add_neg] using integrable_cube_add_const
      (μ0 : Measure ℝ) (fun u : ℝ => u) (-p)
      h0.integrable_first h0.integrable_second h0.integrable_third
  have hshift1 := integrable_cube_add_const (μ1 : Measure ℝ)
    (fun u : ℝ => u) (1 - p) h1.integrable_first h1.integrable_second h1.integrable_third
  have hcube0 : Integrable (fun u : ℝ => ((u - p) / c) ^ 3) (μ0 : Measure ℝ) := by
    simpa only [div_pow] using hshift0.div_const (c ^ 3)
  have hcube1 : Integrable (fun u : ℝ => ((u + (1 - p)) / c) ^ 3) (μ1 : Measure ℝ) := by
    simpa only [div_pow] using hshift1.div_const (c ^ 3)
  have hint0 : Integrable (fun u : ℝ => |(u - p) / c| ^ 3) (μ0 : Measure ℝ) := by
    simpa only [Real.norm_eq_abs, abs_pow] using hcube0.norm
  have hint1 : Integrable (fun u : ℝ => |(u + (1 - p)) / c| ^ 3) (μ1 : Measure ℝ) := by
    simpa only [Real.norm_eq_abs, abs_pow] using hcube1.norm
  have hm0 : Measurable (fun u : ℝ => (u - p) / c) := by fun_prop
  have hm1 : Measurable (fun u : ℝ => (u + (1 - p)) / c) := by fun_prop
  have hf : StronglyMeasurable (fun x : ℝ => |x| ^ 3) :=
    (continuous_abs.pow 3).stronglyMeasurable
  have hi0 := (integrable_map_measure hf.aestronglyMeasurable hm0.aemeasurable).mpr hint0
  have hi1 := (integrable_map_measure hf.aestronglyMeasurable hm1.aemeasurable).mpr hint1
  rw [coe_residualMixtureLaw, residualMixtureMeasure]
  exact (hi0.smul_measure ENNReal.ofReal_ne_top).add_measure
    (hi1.smul_measure ENNReal.ofReal_ne_top)

/-- The same actual mixture satisfies the original target's normalization
predicate at the scale `sqrt (pq+s)`. Zero residual variance is included. -/
theorem actual_standardizedLaw (μ0 μ1 : ProbabilityMeasure ℝ)
    (h0 : CenteredResidualLaw μ0) (h1 : CenteredResidualLaw μ1)
    (p s : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hsecond : s = (1 - p) * residualSecondMoment μ0 + p * residualSecondMoment μ1) :
    StandardizedLaw (residualMixtureLaw μ0 μ1 p (Real.sqrt (p * (1 - p) + s))
      (le_of_lt hp) (le_of_lt hp1)) := by
  have hq : 0 < 1 - p := sub_pos.mpr hp1
  have hs : 0 ≤ s := by
    rw [hsecond]
    exact add_nonneg
      (mul_nonneg (le_of_lt hq) (residualSecondMoment_nonneg μ0))
      (mul_nonneg (le_of_lt hp) (residualSecondMoment_nonneg μ1))
  have hden : 0 < p * (1 - p) + s := add_pos_of_pos_of_nonneg (mul_pos hp hq) hs
  apply (standardizedLaw_iff _).mpr
  refine ⟨actual_abs_cube_integrable μ0 μ1 h0 h1 p _ (le_of_lt hp) (le_of_lt hp1),
    actual_first_moment μ0 μ1 h0 h1 p _ (le_of_lt hp) (le_of_lt hp1), ?_⟩
  rw [actual_second_moment μ0 μ1 h0 h1 p _ (le_of_lt hp) (le_of_lt hp1),
    Real.sq_sqrt (le_of_lt hden)]
  have hnum : p * (1 - p) + (1 - p) * residualSecondMoment μ0 +
      p * residualSecondMoment μ1 = p * (1 - p) + s := by linarith [hsecond]
  rw [hnum, div_self (ne_of_gt hden)]

/-- The allocation of two nonnegative variance contributions belongs to `[0,1]`. -/
theorem allocation_mem_Icc (p z0 z1 s α : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hz0 : 0 ≤ z0) (hz1 : 0 ≤ z1) (hs : 0 < s)
    (hsecond : s = (1 - p) * z0 + p * z1) (hα : α = p * z1 / s) :
    α ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · rw [hα]
    exact div_nonneg (mul_nonneg hp0 hz1) (le_of_lt hs)
  · rw [hα]
    apply (div_le_iff₀ hs).mpr
    have hnon : 0 ≤ (1 - p) * z0 := mul_nonneg (sub_nonneg.mpr hp1) hz0
    linarith [hsecond]

/-- The interval fact for exactly the residual moments used by the actual-law floor. -/
theorem actual_allocation_mem_Icc (μ0 μ1 : ProbabilityMeasure ℝ) (p s α : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hs : 0 < s)
    (hsecond : s = (1 - p) * residualSecondMoment μ0 + p * residualSecondMoment μ1)
    (hα : α = p * residualSecondMoment μ1 / s) : α ∈ Set.Icc (0 : ℝ) 1 :=
  allocation_mem_Icc p (residualSecondMoment μ0) (residualSecondMoment μ1) s α
    hp0 hp1 (residualSecondMoment_nonneg μ0) (residualSecondMoment_nonneg μ1) hs hsecond hα

end BerryEsseen.MomentBudget

#print axioms BerryEsseen.MomentBudget.actual_abs_cube_integrable
#print axioms BerryEsseen.MomentBudget.actual_standardizedLaw
#print axioms BerryEsseen.MomentBudget.actual_allocation_mem_Icc
