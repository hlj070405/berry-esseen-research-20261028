module

public import BerryEsseen.MomentBudget

@[expose] public section

/-! 2026-10-28: cubic budgets of actual probability laws and conditional
random variables. All moments below are integrals on the same probability
space. Finite absolute third moment supplies L1 for every polynomial used
in the exact nonnegative gap identity; no moments are free parameters. -/

noncomputable section

namespace BerryEsseen.ConditionalCubic

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

def mean (μ : Measure Ω) (Y : Ω → ℝ) : ℝ := ∫ ω, Y ω ∂μ

def variance (μ : Measure Ω) (Y : Ω → ℝ) : ℝ :=
  ∫ ω, (Y ω - mean μ Y) ^ 2 ∂μ

def gap (μ : Measure Ω) (Y : Ω → ℝ) (A : ℝ) (ω : Ω) : ℝ :=
  (Y ω + 2 * mean μ Y - 3 * A) * (Y ω - mean μ Y) ^ 2

theorem integrable_powers (μ : Measure Ω) [IsFiniteMeasure μ] (Y : Ω → ℝ)
    (hY : Measurable Y) (h3 : Integrable (fun ω => |Y ω| ^ 3) μ) :
    Integrable Y μ ∧ Integrable (fun ω => Y ω ^ 2) μ ∧
      Integrable (fun ω => Y ω ^ 3) μ := by
  have hn : Integrable (fun ω => ‖Y ω‖ ^ 3) μ := by
    simpa only [Real.norm_eq_abs] using h3
  have h1 := integrable_norm_pow_of_le hY.aestronglyMeasurable (by decide : 1 ≤ 3) hn
  have h2 := integrable_norm_pow_of_le hY.aestronglyMeasurable (by decide : 2 ≤ 3) hn
  refine ⟨?_, ?_, ?_⟩
  · exact (integrable_norm_iff hY.aestronglyMeasurable).mp
      (by simpa only [pow_one] using h1)
  · simpa only [Real.norm_eq_abs, sq_abs] using h2
  · apply (integrable_norm_iff (hY.pow_const 3).aestronglyMeasurable).mp
    simpa only [Real.norm_eq_abs, abs_pow] using h3

lemma integrable_centered (μ : Measure Ω) [IsFiniteMeasure μ] (Y : Ω → ℝ)
    (hY : Measurable Y) (h3 : Integrable (fun ω => |Y ω| ^ 3) μ) :
    Integrable (fun ω => Y ω - mean μ Y) μ :=
  (integrable_powers μ Y hY h3).1.sub (integrable_const _)

lemma integrable_centered_square (μ : Measure Ω) [IsFiniteMeasure μ] (Y : Ω → ℝ)
    (hY : Measurable Y) (h3 : Integrable (fun ω => |Y ω| ^ 3) μ) :
    Integrable (fun ω => (Y ω - mean μ Y) ^ 2) μ := by
  obtain ⟨h1, h2, _⟩ := integrable_powers μ Y hY h3
  convert (h2.sub (h1.const_mul (2 * mean μ Y))).add
    (integrable_const (mean μ Y ^ 2)) using 1
  ext ω
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

lemma integrable_gap (μ : Measure Ω) [IsFiniteMeasure μ] (Y : Ω → ℝ)
    (hY : Measurable Y) (h3 : Integrable (fun ω => |Y ω| ^ 3) μ) (A : ℝ) :
    Integrable (gap μ Y A) μ := by
  have hc := (integrable_powers μ Y hY h3).2.2
  have hv := integrable_centered_square μ Y hY h3
  have hm := integrable_centered μ Y hY h3
  convert (((hc.sub (integrable_const (mean μ Y ^ 3))).sub (hv.const_mul (3 * A))).sub
    (hm.const_mul (3 * mean μ Y ^ 2))) using 1
  ext ω
  simp only [Pi.sub_apply, gap]
  ring

lemma integral_centered_eq_zero (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ)
    (hY : Integrable Y μ) : (∫ ω, Y ω - mean μ Y ∂μ) = 0 := by
  rw [integral_sub hY (integrable_const _), integral_const]
  simp [mean]

theorem variance_eq_second_sub_mean_sq (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω → ℝ) (hY : Measurable Y) (h3 : Integrable (fun ω => |Y ω| ^ 3) μ) :
    variance μ Y = (∫ ω, Y ω ^ 2 ∂μ) - mean μ Y ^ 2 := by
  obtain ⟨h1, h2, _⟩ := integrable_powers μ Y hY h3
  have hp : Integrable (fun ω => Y ω ^ 2 - (2 * mean μ Y) * Y ω) μ :=
    h2.sub (h1.const_mul _)
  have heq : (fun ω => (Y ω - mean μ Y) ^ 2) =
      (fun ω => Y ω ^ 2 - (2 * mean μ Y) * Y ω + mean μ Y ^ 2) := by
    ext ω
    ring
  unfold variance
  rw [heq, integral_add hp (integrable_const _),
    integral_sub h2 (h1.const_mul _), integral_const_mul]
  simp [mean]
  ring

/-- The exact identity uses the actual mean and central second moment.
It is algebraic and remains valid for any real floor `A`. -/
theorem cube_gap_identity (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ)
    (hY : Measurable Y) (h3 : Integrable (fun ω => |Y ω| ^ 3) μ) (A : ℝ) :
    (∫ ω, Y ω ^ 3 ∂μ) - mean μ Y ^ 3 - 3 * A * variance μ Y =
      ∫ ω, gap μ Y A ω ∂μ := by
  obtain ⟨h1, _, hc⟩ := integrable_powers μ Y hY h3
  have hv := integrable_centered_square μ Y hY h3
  have hm := integrable_centered μ Y hY h3
  have hp0 : Integrable (fun ω => Y ω ^ 3 - mean μ Y ^ 3) μ :=
    hc.sub (integrable_const (mean μ Y ^ 3))
  have hp1 : Integrable (fun ω => Y ω ^ 3 - mean μ Y ^ 3 -
      3 * A * (Y ω - mean μ Y) ^ 2) μ := hp0.sub (hv.const_mul (3 * A))
  have heq : gap μ Y A = fun ω => Y ω ^ 3 - mean μ Y ^ 3 -
      3 * A * (Y ω - mean μ Y) ^ 2 - 3 * mean μ Y ^ 2 * (Y ω - mean μ Y) := by
    ext ω
    dsimp [gap]
    ring
  rw [heq, integral_sub hp1 (hm.const_mul _), integral_sub hp0 (hv.const_mul _),
    integral_sub hc (integrable_const _), integral_const_mul, integral_const_mul,
    integral_centered_eq_zero μ Y h1]
  simp [variance]

theorem mean_ge_lower (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ)
    (hY : Measurable Y) (h3 : Integrable (fun ω => |Y ω| ^ 3) μ)
    (A : ℝ) (hlower : ∀ᵐ ω ∂μ, A ≤ Y ω) : A ≤ mean μ Y := by
  have hi := (integrable_powers μ Y hY h3).1
  have h := integral_mono_ae (integrable_const A) hi hlower
  simpa [mean] using h

theorem variance_nonneg (μ : Measure Ω) (Y : Ω → ℝ) : 0 ≤ variance μ Y :=
  integral_nonneg (fun _ => sq_nonneg _)

/-- The cubic budget is stronger than Jensen by `3*A` times the actual
variance. Nonnegativity of `A` is needed only to read it as a positive penalty. -/
theorem cube_ge_mean_cube_add_variance (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω → ℝ) (hY : Measurable Y) (h3 : Integrable (fun ω => |Y ω| ^ 3) μ)
    (A : ℝ) (hlower : ∀ᵐ ω ∂μ, A ≤ Y ω) :
    mean μ Y ^ 3 + 3 * A * variance μ Y ≤ ∫ ω, Y ω ^ 3 ∂μ := by
  have hm := mean_ge_lower μ Y hY h3 A hlower
  have hg : 0 ≤ ∫ ω, gap μ Y A ω ∂μ := by
    apply integral_nonneg_of_ae
    filter_upwards [hlower] with ω hω
    exact mul_nonneg (by linarith : 0 ≤ Y ω + 2 * mean μ Y - 3 * A)
      (sq_nonneg _)
  rw [← cube_gap_identity μ Y hY h3 A] at hg
  linarith

theorem abs_cube_ge_mean_cube_add_variance (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω → ℝ) (hY : Measurable Y) (h3 : Integrable (fun ω => |Y ω| ^ 3) μ)
    (A : ℝ) (hA : 0 ≤ A) (hlower : ∀ᵐ ω ∂μ, A ≤ Y ω) :
    mean μ Y ^ 3 + 3 * A * variance μ Y ≤ ∫ ω, |Y ω| ^ 3 ∂μ := by
  have heq : (∫ ω, |Y ω| ^ 3 ∂μ) = ∫ ω, Y ω ^ 3 ∂μ := by
    apply integral_congr_ae
    filter_upwards [hlower] with ω hω
    rw [abs_of_nonneg (hA.trans hω)]
  rw [heq]
  exact cube_ge_mean_cube_add_variance μ Y hY h3 A hlower

lemma mean_neg (μ : Measure Ω) (Y : Ω → ℝ) :
    mean μ (fun ω => -Y ω) = -mean μ Y := by
  simp only [mean, integral_neg]

lemma variance_neg (μ : Measure Ω) (Y : Ω → ℝ) :
    variance μ (fun ω => -Y ω) = variance μ Y := by
  unfold variance
  rw [mean_neg]
  apply integral_congr_ae
  filter_upwards [] with ω
  ring

lemma integrable_abs_cube_neg (μ : Measure Ω) (Y : Ω → ℝ)
    (h3 : Integrable (fun ω => |Y ω| ^ 3) μ) :
    Integrable (fun ω => |-Y ω| ^ 3) μ := by simpa only [abs_neg] using h3

/-- Reflection keeps the same actual variance and reverses the actual
signed cubic moment; it applies directly to a negative conditional group. -/
theorem reflected_cube_budget (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω → ℝ) (hY : Measurable Y) (h3 : Integrable (fun ω => |Y ω| ^ 3) μ)
    (A : ℝ) (hupper : ∀ᵐ ω ∂μ, Y ω ≤ -A) :
    (-mean μ Y) ^ 3 + 3 * A * variance μ Y ≤ -(∫ ω, Y ω ^ 3 ∂μ) := by
  have h := cube_ge_mean_cube_add_variance μ (fun ω => -Y ω) hY.neg
    (integrable_abs_cube_neg μ Y h3) A (hupper.mono fun ω hω => by linarith)
  have hneg (x : ℝ) : (-x) ^ 3 = -(x ^ 3) := by ring
  simpa only [mean_neg, variance_neg, hneg, integral_neg] using h

theorem reflected_abs_cube_budget (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω → ℝ) (hY : Measurable Y) (h3 : Integrable (fun ω => |Y ω| ^ 3) μ)
    (A : ℝ) (hA : 0 ≤ A) (hupper : ∀ᵐ ω ∂μ, Y ω ≤ -A) :
    (-mean μ Y) ^ 3 + 3 * A * variance μ Y ≤ ∫ ω, |Y ω| ^ 3 ∂μ := by
  have h := abs_cube_ge_mean_cube_add_variance μ (fun ω => -Y ω) hY.neg
    (integrable_abs_cube_neg μ Y h3) A hA (hupper.mono fun ω hω => by linarith)
  simpa only [mean_neg, variance_neg, abs_neg] using h

/-- The law formulation has `Y = id`; every displayed moment is an
ordinary integral under the supplied actual probability law. -/
theorem law_cube_budget (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun y : ℝ => |y| ^ 3) ν) (A : ℝ)
    (hlower : ∀ᵐ y ∂ν, A ≤ y) :
    A ≤ (∫ y : ℝ, y ∂ν) ∧
      (∫ y : ℝ, y ∂ν) ^ 3 + 3 * A * (∫ y : ℝ, (y - ∫ z : ℝ, z ∂ν) ^ 2 ∂ν) ≤
        ∫ y : ℝ, y ^ 3 ∂ν := by
  exact ⟨mean_ge_lower ν id measurable_id h3 A hlower,
    cube_ge_mean_cube_add_variance ν id measurable_id h3 A hlower⟩

end BerryEsseen.ConditionalCubic

#print axioms BerryEsseen.ConditionalCubic.integrable_powers
#print axioms BerryEsseen.ConditionalCubic.integrable_gap
#print axioms BerryEsseen.ConditionalCubic.variance_eq_second_sub_mean_sq
#print axioms BerryEsseen.ConditionalCubic.cube_gap_identity
#print axioms BerryEsseen.ConditionalCubic.mean_ge_lower
#print axioms BerryEsseen.ConditionalCubic.cube_ge_mean_cube_add_variance
#print axioms BerryEsseen.ConditionalCubic.abs_cube_ge_mean_cube_add_variance
#print axioms BerryEsseen.ConditionalCubic.reflected_cube_budget
#print axioms BerryEsseen.ConditionalCubic.reflected_abs_cube_budget
#print axioms BerryEsseen.ConditionalCubic.law_cube_budget
