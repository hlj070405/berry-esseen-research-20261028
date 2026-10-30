module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Probability.Distributions.Gaussian.Real

@[expose] public section

/-! 2026-10-28: the original all-law, all-positive-index proposition.
This file defines the target; it does not assert a proof of the conjecture.
-/

noncomputable section

open MeasureTheory ProbabilityTheory

namespace BerryEsseen

def esseenConstant : ℝ := (3 + Real.sqrt 10) / (6 * Real.sqrt (2 * Real.pi))

def thirdAbsoluteMoment (μ : ProbabilityMeasure ℝ) : ℝ :=
  ∫ x, |x| ^ 3 ∂(μ : Measure ℝ)

structure StandardizedLaw (μ : ProbabilityMeasure ℝ) : Prop where
  integrable_mean : Integrable (fun x : ℝ => x) (μ : Measure ℝ)
  integrable_square : Integrable (fun x : ℝ => x ^ 2) (μ : Measure ℝ)
  integrable_cube : Integrable (fun x : ℝ => |x| ^ 3) (μ : Measure ℝ)
  mean_zero : (∫ x, x ∂(μ : Measure ℝ)) = 0
  second_moment_one : (∫ x, x ^ 2 ∂(μ : Measure ℝ)) = 1

theorem standardizedLaw_iff (μ : ProbabilityMeasure ℝ) :
    StandardizedLaw μ ↔
      Integrable (fun x : ℝ => |x| ^ 3) (μ : Measure ℝ) ∧
      (∫ x, x ∂(μ : Measure ℝ)) = 0 ∧
      (∫ x, x ^ 2 ∂(μ : Measure ℝ)) = 1 := by
  constructor
  · intro h
    exact ⟨h.integrable_cube, h.mean_zero, h.second_moment_one⟩
  · rintro ⟨h3, h0, h2⟩
    have hid : AEStronglyMeasurable (fun x : ℝ => x) (μ : Measure ℝ) :=
      measurable_id.aestronglyMeasurable
    have h3n : Integrable (fun x : ℝ => ‖x‖ ^ 3) (μ : Measure ℝ) := by
      simpa only [Real.norm_eq_abs] using h3
    have h1n := integrable_norm_pow_of_le hid (by decide : 1 ≤ 3) h3n
    have h2n := integrable_norm_pow_of_le hid (by decide : 2 ≤ 3) h3n
    refine ⟨?_, ?_, h3, h0, h2⟩
    · exact (integrable_norm_iff hid).mp (by simpa only [pow_one] using h1n)
    · simpa only [Real.norm_eq_abs, sq_abs] using h2n

def normalizedIidSum (n : ℕ) (x : Fin n → ℝ) : ℝ :=
  (∑ i, x i) / Real.sqrt n

theorem measurable_normalizedIidSum (n : ℕ) : Measurable (normalizedIidSum n) := by
  unfold normalizedIidSum
  fun_prop

def normalizedIidSumLaw (μ : ProbabilityMeasure ℝ) (n : ℕ) : Measure ℝ :=
  Measure.map (normalizedIidSum n)
    (Measure.pi fun _ : Fin n => (μ : Measure ℝ))

instance normalizedIidSumLaw_isProbability (μ : ProbabilityMeasure ℝ) (n : ℕ) :
    IsProbabilityMeasure (normalizedIidSumLaw μ n) := by
  unfold normalizedIidSumLaw
  infer_instance

def SharpIidBerryEsseen : Prop :=
  ∀ (μ : ProbabilityMeasure ℝ), StandardizedLaw μ →
    ∀ (n : ℕ), 0 < n → ∀ x : ℝ,
      |(normalizedIidSumLaw μ n).real (Set.Iic x) -
        (gaussianReal 0 1).real (Set.Iic x)| ≤
      esseenConstant * thirdAbsoluteMoment μ / Real.sqrt n

end BerryEsseen

#print axioms BerryEsseen.standardizedLaw_iff
#print axioms BerryEsseen.measurable_normalizedIidSum
