module

public import BerryEsseen.Target
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-! The actual square-biased probability measure of a standardized law.
Its density is relative to the original measure, which may have atoms. -/

noncomputable section

open MeasureTheory Set Filter

namespace BerryEsseen.SquareBias

def squareMeasure (μ : ProbabilityMeasure ℝ) : Measure ℝ :=
  (μ : Measure ℝ).withDensity (fun x => ENNReal.ofReal (x ^ 2))

theorem squareMeasure_isProbability (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    IsProbabilityMeasure (squareMeasure μ) := by
  constructor
  unfold squareMeasure
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal h.integrable_square
      (Eventually.of_forall fun x => sq_nonneg x), h.second_moment_one]
  norm_num

def squareLaw (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) : ProbabilityMeasure ℝ :=
  ⟨squareMeasure μ, squareMeasure_isProbability μ h⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem integral_squareLaw (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (g : ℝ → E) :
    (∫ x, g x ∂(squareLaw μ h : Measure ℝ)) = ∫ x, x ^ 2 • g x ∂(μ : Measure ℝ) := by
  change (∫ x, g x ∂(squareMeasure μ)) = _
  unfold squareMeasure
  rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (sq_nonneg _)]

theorem integrable_squareLaw_iff (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (g : ℝ → E) :
    Integrable g (squareLaw μ h : Measure ℝ) ↔
      Integrable (fun x => x ^ 2 • g x) (μ : Measure ℝ) := by
  change Integrable g (squareMeasure μ) ↔ _
  unfold squareMeasure
  rw [integrable_withDensity_iff_integrable_smul' (by fun_prop)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (sq_nonneg _)]

theorem integrable_abs_squareLaw (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    Integrable (fun x : ℝ => |x|) (squareLaw μ h : Measure ℝ) := by
  rw [integrable_squareLaw_iff]
  convert h.integrable_cube using 1
  funext x
  change x ^ 2 * |x| = |x| ^ 3
  rw [← sq_abs]
  ring

theorem integral_abs_squareLaw (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    (∫ x : ℝ, |x| ∂(squareLaw μ h : Measure ℝ)) = thirdAbsoluteMoment μ := by
  rw [integral_squareLaw]
  unfold thirdAbsoluteMoment
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    change x ^ 2 * |x| = |x| ^ 3
    rw [← sq_abs]
    ring

def weight (x : ℝ) : ℝ := x ^ 2 - 1

lemma measurable_weight : Measurable weight := by unfold weight; fun_prop

theorem integrable_weight (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    Integrable weight (μ : Measure ℝ) := h.integrable_square.sub (integrable_const 1)

theorem integral_weight (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    (∫ x, weight x ∂(μ : Measure ℝ)) = 0 := by
  unfold weight
  rw [integral_sub h.integrable_square (integrable_const 1), h.second_moment_one]
  simp

theorem integrable_abs_weight_mul_abs (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    Integrable (fun x : ℝ => |weight x| * |x|) (μ : Measure ℝ) := by
  have ha : Integrable (fun x : ℝ => |x|) (μ : Measure ℝ) := by
    simpa only [Real.norm_eq_abs] using h.integrable_mean.norm
  apply (h.integrable_cube.add ha).mono'
    ((continuous_abs.measurable.comp measurable_weight).mul
      continuous_abs.measurable).aestronglyMeasurable
  exact Eventually.of_forall fun x => by
    change ‖|weight x| * |x|‖ ≤ |x| ^ 3 + |x|
    rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_abs]
    calc
      |weight x| * |x| ≤ (x ^ 2 + 1) * |x| := by
        apply mul_le_mul_of_nonneg_right _ (abs_nonneg x)
        calc
          |weight x| = |x ^ 2 - 1| := rfl
          _ ≤ |x ^ 2| + |(1 : ℝ)| := abs_sub (x ^ 2) 1
          _ = x ^ 2 + 1 := by rw [abs_of_nonneg (sq_nonneg x), abs_one]
      _ = |x| ^ 3 + |x| := by rw [← sq_abs]; ring

def cdfDifference (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (s : ℝ) : ℝ :=
  (μ : Measure ℝ).real (Iic s) - (squareLaw μ h : Measure ℝ).real (Iic s)

theorem cdfDifference_eq_integral (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (s : ℝ) :
    cdfDifference μ h s = -∫ x in Iic s, weight x ∂(μ : Measure ℝ) := by
  have hs : (squareLaw μ h : Measure ℝ).real (Iic s) =
      ∫ x in Iic s, x ^ 2 ∂(μ : Measure ℝ) := by
    have hi : (∫ x : ℝ, (Iic s).indicator (fun _ => (1 : ℝ)) x
        ∂(squareLaw μ h : Measure ℝ)) = (squareLaw μ h : Measure ℝ).real (Iic s) := by
      rw [integral_indicator_const (1 : ℝ) measurableSet_Iic]
      simp
    rw [← hi]
    rw [integral_squareLaw]
    have heq : (fun x : ℝ => x ^ 2 • (Iic s).indicator (fun _ => (1 : ℝ)) x) =
        (Iic s).indicator (fun x : ℝ => x ^ 2) := by
      funext x
      by_cases hx : x ∈ Iic s <;> simp [hx]
    rw [heq, integral_indicator measurableSet_Iic]
  unfold cdfDifference
  rw [hs, show (∫ x in Iic s, weight x ∂(μ : Measure ℝ)) =
      (∫ x in Iic s, x ^ 2 ∂(μ : Measure ℝ)) - (μ : Measure ℝ).real (Iic s) by
    unfold weight
    rw [integral_sub h.integrable_square.integrableOn (integrable_const 1)]
    simp]
  ring

end BerryEsseen.SquareBias

#print axioms BerryEsseen.SquareBias.squareMeasure_isProbability
#print axioms BerryEsseen.SquareBias.integrable_abs_squareLaw
#print axioms BerryEsseen.SquareBias.integral_abs_squareLaw
#print axioms BerryEsseen.SquareBias.integrable_abs_weight_mul_abs
#print axioms BerryEsseen.SquareBias.cdfDifference_eq_integral
