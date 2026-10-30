module

public import BerryEsseen.Target
public import Causalean.Stat.CLT.BerryEsseen.SymmetrizedThirdMoment

@[expose] public section

/-! 2026-10-29: the first three moments of the actual independent difference
under the original law's product measure. Only StandardizedLaw is used.
The cubic bound reuses the pinned Causalean probability leaf, and all real
scales, including zero and negative scales, retain the same product law. -/

noncomputable section

open MeasureTheory

namespace BerryEsseen.SymmetrizedThirdMoment

theorem integrable_difference (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ) :
    Integrable (fun p : ℝ × ℝ => p.1 - p.2) ((μ : Measure ℝ).prod (μ : Measure ℝ)) :=
  (hμ.integrable_mean.comp_fst (μ : Measure ℝ)).sub
    (hμ.integrable_mean.comp_snd (μ : Measure ℝ))

theorem integral_difference (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ) :
    (∫ p : ℝ × ℝ, (p.1 - p.2) ∂((μ : Measure ℝ).prod (μ : Measure ℝ))) = 0 := by
  rw [integral_sub (hμ.integrable_mean.comp_fst (μ : Measure ℝ))
    (hμ.integrable_mean.comp_snd (μ : Measure ℝ)),
    integral_fun_fst (fun x : ℝ => x), integral_fun_snd (fun x : ℝ => x)]
  simp only [hμ.mean_zero, smul_zero, sub_zero]

theorem difference_second_moment (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ) :
    Integrable (fun p : ℝ × ℝ => (p.1 - p.2) ^ 2)
      ((μ : Measure ℝ).prod (μ : Measure ℝ)) ∧
    (∫ p : ℝ × ℝ, (p.1 - p.2) ^ 2 ∂((μ : Measure ℝ).prod (μ : Measure ℝ))) = 2 := by
  have hfst := hμ.integrable_square.comp_fst (μ : Measure ℝ)
  have hsnd := hμ.integrable_square.comp_snd (μ : Measure ℝ)
  have hprod := hμ.integrable_mean.mul_prod hμ.integrable_mean
  have hsub : Integrable (fun p : ℝ × ℝ => p.1 ^ 2 - 2 * (p.1 * p.2))
      ((μ : Measure ℝ).prod (μ : Measure ℝ)) := hfst.sub (hprod.const_mul 2)
  have heq : (fun p : ℝ × ℝ => (p.1 - p.2) ^ 2) =
      (fun p : ℝ × ℝ => (p.1 ^ 2 - 2 * (p.1 * p.2)) + p.2 ^ 2) := by
    funext p
    ring
  rw [heq]
  refine ⟨hsub.add hsnd, ?_⟩
  rw [integral_add hsub hsnd, integral_sub hfst (hprod.const_mul 2), integral_const_mul,
    integral_fun_fst (fun x : ℝ => x ^ 2),
    integral_fun_snd (fun x : ℝ => x ^ 2),
    integral_prod_mul (fun x : ℝ => x) (fun y : ℝ => y)]
  simp only [probReal_univ, one_smul, hμ.mean_zero, hμ.second_moment_one]
  norm_num

theorem difference_third_absolute_moment (μ : ProbabilityMeasure ℝ)
    (hμ : StandardizedLaw μ) :
    Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ 3)
      ((μ : Measure ℝ).prod (μ : Measure ℝ)) ∧
    (∫ p : ℝ × ℝ, |p.1 - p.2| ^ 3 ∂((μ : Measure ℝ).prod (μ : Measure ℝ))) ≤
      2 * (thirdAbsoluteMoment μ + 1) := by
  exact Causalean.Stat.CLT.BerryEsseen.symmetrized_unit_third_moment_le
    (μ : Measure ℝ) hμ.integrable_mean hμ.mean_zero
    hμ.integrable_square hμ.second_moment_one hμ.integrable_cube

theorem scaled_difference_second_moment (μ : ProbabilityMeasure ℝ)
    (hμ : StandardizedLaw μ) (c : ℝ) :
    Integrable (fun p : ℝ × ℝ => (c * (p.1 - p.2)) ^ 2)
      ((μ : Measure ℝ).prod (μ : Measure ℝ)) ∧
    (∫ p : ℝ × ℝ, (c * (p.1 - p.2)) ^ 2 ∂((μ : Measure ℝ).prod (μ : Measure ℝ))) =
      2 * c ^ 2 := by
  have h := difference_second_moment μ hμ
  have heq : (fun p : ℝ × ℝ => (c * (p.1 - p.2)) ^ 2) =
      (fun p : ℝ × ℝ => c ^ 2 * (p.1 - p.2) ^ 2) := by
    funext p
    ring
  rw [heq]
  refine ⟨h.1.const_mul _, ?_⟩
  rw [integral_const_mul, h.2]
  ring

theorem scaled_difference_third_absolute_moment (μ : ProbabilityMeasure ℝ)
    (hμ : StandardizedLaw μ) (c : ℝ) :
    Integrable (fun p : ℝ × ℝ => |c * (p.1 - p.2)| ^ 3)
      ((μ : Measure ℝ).prod (μ : Measure ℝ)) ∧
    (∫ p : ℝ × ℝ, |c * (p.1 - p.2)| ^ 3 ∂((μ : Measure ℝ).prod (μ : Measure ℝ))) ≤
      2 * |c| ^ 3 * (thirdAbsoluteMoment μ + 1) := by
  have h := difference_third_absolute_moment μ hμ
  have heq : (fun p : ℝ × ℝ => |c * (p.1 - p.2)| ^ 3) =
      (fun p : ℝ × ℝ => |c| ^ 3 * |p.1 - p.2| ^ 3) := by
    funext p
    rw [abs_mul, mul_pow]
  rw [heq]
  refine ⟨h.1.const_mul _, ?_⟩
  rw [integral_const_mul]
  calc
    _ ≤ |c| ^ 3 * (2 * (thirdAbsoluteMoment μ + 1)) :=
      mul_le_mul_of_nonneg_left h.2 (pow_nonneg (abs_nonneg c) 3)
    _ = _ := by ring

end BerryEsseen.SymmetrizedThirdMoment

#print axioms Causalean.Stat.CLT.BerryEsseen.symmetrized_unit_third_moment_le
#print axioms BerryEsseen.SymmetrizedThirdMoment.integrable_difference
#print axioms BerryEsseen.SymmetrizedThirdMoment.integral_difference
#print axioms BerryEsseen.SymmetrizedThirdMoment.difference_second_moment
#print axioms BerryEsseen.SymmetrizedThirdMoment.difference_third_absolute_moment
#print axioms BerryEsseen.SymmetrizedThirdMoment.scaled_difference_second_moment
#print axioms BerryEsseen.SymmetrizedThirdMoment.scaled_difference_third_absolute_moment
