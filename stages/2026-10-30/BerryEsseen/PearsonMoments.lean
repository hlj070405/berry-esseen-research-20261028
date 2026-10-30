module

public import BerryEsseen.CharacteristicExpansion
public import Mathlib.Tactic.Ring

@[expose] public section

/-! 2026-10-28: actual-law Pearson identities from (ut:pearson).
The coefficient is the original signed `CharacteristicExpansion.gamma`.
Each identity assumes only its required finite absolute moment and proves
integrability of its polynomial. No reflected contact or free moments enter. -/

noncomputable section

namespace BerryEsseen.PearsonMoments

open MeasureTheory
open CharacteristicExpansion
open scoped BigOperators

def residual (μ : ProbabilityMeasure ℝ) (x : ℝ) : ℝ := x ^ 2 - gamma μ * x - 1

lemma integrable_moment_of_abs (μ : ProbabilityMeasure ℝ) (N : ℕ)
    (hN : Integrable (fun x : ℝ => |x| ^ N) (μ : Measure ℝ)) (k : ℕ) (hk : k ≤ N) :
    Integrable (fun x : ℝ => x ^ k) (μ : Measure ℝ) := by
  have hid : AEStronglyMeasurable (fun x : ℝ => x) (μ : Measure ℝ) :=
    measurable_id.aestronglyMeasurable
  have hn : Integrable (fun x : ℝ => ‖x‖ ^ N) (μ : Measure ℝ) := by
    simpa only [Real.norm_eq_abs] using hN
  have hkI := integrable_norm_pow_of_le hid hk hn
  apply (integrable_norm_iff (measurable_id.pow_const k).aestronglyMeasurable).mp
  simpa only [Real.norm_eq_abs, abs_pow, id_eq] using hkI

lemma gamma_eq_integral_cube (μ : ProbabilityMeasure ℝ) :
    gamma μ = ∫ x : ℝ, x ^ 3 ∂(μ : Measure ℝ) := rfl

lemma integrable_signed_cube (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    Integrable (fun x : ℝ => x ^ 3) (μ : Measure ℝ) :=
  integrable_moment_of_abs μ 3 h.integrable_cube 3 le_rfl

lemma moment_four_eq_abs (μ : ProbabilityMeasure ℝ) :
    moment μ 4 = ∫ x : ℝ, |x| ^ 4 ∂(μ : Measure ℝ) := by
  apply integral_congr_ae
  filter_upwards [] with x
  exact ((by decide : Even (4 : ℕ)).pow_abs x).symm

lemma moment_six_eq_sixthMoment (μ : ProbabilityMeasure ℝ) :
    moment μ 6 = sixthMoment μ := by
  apply integral_congr_ae
  filter_upwards [] with x
  exact ((by decide : Even (6 : ℕ)).pow_abs x).symm

private def polyValue (N : ℕ) (c : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (N + 1), c k * x ^ k

private lemma integrable_polyValue (μ : ProbabilityMeasure ℝ) (N : ℕ)
    (hN : Integrable (fun x : ℝ => |x| ^ N) (μ : Measure ℝ)) (c : ℕ → ℝ) :
    Integrable (polyValue N c) (μ : Measure ℝ) := by
  apply integrable_finsetSum
  intro k hk
  exact (integrable_moment_of_abs μ N hN k (by
    have hlt := Finset.mem_range.mp hk
    omega)).const_mul (c k)

private lemma integral_polyValue (μ : ProbabilityMeasure ℝ) (N : ℕ)
    (hN : Integrable (fun x : ℝ => |x| ^ N) (μ : Measure ℝ)) (c : ℕ → ℝ) :
    (∫ x, polyValue N c x ∂(μ : Measure ℝ)) =
      ∑ k ∈ Finset.range (N + 1), c k * moment μ k := by
  unfold polyValue
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k hk
    exact integral_const_mul _ _
  · intro k hk
    exact (integrable_moment_of_abs μ N hN k (by
      have hlt := Finset.mem_range.mp hk
      omega)).const_mul (c k)

private def coeffFour (g : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => 2 * g
  | 2 => g ^ 2 - 2
  | 3 => -(2 * g)
  | 4 => 1
  | _ => 0

private def coeffFive (g : ℝ) : ℕ → ℝ
  | 0 => 2 * g
  | 1 => 1 + 4 * g ^ 2
  | 2 => 2 * g ^ 3 - 2 * g
  | 3 => -(3 * g ^ 2) - 2
  | 4 => 0
  | 5 => 1
  | _ => 0

private def coeffSix (g : ℝ) : ℕ → ℝ
  | 0 => 3 * g ^ 2 + 2
  | 1 => 6 * g ^ 3 + 6 * g
  | 2 => 3 * g ^ 4 - 3
  | 3 => -(4 * g ^ 3) - 6 * g
  | 4 => 0
  | 5 => 0
  | 6 => 1
  | _ => 0

private lemma residual_sq_eq_poly (μ : ProbabilityMeasure ℝ) :
    (fun x => residual μ x ^ 2) = polyValue 4 (coeffFour (gamma μ)) := by
  ext x
  simp [residual, polyValue, coeffFour, Finset.sum_range_succ]
  ring

private lemma fifth_integrand_eq_poly (μ : ProbabilityMeasure ℝ) :
    (fun x => residual μ x ^ 2 * (x + 2 * gamma μ)) =
      polyValue 5 (coeffFive (gamma μ)) := by
  ext x
  simp [residual, polyValue, coeffFive, Finset.sum_range_succ]
  ring

private lemma sixth_integrand_eq_poly (μ : ProbabilityMeasure ℝ) :
    (fun x => residual μ x ^ 2 * ((x + gamma μ) ^ 2 + 2 * gamma μ ^ 2 + 2)) =
      polyValue 6 (coeffSix (gamma μ)) := by
  ext x
  simp [residual, polyValue, coeffSix, Finset.sum_range_succ]
  ring

theorem integrable_residual_sq (μ : ProbabilityMeasure ℝ)
    (h4 : Integrable (fun x : ℝ => |x| ^ 4) (μ : Measure ℝ)) :
    Integrable (fun x => residual μ x ^ 2) (μ : Measure ℝ) := by
  rw [residual_sq_eq_poly]
  exact integrable_polyValue μ 4 h4 _

theorem integrable_fifth_integrand (μ : ProbabilityMeasure ℝ)
    (h5 : Integrable (fun x : ℝ => |x| ^ 5) (μ : Measure ℝ)) :
    Integrable (fun x => residual μ x ^ 2 * (x + 2 * gamma μ)) (μ : Measure ℝ) := by
  rw [fifth_integrand_eq_poly]
  exact integrable_polyValue μ 5 h5 _

theorem integrable_sixth_integrand (μ : ProbabilityMeasure ℝ)
    (h6 : Integrable (fun x : ℝ => |x| ^ 6) (μ : Measure ℝ)) :
    Integrable (fun x => residual μ x ^ 2 * ((x + gamma μ) ^ 2 + 2 * gamma μ ^ 2 + 2))
      (μ : Measure ℝ) := by
  rw [sixth_integrand_eq_poly]
  exact integrable_polyValue μ 6 h6 _

theorem residual_square_identity (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (h4 : Integrable (fun x : ℝ => |x| ^ 4) (μ : Measure ℝ)) :
    (∫ x, residual μ x ^ 2 ∂(μ : Measure ℝ)) = moment μ 4 - 1 - gamma μ ^ 2 := by
  have hm3 : moment μ 3 = gamma μ := rfl
  rw [residual_sq_eq_poly, integral_polyValue μ 4 h4]
  simp [Finset.sum_range_succ, coeffFour, moment_zero, moment_one μ h, moment_two μ h, hm3]
  ring

theorem pearson_bound (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (h4 : Integrable (fun x : ℝ => |x| ^ 4) (μ : Measure ℝ)) :
    gamma μ ^ 2 ≤ moment μ 4 - 1 := by
  have hn : 0 ≤ ∫ x, residual μ x ^ 2 ∂(μ : Measure ℝ) := integral_nonneg (fun _ => sq_nonneg _)
  rw [residual_square_identity μ h h4] at hn
  linarith

theorem gamma_abs_le_sqrt_of_moment_ceiling (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (h4 : Integrable (fun x : ℝ => |x| ^ 4) (μ : Measure ℝ))
    (M : ℝ) (hM : moment μ 4 ≤ M) : |gamma μ| ≤ Real.sqrt (M - 1) := by
  have hp := pearson_bound μ h h4
  have hM0 : 0 ≤ M - 1 := by linarith [sq_nonneg (gamma μ)]
  apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [sq_abs, Real.sq_sqrt hM0]
  linarith

theorem fifth_moment_identity (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (h5 : Integrable (fun x : ℝ => |x| ^ 5) (μ : Measure ℝ)) :
    moment μ 5 = gamma μ ^ 3 + 2 * gamma μ +
      ∫ x, residual μ x ^ 2 * (x + 2 * gamma μ) ∂(μ : Measure ℝ) := by
  have hm3 : moment μ 3 = gamma μ := rfl
  rw [fifth_integrand_eq_poly, integral_polyValue μ 5 h5]
  simp [Finset.sum_range_succ, coeffFive, moment_zero, moment_one μ h, moment_two μ h, hm3]
  ring

theorem sixth_moment_identity (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (h6 : Integrable (fun x : ℝ => |x| ^ 6) (μ : Measure ℝ)) :
    moment μ 6 = 1 + 3 * gamma μ ^ 2 + gamma μ ^ 4 +
      ∫ x, residual μ x ^ 2 * ((x + gamma μ) ^ 2 + 2 * gamma μ ^ 2 + 2)
        ∂(μ : Measure ℝ) := by
  have hm3 : moment μ 3 = gamma μ := rfl
  rw [sixth_integrand_eq_poly, integral_polyValue μ 6 h6]
  simp [Finset.sum_range_succ, coeffSix, moment_zero, moment_one μ h, moment_two μ h, hm3]
  ring

theorem sixth_absolute_moment_identity (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (h6 : Integrable (fun x : ℝ => |x| ^ 6) (μ : Measure ℝ)) :
    sixthMoment μ = 1 + 3 * gamma μ ^ 2 + gamma μ ^ 4 +
      ∫ x, residual μ x ^ 2 * ((x + gamma μ) ^ 2 + 2 * gamma μ ^ 2 + 2)
        ∂(μ : Measure ℝ) := by
  rw [← moment_six_eq_sixthMoment]
  exact sixth_moment_identity μ h h6

end BerryEsseen.PearsonMoments

#print axioms BerryEsseen.PearsonMoments.integrable_residual_sq
#print axioms BerryEsseen.PearsonMoments.integrable_fifth_integrand
#print axioms BerryEsseen.PearsonMoments.integrable_sixth_integrand
#print axioms BerryEsseen.PearsonMoments.residual_square_identity
#print axioms BerryEsseen.PearsonMoments.pearson_bound
#print axioms BerryEsseen.PearsonMoments.gamma_abs_le_sqrt_of_moment_ceiling
#print axioms BerryEsseen.PearsonMoments.fifth_moment_identity
#print axioms BerryEsseen.PearsonMoments.sixth_moment_identity
#print axioms BerryEsseen.PearsonMoments.sixth_absolute_moment_identity
