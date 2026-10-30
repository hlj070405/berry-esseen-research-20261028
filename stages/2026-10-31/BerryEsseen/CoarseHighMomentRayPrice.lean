module

public import BerryEsseen.HighMomentRayPrice

@[expose] public section

/-! 2026-10-29: a polynomial forcing for the same actual high-moment iid CF.
The proved B_beta(t) <= beta*t^2/2 removes the sine primitive from the
normalized error price. After division by beta > 0, the only coefficient
is lambda = min (beta/rho0^2) (1/(N*beta)). No numerical all-beta or CDF
bound is asserted here. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped Interval

namespace BerryEsseen.CoarseHighMomentRayPrice

open HighMomentRayDamping

def lambda (N : ℕ) (β : ℝ) : ℝ := min (β / rho0 ^ 2) (1 / ((N : ℝ) * β))

def coarseIntegrand (N : ℕ) (β t : ℝ) : ℝ :=
  Real.exp (t ^ 2 / 2) * lossEnvelope N β t *
    (t ^ 2 / 2 + lambda N β * t ^ 3 / 3)

def coarsePrice (N : ℕ) (β t : ℝ) : ℝ :=
  Real.exp (-(t ^ 2 / 2)) * ∫ u in (0 : ℝ)..t, coarseIntegrand N β u

lemma loss_div_eq_lambda (N : ℕ) (β : ℝ) (hβ : 0 < β) :
    loss N β / β = lambda N β := by
  unfold loss lambda
  rw [← min_div_div_right hβ.le]
  congr 1
  · field_simp [hβ.ne', rho0_pos.ne']
  · ring

lemma loss_eq_beta_mul_lambda (N : ℕ) (β : ℝ) (hβ : 0 < β) :
    loss N β = β * lambda N β := by
  calc
    _ = (loss N β / β) * β := (div_mul_cancel₀ _ hβ.ne').symm
    _ = _ := by rw [loss_div_eq_lambda N β hβ]; ring

lemma continuous_coarseIntegrand (N : ℕ) (β : ℝ) : Continuous (coarseIntegrand N β) := by
  exact ((by fun_prop : Continuous (fun t : ℝ => Real.exp (t ^ 2 / 2))).mul
    (HighMomentRayPrice.continuous_lossEnvelope N β)).mul (by fun_prop)

lemma continuous_coarsePrice (N : ℕ) (β : ℝ) : Continuous (coarsePrice N β) := by
  exact (by fun_prop : Continuous (fun t : ℝ => Real.exp (-(t ^ 2 / 2)))).mul
    (intervalIntegral.continuous_primitive
      (fun a b => (continuous_coarseIntegrand N β).intervalIntegrable a b) 0)

/-- A global nonnegative-frequency bound; saturation of the sine does not
require a cutoff because sin(min(x,pi/2)) <= x for every x >= 0. -/
theorem B_le_quadratic (β : ℝ) (hβ : 0 ≤ β) (t : ℝ) (ht : 0 ≤ t) :
    HighMomentRayPrice.B β t ≤ β * t ^ 2 / 2 := by
  unfold HighMomentRayPrice.B
  calc
    _ ≤ ∫ v in (0 : ℝ)..t, β * v := by
      apply intervalIntegral.integral_mono_on ht
        ((HighMomentRayPrice.continuous_sineKernel β).intervalIntegrable 0 t)
        ((by fun_prop : Continuous (fun v : ℝ => β * v)).intervalIntegrable 0 t)
      intro v hv
      have hv0 : 0 ≤ v := hv.1
      have hmin : 0 ≤ min (β * v / 2) (Real.pi / 2) := le_min (by positivity) (by positivity)
      have hh := (Real.sin_le hmin).trans (min_le_left (β * v / 2) (Real.pi / 2))
      unfold HighMomentRayPrice.sineKernel
      linarith only [hh]
    _ = _ := by
      rw [intervalIntegral.integral_const_mul, integral_id]
      ring

private lemma fine_integrand_le (N : ℕ) (β : ℝ) (hβ : 0 < β)
    (t : ℝ) (ht : 0 ≤ t) :
    HighMomentRayPrice.integrand N β t ≤ β * coarseIntegrand N β t := by
  have hB := B_le_quadratic β hβ.le t ht
  have hf : HighMomentRayPrice.B β t + loss N β * t ^ 3 / 3 ≤
      β * (t ^ 2 / 2 + lambda N β * t ^ 3 / 3) := by
    calc
      _ ≤ β * t ^ 2 / 2 + loss N β * t ^ 3 / 3 := by linarith only [hB]
      _ = _ := by rw [loss_eq_beta_mul_lambda N β hβ]; ring
  have hm := mul_le_mul_of_nonneg_left hf (HighMomentRayPrice.lossEnvelope_nonneg N β t)
  unfold HighMomentRayPrice.integrand HighMomentRayPrice.forcing coarseIntegrand
  convert mul_le_mul_of_nonneg_left hm (Real.exp_pos (t ^ 2 / 2)).le using 1
  ring

theorem fine_price_le_beta_mul_coarsePrice (N : ℕ) (β : ℝ) (hβ : 0 < β)
    (t : ℝ) (ht : 0 ≤ t) :
    HighMomentRayPrice.price N β t ≤ β * coarsePrice N β t := by
  calc
    _ ≤ Real.exp (-(t ^ 2 / 2)) *
        ∫ u in (0 : ℝ)..t, β * coarseIntegrand N β u := by
      unfold HighMomentRayPrice.price
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      exact intervalIntegral.integral_mono_on ht
        ((HighMomentRayPrice.continuous_integrand N β).intervalIntegrable 0 t)
        ((continuous_const.mul (continuous_coarseIntegrand N β)).intervalIntegrable 0 t)
        (fun u hu => fine_integrand_le N β hβ u hu.1)
    _ = _ := by
      rw [intervalIntegral.integral_const_mul]
      unfold coarsePrice
      ring

lemma beta_pos (μ : ProbabilityMeasure ℝ) (n : ℕ) (hn : 0 < n)
    (hρ : rho0 ≤ thirdAbsoluteMoment μ) : 0 < beta μ n := by
  exact div_pos (lt_of_lt_of_le rho0_pos hρ) (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn))

/-- The same original law and frequency are retained. The right-hand side
contains only exponentials, polynomials, N and beta, with no sine primitive. -/
theorem normalized_power_error_div_beta_le_coarsePrice (μ : ProbabilityMeasure ℝ)
    (h : StandardizedLaw μ) (n N : ℕ) (hN : 0 < N) (hNn : N ≤ n)
    (hρ : rho0 ≤ thirdAbsoluteMoment μ) (t : ℝ) (ht : 0 ≤ t) :
    ‖charFun (μ : Measure ℝ) (t / Real.sqrt n) ^ n -
      (Real.exp (-(t ^ 2 / 2)) : ℂ)‖ / beta μ n ≤ coarsePrice N (beta μ n) t := by
  have hn : 0 < n := lt_of_lt_of_le hN hNn
  have hβ := beta_pos μ n hn hρ
  apply (div_le_iff₀ hβ).mpr
  have hh := (HighMomentRayPrice.normalized_power_sub_gaussian_le_price μ h n N hN hNn hρ t ht).trans
    (fine_price_le_beta_mul_coarsePrice N (beta μ n) hβ t ht)
  simpa only [mul_comm] using hh

theorem normalized_iid_error_div_beta_le_coarsePrice (μ : ProbabilityMeasure ℝ)
    (h : StandardizedLaw μ) (n N : ℕ) (hN : 0 < N) (hNn : N ≤ n)
    (hρ : rho0 ≤ thirdAbsoluteMoment μ) (t : ℝ) (ht : 0 ≤ t) :
    ‖charFun (normalizedIidSumLaw μ n) t - charFun (gaussianReal 0 1) t‖ / beta μ n ≤
      coarsePrice N (beta μ n) t := by
  rw [PrawitzSmoothing.charFun_normalizedIidSumLaw, PrawitzSmoothing.charFun_standardGaussian]
  exact normalized_power_error_div_beta_le_coarsePrice μ h n N hN hNn hρ t ht

end BerryEsseen.CoarseHighMomentRayPrice

#print axioms BerryEsseen.CoarseHighMomentRayPrice.B_le_quadratic
#print axioms BerryEsseen.CoarseHighMomentRayPrice.fine_price_le_beta_mul_coarsePrice
#print axioms BerryEsseen.CoarseHighMomentRayPrice.normalized_power_error_div_beta_le_coarsePrice
#print axioms BerryEsseen.CoarseHighMomentRayPrice.normalized_iid_error_div_beta_le_coarsePrice
