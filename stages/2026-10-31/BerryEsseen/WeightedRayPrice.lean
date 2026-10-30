module

public import BerryEsseen.GenericRayPrice
public import BerryEsseen.IidErrorCells
public import BerryEsseen.CoefficientPolynomialForcing
public import BerryEsseen.ThirdMomentRegion

@[expose] public section

/-! 2026-10-30: the actual normalized error under a licensed forcing.
The public restart identity supplies the exact Jacobian. This template
permits the stronger P6 sine majorant without repeating probability theory.
The prefix restriction is on integration frequency, never the CDF threshold. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped Interval

namespace BerryEsseen.WeightedRayPrice

open HighMomentRayDamping

def integrand (L F : ℝ → ℝ) (u : ℝ) : ℝ := Real.exp (u ^ 2 / 2) * L u * F u

def price (L F : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (-(t ^ 2 / 2)) * ∫ u in (0 : ℝ)..t, integrand L F u

lemma continuous_integrand (L F : ℝ → ℝ) (hL : Continuous L) (hF : Continuous F) :
    Continuous (integrand L F) := by unfold integrand; fun_prop

theorem continuous_price (L F : ℝ → ℝ) (hL : Continuous L) (hF : Continuous F) :
    Continuous (price L F) :=
  (by fun_prop : Continuous (fun t : ℝ => Real.exp (-(t ^ 2 / 2)))).mul
    (intervalIntegral.continuous_primitive
      (fun a b => (continuous_integrand L F hL hF).intervalIntegrable a b) 0)

lemma continuous_actual_cell (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (t : ℝ) : Continuous (IidErrorCells.cellResidual μ n t) := by
  have hc : Continuous (fun u : ℝ => charFun (μ : Measure ℝ) (u / Real.sqrt n)) :=
    continuous_charFun.comp (continuous_id.div_const _)
  have hg := (SquareBiasFourier.continuous_firstResidual μ h).comp
    (continuous_id.div_const (Real.sqrt n))
  have hr : Continuous (IidErrorCells.normalizedResidual μ n) := by
    unfold IidErrorCells.normalizedResidual
    exact (continuous_const.mul (hc.pow (n - 1))).mul hg
  exact (by fun_prop : Continuous (fun u : ℝ =>
    ((Real.exp (-((t ^ 2 - u ^ 2) / 2)) : ℝ) : ℂ))).mul hr

/-- Both inputs concern the same original law: its actual predecessor
power and its actual sine residual. No CF-error envelope is assumed. -/
theorem normalized_error_div_beta_le_price (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (hn : 0 < n) (L F : ℝ → ℝ) (hL : Continuous L) (hF : Continuous F)
    (hPred : ∀ u, 0 ≤ u →
      ‖charFun (μ : Measure ℝ) (u / Real.sqrt n)‖ ^ (n - 1) ≤ L u)
    (t : ℝ) (ht : 0 ≤ t)
    (hForce : ∀ u ∈ Icc 0 t, Real.sqrt n * IidSmoothingPrice.sinePrimitive μ (u / Real.sqrt n) ≤
      beta μ n * F u) :
    ‖charFun (μ : Measure ℝ) (t / Real.sqrt n) ^ n -
      (Real.exp (-(t ^ 2 / 2)) : ℂ)‖ / beta μ n ≤ price L F t := by
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  have hρp : 0 < thirdAbsoluteMoment μ :=
    lt_of_lt_of_le zero_lt_one (ThirdMomentRegion.one_le_third μ h)
  have hβ : 0 < beta μ n := div_pos hρp hs
  have hz : IidErrorCells.actualError μ n 0 = 0 := by simp [IidErrorCells.actualError]
  have hid := IidErrorCells.normalized_restart_identity μ h n hn 0 t
  rw [hz, mul_zero, zero_add] at hid
  have hpoint (u : ℝ) (hu : u ∈ Icc 0 t) :
      ‖IidErrorCells.cellResidual μ n t u‖ ≤
        beta μ n * Real.exp (-(t ^ 2 / 2)) * integrand L F u := by
    have hp := hPred u hu.1
    have hsn := (norm_nonneg _).trans (IidSmoothingPrice.norm_firstResidual_le_sinePrimitive
      μ h (u / Real.sqrt n) (div_nonneg hu.1 hs.le))
    have hsn' : 0 ≤ Real.sqrt n * IidSmoothingPrice.sinePrimitive μ (u / Real.sqrt n) :=
      mul_nonneg hs.le hsn
    have hL0 := (pow_nonneg (norm_nonneg _) (n - 1)).trans hp
    have hm := mul_le_mul hp (hForce u hu) hsn' hL0
    have hr := IidErrorCells.norm_normalizedResidual_le μ h n hn
      (fun s => ‖charFun (μ : Measure ℝ) s‖) u hu.1 le_rfl
    have hres : ‖IidErrorCells.normalizedResidual μ n u‖ ≤ beta μ n * L u * F u := by
      apply hr.trans
      convert hm using 1 <;> ring
    unfold IidErrorCells.cellResidual
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply (mul_le_mul_of_nonneg_left hres (Real.exp_nonneg _)).trans_eq
    rw [show -((t ^ 2 - u ^ 2) / 2) = -(t ^ 2 / 2) + u ^ 2 / 2 by ring, Real.exp_add]
    unfold integrand
    ring
  have hi := intervalIntegral.integral_mono_on (μ := volume) ht
    ((continuous_actual_cell μ h n t).norm.intervalIntegrable 0 t)
    (((continuous_const.mul (continuous_integrand L F hL hF))).intervalIntegrable 0 t)
    (fun u hu => hpoint u hu)
  have hnorm := (intervalIntegral.norm_integral_le_integral_norm (μ := volume)
    (f := IidErrorCells.cellResidual μ n t) ht).trans hi
  simp only [Pi.mul_apply] at hnorm
  rw [← hid, intervalIntegral.integral_const_mul] at hnorm
  change ‖IidErrorCells.actualError μ n t‖ / beta μ n ≤ _
  apply (div_le_iff₀ hβ).mpr
  unfold price
  convert hnorm using 1
  ring

def polynomialForcing (N : ℕ) (β t : ℝ) : ℝ :=
  CoefficientPolynomialForcing.P6 β t + CoarseHighMomentRayPrice.lambda N β * t ^ 3 / 3

lemma continuous_polynomialForcing (N : ℕ) (β : ℝ) : Continuous (polynomialForcing N β) := by
  unfold polynomialForcing CoefficientPolynomialForcing.P6
  fun_prop

lemma scaled_sine_le_polynomialForcing (μ : ProbabilityMeasure ℝ) (n N : ℕ)
    (hN : 0 < N) (hNn : N ≤ n) (hρ : rho0 ≤ thirdAbsoluteMoment μ)
    (t : ℝ) (ht : 0 ≤ t) (hCap : beta μ n * t ≤ Real.pi) :
    Real.sqrt n * IidSmoothingPrice.sinePrimitive μ (t / Real.sqrt n) ≤
      beta μ n * polynomialForcing N (beta μ n) t := by
  have hβ := CoarseHighMomentRayPrice.beta_pos μ n (lt_of_lt_of_le hN hNn) hρ
  have hb := (div_le_iff₀ hβ).mp
    (CoefficientPolynomialForcing.B_div_beta_le_P6 (beta μ n) t hβ ht hCap)
  have hf := HighMomentRayPrice.scaled_sinePrimitive_le_loss μ n N hN hNn hρ t ht
  apply hf.trans
  unfold polynomialForcing
  rw [CoarseHighMomentRayPrice.loss_eq_beta_mul_lambda N (beta μ n) hβ]
  nlinarith only [hb]

theorem normalized_error_div_beta_le_polynomialPrice (μ : ProbabilityMeasure ℝ)
    (h : StandardizedLaw μ) (n N : ℕ) (hN : 0 < N) (hNn : N ≤ n)
    (hρ : rho0 ≤ thirdAbsoluteMoment μ) (L : ℝ → ℝ) (hL : Continuous L)
    (hPred : ∀ u, 0 ≤ u → ‖charFun (μ : Measure ℝ) (u / Real.sqrt n)‖ ^ (n - 1) ≤ L u)
    (t : ℝ) (ht : 0 ≤ t) (hCap : beta μ n * t ≤ Real.pi) :
    ‖charFun (μ : Measure ℝ) (t / Real.sqrt n) ^ n -
      (Real.exp (-(t ^ 2 / 2)) : ℂ)‖ / beta μ n ≤
      price L (polynomialForcing N (beta μ n)) t := by
  have hβ := CoarseHighMomentRayPrice.beta_pos μ n (lt_of_lt_of_le hN hNn) hρ
  exact normalized_error_div_beta_le_price μ h n (lt_of_lt_of_le hN hNn) L _ hL
    (continuous_polynomialForcing N _) hPred t ht (fun u hu =>
      scaled_sine_le_polynomialForcing μ n N hN hNn hρ u hu.1
        ((mul_le_mul_of_nonneg_left hu.2 hβ.le).trans hCap))

end BerryEsseen.WeightedRayPrice

#print axioms BerryEsseen.WeightedRayPrice.normalized_error_div_beta_le_price
#print axioms BerryEsseen.WeightedRayPrice.normalized_error_div_beta_le_polynomialPrice
