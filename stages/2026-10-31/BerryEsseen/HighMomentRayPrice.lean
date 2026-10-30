module

public import BerryEsseen.HighMomentRayDamping
public import BerryEsseen.IidSmoothingPrice
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

/-! 2026-10-29: the actual normalized iid CF error is bounded by a
one-parameter integral price. The original law enters the price only through
beta = rho/sqrt n; N records the proved range n >= N >= 1. The forcing is
derived by an exact real-frequency substitution in the square-bias sine
primitive. There is no free modulus envelope or numerical CDF assertion. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped Interval

namespace BerryEsseen.HighMomentRayPrice

open HighMomentRayDamping

def sineKernel (β v : ℝ) : ℝ :=
  2 * Real.sin (min (β * v / 2) (Real.pi / 2))

def B (β t : ℝ) : ℝ := ∫ v in (0 : ℝ)..t, sineKernel β v

def forcing (N : ℕ) (β t : ℝ) : ℝ :=
  lossEnvelope N β t * (B β t + loss N β * t ^ 3 / 3)

def integrand (N : ℕ) (β t : ℝ) : ℝ := Real.exp (t ^ 2 / 2) * forcing N β t

def price (N : ℕ) (β t : ℝ) : ℝ :=
  Real.exp (-(t ^ 2 / 2)) * ∫ u in (0 : ℝ)..t, integrand N β u

lemma continuous_sineKernel (β : ℝ) : Continuous (sineKernel β) := by
  unfold sineKernel
  fun_prop

lemma continuous_B (β : ℝ) : Continuous (B β) :=
  intervalIntegral.continuous_primitive
    (fun a b => (continuous_sineKernel β).intervalIntegrable a b) 0

lemma continuous_lossEnvelope (N : ℕ) (β : ℝ) : Continuous (lossEnvelope N β) := by
  unfold lossEnvelope exponent
  fun_prop

lemma lossEnvelope_nonneg (N : ℕ) (β t : ℝ) : 0 ≤ lossEnvelope N β t := by
  unfold lossEnvelope
  positivity

lemma continuous_forcing (N : ℕ) (β : ℝ) : Continuous (forcing N β) := by
  exact (continuous_lossEnvelope N β).mul ((continuous_B β).add (by fun_prop))

lemma continuous_integrand (N : ℕ) (β : ℝ) : Continuous (integrand N β) := by
  exact (by fun_prop : Continuous (fun t : ℝ => Real.exp (t ^ 2 / 2))).mul
    (continuous_forcing N β)

lemma continuous_price (N : ℕ) (β : ℝ) : Continuous (price N β) := by
  exact (by fun_prop : Continuous (fun t : ℝ => Real.exp (-(t ^ 2 / 2)))).mul
    (intervalIntegral.continuous_primitive
      (fun a b => (continuous_integrand N β).intervalIntegrable a b) 0)

private lemma normalized_square (n : ℕ) (hn : 0 < n) (t : ℝ) :
    (n : ℝ) * ((t / Real.sqrt n) ^ 2 / 2) = t ^ 2 / 2 := by
  rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  field_simp [(Nat.cast_pos.mpr hn : (0 : ℝ) < n).ne']

private lemma scaled_kernel_le (μ : ProbabilityMeasure ℝ) (n : ℕ) (hn : 0 < n)
    (v : ℝ) (hv : 0 ≤ v) :
    SquareBiasSine.sineKernelPrice μ (v / Real.sqrt n) ≤
      sineKernel (beta μ n) v + v ^ 2 / (n : ℝ) := by
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  have hd : 0 ≤ v / Real.sqrt n := div_nonneg hv hs.le
  have hmin : 0 ≤ min (v / Real.sqrt n) (Real.pi / 2) :=
    le_min hd (by positivity)
  have hsin : Real.sin (min (v / Real.sqrt n) (Real.pi / 2)) ≤ v / Real.sqrt n :=
    (Real.sin_le hmin).trans (min_le_left _ _)
  have hm := mul_le_mul_of_nonneg_left hsin hd
  have harg : thirdAbsoluteMoment μ * (v / Real.sqrt n) / 2 = beta μ n * v / 2 := by
    unfold beta
    ring
  unfold SquareBiasSine.sineKernelPrice
  rw [abs_of_nonneg hd, harg]
  change sineKernel (beta μ n) v +
    v / Real.sqrt n * Real.sin (min (v / Real.sqrt n) (Real.pi / 2)) ≤ _
  have hsq : v / Real.sqrt n * (v / Real.sqrt n) = v ^ 2 / (n : ℝ) := by
    rw [← sq, div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  rw [hsq] at hm
  exact add_le_add_right hm _

/-- Exact Jacobian for the proved sine primitive, followed by a quadratic
bound on its second summand. This statement needs no lower moment cutoff. -/
theorem scaled_sinePrimitive_le (μ : ProbabilityMeasure ℝ) (n : ℕ) (hn : 0 < n)
    (t : ℝ) (ht : 0 ≤ t) :
    Real.sqrt n * IidSmoothingPrice.sinePrimitive μ (t / Real.sqrt n) ≤
      B (beta μ n) t + t ^ 3 / (3 * (n : ℝ)) := by
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  have hsub := intervalIntegral.integral_comp_div (a := (0 : ℝ)) (b := t)
    (SquareBiasSine.sineKernelPrice μ) hs.ne'
  simp only [zero_div, smul_eq_mul] at hsub
  change Real.sqrt n * (∫ v in (0 : ℝ)..t / Real.sqrt n,
    SquareBiasSine.sineKernelPrice μ v) ≤ _
  rw [← hsub]
  have hcont : Continuous (fun v : ℝ =>
      sineKernel (beta μ n) v + v ^ 2 / (n : ℝ)) :=
    (continuous_sineKernel _).add (by fun_prop)
  calc
    _ ≤ ∫ v in (0 : ℝ)..t, (sineKernel (beta μ n) v + v ^ 2 / (n : ℝ)) := by
      exact intervalIntegral.integral_mono_on ht
        (((SquareBiasSine.continuous_sineKernelPrice μ).comp
          (continuous_id.div_const _)).intervalIntegrable 0 t)
        (hcont.intervalIntegrable 0 t)
        (fun v hv => scaled_kernel_le μ n hn v hv.1)
    _ = B (beta μ n) t + t ^ 3 / (3 * (n : ℝ)) := by
      rw [intervalIntegral.integral_add ((continuous_sineKernel _).intervalIntegrable 0 t)
        ((by fun_prop : Continuous (fun v : ℝ => v ^ 2 / (n : ℝ))).intervalIntegrable 0 t)]
      rw [intervalIntegral.integral_div, integral_pow]
      simp only [B, Nat.reduceAdd, Nat.cast_ofNat, zero_pow (by norm_num : 3 ≠ 0), sub_zero]
      ring

theorem scaled_sinePrimitive_le_loss (μ : ProbabilityMeasure ℝ) (n N : ℕ)
    (hN : 0 < N) (hNn : N ≤ n) (hρ : rho0 ≤ thirdAbsoluteMoment μ)
    (t : ℝ) (ht : 0 ≤ t) :
    Real.sqrt n * IidSmoothingPrice.sinePrimitive μ (t / Real.sqrt n) ≤
      B (beta μ n) t + loss N (beta μ n) * t ^ 3 / 3 := by
  have hn : 0 < n := lt_of_lt_of_le hN hNn
  apply (scaled_sinePrimitive_le μ n hn t ht).trans
  have hm := mul_le_mul_of_nonneg_right (inv_n_le_loss μ n N hN hNn hρ)
    (show 0 ≤ t ^ 3 / 3 by positivity)
  convert add_le_add_right hm (B (beta μ n) t) using 1 <;> ring

private def actualIntegrand (μ : ProbabilityMeasure ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  Real.exp (t ^ 2 / 2) * ‖charFun (μ : Measure ℝ) (t / Real.sqrt n)‖ ^ (n - 1) *
    (Real.sqrt n * IidSmoothingPrice.sinePrimitive μ (t / Real.sqrt n))

private lemma continuous_actualIntegrand (μ : ProbabilityMeasure ℝ) (n : ℕ) :
    Continuous (actualIntegrand μ n) := by
  have hc : Continuous (fun t : ℝ => ‖charFun (μ : Measure ℝ) (t / Real.sqrt n)‖) :=
    continuous_charFun.norm.comp (continuous_id.div_const _)
  exact ((by fun_prop : Continuous (fun t : ℝ => Real.exp (t ^ 2 / 2))).mul
    (hc.pow (n - 1))).mul (continuous_const.mul
      ((IidSmoothingPrice.continuous_sinePrimitive μ).comp (continuous_id.div_const _)))

private lemma rawSinePrice_eq_normalized (μ : ProbabilityMeasure ℝ) (n : ℕ) (hn : 0 < n)
    (t : ℝ) :
    IidSmoothingPrice.rawSinePrice μ n (fun s => ‖charFun (μ : Measure ℝ) s‖)
      (t / Real.sqrt n) =
      Real.exp (-(t ^ 2 / 2)) * ∫ u in (0 : ℝ)..t, actualIntegrand μ n u := by
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  have hs2 := Real.sq_sqrt (Nat.cast_nonneg n)
  let P := IidSmoothingPrice.priceIntegrand μ n (fun s => ‖charFun (μ : Measure ℝ) s‖)
  have hsub := intervalIntegral.inv_smul_integral_comp_div
    (a := (0 : ℝ)) (b := t) P (Real.sqrt n)
  simp only [zero_div, smul_eq_mul] at hsub
  have hpoint (u : ℝ) : (Real.sqrt n)⁻¹ * P (u / Real.sqrt n) = actualIntegrand μ n u := by
    dsimp [P, IidSmoothingPrice.priceIntegrand, actualIntegrand]
    rw [normalized_square n hn u]
    field_simp [hs.ne']
    rw [hs2]
  unfold IidSmoothingPrice.rawSinePrice
  rw [normalized_square n hn t]
  change Real.exp (-(t ^ 2 / 2)) * (∫ u in (0 : ℝ)..t / Real.sqrt n, P u) = _
  rw [← hsub, ← intervalIntegral.integral_const_mul]
  congr 1
  apply intervalIntegral.integral_congr
  intro u _
  exact hpoint u

private lemma actualIntegrand_le (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n N : ℕ) (hN : 0 < N) (hNn : N ≤ n) (hρ : rho0 ≤ thirdAbsoluteMoment μ)
    (t : ℝ) (ht : 0 ≤ t) : actualIntegrand μ n t ≤ integrand N (beta μ n) t := by
  have hn : 0 < n := lt_of_lt_of_le hN hNn
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  have hp := normalized_pred_power_le_lossEnvelope μ h n N hN hNn hρ t
  have hf := scaled_sinePrimitive_le_loss μ n N hN hNn hρ t ht
  have hprim : 0 ≤ IidSmoothingPrice.sinePrimitive μ (t / Real.sqrt n) :=
    (norm_nonneg _).trans (IidSmoothingPrice.norm_firstResidual_le_sinePrimitive μ h
      (t / Real.sqrt n) (div_nonneg ht hs.le))
  have hm := mul_le_mul hp hf (mul_nonneg hs.le hprim) (lossEnvelope_nonneg _ _ _)
  unfold actualIntegrand integrand forcing
  convert mul_le_mul_of_nonneg_left hm (Real.exp_pos (t ^ 2 / 2)).le using 1
  ring

/-- The actual normalized iid power error has a price with no free q and
no residual dependence on the original law beyond beta. -/
theorem normalized_power_sub_gaussian_le_price (μ : ProbabilityMeasure ℝ)
    (h : StandardizedLaw μ) (n N : ℕ) (hN : 0 < N) (hNn : N ≤ n)
    (hρ : rho0 ≤ thirdAbsoluteMoment μ) (t : ℝ) (ht : 0 ≤ t) :
    ‖charFun (μ : Measure ℝ) (t / Real.sqrt n) ^ n -
      (Real.exp (-(t ^ 2 / 2)) : ℂ)‖ ≤ price N (beta μ n) t := by
  have hn : 0 < n := lt_of_lt_of_le hN hNn
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  have hraw := IidSmoothingPrice.norm_iid_sub_gaussian_le μ h n hn
    (fun s => ‖charFun (μ : Measure ℝ) s‖) continuous_charFun.norm
    (t / Real.sqrt n) (div_nonneg ht hs.le) (fun _ _ => le_rfl)
  have hg : IidSmoothingPrice.scaledGaussian n (t / Real.sqrt n) =
      (Real.exp (-(t ^ 2 / 2)) : ℂ) := by
    unfold IidSmoothingPrice.scaledGaussian
    rw [normalized_square n hn t]
  rw [hg, rawSinePrice_eq_normalized μ n hn t] at hraw
  apply hraw.trans
  unfold price
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  exact intervalIntegral.integral_mono_on ht
    ((continuous_actualIntegrand μ n).intervalIntegrable 0 t)
    ((continuous_integrand N (beta μ n)).intervalIntegrable 0 t)
    (fun u hu => actualIntegrand_le μ h n N hN hNn hρ u hu.1)

theorem normalized_iid_sub_gaussian_le_price (μ : ProbabilityMeasure ℝ)
    (h : StandardizedLaw μ) (n N : ℕ) (hN : 0 < N) (hNn : N ≤ n)
    (hρ : rho0 ≤ thirdAbsoluteMoment μ) (t : ℝ) (ht : 0 ≤ t) :
    ‖charFun (normalizedIidSumLaw μ n) t - charFun (gaussianReal 0 1) t‖ ≤
      price N (beta μ n) t := by
  rw [PrawitzSmoothing.charFun_normalizedIidSumLaw, PrawitzSmoothing.charFun_standardGaussian]
  exact normalized_power_sub_gaussian_le_price μ h n N hN hNn hρ t ht

end BerryEsseen.HighMomentRayPrice

#print axioms BerryEsseen.HighMomentRayPrice.scaled_sinePrimitive_le
#print axioms BerryEsseen.HighMomentRayPrice.scaled_sinePrimitive_le_loss
#print axioms BerryEsseen.HighMomentRayPrice.normalized_power_sub_gaussian_le_price
#print axioms BerryEsseen.HighMomentRayPrice.normalized_iid_sub_gaussian_le_price
