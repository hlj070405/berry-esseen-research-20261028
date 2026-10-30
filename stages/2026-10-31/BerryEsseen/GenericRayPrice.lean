module

public import BerryEsseen.CoefficientRayPrice
public import BerryEsseen.CoefficientPriceCells

@[expose] public section

/-! 2026-10-29: a reusable price for any continuous, genuinely licensed
normalized predecessor-power bound.  The original distribution, sine
residual, third-moment forcing and loss are preserved.  New frequency
envelopes can instantiate this theorem without copying probability theory. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped Interval

namespace BerryEsseen.GenericRayPrice

open HighMomentRayDamping

def integrand (N : ℕ) (β : ℝ) (L : ℝ → ℝ) (u : ℝ) : ℝ :=
  Real.exp (u ^ 2 / 2) * L u *
    (u ^ 2 / 2 + CoarseHighMomentRayPrice.lambda N β * u ^ 3 / 3)

def price (N : ℕ) (β : ℝ) (L : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (-(t ^ 2 / 2)) * ∫ u in (0 : ℝ)..t, integrand N β L u

lemma continuous_integrand (N : ℕ) (β : ℝ) (L : ℝ → ℝ) (hL : Continuous L) :
    Continuous (integrand N β L) := by
  unfold integrand
  fun_prop

theorem continuous_price (N : ℕ) (β : ℝ) (L : ℝ → ℝ) (hL : Continuous L) :
    Continuous (price N β L) := by
  exact (by fun_prop : Continuous (fun t : ℝ => Real.exp (-(t ^ 2 / 2)))).mul
    (intervalIntegral.continuous_primitive
      (fun a b => (continuous_integrand N β L hL).intervalIntegrable a b) 0)

/-- A normalized n-th power bound licenses the original n-1 loss.
This is a scalar consequence, including n=1 and either sign of E. -/
theorem pred_power_from_normalized_bound (x E e : ℝ) (n : ℕ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hn : 0 < n)
    (he : 1 / (n : ℝ) ≤ e) (he1 : e ≤ 1) (hpow : x ^ n ≤ Real.exp E) :
    x ^ (n - 1) ≤ Real.exp ((1 - e) * E) := by
  have hnp : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  by_cases hEn : E ≤ 0
  · have hp : (Real.exp (E / n)) ^ n = Real.exp E := by
      rw [← Real.exp_nat_mul]
      congr 1
      field_simp [hnp.ne']
    have hxexp : x ≤ Real.exp (E / n) :=
      (pow_le_pow_iff_left₀ hx0 (Real.exp_nonneg _) hn.ne').mp (hpow.trans_eq hp.symm)
    have hpre := pow_le_pow_left₀ hx0 hxexp (n - 1)
    rw [← Real.exp_nat_mul] at hpre
    have hk : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
    have hf : 1 - e ≤ ((n - 1 : ℕ) : ℝ) / (n : ℝ) := by
      rw [hk]
      apply (le_div_iff₀ hnp).mpr
      have hh := (div_le_iff₀ hnp).mp he
      nlinarith only [hh]
    apply hpre.trans
    apply Real.exp_le_exp.mpr
    convert mul_le_mul_of_nonpos_right hf hEn using 1 <;> ring
  · have hxpow : x ^ (n - 1) ≤ 1 := by
      simpa only [one_pow] using pow_le_pow_left₀ hx0 hx1 (n - 1)
    exact hxpow.trans (Real.one_le_exp (mul_nonneg (sub_nonneg.mpr he1) (le_of_not_ge hEn)))

private lemma normalized_square (n : ℕ) (hn : 0 < n) (t : ℝ) :
    (n : ℝ) * ((t / Real.sqrt n) ^ 2 / 2) = t ^ 2 / 2 := by
  rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  field_simp [(Nat.cast_pos.mpr hn : (0 : ℝ) < n).ne']

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
    (L : ℝ → ℝ) (hPred : ∀ u, 0 ≤ u →
      ‖charFun (μ : Measure ℝ) (u / Real.sqrt n)‖ ^ (n - 1) ≤ L u)
    (t : ℝ) (ht : 0 ≤ t) :
    actualIntegrand μ n t ≤ beta μ n * integrand N (beta μ n) L t := by
  have hn : 0 < n := lt_of_lt_of_le hN hNn
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  have hβ := CoarseHighMomentRayPrice.beta_pos μ n hn hρ
  have hp := hPred t ht
  have hB := CoarseHighMomentRayPrice.B_le_quadratic (beta μ n) hβ.le t ht
  have hf : Real.sqrt n * IidSmoothingPrice.sinePrimitive μ (t / Real.sqrt n) ≤
      beta μ n * (t ^ 2 / 2 + CoarseHighMomentRayPrice.lambda N (beta μ n) * t ^ 3 / 3) := by
    apply (HighMomentRayPrice.scaled_sinePrimitive_le_loss μ n N hN hNn hρ t ht).trans
    calc
      _ ≤ beta μ n * t ^ 2 / 2 + loss N (beta μ n) * t ^ 3 / 3 := by linarith only [hB]
      _ = _ := by rw [CoarseHighMomentRayPrice.loss_eq_beta_mul_lambda N (beta μ n) hβ]; ring
  have hprim : 0 ≤ IidSmoothingPrice.sinePrimitive μ (t / Real.sqrt n) :=
    (norm_nonneg _).trans (IidSmoothingPrice.norm_firstResidual_le_sinePrimitive μ h
      (t / Real.sqrt n) (div_nonneg ht hs.le))
  have hL0 := (pow_nonneg (norm_nonneg _) (n - 1)).trans hp
  have hm := mul_le_mul hp hf (mul_nonneg hs.le hprim) hL0
  unfold actualIntegrand integrand
  convert mul_le_mul_of_nonneg_left hm (Real.exp_pos (t ^ 2 / 2)).le using 1 <;> ring

/-- A real same-law predecessor envelope, rather than a freely assumed
CF-error price, controls the exact normalized iid error. -/
theorem normalized_power_error_div_beta_le_price (μ : ProbabilityMeasure ℝ)
    (h : StandardizedLaw μ) (n N : ℕ) (hN : 0 < N) (hNn : N ≤ n)
    (hρ : rho0 ≤ thirdAbsoluteMoment μ) (L : ℝ → ℝ) (hCont : Continuous L)
    (hPred : ∀ u, 0 ≤ u → ‖charFun (μ : Measure ℝ) (u / Real.sqrt n)‖ ^ (n - 1) ≤ L u)
    (t : ℝ) (ht : 0 ≤ t) :
    ‖charFun (μ : Measure ℝ) (t / Real.sqrt n) ^ n -
      (Real.exp (-(t ^ 2 / 2)) : ℂ)‖ / beta μ n ≤ price N (beta μ n) L t := by
  have hn : 0 < n := lt_of_lt_of_le hN hNn
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  have hβ := CoarseHighMomentRayPrice.beta_pos μ n hn hρ
  have hraw := IidSmoothingPrice.norm_iid_sub_gaussian_le μ h n hn
    (fun s => ‖charFun (μ : Measure ℝ) s‖) continuous_charFun.norm
    (t / Real.sqrt n) (div_nonneg ht hs.le) (fun _ _ => le_rfl)
  have hg : IidSmoothingPrice.scaledGaussian n (t / Real.sqrt n) =
      (Real.exp (-(t ^ 2 / 2)) : ℂ) := by
    unfold IidSmoothingPrice.scaledGaussian
    rw [normalized_square n hn t]
  rw [hg, rawSinePrice_eq_normalized μ n hn t] at hraw
  apply (div_le_iff₀ hβ).mpr
  have hint : (∫ u in (0 : ℝ)..t, actualIntegrand μ n u) ≤
      beta μ n * ∫ u in (0 : ℝ)..t, integrand N (beta μ n) L u := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on ht
      ((continuous_actualIntegrand μ n).intervalIntegrable 0 t)
      ((continuous_const.mul (continuous_integrand N (beta μ n) L hCont)).intervalIntegrable 0 t)
      (fun u hu => actualIntegrand_le μ h n N hN hNn hρ L hPred u hu.1)
  have hh := hraw.trans (mul_le_mul_of_nonneg_left hint (Real.exp_pos _).le)
  unfold price
  convert hh using 1
  ring

theorem price_mono (N : ℕ) (hN : 0 < N) (β : ℝ) (hβ : 0 < β)
    (L M : ℝ → ℝ) (hL : Continuous L) (hM : Continuous M) (t : ℝ) (ht : 0 ≤ t)
    (hLM : ∀ u ∈ Icc 0 t, L u ≤ M u) : price N β L t ≤ price N β M t := by
  apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
  apply intervalIntegral.integral_mono_on ht
    ((continuous_integrand N β L hL).intervalIntegrable 0 t)
    ((continuous_integrand N β M hM).intervalIntegrable 0 t)
  intro u hu
  have hu0 : 0 ≤ u := hu.1
  have hl := CoefficientPriceCells.lambda_nonneg N hN β hβ
  unfold integrand
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hLM u hu) (Real.exp_nonneg _)) (by positivity)

end BerryEsseen.GenericRayPrice

#print axioms BerryEsseen.GenericRayPrice.pred_power_from_normalized_bound
#print axioms BerryEsseen.GenericRayPrice.normalized_power_error_div_beta_le_price
#print axioms BerryEsseen.GenericRayPrice.price_mono
