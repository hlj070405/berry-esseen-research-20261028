module

public import BerryEsseen.CoarseHighMomentRayPrice

@[expose] public section

/-! 2026-10-29: retain the actual sample-size/moment correlation in the
one-parameter CF price. The cubic coefficient c is justified by the actual
law through rho+1 <= c*rho. A node theorem derives that qualification from
n >= N and an upper endpoint for s=1/beta^2. Neither the coefficient nor the
characteristic-function error is assumed as an unexplained numerical input. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped Interval

namespace BerryEsseen.CoefficientRayPrice

open HighMomentRayDamping

def oldCoefficient : ℝ := 1 + 1 / rho0

def exponent (c a b β t : ℝ) : ℝ := -a * t ^ 2 + b * c * β * |t| ^ 3

def envelope (c β t : ℝ) : ℝ :=
  min 1 (min (Real.exp (exponent c (1 / 2) (1 / 10) β t))
    (min (Real.exp (exponent c ClassicalCosineCubic.a ClassicalCosineCubic.b β t))
      (Real.exp (exponent c ClassicalRationalCosine.a ClassicalRationalCosine.b β t))))

def lossEnvelope (N : ℕ) (c β t : ℝ) : ℝ :=
  min 1 (min (Real.exp ((1 - loss N β) * exponent c (1 / 2) (1 / 10) β t))
    (min (Real.exp ((1 - loss N β) *
      exponent c ClassicalCosineCubic.a ClassicalCosineCubic.b β t))
      (Real.exp ((1 - loss N β) *
        exponent c ClassicalRationalCosine.a ClassicalRationalCosine.b β t))))

def coarseIntegrand (N : ℕ) (c β t : ℝ) : ℝ :=
  Real.exp (t ^ 2 / 2) * lossEnvelope N c β t *
    (t ^ 2 / 2 + CoarseHighMomentRayPrice.lambda N β * t ^ 3 / 3)

def coarsePrice (N : ℕ) (c β t : ℝ) : ℝ :=
  Real.exp (-(t ^ 2 / 2)) * ∫ u in (0 : ℝ)..t, coarseIntegrand N c β u

lemma continuous_envelope (c β : ℝ) : Continuous (envelope c β) := by
  unfold envelope exponent
  fun_prop

lemma continuous_lossEnvelope (N : ℕ) (c β : ℝ) : Continuous (lossEnvelope N c β) := by
  unfold lossEnvelope exponent
  fun_prop

lemma envelope_nonneg (c β t : ℝ) : 0 ≤ envelope c β t := by
  unfold envelope
  positivity

lemma lossEnvelope_nonneg (N : ℕ) (c β t : ℝ) : 0 ≤ lossEnvelope N c β t := by
  unfold lossEnvelope
  positivity

lemma continuous_coarseIntegrand (N : ℕ) (c β : ℝ) : Continuous (coarseIntegrand N c β) := by
  exact ((by fun_prop : Continuous (fun t : ℝ => Real.exp (t ^ 2 / 2))).mul
    (continuous_lossEnvelope N c β)).mul (by fun_prop)

lemma continuous_coarsePrice (N : ℕ) (c β : ℝ) : Continuous (coarsePrice N c β) := by
  exact (by fun_prop : Continuous (fun t : ℝ => Real.exp (-(t ^ 2 / 2)))).mul
    (intervalIntegral.continuous_primitive
      (fun a b => (continuous_coarseIntegrand N c β).intervalIntegrable a b) 0)

lemma coefficient_nonneg (μ : ProbabilityMeasure ℝ) (c : ℝ)
    (hρ : rho0 ≤ thirdAbsoluteMoment μ)
    (hC : thirdAbsoluteMoment μ + 1 ≤ c * thirdAbsoluteMoment μ) : 0 ≤ c := by
  have hρp : 0 < thirdAbsoluteMoment μ := lt_of_lt_of_le rho0_pos hρ
  by_contra hc
  have hh := mul_neg_of_neg_of_pos (lt_of_not_ge hc) hρp
  linarith only [hh, hC, hρp]

/-- The upper endpoint b of s=1/beta^2 supplies the missing sample-size
qualification. The lower endpoint is retained to match an actual node. -/
theorem node_coefficient_qualifies (μ : ProbabilityMeasure ℝ) (n N : ℕ)
    (hN : 0 < N) (hNn : N ≤ n) (hρ : rho0 ≤ thirdAbsoluteMoment μ)
    (a b c : ℝ) (ha : 0 < a) (has : a ≤ 1 / beta μ n ^ 2)
    (hsb : 1 / beta μ n ^ 2 ≤ b)
    (hc : min oldCoefficient (1 + Real.sqrt (b / (N : ℝ))) ≤ c) :
    thirdAbsoluteMoment μ + 1 ≤ c * thirdAbsoluteMoment μ := by
  have hn : 0 < n := lt_of_lt_of_le hN hNn
  have hnp : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hNp : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hρp : 0 < thirdAbsoluteMoment μ := lt_of_lt_of_le rho0_pos hρ
  have hβ : 0 < beta μ n := CoarseHighMomentRayPrice.beta_pos μ n hn hρ
  have hb : 0 < b := ha.trans_le (has.trans hsb)
  have hfactor : (1 : ℝ) ≤ b * beta μ n ^ 2 :=
    (div_le_iff₀ (sq_pos_of_pos hβ)).mp hsb
  have hm := mul_le_mul_of_nonneg_right hfactor (Nat.cast_nonneg n)
  have heq := congrArg (fun z : ℝ => b * z) (beta_sq_mul_n μ n hn)
  have hNcast : (N : ℝ) ≤ n := Nat.cast_le.mpr hNn
  have hmoment : (N : ℝ) ≤ b * thirdAbsoluteMoment μ ^ 2 := by
    nlinarith only [hm, heq, hNcast]
  have hratio : (1 : ℝ) ≤ (b * thirdAbsoluteMoment μ ^ 2) / (N : ℝ) :=
    (le_div_iff₀ hNp).mpr (by simpa using hmoment)
  have hsqrt : Real.sqrt (b / (N : ℝ)) ^ 2 = b / (N : ℝ) :=
    Real.sq_sqrt (div_nonneg hb.le hNp.le)
  have hprod : (1 : ℝ) ≤ Real.sqrt (b / (N : ℝ)) * thirdAbsoluteMoment μ := by
    apply (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1)
      (mul_nonneg (Real.sqrt_nonneg _) hρp.le)).mp
    rw [one_pow, mul_pow, hsqrt]
    convert hratio using 1
    ring
  have hnew : thirdAbsoluteMoment μ + 1 ≤
      (1 + Real.sqrt (b / (N : ℝ))) * thirdAbsoluteMoment μ := by
    nlinarith only [hprod]
  have hu : (1 : ℝ) ≤ thirdAbsoluteMoment μ / rho0 :=
    (le_div_iff₀ rho0_pos).mpr (by simpa using hρ)
  have hold : thirdAbsoluteMoment μ + 1 ≤ oldCoefficient * thirdAbsoluteMoment μ := by
    unfold oldCoefficient
    calc
      _ ≤ thirdAbsoluteMoment μ + thirdAbsoluteMoment μ / rho0 := by linarith only [hu]
      _ = _ := by ring
  have hmin : thirdAbsoluteMoment μ + 1 ≤
      min oldCoefficient (1 + Real.sqrt (b / (N : ℝ))) * thirdAbsoluteMoment μ := by
    rw [min_mul_of_nonneg _ _ hρp.le]
    exact le_min hold hnew
  exact hmin.trans (mul_le_mul_of_nonneg_right hc hρp.le)

private def rawExponent (ρ a b s : ℝ) : ℝ := -a * s ^ 2 + b * (ρ + 1) * |s| ^ 3

private lemma le_exp_of_sq (x v : ℝ) (hx : 0 ≤ x) (h : x ^ 2 ≤ 1 + 2 * v) :
    x ≤ Real.exp v := by
  apply (sq_le_sq₀ hx (Real.exp_nonneg v)).mp
  rw [← Real.exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  exact h.trans (by linarith [Real.add_one_le_exp (2 * v)])

private lemma scaled_rawExponent (ρ a b : ℝ) (n : ℕ) (hn : 0 < n) (t : ℝ) :
    (n : ℝ) * rawExponent ρ a b (t / Real.sqrt n) =
      -a * t ^ 2 + b * ((ρ + 1) / Real.sqrt n) * |t| ^ 3 := by
  let s : ℝ := Real.sqrt n
  have hs : 0 < s := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  have hs2 : s ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
  change (n : ℝ) * rawExponent ρ a b (t / s) =
    -a * t ^ 2 + b * ((ρ + 1) / s) * |t| ^ 3
  dsimp [rawExponent]
  rw [abs_div, abs_of_pos hs, div_pow, div_pow, ← hs2]
  field_simp [hs.ne']

private lemma scaled_rawExponent_le (μ : ProbabilityMeasure ℝ) (n : ℕ) (hn : 0 < n)
    (c : ℝ) (hC : thirdAbsoluteMoment μ + 1 ≤ c * thirdAbsoluteMoment μ)
    (a b : ℝ) (hb : 0 ≤ b) (t : ℝ) :
    (n : ℝ) * rawExponent (thirdAbsoluteMoment μ) a b (t / Real.sqrt n) ≤
      exponent c a b (beta μ n) t := by
  rw [scaled_rawExponent _ _ _ n hn]
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  have hd := div_le_div_of_nonneg_right hC hs.le
  have hm := mul_le_mul_of_nonneg_left hd (mul_nonneg hb (by positivity : 0 ≤ |t| ^ 3))
  dsimp [exponent, beta]
  convert add_le_add_left hm (-a * t ^ 2) using 1 <;> ring

private lemma power_le_exp (x v E : ℝ) (hx : 0 ≤ x) (hv : x ≤ Real.exp v)
    (n : ℕ) (hE : (n : ℝ) * v ≤ E) : x ^ n ≤ Real.exp E := by
  have hh := pow_le_pow_left₀ hx hv n
  rw [← Real.exp_nat_mul] at hh
  exact hh.trans (Real.exp_le_exp.mpr hE)

private lemma pred_power_le_loss_exp (x v E e : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1)
    (hv : x ≤ Real.exp v) (n : ℕ) (hn : 0 < n) (he : 1 / (n : ℝ) ≤ e)
    (he1 : e ≤ 1) (hE : (n : ℝ) * v ≤ E) :
    x ^ (n - 1) ≤ Real.exp ((1 - e) * E) := by
  have hk : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  have hnp : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  by_cases hEn : E ≤ 0
  · have hf : 1 - e ≤ ((n - 1 : ℕ) : ℝ) / (n : ℝ) := by
      rw [hk]
      apply (le_div_iff₀ hnp).mpr
      have hh := (div_le_iff₀ hnp).mp he
      nlinarith only [hh]
    have hm := mul_le_mul_of_nonneg_left hE
      (div_nonneg (Nat.cast_nonneg (n - 1)) hnp.le)
    have hid : ((n - 1 : ℕ) : ℝ) / (n : ℝ) * ((n : ℝ) * v) =
        ((n - 1 : ℕ) : ℝ) * v := by field_simp [hnp.ne']
    rw [hid] at hm
    apply power_le_exp x v _ hx hv (n - 1)
    exact hm.trans (mul_le_mul_of_nonpos_right hf hEn)
  · have hp : 0 ≤ (1 - e) * E := mul_nonneg (sub_nonneg.mpr he1) (le_of_not_ge hEn)
    have hxpow : x ^ (n - 1) ≤ 1 := by simpa using pow_le_pow_left₀ hx hx1 (n - 1)
    exact hxpow.trans (Real.one_le_exp hp)

private lemma raw_bounds (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (s : ℝ) :
    (‖charFun (μ : Measure ℝ) s‖ ≤
      Real.exp (rawExponent (thirdAbsoluteMoment μ) (1 / 2) (1 / 10) s)) ∧
    (‖charFun (μ : Measure ℝ) s‖ ≤ Real.exp (rawExponent (thirdAbsoluteMoment μ)
      ClassicalCosineCubic.a ClassicalCosineCubic.b s)) ∧
    (‖charFun (μ : Measure ℝ) s‖ ≤ Real.exp (rawExponent (thirdAbsoluteMoment μ)
      ClassicalRationalCosine.a ClassicalRationalCosine.b s)) := by
  refine ⟨?_, ?_, ?_⟩
  · apply le_exp_of_sq _ _ (norm_nonneg _)
    have hh := ClassicalDamping.charFun_norm_sq_le μ h s
    dsimp [rawExponent]
    nlinarith only [hh]
  · apply le_exp_of_sq _ _ (norm_nonneg _)
    have hh := ClassicalCosineCubic.charFun_norm_sq_le μ h s
    dsimp [rawExponent, ClassicalCosineCubic.polynomial] at *
    nlinarith only [hh]
  · apply le_exp_of_sq _ _ (norm_nonneg _)
    have hh := ClassicalRationalCosine.charFun_norm_sq_le μ h s
    dsimp [rawExponent, ClassicalRationalCosine.polynomial] at *
    nlinarith only [hh]

theorem normalized_power_le_envelope (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (hn : 0 < n) (c : ℝ)
    (hC : thirdAbsoluteMoment μ + 1 ≤ c * thirdAbsoluteMoment μ) (t : ℝ) :
    ‖charFun (μ : Measure ℝ) (t / Real.sqrt n)‖ ^ n ≤ envelope c (beta μ n) t := by
  obtain ⟨h0, hθ, hr⟩ := raw_bounds μ h (t / Real.sqrt n)
  unfold envelope
  refine le_min (by simpa using pow_le_pow_left₀ (norm_nonneg _) (norm_charFun_le_one _) n)
    (le_min ?_ (le_min ?_ ?_))
  · exact power_le_exp _ _ _ (norm_nonneg _) h0 n
      (scaled_rawExponent_le μ n hn c hC _ _ (by norm_num) t)
  · exact power_le_exp _ _ _ (norm_nonneg _) hθ n
      (scaled_rawExponent_le μ n hn c hC _ _ ClassicalCosineCubic.b_nonneg t)
  · exact power_le_exp _ _ _ (norm_nonneg _) hr n
      (scaled_rawExponent_le μ n hn c hC _ _ ClassicalRationalCosine.b_nonneg t)

theorem normalized_iid_norm_le_envelope (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (hn : 0 < n) (c : ℝ)
    (hC : thirdAbsoluteMoment μ + 1 ≤ c * thirdAbsoluteMoment μ) (t : ℝ) :
    ‖charFun (normalizedIidSumLaw μ n) t‖ ≤ envelope c (beta μ n) t := by
  rw [PrawitzSmoothing.charFun_normalizedIidSumLaw, norm_pow]
  exact normalized_power_le_envelope μ h n hn c hC t

theorem normalized_pred_power_le_lossEnvelope (μ : ProbabilityMeasure ℝ)
    (h : StandardizedLaw μ) (n N : ℕ) (hN : 0 < N) (hNn : N ≤ n)
    (hρ : rho0 ≤ thirdAbsoluteMoment μ) (c : ℝ)
    (hC : thirdAbsoluteMoment μ + 1 ≤ c * thirdAbsoluteMoment μ) (t : ℝ) :
    ‖charFun (μ : Measure ℝ) (t / Real.sqrt n)‖ ^ (n - 1) ≤
      lossEnvelope N c (beta μ n) t := by
  have hn : 0 < n := lt_of_lt_of_le hN hNn
  have he := inv_n_le_loss μ n N hN hNn hρ
  have he1 := loss_le_one N hN (beta μ n)
  obtain ⟨h0, hθ, hr⟩ := raw_bounds μ h (t / Real.sqrt n)
  unfold lossEnvelope
  refine le_min (by simpa using pow_le_pow_left₀ (norm_nonneg _) (norm_charFun_le_one _) (n - 1))
    (le_min ?_ (le_min ?_ ?_))
  · exact pred_power_le_loss_exp _ _ _ _ (norm_nonneg _) (norm_charFun_le_one _) h0 n hn he he1
      (scaled_rawExponent_le μ n hn c hC _ _ (by norm_num) t)
  · exact pred_power_le_loss_exp _ _ _ _ (norm_nonneg _) (norm_charFun_le_one _) hθ n hn he he1
      (scaled_rawExponent_le μ n hn c hC _ _ ClassicalCosineCubic.b_nonneg t)
  · exact pred_power_le_loss_exp _ _ _ _ (norm_nonneg _) (norm_charFun_le_one _) hr n hn he he1
      (scaled_rawExponent_le μ n hn c hC _ _ ClassicalRationalCosine.b_nonneg t)

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
    (c : ℝ) (hC : thirdAbsoluteMoment μ + 1 ≤ c * thirdAbsoluteMoment μ)
    (t : ℝ) (ht : 0 ≤ t) :
    actualIntegrand μ n t ≤ beta μ n * coarseIntegrand N c (beta μ n) t := by
  have hn : 0 < n := lt_of_lt_of_le hN hNn
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  have hβ := CoarseHighMomentRayPrice.beta_pos μ n hn hρ
  have hp := normalized_pred_power_le_lossEnvelope μ h n N hN hNn hρ c hC t
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
  have hm := mul_le_mul hp hf (mul_nonneg hs.le hprim) (lossEnvelope_nonneg _ _ _ _)
  unfold actualIntegrand coarseIntegrand
  convert mul_le_mul_of_nonneg_left hm (Real.exp_pos (t ^ 2 / 2)).le using 1 <;> ring

/-- Actual same-law normalized CF error, with a qualified cubic coefficient
and no free q, error-price premise, or change to the moment/sample range. -/
theorem normalized_power_error_div_beta_le_coarsePrice (μ : ProbabilityMeasure ℝ)
    (h : StandardizedLaw μ) (n N : ℕ) (hN : 0 < N) (hNn : N ≤ n)
    (hρ : rho0 ≤ thirdAbsoluteMoment μ) (c : ℝ)
    (hC : thirdAbsoluteMoment μ + 1 ≤ c * thirdAbsoluteMoment μ) (t : ℝ) (ht : 0 ≤ t) :
    ‖charFun (μ : Measure ℝ) (t / Real.sqrt n) ^ n -
      (Real.exp (-(t ^ 2 / 2)) : ℂ)‖ / beta μ n ≤ coarsePrice N c (beta μ n) t := by
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
      beta μ n * ∫ u in (0 : ℝ)..t, coarseIntegrand N c (beta μ n) u := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on ht
      ((continuous_actualIntegrand μ n).intervalIntegrable 0 t)
      ((continuous_const.mul (continuous_coarseIntegrand N c (beta μ n))).intervalIntegrable 0 t)
      (fun u hu => actualIntegrand_le μ h n N hN hNn hρ c hC u hu.1)
  have hh := hraw.trans (mul_le_mul_of_nonneg_left hint (Real.exp_pos _).le)
  unfold coarsePrice
  convert hh using 1
  ring

theorem normalized_iid_error_div_beta_le_coarsePrice (μ : ProbabilityMeasure ℝ)
    (h : StandardizedLaw μ) (n N : ℕ) (hN : 0 < N) (hNn : N ≤ n)
    (hρ : rho0 ≤ thirdAbsoluteMoment μ) (c : ℝ)
    (hC : thirdAbsoluteMoment μ + 1 ≤ c * thirdAbsoluteMoment μ) (t : ℝ) (ht : 0 ≤ t) :
    ‖charFun (normalizedIidSumLaw μ n) t - charFun (gaussianReal 0 1) t‖ / beta μ n ≤
      coarsePrice N c (beta μ n) t := by
  rw [PrawitzSmoothing.charFun_normalizedIidSumLaw, PrawitzSmoothing.charFun_standardGaussian]
  exact normalized_power_error_div_beta_le_coarsePrice μ h n N hN hNn hρ c hC t ht

end BerryEsseen.CoefficientRayPrice

#print axioms BerryEsseen.CoefficientRayPrice.node_coefficient_qualifies
#print axioms BerryEsseen.CoefficientRayPrice.normalized_power_le_envelope
#print axioms BerryEsseen.CoefficientRayPrice.normalized_pred_power_le_lossEnvelope
#print axioms BerryEsseen.CoefficientRayPrice.normalized_power_error_div_beta_le_coarsePrice
#print axioms BerryEsseen.CoefficientRayPrice.normalized_iid_error_div_beta_le_coarsePrice
