module

public import BerryEsseen.ClassicalRationalCosine

@[expose] public section

/-! 2026-10-29: one-parameter damping for the actual iid high-moment law.
For n >= N >= 1 and rho >= 7361/4000, beta = rho/sqrt n eliminates
rho and n from the nth-power modulus. The (n-1)st power retains the
proved loss e = min (beta^2/rho0^2) (1/N). No CDF integral estimate or
numerical Berry--Esseen constant is asserted in this module. -/

noncomputable section

open MeasureTheory ProbabilityTheory

namespace BerryEsseen.HighMomentRayDamping

def rho0 : ℝ := 7361 / 4000

def beta (μ : ProbabilityMeasure ℝ) (n : ℕ) : ℝ :=
  thirdAbsoluteMoment μ / Real.sqrt n

def loss (N : ℕ) (β : ℝ) : ℝ := min (β ^ 2 / rho0 ^ 2) (1 / (N : ℝ))

def exponent (a b β t : ℝ) : ℝ :=
  -a * t ^ 2 + b * (1 + 1 / rho0) * β * |t| ^ 3

def envelope (β t : ℝ) : ℝ :=
  min 1 (min (Real.exp (exponent (1 / 2) (1 / 10) β t))
    (min (Real.exp (exponent ClassicalCosineCubic.a ClassicalCosineCubic.b β t))
      (Real.exp (exponent ClassicalRationalCosine.a ClassicalRationalCosine.b β t))))

def lossEnvelope (N : ℕ) (β t : ℝ) : ℝ :=
  min 1 (min (Real.exp ((1 - loss N β) * exponent (1 / 2) (1 / 10) β t))
    (min (Real.exp ((1 - loss N β) *
      exponent ClassicalCosineCubic.a ClassicalCosineCubic.b β t))
      (Real.exp ((1 - loss N β) *
        exponent ClassicalRationalCosine.a ClassicalRationalCosine.b β t))))

private def rawExponent (ρ a b s : ℝ) : ℝ :=
  -a * s ^ 2 + b * (ρ + 1) * |s| ^ 3

lemma rho0_pos : 0 < rho0 := by norm_num [rho0]

lemma loss_nonneg (N : ℕ) (β : ℝ) : 0 ≤ loss N β := by
  unfold loss
  positivity

lemma loss_le_one (N : ℕ) (hN : 0 < N) (β : ℝ) : loss N β ≤ 1 := by
  have hp : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have h1 : (1 : ℝ) ≤ N := by exact_mod_cast (Nat.succ_le_iff.mpr hN)
  exact (min_le_right _ _).trans ((div_le_iff₀ hp).mpr (by linarith))

lemma beta_sq_mul_n (μ : ProbabilityMeasure ℝ) (n : ℕ) (hn : 0 < n) :
    beta μ n ^ 2 * (n : ℝ) = thirdAbsoluteMoment μ ^ 2 := by
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  have hs2 := Real.sq_sqrt (Nat.cast_nonneg n)
  unfold beta
  rw [div_pow]
  rw [hs2]
  exact div_mul_cancel₀ _ (Nat.cast_pos.mpr hn).ne'

/-- Both constraints are needed: rho controls the small-beta end, while N
controls the large-beta end. This theorem does not cover any n < N. -/
theorem inv_n_le_loss (μ : ProbabilityMeasure ℝ) (n N : ℕ) (hN : 0 < N)
    (hNn : N ≤ n) (hρ : rho0 ≤ thirdAbsoluteMoment μ) :
    1 / (n : ℝ) ≤ loss N (beta μ n) := by
  have hn : 0 < n := lt_of_lt_of_le hN hNn
  have hnp : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hrp : 0 < rho0 ^ 2 := sq_pos_of_pos rho0_pos
  apply le_min
  · apply (div_le_div_iff₀ hnp hrp).mpr
    have hsq : rho0 ^ 2 ≤ thirdAbsoluteMoment μ ^ 2 := by
      nlinarith [rho0_pos]
    nlinarith only [beta_sq_mul_n μ n hn, hsq]
  · exact one_div_le_one_div_of_le (Nat.cast_pos.mpr hN) (Nat.cast_le.mpr hNn)

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
    (hρ : rho0 ≤ thirdAbsoluteMoment μ) (a b : ℝ) (hb : 0 ≤ b) (t : ℝ) :
    (n : ℝ) * rawExponent (thirdAbsoluteMoment μ) a b (t / Real.sqrt n) ≤
      exponent a b (beta μ n) t := by
  rw [scaled_rawExponent _ _ _ n hn]
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  have hu : (1 : ℝ) ≤ thirdAbsoluteMoment μ / rho0 :=
    (le_div_iff₀ rho0_pos).mpr (by simpa using hρ)
  have hc : thirdAbsoluteMoment μ + 1 ≤
      (1 + 1 / rho0) * thirdAbsoluteMoment μ := by
    calc
      _ ≤ thirdAbsoluteMoment μ + thirdAbsoluteMoment μ / rho0 := by linarith only [hu]
      _ = _ := by ring
  have hd := div_le_div_of_nonneg_right hc hs.le
  have hm := mul_le_mul_of_nonneg_left hd (mul_nonneg hb (by positivity : 0 ≤ |t| ^ 3))
  dsimp [exponent, beta]
  convert add_le_add_left hm (-a * t ^ 2) using 1 <;> ring

private lemma power_le_exp (x v E : ℝ) (hx : 0 ≤ x) (hv : x ≤ Real.exp v)
    (n : ℕ) (hE : (n : ℝ) * v ≤ E) : x ^ n ≤ Real.exp E := by
  have hh := pow_le_pow_left₀ hx hv n
  rw [← Real.exp_nat_mul] at hh
  exact hh.trans (Real.exp_le_exp.mpr hE)

/-- The exponent comparison must split by the sign of E. A positive E is
paid by x <= 1; a nonpositive E reverses the factor comparison. -/
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
    have hxpow : x ^ (n - 1) ≤ 1 := by
      simpa using pow_le_pow_left₀ hx hx1 (n - 1)
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

/-- Q_beta bounds the nth power of the original, same-law CF. -/
theorem normalized_power_le_envelope (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (hn : 0 < n) (hρ : rho0 ≤ thirdAbsoluteMoment μ) (t : ℝ) :
    ‖charFun (μ : Measure ℝ) (t / Real.sqrt n)‖ ^ n ≤ envelope (beta μ n) t := by
  obtain ⟨h0, hθ, hr⟩ := raw_bounds μ h (t / Real.sqrt n)
  unfold envelope
  refine le_min (by simpa using pow_le_pow_left₀ (norm_nonneg _) (norm_charFun_le_one _) n)
    (le_min ?_ (le_min ?_ ?_))
  · exact power_le_exp _ _ _ (norm_nonneg _) h0 n
      (scaled_rawExponent_le μ n hn hρ _ _ (by norm_num) t)
  · exact power_le_exp _ _ _ (norm_nonneg _) hθ n
      (scaled_rawExponent_le μ n hn hρ _ _ ClassicalCosineCubic.b_nonneg t)
  · exact power_le_exp _ _ _ (norm_nonneg _) hr n
      (scaled_rawExponent_le μ n hn hρ _ _ ClassicalRationalCosine.b_nonneg t)

theorem normalized_iid_norm_le_envelope (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (hn : 0 < n) (hρ : rho0 ≤ thirdAbsoluteMoment μ) (t : ℝ) :
    ‖charFun (normalizedIidSumLaw μ n) t‖ ≤ envelope (beta μ n) t := by
  rw [PrawitzSmoothing.charFun_normalizedIidSumLaw, norm_pow]
  exact normalized_power_le_envelope μ h n hn hρ t

/-- The actual residual power has a one-parameter loss envelope, uniformly
for all n >= N. Natural powers avoid any real-power convention at CF zeros. -/
theorem normalized_pred_power_le_lossEnvelope (μ : ProbabilityMeasure ℝ)
    (h : StandardizedLaw μ) (n N : ℕ) (hN : 0 < N) (hNn : N ≤ n)
    (hρ : rho0 ≤ thirdAbsoluteMoment μ) (t : ℝ) :
    ‖charFun (μ : Measure ℝ) (t / Real.sqrt n)‖ ^ (n - 1) ≤
      lossEnvelope N (beta μ n) t := by
  have hn : 0 < n := lt_of_lt_of_le hN hNn
  have he := inv_n_le_loss μ n N hN hNn hρ
  have he1 := loss_le_one N hN (beta μ n)
  obtain ⟨h0, hθ, hr⟩ := raw_bounds μ h (t / Real.sqrt n)
  unfold lossEnvelope
  refine le_min (by simpa using pow_le_pow_left₀ (norm_nonneg _) (norm_charFun_le_one _) (n - 1))
    (le_min ?_ (le_min ?_ ?_))
  · exact pred_power_le_loss_exp _ _ _ _ (norm_nonneg _) (norm_charFun_le_one _) h0 n hn he he1
      (scaled_rawExponent_le μ n hn hρ _ _ (by norm_num) t)
  · exact pred_power_le_loss_exp _ _ _ _ (norm_nonneg _) (norm_charFun_le_one _) hθ n hn he he1
      (scaled_rawExponent_le μ n hn hρ _ _ ClassicalCosineCubic.b_nonneg t)
  · exact pred_power_le_loss_exp _ _ _ _ (norm_nonneg _) (norm_charFun_le_one _) hr n hn he he1
      (scaled_rawExponent_le μ n hn hρ _ _ ClassicalRationalCosine.b_nonneg t)

end BerryEsseen.HighMomentRayDamping

#print axioms BerryEsseen.HighMomentRayDamping.inv_n_le_loss
#print axioms BerryEsseen.HighMomentRayDamping.normalized_power_le_envelope
#print axioms BerryEsseen.HighMomentRayDamping.normalized_iid_norm_le_envelope
#print axioms BerryEsseen.HighMomentRayDamping.normalized_pred_power_le_lossEnvelope
