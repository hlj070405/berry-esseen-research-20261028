module

public import BerryEsseen.IidTaylorPrice
public import BerryEsseen.HighMomentRayDamping
public import BerryEsseen.ThirdMomentRegion

@[expose] public section

/-! 2026-10-29: a global exponential branch from the actual compensated
Taylor disk.  The fourth and sixth powers below are deterministic powers
of frequency, and introduce no fourth/sixth moment assumption.
The uniform bound 1/n <= beta^2/rho0^2 makes the spectral rate independent
of n and s.  This exponent may be positive at large frequencies; the
residual-power proof therefore retains the original sign split.
No envelope profile, grid or numerical price is introduced here. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace BerryEsseen.CompensatedTaylorDamping

open HighMomentRayDamping (rho0 rho0_pos beta beta_sq_mul_n loss inv_n_le_loss loss_le_one)

def correction (β t : ℝ) : ℝ := t ^ 4 / 8 + β ^ 2 * t ^ 6 / 512

def exponent (β t : ℝ) : ℝ :=
  -t ^ 2 / 2 + 5 * β * |t| ^ 3 / 48 + (β ^ 2 / rho0 ^ 2) * correction β t

def spectralExponent (v : ℝ) : ℝ :=
  -v ^ 2 / 2 + 5 * |v| ^ 3 / 48 + (v ^ 4 / 8 + v ^ 6 / 512) / rho0 ^ 2

lemma correction_nonneg (β t : ℝ) : 0 ≤ correction β t := by unfold correction; positivity

lemma continuous_exponent (β : ℝ) : Continuous (exponent β) := by unfold exponent correction; fun_prop

lemma continuous_spectralExponent : Continuous spectralExponent := by unfold spectralExponent; fun_prop

@[simp] lemma exponent_zero (β : ℝ) : exponent β 0 = 0 := by simp [exponent, correction]

@[simp] lemma spectralExponent_zero : spectralExponent 0 = 0 := by simp [spectralExponent]

private def rawExponent (ρ u : ℝ) : ℝ :=
  -u ^ 2 / 2 + 5 * ρ * |u| ^ 3 / 48 + u ^ 4 / 8 + ρ ^ 2 * u ^ 6 / 512

private lemma center_norm_sq (μ : ProbabilityMeasure ℝ) (u : ℝ) :
    ‖IidTaylorPrice.center μ u‖ ^ 2 =
      1 - u ^ 2 + u ^ 4 / 4 + ZeroBias.gamma μ ^ 2 * u ^ 6 / 256 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [IidTaylorPrice.center, Complex.sub_re, Complex.sub_im, Complex.one_re,
    Complex.one_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, zero_mul, mul_zero, one_mul, sub_zero, zero_sub, zero_add]
  ring

private lemma norm_le_half_sq (z : ℂ) : ‖z‖ ≤ (1 + ‖z‖ ^ 2) / 2 := by
  nlinarith only [sq_nonneg (‖z‖ - 1)]

private lemma charFun_le_raw_exp (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (u : ℝ) :
    ‖charFun (μ : Measure ℝ) u‖ ≤ Real.exp (rawExponent (thirdAbsoluteMoment μ) u) := by
  have hγ := pow_le_pow_left₀ (abs_nonneg (ZeroBias.gamma μ))
    (ThirdMomentRegion.abs_gamma_le_third μ) 2
  rw [sq_abs] at hγ
  have hm := mul_le_mul_of_nonneg_right hγ (show 0 ≤ u ^ 6 / 512 by positivity)
  have hz := norm_le_half_sq (IidTaylorPrice.center μ u)
  rw [center_norm_sq] at hz
  have hc : ‖IidTaylorPrice.center μ u‖ ≤
      1 - u ^ 2 / 2 + u ^ 4 / 8 + thirdAbsoluteMoment μ ^ 2 * u ^ 6 / 512 := by
    nlinarith only [hz, hm]
  have hq := IidTaylorPrice.charFun_norm_le μ h u
  unfold IidTaylorPrice.modulus IidTaylorPrice.radius at hq
  calc
    _ ≤ 1 + rawExponent (thirdAbsoluteMoment μ) u := by
      unfold rawExponent
      nlinarith only [hq, hc]
    _ = rawExponent (thirdAbsoluteMoment μ) u + 1 := by ring
    _ ≤ _ := Real.add_one_le_exp _

private lemma scaled_rawExponent (μ : ProbabilityMeasure ℝ) (n : ℕ) (hn : 0 < n) (t : ℝ) :
    (n : ℝ) * rawExponent (thirdAbsoluteMoment μ) (t / Real.sqrt n) =
      -t ^ 2 / 2 + 5 * beta μ n * |t| ^ 3 / 48 + (1 / (n : ℝ)) * correction (beta μ n) t := by
  let r : ℝ := Real.sqrt n
  have hr : 0 < r := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  have hr2 : r ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
  change (n : ℝ) * rawExponent (thirdAbsoluteMoment μ) (t / r) =
    -t ^ 2 / 2 + 5 * (thirdAbsoluteMoment μ / r) * |t| ^ 3 / 48 +
      (1 / (n : ℝ)) * correction (thirdAbsoluteMoment μ / r) t
  unfold rawExponent correction
  simp only [abs_div, abs_of_pos hr, div_pow]
  rw [← hr2]
  field_simp [hr.ne']
  ring

private lemma scaled_rawExponent_le (μ : ProbabilityMeasure ℝ) (n : ℕ) (hn : 0 < n)
    (hρ : rho0 ≤ thirdAbsoluteMoment μ) (t : ℝ) :
    (n : ℝ) * rawExponent (thirdAbsoluteMoment μ) (t / Real.sqrt n) ≤ exponent (beta μ n) t := by
  have hi := inv_n_le_loss μ n n hn le_rfl hρ
  unfold loss at hi
  have hi' := hi.trans (min_le_left _ _)
  have hm := mul_le_mul_of_nonneg_right hi' (correction_nonneg (beta μ n) t)
  rw [scaled_rawExponent μ n hn t]
  unfold exponent
  nlinarith only [hm]

/-- Actual one-factor CF at its original normalized frequency. -/
theorem normalized_factor_le_exp (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (hn : 0 < n) (hρ : rho0 ≤ thirdAbsoluteMoment μ) (t : ℝ) :
    ‖charFun (μ : Measure ℝ) (t / Real.sqrt n)‖ ≤ Real.exp (exponent (beta μ n) t / (n : ℝ)) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hE : rawExponent (thirdAbsoluteMoment μ) (t / Real.sqrt n) ≤ exponent (beta μ n) t / (n : ℝ) := by
    apply (le_div_iff₀ hnR).mpr
    simpa only [mul_comm] using scaled_rawExponent_le μ n hn hρ t
  exact (charFun_le_raw_exp μ h (t / Real.sqrt n)).trans (Real.exp_le_exp.mpr hE)

/-- The true nth power, including n=1; no free CF modulus is an input. -/
theorem normalized_power_le_exp (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (hn : 0 < n) (hρ : rho0 ≤ thirdAbsoluteMoment μ) (t : ℝ) :
    ‖charFun (μ : Measure ℝ) (t / Real.sqrt n)‖ ^ n ≤ Real.exp (exponent (beta μ n) t) := by
  have hp := pow_le_pow_left₀ (norm_nonneg _)
    (normalized_factor_le_exp μ h n hn hρ t) n
  rw [← Real.exp_nat_mul] at hp
  have he : (n : ℝ) * (exponent (beta μ n) t / (n : ℝ)) = exponent (beta μ n) t := by
    field_simp [(Nat.cast_pos.mpr hn : (0 : ℝ) < n).ne']
  simpa only [he] using hp

/-- Residual power under the original loss. Negative exponents reverse the
loss-factor comparison; positive exponents use the actual CF modulus <=1. -/
theorem normalized_pred_power_le_loss_exp (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n N : ℕ) (hN : 0 < N) (hNn : N ≤ n) (hρ : rho0 ≤ thirdAbsoluteMoment μ) (t : ℝ) :
    ‖charFun (μ : Measure ℝ) (t / Real.sqrt n)‖ ^ (n - 1) ≤
      Real.exp ((1 - loss N (beta μ n)) * exponent (beta μ n) t) := by
  have hn : 0 < n := lt_of_lt_of_le hN hNn
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have he := inv_n_le_loss μ n N hN hNn hρ
  have he1 := loss_le_one N hN (beta μ n)
  have hk : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  by_cases hE : exponent (beta μ n) t ≤ 0
  · have hr : 1 - loss N (beta μ n) ≤ ((n - 1 : ℕ) : ℝ) / (n : ℝ) := by
      rw [hk]
      apply (le_div_iff₀ hnR).mpr
      have hh := (div_le_iff₀ hnR).mp he
      nlinarith only [hh]
    have hp := pow_le_pow_left₀ (norm_nonneg _)
      (normalized_factor_le_exp μ h n hn hρ t) (n - 1)
    rw [← Real.exp_nat_mul] at hp
    have harg : ((n - 1 : ℕ) : ℝ) * (exponent (beta μ n) t / (n : ℝ)) ≤
        (1 - loss N (beta μ n)) * exponent (beta μ n) t := by
      have hm := mul_le_mul_of_nonpos_right hr hE
      convert hm using 1
      ring
    exact hp.trans (Real.exp_le_exp.mpr harg)
  · have hp : ‖charFun (μ : Measure ℝ) (t / Real.sqrt n)‖ ^ (n - 1) ≤ 1 := by
      simpa using pow_le_pow_left₀ (norm_nonneg _) (norm_charFun_le_one _) (n - 1)
    apply hp.trans (Real.one_le_exp _)
    exact mul_nonneg (sub_nonneg.mpr he1) (le_of_not_ge hE)

theorem exponent_spectral_eq (β v : ℝ) (hβ : 0 < β) :
    exponent β (v / β) = (1 / β ^ 2) * spectralExponent v := by
  unfold exponent correction spectralExponent
  simp only [abs_div, abs_of_pos hβ, div_pow]
  field_simp [hβ.ne', rho0_pos.ne']

end BerryEsseen.CompensatedTaylorDamping

#print axioms BerryEsseen.CompensatedTaylorDamping.normalized_factor_le_exp
#print axioms BerryEsseen.CompensatedTaylorDamping.normalized_power_le_exp
#print axioms BerryEsseen.CompensatedTaylorDamping.normalized_pred_power_le_loss_exp
#print axioms BerryEsseen.CompensatedTaylorDamping.exponent_spectral_eq
