module

public import BerryEsseen.CompensatedTaylorDamping
public import BerryEsseen.GenericRayPrice

@[expose] public section

/-! 2026-10-30: a fixed-radius reference vector for the actual compensated
Taylor circle.  The vector is an algebraic comparison object, not the CF
of an assumed law with gamma=rho.  Signed frequencies are retained.
The reference rate is nonincreasing in its nonnegative radius parameter.
The full-power bound needs only rho>=R>0; the optional predecessor bound
explicitly retains rho>=rho0 to license the original loss.  No new price,
profile, logarithmic optimization or numerical bound is introduced. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace BerryEsseen.ReferenceCircleDamping

open HighMomentRayDamping (rho0 rho0_pos beta beta_sq_mul_n loss inv_n_le_loss loss_le_one)

def reference (R v : ℝ) : ℂ :=
  ((R ^ 2 - v ^ 2 / 2 : ℝ) : ℂ) - Complex.I * ((v ^ 3 / 16 : ℝ) : ℂ)

def H (R v : ℝ) : ℝ := 5 * |v| ^ 3 / 48 + ‖reference R v‖ - R ^ 2

def G (R v : ℝ) : ℝ := min 0 (H R v)

def exponent (R β t : ℝ) : ℝ := (1 / β ^ 2) * G R (β * t)

lemma continuous_H (R : ℝ) : Continuous (H R) := by unfold H reference; fun_prop

lemma continuous_G (R : ℝ) : Continuous (G R) := by
  unfold G
  exact continuous_const.min (continuous_H R)

lemma G_nonpos (R v : ℝ) : G R v ≤ 0 := min_le_left _ _

@[simp] lemma H_zero (R : ℝ) : H R 0 = 0 := by
  simp [H, reference, Complex.norm_real, Real.norm_eq_abs]

@[simp] lemma G_zero (R : ℝ) : G R 0 = 0 := by simp [G]

lemma exponent_nonpos (R β t : ℝ) : exponent R β t ≤ 0 :=
  mul_nonpos_of_nonneg_of_nonpos (by positivity) (G_nonpos R (β * t))

/-- A real nonnegative translation of the reference vector proves the
pure-parameter comparison, independently of any probability law. -/
theorem H_le_of_le (R S v : ℝ) (hR : 0 ≤ R) (hRS : R ≤ S) : H S v ≤ H R v := by
  have hd : 0 ≤ S ^ 2 - R ^ 2 := sub_nonneg.mpr (pow_le_pow_left₀ hR hRS 2)
  have hz : reference S v = reference R v + ((S ^ 2 - R ^ 2 : ℝ) : ℂ) := by
    unfold reference
    push_cast
    ring
  have hn := norm_add_le (reference R v) ((S ^ 2 - R ^ 2 : ℝ) : ℂ)
  rw [← hz, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hd] at hn
  unfold H
  linarith only [hn]

theorem G_le_of_le (R S v : ℝ) (hR : 0 ≤ R) (hRS : R ≤ S) : G S v ≤ G R v :=
  min_le_min le_rfl (H_le_of_le R S v hR hRS)

lemma reference_norm_sq (R v : ℝ) :
    ‖reference R v‖ ^ 2 = (R ^ 2 - v ^ 2 / 2) ^ 2 + v ^ 6 / 256 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [reference, Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, mul_zero,
    one_mul, sub_zero, zero_sub, zero_add]
  ring

private lemma center_norm_sq (μ : ProbabilityMeasure ℝ) (u : ℝ) :
    ‖IidTaylorPrice.center μ u‖ ^ 2 =
      1 - u ^ 2 + u ^ 4 / 4 + ZeroBias.gamma μ ^ 2 * u ^ 6 / 256 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [IidTaylorPrice.center, Complex.sub_re, Complex.sub_im, Complex.one_re,
    Complex.one_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, zero_mul, mul_zero, one_mul, sub_zero, zero_sub, zero_add]
  ring

private lemma scaled_center_norm_le (μ : ProbabilityMeasure ℝ) (u : ℝ) :
    thirdAbsoluteMoment μ ^ 2 * ‖IidTaylorPrice.center μ u‖ ≤
      ‖reference (thirdAbsoluteMoment μ) (thirdAbsoluteMoment μ * u)‖ := by
  apply (sq_le_sq₀ (mul_nonneg (sq_nonneg _) (norm_nonneg _)) (norm_nonneg _)).mp
  rw [mul_pow, center_norm_sq, reference_norm_sq]
  have hγ := pow_le_pow_left₀ (abs_nonneg (ZeroBias.gamma μ))
    (ThirdMomentRegion.abs_gamma_le_third μ) 2
  rw [sq_abs] at hγ
  have hm := mul_le_mul_of_nonneg_right hγ
    (show 0 ≤ thirdAbsoluteMoment μ ^ 4 * u ^ 6 / 256 by positivity)
  nlinarith only [hm]

/-- The true original-law circle is compared only by |gamma|<=rho. -/
theorem rho_sq_mul_norm_sub_one_le_H (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (u : ℝ) :
    thirdAbsoluteMoment μ ^ 2 * (‖charFun (μ : Measure ℝ) u‖ - 1) ≤
      H (thirdAbsoluteMoment μ) (thirdAbsoluteMoment μ * u) := by
  have hρ0 : 0 ≤ thirdAbsoluteMoment μ :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (ThirdMomentRegion.one_le_third μ h)
  have hq := mul_le_mul_of_nonneg_left (IidTaylorPrice.charFun_norm_le μ h u)
    (sq_nonneg (thirdAbsoluteMoment μ))
  unfold IidTaylorPrice.modulus IidTaylorPrice.radius at hq
  have hc := scaled_center_norm_le μ u
  unfold H
  rw [abs_mul, abs_of_nonneg hρ0, mul_pow]
  nlinarith only [hq, hc]

theorem charFun_norm_le_affine (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (R : ℝ) (hR : 0 < R) (hρ : R ≤ thirdAbsoluteMoment μ) (u : ℝ) :
    ‖charFun (μ : Measure ℝ) u‖ ≤
      1 + H R (thirdAbsoluteMoment μ * u) / thirdAbsoluteMoment μ ^ 2 := by
  have hρp : 0 < thirdAbsoluteMoment μ := hR.trans_le hρ
  have hh := (rho_sq_mul_norm_sub_one_le_H μ h u).trans
    (H_le_of_le R (thirdAbsoluteMoment μ) (thirdAbsoluteMoment μ * u) hR.le hρ)
  have hd : ‖charFun (μ : Measure ℝ) u‖ - 1 ≤
      H R (thirdAbsoluteMoment μ * u) / thirdAbsoluteMoment μ ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hρp)).mpr
    simpa only [mul_comm] using hh
  linarith only [hd]

theorem charFun_norm_le_exp (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (R : ℝ) (hR : 0 < R) (hρ : R ≤ thirdAbsoluteMoment μ) (u : ℝ) :
    ‖charFun (μ : Measure ℝ) u‖ ≤
      Real.exp (G R (thirdAbsoluteMoment μ * u) / thirdAbsoluteMoment μ ^ 2) := by
  have he : ‖charFun (μ : Measure ℝ) u‖ ≤
      Real.exp (H R (thirdAbsoluteMoment μ * u) / thirdAbsoluteMoment μ ^ 2) := by
    calc
      _ ≤ 1 + H R (thirdAbsoluteMoment μ * u) / thirdAbsoluteMoment μ ^ 2 :=
        charFun_norm_le_affine μ h R hR hρ u
      _ = H R (thirdAbsoluteMoment μ * u) / thirdAbsoluteMoment μ ^ 2 + 1 := by ring
      _ ≤ _ := Real.add_one_le_exp _
  by_cases hh : H R (thirdAbsoluteMoment μ * u) ≤ 0
  · simpa only [G, min_eq_right hh] using he
  · have hz : G R (thirdAbsoluteMoment μ * u) = 0 := min_eq_left (le_of_not_ge hh)
    simpa only [hz, zero_div, Real.exp_zero] using norm_charFun_le_one (μ := (μ : Measure ℝ)) u

/-- Full real frequencies and every positive n, including n=1. -/
theorem normalized_power_le_exp (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (hn : 0 < n) (R : ℝ) (hR : 0 < R) (hρ : R ≤ thirdAbsoluteMoment μ) (t : ℝ) :
    ‖charFun (μ : Measure ℝ) (t / Real.sqrt n)‖ ^ n ≤ Real.exp (exponent R (beta μ n) t) := by
  have hρp : 0 < thirdAbsoluteMoment μ := hR.trans_le hρ
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hβ : 0 < beta μ n := div_pos hρp (Real.sqrt_pos.mpr hnR)
  have hp := pow_le_pow_left₀ (norm_nonneg _)
    (charFun_norm_le_exp μ h R hR hρ (t / Real.sqrt n)) n
  rw [← Real.exp_nat_mul] at hp
  have hv : thirdAbsoluteMoment μ * (t / Real.sqrt n) = beta μ n * t := by unfold beta; ring
  have he : (n : ℝ) * (G R (thirdAbsoluteMoment μ * (t / Real.sqrt n)) / thirdAbsoluteMoment μ ^ 2) =
      exponent R (beta μ n) t := by
    rw [hv]
    unfold exponent
    rw [← beta_sq_mul_n μ n hn]
    field_simp [hβ.ne', hnR.ne']
  exact hp.trans_eq (congrArg Real.exp he)

/-- The reference-radius input does not by itself license the old loss.
Its original rho>=rho0 hypothesis is explicitly retained here. -/
theorem normalized_pred_power_le_loss_exp (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n N : ℕ) (hN : 0 < N) (hNn : N ≤ n) (R : ℝ) (hR : 0 < R)
    (hρR : R ≤ thirdAbsoluteMoment μ) (hρ0 : rho0 ≤ thirdAbsoluteMoment μ) (t : ℝ) :
    ‖charFun (μ : Measure ℝ) (t / Real.sqrt n)‖ ^ (n - 1) ≤
      Real.exp ((1 - loss N (beta μ n)) * exponent R (beta μ n) t) := by
  have hn : 0 < n := lt_of_lt_of_le hN hNn
  exact GenericRayPrice.pred_power_from_normalized_bound _ _ _ n (norm_nonneg _)
    (norm_charFun_le_one _) hn (inv_n_le_loss μ n N hN hNn hρ0)
    (loss_le_one N hN (beta μ n)) (normalized_power_le_exp μ h n hn R hR hρR t)

def youngRate (R v : ℝ) : ℝ :=
  -v ^ 2 / 2 + 5 * |v| ^ 3 / 48 + (v ^ 4 / 8 + v ^ 6 / 512) / R ^ 2

/-- Exact amount lost by the previous Young bound for the reference norm. -/
theorem young_identity (R v : ℝ) (hR : 0 < R) :
    youngRate R v = H R v + (‖reference R v‖ - R ^ 2) ^ 2 / (2 * R ^ 2) := by
  have hn := reference_norm_sq R v
  unfold youngRate H
  field_simp [hR.ne']
  nlinarith only [hn]

theorem H_le_youngRate (R v : ℝ) (hR : 0 < R) : H R v ≤ youngRate R v := by
  have hh := young_identity R v hR
  have hp : 0 ≤ (‖reference R v‖ - R ^ 2) ^ 2 / (2 * R ^ 2) := by positivity
  linarith only [hh, hp]

theorem H_rho0_le_ET (v : ℝ) : H rho0 v ≤ CompensatedTaylorDamping.spectralExponent v := by
  simpa only [youngRate, CompensatedTaylorDamping.spectralExponent] using H_le_youngRate rho0 v rho0_pos

theorem G_le_ET (R v : ℝ) (hR : rho0 ≤ R) : G R v ≤ CompensatedTaylorDamping.spectralExponent v :=
  (min_le_right 0 (H R v)).trans
    ((H_le_of_le rho0 R v rho0_pos.le hR).trans (H_rho0_le_ET v))

theorem G_le_clipped_ET (R v : ℝ) (hR : rho0 ≤ R) :
    G R v ≤ min 0 (CompensatedTaylorDamping.spectralExponent v) :=
  le_min (G_nonpos R v) (G_le_ET R v hR)

end BerryEsseen.ReferenceCircleDamping

#print axioms BerryEsseen.ReferenceCircleDamping.H_le_of_le
#print axioms BerryEsseen.ReferenceCircleDamping.rho_sq_mul_norm_sub_one_le_H
#print axioms BerryEsseen.ReferenceCircleDamping.normalized_power_le_exp
#print axioms BerryEsseen.ReferenceCircleDamping.normalized_pred_power_le_loss_exp
#print axioms BerryEsseen.ReferenceCircleDamping.young_identity
#print axioms BerryEsseen.ReferenceCircleDamping.G_le_clipped_ET
