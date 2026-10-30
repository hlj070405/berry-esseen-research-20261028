module

public import BerryEsseen.SecondOrderDamping
public import BerryEsseen.FiniteRhoSinePrice

@[expose] public section

/-! 2026-10-30: fixed upper-moment spectra for every positive iid sample
size. The original-law square polynomials and compensated Taylor disk
are rescaled by an arbitrary fixed sigma>0. The signed third moment is
bounded by its genuine upper-moment root, with no equality or attainability
assumption. Both powers retain their exact exponents, including n=1. -/

noncomputable section

open MeasureTheory ProbabilityTheory

namespace BerryEsseen.UpperMomentDamping

abbrev g4 (c v : ℝ) : ℝ := CoefficientHybridSecond.spectralExponent2 c v

def gammaCap (U : ℝ) : ℝ :=
  Real.sqrt ((U ^ 2 - 4 + U * Real.sqrt (U ^ 2 + 8)) / 2)

def reference (σ Γ v : ℝ) : ℂ :=
  ((σ ^ 2 - v ^ 2 / 2 : ℝ) : ℂ) - Complex.I * (((Γ / σ) * v ^ 3 / 16 : ℝ) : ℂ)

def H (U σ Γ v : ℝ) : ℝ :=
  5 * (U / σ) * |v| ^ 3 / 48 + ‖reference σ Γ v‖ - σ ^ 2

def h (U σ Γ v : ℝ) : ℝ := min 0 (H U σ Γ v)

def spectrum (U σ Γ v : ℝ) : ℝ :=
  min (g4 ((U + 1) / σ) v - (g4 ((U + 1) / σ) v) ^ 2 / σ ^ 2)
    (h U σ Γ v - (h U σ Γ v) ^ 2 / (2 * σ ^ 2))

def G (U σ v : ℝ) : ℝ := spectrum U σ (gammaCap U) v

def betaScale (σ : ℝ) (n : ℕ) : ℝ := σ / Real.sqrt n

def sScale (σ : ℝ) (n : ℕ) : ℝ := (n : ℝ) / σ ^ 2

lemma continuous_H (U σ Γ : ℝ) : Continuous (H U σ Γ) := by
  unfold H reference
  fun_prop

lemma continuous_h (U σ Γ : ℝ) : Continuous (h U σ Γ) :=
  continuous_const.min (continuous_H U σ Γ)

lemma continuous_spectrum (U σ Γ : ℝ) : Continuous (spectrum U σ Γ) := by
  have hc := CoefficientHybridSecond.continuous_spectralExponent2 ((U + 1) / σ)
  have hh := continuous_h U σ Γ
  exact (hc.sub ((hc.pow 2).div_const _)).min (hh.sub ((hh.pow 2).div_const _))

lemma continuous_G (U σ : ℝ) : Continuous (G U σ) := continuous_spectrum U σ (gammaCap U)

lemma h_nonpos (U σ Γ v : ℝ) : h U σ Γ v ≤ 0 := min_le_left _ _

lemma spectrum_nonpos (U σ Γ v : ℝ) : spectrum U σ Γ v ≤ 0 := by
  have hc := CoefficientHybridSecond.spectralExponent2_nonpos ((U + 1) / σ) v
  have hp : 0 ≤ (g4 ((U + 1) / σ) v) ^ 2 / σ ^ 2 := by positivity
  exact (min_le_left _ _).trans (by linarith only [hc, hp])

lemma G_nonpos (U σ v : ℝ) : G U σ v ≤ 0 := spectrum_nonpos U σ (gammaCap U) v

@[simp] lemma H_zero (U σ Γ : ℝ) : H U σ Γ 0 = 0 := by
  simp [H, reference, Complex.norm_real, Real.norm_eq_abs]

@[simp] lemma h_zero (U σ Γ : ℝ) : h U σ Γ 0 = 0 := by simp [h]

@[simp] lemma spectrum_zero (U σ Γ : ℝ) : spectrum U σ Γ 0 = 0 := by
  simp [spectrum, CoefficientHybridSecond.spectralExponent2,
    CoefficientRaySpectral.spectralExponent, CoefficientRayPrice.exponent]

@[simp] lemma G_zero (U σ : ℝ) : G U σ 0 = 0 := spectrum_zero U σ (gammaCap U)

private lemma scaled_square_bound (μ : ProbabilityMeasure ℝ) (U σ a b u : ℝ)
    (hσ : 0 < σ) (hρ : thirdAbsoluteMoment μ ≤ U) (hb : 0 ≤ b)
    (hsq : ‖charFun (μ : Measure ℝ) u‖ ^ 2 ≤
      1 - 2 * a * u ^ 2 + 2 * b * (thirdAbsoluteMoment μ + 1) * |u| ^ 3) :
    σ ^ 2 * (‖charFun (μ : Measure ℝ) u‖ ^ 2 - 1) ≤
      2 * CoefficientRayPrice.exponent ((U + 1) / σ) a b 1 (σ * u) := by
  have hs := mul_le_mul_of_nonneg_left hsq (sq_nonneg σ)
  have hc := mul_le_mul_of_nonneg_left (add_le_add_right hρ 1)
    (show 0 ≤ 2 * b * σ ^ 2 * |u| ^ 3 by positivity)
  have he : CoefficientRayPrice.exponent ((U + 1) / σ) a b 1 (σ * u) =
      -a * σ ^ 2 * u ^ 2 + b * (U + 1) * σ ^ 2 * |u| ^ 3 := by
    unfold CoefficientRayPrice.exponent
    simp only [mul_one, abs_mul, abs_of_pos hσ, mul_pow]
    field_simp [hσ.ne']
  rw [he]
  nlinarith only [hs, hc]

/-- Four raw square inequalities and the same law's unit bound at every
real frequency, rescaled by the fixed sigma rather than by its moment. -/
theorem squared_raw_bound (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (U σ : ℝ) (hσ : 0 < σ) (hρ : thirdAbsoluteMoment μ ≤ U) (u : ℝ) :
    σ ^ 2 * (‖charFun (μ : Measure ℝ) u‖ ^ 2 - 1) ≤
      2 * g4 ((U + 1) / σ) (σ * u) := by
  have h0raw : ‖charFun (μ : Measure ℝ) u‖ ^ 2 ≤
      1 - 2 * (1 / 2 : ℝ) * u ^ 2 + 2 * (1 / 10 : ℝ) *
        (thirdAbsoluteMoment μ + 1) * |u| ^ 3 := by
    have hh := ClassicalDamping.charFun_norm_sq_le μ hμ u
    nlinarith only [hh]
  have h0 := scaled_square_bound μ U σ (1 / 2) (1 / 10) u hσ hρ (by norm_num) h0raw
  have hθ := scaled_square_bound μ U σ ClassicalCosineCubic.a ClassicalCosineCubic.b u hσ hρ
    ClassicalCosineCubic.b_nonneg (by
      simpa only [ClassicalCosineCubic.polynomial] using ClassicalCosineCubic.charFun_norm_sq_le μ hμ u)
  have hr := scaled_square_bound μ U σ ClassicalRationalCosine.a ClassicalRationalCosine.b u hσ hρ
    ClassicalRationalCosine.b_nonneg (by
      simpa only [ClassicalRationalCosine.polynomial] using ClassicalRationalCosine.charFun_norm_sq_le μ hμ u)
  have h3 := scaled_square_bound μ U σ ClassicalThreeHalvesCosine.a ClassicalThreeHalvesCosine.b u hσ hρ
    ClassicalThreeHalvesCosine.b_nonneg (by
      simpa only [ClassicalThreeHalvesCosine.polynomial] using ClassicalThreeHalvesCosine.charFun_norm_sq_le μ hμ u)
  have hunit : σ ^ 2 * (‖charFun (μ : Measure ℝ) u‖ ^ 2 - 1) ≤ 0 := by
    have hx : ‖charFun (μ : Measure ℝ) u‖ ^ 2 ≤ 1 := by
      simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg _) (norm_charFun_le_one _) 2
    exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (sub_nonpos.mpr hx)
  unfold g4 CoefficientHybridSecond.spectralExponent2 CoefficientRaySpectral.spectralExponent
  simp only [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2), mul_zero]
  exact le_min (le_min hunit (le_min h0 (le_min hθ hr))) h3

lemma reference_norm_sq (σ Γ v : ℝ) :
    ‖reference σ Γ v‖ ^ 2 = (σ ^ 2 - v ^ 2 / 2) ^ 2 + (Γ / σ) ^ 2 * v ^ 6 / 256 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [reference, Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, mul_zero,
    one_mul, sub_zero, zero_sub, zero_add]
  ring

private lemma center_norm_sq (μ : ProbabilityMeasure ℝ) (u : ℝ) :
    ‖IidTaylorPrice.center μ u‖ ^ 2 =
      (1 - u ^ 2 / 2) ^ 2 + ZeroBias.gamma μ ^ 2 * u ^ 6 / 256 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [IidTaylorPrice.center, Complex.sub_re, Complex.sub_im, Complex.one_re,
    Complex.one_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, zero_mul, mul_zero, one_mul, sub_zero, zero_sub, zero_add]
  ring

lemma scaled_center_norm_le (μ : ProbabilityMeasure ℝ) (σ Γ u : ℝ)
    (hσ : 0 < σ) (hγ : |ZeroBias.gamma μ| ≤ Γ) :
    σ ^ 2 * ‖IidTaylorPrice.center μ u‖ ≤ ‖reference σ Γ (σ * u)‖ := by
  have hγ2 := pow_le_pow_left₀ (abs_nonneg (ZeroBias.gamma μ)) hγ 2
  rw [sq_abs] at hγ2
  have hm := mul_le_mul_of_nonneg_right hγ2 (show 0 ≤ σ ^ 4 * u ^ 6 / 256 by positivity)
  have he : ‖reference σ Γ (σ * u)‖ ^ 2 =
      σ ^ 4 * ((1 - u ^ 2 / 2) ^ 2 + Γ ^ 2 * u ^ 6 / 256) := by
    rw [reference_norm_sq]
    field_simp [hσ.ne']
  apply (sq_le_sq₀ (mul_nonneg (sq_nonneg _) (norm_nonneg _)) (norm_nonneg _)).mp
  rw [mul_pow, center_norm_sq, he]
  nlinarith only [hm]

/-- The actual Taylor disk, with the signed gamma bounded in absolute
value. Neither the reference vector nor its cap is an assumed law. -/
theorem linear_raw_bound_cap (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (U σ Γ : ℝ) (hσ : 0 < σ) (hρ : thirdAbsoluteMoment μ ≤ U)
    (hγ : |ZeroBias.gamma μ| ≤ Γ) (u : ℝ) :
    σ ^ 2 * (‖charFun (μ : Measure ℝ) u‖ - 1) ≤ h U σ Γ (σ * u) := by
  have hq := mul_le_mul_of_nonneg_left (IidTaylorPrice.charFun_norm_le μ hμ u) (sq_nonneg σ)
  unfold IidTaylorPrice.modulus IidTaylorPrice.radius at hq
  have hc := scaled_center_norm_le μ σ Γ u hσ hγ
  have hρs := mul_le_mul_of_nonneg_right hρ (show 0 ≤ 5 * σ ^ 2 * |u| ^ 3 / 48 by positivity)
  have hH : σ ^ 2 * (‖charFun (μ : Measure ℝ) u‖ - 1) ≤ H U σ Γ (σ * u) := by
    unfold H
    rw [abs_mul, abs_of_pos hσ, mul_pow]
    field_simp [hσ.ne']
    nlinarith only [hq, hc, hρs]
  have hu : σ ^ 2 * (‖charFun (μ : Measure ℝ) u‖ - 1) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (sub_nonpos.mpr (norm_charFun_le_one _))
  exact le_min hu hH

theorem linear_raw_bound (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (U σ : ℝ) (hσ : 0 < σ) (hρ : thirdAbsoluteMoment μ ≤ U) (u : ℝ) :
    σ ^ 2 * (‖charFun (μ : Measure ℝ) u‖ - 1) ≤ h U σ (gammaCap U) (σ * u) := by
  have hU : 0 ≤ U := ((by norm_num : (0 : ℝ) ≤ 1).trans
    (ThirdMomentRegion.one_le_third μ hμ)).trans hρ
  exact linear_raw_bound_cap μ hμ U σ (gammaCap U) hσ hρ
    (FiniteRhoSinePrice.abs_gamma_le_root_at_R μ hμ U hU hρ) u

private lemma square_factor_le_exp (x g σ : ℝ) (hx : 0 ≤ x) (hσ : 0 < σ) (hg : g ≤ 0)
    (hraw : σ ^ 2 * (x ^ 2 - 1) ≤ 2 * g) :
    x ≤ Real.exp ((g - g ^ 2 / σ ^ 2) / σ ^ 2) := by
  have hd : x ^ 2 - 1 ≤ (2 * g) / σ ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hσ)).mpr
    simpa only [mul_comm] using hraw
  have hb : x ^ 2 ≤ 1 + 2 * g / σ ^ 2 := by linarith only [hd]
  have hy : 2 * g / σ ^ 2 ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _)
  have he := hb.trans (SecondOrderDamping.one_add_le_secondOrder_exp _ hy)
  apply (sq_le_sq₀ hx (Real.exp_nonneg _)).mp
  rw [← Real.exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  convert he using 1
  congr 1
  field_simp [hσ.ne']

private lemma linear_factor_le_exp (x z σ : ℝ) (hσ : 0 < σ) (hz : z ≤ 0)
    (hraw : σ ^ 2 * (x - 1) ≤ z) :
    x ≤ Real.exp ((z - z ^ 2 / (2 * σ ^ 2)) / σ ^ 2) := by
  have hd : x - 1 ≤ z / σ ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hσ)).mpr
    simpa only [mul_comm] using hraw
  have hb : x ≤ 1 + z / σ ^ 2 := by linarith only [hd]
  have hy : z / σ ^ 2 ≤ 0 := div_nonpos_of_nonpos_of_nonneg hz (sq_nonneg _)
  have he := hb.trans (SecondOrderDamping.one_add_le_secondOrder_exp _ hy)
  convert he using 1
  congr 1
  field_simp [hσ.ne']

theorem charFun_norm_le_exp_cap (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (U σ Γ : ℝ) (hσ : 0 < σ) (hρ : thirdAbsoluteMoment μ ≤ U)
    (hγ : |ZeroBias.gamma μ| ≤ Γ) (u : ℝ) :
    ‖charFun (μ : Measure ℝ) u‖ ≤ Real.exp (spectrum U σ Γ (σ * u) / σ ^ 2) := by
  have hc := square_factor_le_exp _ (g4 ((U + 1) / σ) (σ * u)) σ (norm_nonneg _) hσ
    (CoefficientHybridSecond.spectralExponent2_nonpos _ _) (squared_raw_bound μ hμ U σ hσ hρ u)
  have hh := linear_factor_le_exp _ (h U σ Γ (σ * u)) σ hσ (h_nonpos _ _ _ _)
    (linear_raw_bound_cap μ hμ U σ Γ hσ hρ hγ u)
  unfold spectrum
  rcases le_total (g4 ((U + 1) / σ) (σ * u) - (g4 ((U + 1) / σ) (σ * u)) ^ 2 / σ ^ 2)
    (h U σ Γ (σ * u) - (h U σ Γ (σ * u)) ^ 2 / (2 * σ ^ 2)) with he | he
  · rw [min_eq_left he]
    exact hc
  · rw [min_eq_right he]
    exact hh

/-- No independent CF input remains: only the original standardized law,
its genuine third-absolute-moment upper bound, and fixed sigma>0. -/
theorem charFun_norm_le_exp (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (U σ : ℝ) (hσ : 0 < σ) (hρ : thirdAbsoluteMoment μ ≤ U) (u : ℝ) :
    ‖charFun (μ : Measure ℝ) u‖ ≤ Real.exp (G U σ (σ * u) / σ ^ 2) := by
  have hU : 0 ≤ U := ((by norm_num : (0 : ℝ) ≤ 1).trans
    (ThirdMomentRegion.one_le_third μ hμ)).trans hρ
  exact charFun_norm_le_exp_cap μ hμ U σ (gammaCap U) hσ hρ
    (FiniteRhoSinePrice.abs_gamma_le_root_at_R μ hμ U hU hρ) u

lemma sScale_eq_inv_betaScale_sq (σ : ℝ) (n : ℕ) (hσ : 0 < σ) (hn : 0 < n) :
    sScale σ n = 1 / (betaScale σ n) ^ 2 := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  unfold sScale betaScale
  rw [div_pow, Real.sq_sqrt hnR.le]
  field_simp [hσ.ne', hnR.ne']

/-- A fixed spectrum for all n, with no finite upper sample-size cutoff. -/
theorem normalized_power_le_exp (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (U σ : ℝ) (hσ : 0 < σ) (hρ : thirdAbsoluteMoment μ ≤ U)
    (n : ℕ) (_hn : 0 < n) (t : ℝ) :
    ‖charFun (μ : Measure ℝ) (t / Real.sqrt n)‖ ^ n ≤
      Real.exp (sScale σ n * G U σ (betaScale σ n * t)) := by
  have hp := pow_le_pow_left₀ (norm_nonneg _)
    (charFun_norm_le_exp μ hμ U σ hσ hρ (t / Real.sqrt n)) n
  rw [← Real.exp_nat_mul] at hp
  have hv : σ * (t / Real.sqrt n) = betaScale σ n * t := by unfold betaScale; ring
  rw [hv] at hp
  exact hp.trans_eq (congrArg Real.exp (by unfold sScale; ring))

/-- The predecessor exponent is exact. At n=1 both sides are one. -/
theorem normalized_pred_power_le_exp (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (U σ : ℝ) (hσ : 0 < σ) (hρ : thirdAbsoluteMoment μ ≤ U)
    (n : ℕ) (hn : 0 < n) (t : ℝ) :
    ‖charFun (μ : Measure ℝ) (t / Real.sqrt n)‖ ^ (n - 1) ≤
      Real.exp ((sScale σ n - 1 / σ ^ 2) * G U σ (betaScale σ n * t)) := by
  have hp := pow_le_pow_left₀ (norm_nonneg _)
    (charFun_norm_le_exp μ hμ U σ hσ hρ (t / Real.sqrt n)) (n - 1)
  rw [← Real.exp_nat_mul] at hp
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (Nat.succ_le_of_lt hn)]
    norm_num
  rw [hcast] at hp
  have hv : σ * (t / Real.sqrt n) = betaScale σ n * t := by unfold betaScale; ring
  rw [hv] at hp
  exact hp.trans_eq (congrArg Real.exp (by unfold sScale; ring))

end BerryEsseen.UpperMomentDamping

#print axioms BerryEsseen.UpperMomentDamping.squared_raw_bound
#print axioms BerryEsseen.UpperMomentDamping.continuous_G
#print axioms BerryEsseen.UpperMomentDamping.G_nonpos
#print axioms BerryEsseen.UpperMomentDamping.linear_raw_bound_cap
#print axioms BerryEsseen.UpperMomentDamping.linear_raw_bound
#print axioms BerryEsseen.UpperMomentDamping.charFun_norm_le_exp
#print axioms BerryEsseen.UpperMomentDamping.sScale_eq_inv_betaScale_sq
#print axioms BerryEsseen.UpperMomentDamping.normalized_power_le_exp
#print axioms BerryEsseen.UpperMomentDamping.normalized_pred_power_le_exp
