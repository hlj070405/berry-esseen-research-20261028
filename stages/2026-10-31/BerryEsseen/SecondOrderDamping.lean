module

public import BerryEsseen.CoefficientHybridSecond
public import BerryEsseen.ReferenceCircleDamping
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

@[expose] public section

/-! 2026-10-30: retain the second-order benefit of exponentiating a
nonpositive affine CF bound.  The cosine branch is reconstructed from
four original same-law CF square inequalities, not from their exponential
consequences.  The reference branch likewise uses its raw affine bound.
Eta is a fixed spectrum parameter, licensed by eta*rho^2<=1.  For a finite
node, eta=a/M is licensed by the actual n<=M and s>=a>0.  No profile,
numerical certificate or stronger moment assumption is introduced. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace BerryEsseen.SecondOrderDamping

open HighMomentRayDamping (rho0 beta beta_sq_mul_n loss inv_n_le_loss loss_le_one)

abbrev g4 (c v : ℝ) : ℝ := CoefficientHybridSecond.spectralExponent2 c v

def spectrum (η c R v : ℝ) : ℝ :=
  min (g4 c v - η * (g4 c v) ^ 2)
    (ReferenceCircleDamping.G R v - (η / 2) * (ReferenceCircleDamping.G R v) ^ 2)

def exponent (η c R β t : ℝ) : ℝ := (1 / β ^ 2) * spectrum η c R (β * t)

lemma continuous_spectrum (η c R : ℝ) : Continuous (spectrum η c R) := by
  have hc := CoefficientHybridSecond.continuous_spectralExponent2 c
  have hr := ReferenceCircleDamping.continuous_G R
  unfold spectrum
  exact (hc.sub ((hc.pow 2).const_mul η)).min (hr.sub ((hr.pow 2).const_mul (η / 2)))

lemma spectrum_nonpos (η c R v : ℝ) (hη : 0 ≤ η) : spectrum η c R v ≤ 0 := by
  have hg := CoefficientHybridSecond.spectralExponent2_nonpos c v
  have hp : 0 ≤ η * (g4 c v) ^ 2 := mul_nonneg hη (sq_nonneg _)
  exact (min_le_left _ _).trans (by linarith only [hg, hp])

@[simp] lemma spectrum_zero (η c R : ℝ) : spectrum η c R 0 = 0 := by
  simp [spectrum, CoefficientHybridSecond.spectralExponent2, CoefficientRaySpectral.spectralExponent,
    CoefficientRayPrice.exponent]

private def scalarGap (y : ℝ) : ℝ := Real.exp (y - y ^ 2 / 2) - 1 - y
private def scalarSlope (y : ℝ) : ℝ := (1 - y) * Real.exp (y - y ^ 2 / 2) - 1

private lemma scalarGap_hasDerivAt (y : ℝ) : HasDerivAt scalarGap (scalarSlope y) y := by
  unfold scalarGap scalarSlope
  convert ((((hasDerivAt_id' y).fun_sub (((hasDerivAt_id' y).fun_pow 2).div_const 2)).exp).sub_const 1).fun_sub
    (hasDerivAt_id' y) using 1
  ring

private lemma scalarSlope_nonpos (y : ℝ) : scalarSlope y ≤ 0 := by
  have hl : 1 - y ≤ Real.exp (-y) := by linarith only [Real.add_one_le_exp (-y)]
  have hm := mul_le_mul_of_nonneg_right hl (Real.exp_nonneg (y - y ^ 2 / 2))
  rw [← Real.exp_add, show -y + (y - y ^ 2 / 2) = -(y ^ 2 / 2) by ring] at hm
  have he : Real.exp (-(y ^ 2 / 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith only [sq_nonneg y])
  unfold scalarSlope
  linarith only [hm, he]

/-- No lower bound such as y>-1 is needed for this scalar inequality. -/
theorem one_add_le_secondOrder_exp (y : ℝ) (hy : y ≤ 0) : 1 + y ≤ Real.exp (y - y ^ 2 / 2) := by
  have ha : Antitone scalarGap := antitone_of_hasDerivAt_nonpos scalarGap_hasDerivAt scalarSlope_nonpos
  have hh := ha hy
  have hz : scalarGap 0 = 0 := by simp [scalarGap]
  rw [hz] at hh
  unfold scalarGap at hh
  linarith only [hh]

private lemma scaled_square_bound (μ : ProbabilityMeasure ℝ) (c a b u : ℝ)
    (hρ0 : 0 ≤ thirdAbsoluteMoment μ)
    (hC : thirdAbsoluteMoment μ + 1 ≤ c * thirdAbsoluteMoment μ) (hb : 0 ≤ b)
    (hsq : ‖charFun (μ : Measure ℝ) u‖ ^ 2 ≤
      1 - 2 * a * u ^ 2 + 2 * b * (thirdAbsoluteMoment μ + 1) * |u| ^ 3) :
    thirdAbsoluteMoment μ ^ 2 * (‖charFun (μ : Measure ℝ) u‖ ^ 2 - 1) ≤
      2 * CoefficientRayPrice.exponent c a b 1 (thirdAbsoluteMoment μ * u) := by
  have hs := mul_le_mul_of_nonneg_left hsq (sq_nonneg (thirdAbsoluteMoment μ))
  have hc := mul_le_mul_of_nonneg_left hC
    (show 0 ≤ 2 * b * thirdAbsoluteMoment μ ^ 2 * |u| ^ 3 by positivity)
  unfold CoefficientRayPrice.exponent
  simp only [mul_one, abs_mul, abs_of_nonneg hρ0, mul_pow]
  nlinarith only [hs, hc]

/-- The four raw square theorems and the true unit bound are consumed
anew. An already exponentiated modulus is not used as square data. -/
theorem squared_raw_bound (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (c : ℝ)
    (hC : thirdAbsoluteMoment μ + 1 ≤ c * thirdAbsoluteMoment μ) (u : ℝ) :
    thirdAbsoluteMoment μ ^ 2 * (‖charFun (μ : Measure ℝ) u‖ ^ 2 - 1) ≤
      2 * g4 c (thirdAbsoluteMoment μ * u) := by
  have hρ0 : 0 ≤ thirdAbsoluteMoment μ :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (ThirdMomentRegion.one_le_third μ h)
  have h0raw : ‖charFun (μ : Measure ℝ) u‖ ^ 2 ≤
      1 - 2 * (1 / 2 : ℝ) * u ^ 2 + 2 * (1 / 10 : ℝ) * (thirdAbsoluteMoment μ + 1) * |u| ^ 3 := by
    have hh := ClassicalDamping.charFun_norm_sq_le μ h u
    nlinarith only [hh]
  have h0 := scaled_square_bound μ c (1 / 2) (1 / 10) u hρ0 hC (by norm_num) h0raw
  have hθ := scaled_square_bound μ c ClassicalCosineCubic.a ClassicalCosineCubic.b u hρ0 hC
    ClassicalCosineCubic.b_nonneg (by
      simpa only [ClassicalCosineCubic.polynomial] using ClassicalCosineCubic.charFun_norm_sq_le μ h u)
  have hr := scaled_square_bound μ c ClassicalRationalCosine.a ClassicalRationalCosine.b u hρ0 hC
    ClassicalRationalCosine.b_nonneg (by
      simpa only [ClassicalRationalCosine.polynomial] using ClassicalRationalCosine.charFun_norm_sq_le μ h u)
  have h3 := scaled_square_bound μ c ClassicalThreeHalvesCosine.a ClassicalThreeHalvesCosine.b u hρ0 hC
    ClassicalThreeHalvesCosine.b_nonneg (by
      simpa only [ClassicalThreeHalvesCosine.polynomial] using ClassicalThreeHalvesCosine.charFun_norm_sq_le μ h u)
  have hunit : thirdAbsoluteMoment μ ^ 2 * (‖charFun (μ : Measure ℝ) u‖ ^ 2 - 1) ≤ 0 := by
    have hx : ‖charFun (μ : Measure ℝ) u‖ ^ 2 ≤ 1 := by
      simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg _) (norm_charFun_le_one _) 2
    exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (sub_nonpos.mpr hx)
  unfold g4 CoefficientHybridSecond.spectralExponent2 CoefficientRaySpectral.spectralExponent
  simp only [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2), mul_zero]
  exact le_min (le_min hunit (le_min h0 (le_min hθ hr))) h3

theorem linear_raw_bound (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (R : ℝ) (hR : 0 < R) (hρ : R ≤ thirdAbsoluteMoment μ) (u : ℝ) :
    thirdAbsoluteMoment μ ^ 2 * (‖charFun (μ : Measure ℝ) u‖ - 1) ≤
      ReferenceCircleDamping.G R (thirdAbsoluteMoment μ * u) := by
  have hH := (ReferenceCircleDamping.rho_sq_mul_norm_sub_one_le_H μ h u).trans
    (ReferenceCircleDamping.H_le_of_le R (thirdAbsoluteMoment μ) (thirdAbsoluteMoment μ * u) hR.le hρ)
  have hu : thirdAbsoluteMoment μ ^ 2 * (‖charFun (μ : Measure ℝ) u‖ - 1) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (sub_nonpos.mpr (norm_charFun_le_one _))
  exact le_min hu hH

private lemma square_factor_le_exp (x g ρ η : ℝ) (hx : 0 ≤ x) (hρ : 0 < ρ) (hg : g ≤ 0)
    (hη : η * ρ ^ 2 ≤ 1) (hraw : ρ ^ 2 * (x ^ 2 - 1) ≤ 2 * g) :
    x ≤ Real.exp ((1 / ρ ^ 2) * (g - η * g ^ 2)) := by
  let k := 1 / ρ ^ 2
  have hk : 0 < k := by dsimp [k]; positivity
  have hηk : η ≤ k := (le_div_iff₀ (sq_pos_of_pos hρ)).mpr hη
  have hd : x ^ 2 - 1 ≤ (2 * g) / ρ ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hρ)).mpr
    simpa only [mul_comm] using hraw
  have hb : x ^ 2 ≤ 1 + 2 * k * g := by
    calc
      _ ≤ 1 + (2 * g) / ρ ^ 2 := by linarith only [hd]
      _ = _ := by dsimp [k]; ring
  have hy : 2 * k * g ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hg
  have he := hb.trans (one_add_le_secondOrder_exp (2 * k * g) hy)
  have hp := mul_le_mul_of_nonneg_left hηk (show 0 ≤ 2 * k * g ^ 2 by positivity)
  have harg : 2 * k * g - (2 * k * g) ^ 2 / 2 ≤ 2 * (k * (g - η * g ^ 2)) := by
    nlinarith only [hp]
  apply (sq_le_sq₀ hx (Real.exp_nonneg _)).mp
  rw [← Real.exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  exact he.trans (Real.exp_le_exp.mpr harg)

private lemma linear_factor_le_exp (x z ρ η : ℝ) (hρ : 0 < ρ) (hz : z ≤ 0)
    (hη : η * ρ ^ 2 ≤ 1) (hraw : ρ ^ 2 * (x - 1) ≤ z) :
    x ≤ Real.exp ((1 / ρ ^ 2) * (z - (η / 2) * z ^ 2)) := by
  let k := 1 / ρ ^ 2
  have hk : 0 < k := by dsimp [k]; positivity
  have hηk : η ≤ k := (le_div_iff₀ (sq_pos_of_pos hρ)).mpr hη
  have hd : x - 1 ≤ z / ρ ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hρ)).mpr
    simpa only [mul_comm] using hraw
  have hb : x ≤ 1 + k * z := by
    calc
      _ ≤ 1 + z / ρ ^ 2 := by linarith only [hd]
      _ = _ := by dsimp [k]; ring
  have hy : k * z ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hk.le hz
  have he := hb.trans (one_add_le_secondOrder_exp (k * z) hy)
  have hp := mul_le_mul_of_nonneg_left hηk (show 0 ≤ k * z ^ 2 / 2 by positivity)
  have harg : k * z - (k * z) ^ 2 / 2 ≤ k * (z - (η / 2) * z ^ 2) := by nlinarith only [hp]
  exact he.trans (Real.exp_le_exp.mpr harg)

private lemma charFun_factor_le_exp (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (η c R : ℝ) (hR : 0 < R) (hρ : R ≤ thirdAbsoluteMoment μ)
    (hC : thirdAbsoluteMoment μ + 1 ≤ c * thirdAbsoluteMoment μ)
    (hη : η * thirdAbsoluteMoment μ ^ 2 ≤ 1) (u : ℝ) :
    ‖charFun (μ : Measure ℝ) u‖ ≤
      Real.exp ((1 / thirdAbsoluteMoment μ ^ 2) * spectrum η c R (thirdAbsoluteMoment μ * u)) := by
  have hρp : 0 < thirdAbsoluteMoment μ := hR.trans_le hρ
  have hc := square_factor_le_exp _ (g4 c (thirdAbsoluteMoment μ * u)) _ η (norm_nonneg _) hρp
    (CoefficientHybridSecond.spectralExponent2_nonpos c _) hη (squared_raw_bound μ h c hC u)
  have hr := linear_factor_le_exp _ (ReferenceCircleDamping.G R (thirdAbsoluteMoment μ * u)) _ η hρp
    (ReferenceCircleDamping.G_nonpos R _) hη (linear_raw_bound μ h R hR hρ u)
  unfold spectrum
  rcases le_total (g4 c (thirdAbsoluteMoment μ * u) - η * (g4 c (thirdAbsoluteMoment μ * u)) ^ 2)
    (ReferenceCircleDamping.G R (thirdAbsoluteMoment μ * u) -
      (η / 2) * (ReferenceCircleDamping.G R (thirdAbsoluteMoment μ * u)) ^ 2) with hh | hh
  · rw [min_eq_left hh]
    exact hc
  · rw [min_eq_right hh]
    exact hr

/-- Eta>=0 is retained to license a nonpositive fixed spectrum; its upper
admissibility bound is what the scalar domination itself consumes. -/
theorem normalized_power_le_exp (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (hn : 0 < n) (η c R : ℝ) (_hη0 : 0 ≤ η) (hR : 0 < R)
    (hρ : R ≤ thirdAbsoluteMoment μ) (hC : thirdAbsoluteMoment μ + 1 ≤ c * thirdAbsoluteMoment μ)
    (hη : η * thirdAbsoluteMoment μ ^ 2 ≤ 1) (t : ℝ) :
    ‖charFun (μ : Measure ℝ) (t / Real.sqrt n)‖ ^ n ≤ Real.exp (exponent η c R (beta μ n) t) := by
  have hρp : 0 < thirdAbsoluteMoment μ := hR.trans_le hρ
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hβ : 0 < beta μ n := div_pos hρp (Real.sqrt_pos.mpr hnR)
  have hp := pow_le_pow_left₀ (norm_nonneg _) (charFun_factor_le_exp μ h η c R hR hρ hC hη (t / Real.sqrt n)) n
  rw [← Real.exp_nat_mul] at hp
  have hv : thirdAbsoluteMoment μ * (t / Real.sqrt n) = beta μ n * t := by unfold beta; ring
  have he : (n : ℝ) * ((1 / thirdAbsoluteMoment μ ^ 2) *
      spectrum η c R (thirdAbsoluteMoment μ * (t / Real.sqrt n))) = exponent η c R (beta μ n) t := by
    rw [hv]
    unfold exponent
    rw [← beta_sq_mul_n μ n hn]
    field_simp [hβ.ne', hnR.ne']
  exact hp.trans_eq (congrArg Real.exp he)

/-- Only the original rho>=rho0 premise licenses the unchanged loss. -/
theorem normalized_pred_power_le_loss_exp (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n N : ℕ) (hN : 0 < N) (hNn : N ≤ n) (η c R : ℝ) (hη0 : 0 ≤ η) (hR : 0 < R)
    (hρ : R ≤ thirdAbsoluteMoment μ) (hC : thirdAbsoluteMoment μ + 1 ≤ c * thirdAbsoluteMoment μ)
    (hη : η * thirdAbsoluteMoment μ ^ 2 ≤ 1) (hρ0 : rho0 ≤ thirdAbsoluteMoment μ) (t : ℝ) :
    ‖charFun (μ : Measure ℝ) (t / Real.sqrt n)‖ ^ (n - 1) ≤
      Real.exp ((1 - loss N (beta μ n)) * exponent η c R (beta μ n) t) := by
  have hn : 0 < n := lt_of_lt_of_le hN hNn
  exact GenericRayPrice.pred_power_from_normalized_bound _ _ _ n (norm_nonneg _) (norm_charFun_le_one _) hn
    (inv_n_le_loss μ n N hN hNn hρ0) (loss_le_one N hN (beta μ n))
    (normalized_power_le_exp μ h n hn η c R hη0 hR hρ hC hη t)

theorem finite_band_admissible (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n M : ℕ) (hn : 0 < n) (hnM : n ≤ M) (a : ℝ) (ha : 0 < a)
    (hs : a ≤ 1 / beta μ n ^ 2) :
    0 ≤ a / (M : ℝ) ∧ (a / (M : ℝ)) * thirdAbsoluteMoment μ ^ 2 ≤ 1 := by
  have hM : (0 : ℝ) < M := Nat.cast_pos.mpr (lt_of_lt_of_le hn hnM)
  have hρp : 0 < thirdAbsoluteMoment μ := lt_of_lt_of_le zero_lt_one (ThirdMomentRegion.one_le_third μ h)
  have hβ : 0 < beta μ n := div_pos hρp (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn))
  have hb : a * beta μ n ^ 2 ≤ 1 := (le_div_iff₀ (sq_pos_of_pos hβ)).mp hs
  have hm := mul_le_mul_of_nonneg_right hb (Nat.cast_nonneg n)
  have hmoment : a * thirdAbsoluteMoment μ ^ 2 ≤ (M : ℝ) := by
    calc
      _ = (a * beta μ n ^ 2) * (n : ℝ) := by rw [← beta_sq_mul_n μ n hn]; ring
      _ ≤ (n : ℝ) := by simpa only [one_mul] using hm
      _ ≤ (M : ℝ) := Nat.cast_le.mpr hnM
  refine ⟨div_nonneg ha.le hM.le, ?_⟩
  calc
    _ = (a * thirdAbsoluteMoment μ ^ 2) / (M : ℝ) := by ring
    _ ≤ 1 := (div_le_one hM).mpr hmoment

/-- The same a is a fixed whole-node lower bound on actual s. -/
theorem normalized_power_le_finite_band (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n M : ℕ) (hn : 0 < n) (hnM : n ≤ M) (a : ℝ) (ha : 0 < a)
    (hs : a ≤ 1 / beta μ n ^ 2) (c R : ℝ) (hR : 0 < R) (hρ : R ≤ thirdAbsoluteMoment μ)
    (hC : thirdAbsoluteMoment μ + 1 ≤ c * thirdAbsoluteMoment μ) (t : ℝ) :
    ‖charFun (μ : Measure ℝ) (t / Real.sqrt n)‖ ^ n ≤
      Real.exp (exponent (a / (M : ℝ)) c R (beta μ n) t) := by
  obtain ⟨hη0, hη⟩ := finite_band_admissible μ h n M hn hnM a ha hs
  exact normalized_power_le_exp μ h n hn (a / (M : ℝ)) c R hη0 hR hρ hC hη t

end BerryEsseen.SecondOrderDamping

#print axioms BerryEsseen.SecondOrderDamping.one_add_le_secondOrder_exp
#print axioms BerryEsseen.SecondOrderDamping.squared_raw_bound
#print axioms BerryEsseen.SecondOrderDamping.linear_raw_bound
#print axioms BerryEsseen.SecondOrderDamping.normalized_power_le_exp
#print axioms BerryEsseen.SecondOrderDamping.normalized_pred_power_le_loss_exp
#print axioms BerryEsseen.SecondOrderDamping.finite_band_admissible
#print axioms BerryEsseen.SecondOrderDamping.normalized_power_le_finite_band
