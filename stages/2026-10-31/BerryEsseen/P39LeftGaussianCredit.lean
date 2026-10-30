module

public import BerryEsseen.P39Count10Coarse
public import BerryEsseen.P39ModeNoiseUpperBounds

@[expose] public section

/-! 2026-10-31: continuous Gaussian credit at count 10, phase zero.
The noise derivative is bounded on the entire real interval [0,1/5].
The zero-noise baseline uses only an already proved scalar price; its
reference contribution is removed by its actual nonnegativity. No
original-law profile or positive-phase exclusion is asserted. -/

noncomputable section
open MeasureTheory Set

namespace BerryEsseen.P39LeftGaussianCredit

open GaussianTools MomentBudgetNoise

def zeroBaseline (p : ℝ) : ℝ := BinomialWeights.lowerPrefix 26 10 p -
  Phi (P39NoiseGate.noiseArgument p 10 0) - (803 / 10000) * P39Reference.rho0 p

theorem variance_and_sqrt_bounds {p lambda : ℝ}
    (hp : p ∈ Icc (39 / 100 : ℝ) (2 / 5)) (hl : lambda ∈ Icc (0 : ℝ) (1 / 5)) :
    (30927 / 5000 : ℝ) ≤ 26 * variance p + lambda ∧
      26 * variance p + lambda ≤ (161 : ℝ) / 25 ∧
      (12 : ℝ) / 5 ≤ Real.sqrt (26 * variance p + lambda) ∧
      Real.sqrt (26 * variance p + lambda) ≤ (127 : ℝ) / 50 := by
  have hv := P39ModeNoiseUpperBounds.variance_bounds hp
  have hlow : (30927 / 5000 : ℝ) ≤ 26 * variance p + lambda := by linarith only [hv.1, hl.1]
  have hupp : 26 * variance p + lambda ≤ (161 : ℝ) / 25 := by linarith only [hv.2, hl.2]
  refine ⟨hlow, hupp, ?_, ?_⟩
  · apply Real.le_sqrt_of_sq_le
    nlinarith only [hlow]
  · apply Real.sqrt_le_iff.mpr
    exact ⟨by norm_num, by nlinarith only [hupp]⟩

theorem count10_argument_abs_le {p lambda : ℝ}
    (hp : p ∈ Icc (39 / 100 : ℝ) (2 / 5)) (hl : lambda ∈ Icc (0 : ℝ) (1 / 5)) :
    |P39NoiseGate.noiseArgument p 10 lambda| ≤ (1 : ℝ) / 6 := by
  have hs := (variance_and_sqrt_bounds hp hl).2.2.1
  have hV := P39NoiseGate.actual_variance_pos hp hl.1
  have hN : 10 - 26 * p ≤ 0 := by linarith only [hp.1]
  unfold P39NoiseGate.noiseArgument
  rw [abs_div, abs_of_pos (Real.sqrt_pos.mpr hV), abs_of_nonpos hN]
  apply (div_le_iff₀ (Real.sqrt_pos.mpr hV)).mpr
  nlinarith only [hs, hp.2]

theorem phi_zero_lower : (199 : ℝ) / 500 ≤ phi 0 := by
  have hc : (199 : ℝ) / 500 ≤ RationalGaussianPrices.densityLower := by
    norm_num [RationalGaussianPrices.densityLower]
  exact hc.trans RationalGaussianPrices.densityLower_lt_phi_zero.le

theorem count10_phi_lower {p lambda : ℝ}
    (hp : p ∈ Icc (39 / 100 : ℝ) (2 / 5)) (hl : lambda ∈ Icc (0 : ℝ) (1 / 5)) :
    (39 : ℝ) / 100 ≤ phi (P39NoiseGate.noiseArgument p 10 lambda) := by
  let z := P39NoiseGate.noiseArgument p 10 lambda
  have hz := count10_argument_abs_le hp hl
  have hsq := (sq_le_sq₀ (abs_nonneg z) (by norm_num : (0 : ℝ) ≤ 1 / 6)).mpr hz
  rw [sq_abs] at hsq
  have hpoly : 0 ≤ 1 - z ^ 2 / 2 := by nlinarith only [hsq]
  have hscalar : (39 : ℝ) / 100 ≤ (199 / 500) * (1 - z ^ 2 / 2) := by nlinarith only [hsq]
  have hd := mul_le_mul_of_nonneg_right phi_zero_lower hpoly
  have he := mul_le_mul_of_nonneg_left (Real.one_sub_le_exp_neg (z ^ 2 / 2)) (phi_nonneg 0)
  change (39 : ℝ) / 100 ≤ phi z
  rw [GaussianPrices.phi_eq_phi_zero_mul_exp]
  exact hscalar.trans (hd.trans he)

/-- The actual Gaussian derivative has a uniform positive credit.
This includes both endpoints and zero noise. -/
theorem negative_gaussianSlope_lower {p lambda : ℝ}
    (hp : p ∈ Icc (39 / 100 : ℝ) (2 / 5)) (hl : lambda ∈ Icc (0 : ℝ) (1 / 5)) :
    (1 : ℝ) / 600 ≤ -P39NoiseGate.gaussianSlope p 10 lambda := by
  have hb := variance_and_sqrt_bounds hp hl
  have hV := P39NoiseGate.actual_variance_pos hp hl.1
  have hnum := mul_le_mul (count10_phi_lower hp hl)
    (show (7 : ℝ) / 50 ≤ 26 * p - 10 by linarith only [hp.1])
    (by norm_num : (0 : ℝ) ≤ 7 / 50) (phi_nonneg _)
  have hden := mul_le_mul hb.2.1 hb.2.2.2 (Real.sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 161 / 25)
  have he : -P39NoiseGate.gaussianSlope p 10 lambda =
      phi (P39NoiseGate.noiseArgument p 10 lambda) * (26 * p - 10) /
        (2 * (26 * variance p + lambda) * Real.sqrt (26 * variance p + lambda)) := by
    unfold P39NoiseGate.gaussianSlope
    ring
  rw [he]
  apply (le_div_iff₀ (by positivity : 0 < 2 * (26 * variance p + lambda) *
    Real.sqrt (26 * variance p + lambda))).mpr
  nlinarith only [hnum, hden]

/-- The reused mean-value theorem is proved from the actual Phi and
noiseArgument derivatives. A negative loss slope yields positive credit
on the whole interval, rather than a comparison of sampled endpoints. -/
theorem count10_gaussian_credit {p lambda : ℝ}
    (hp : p ∈ Icc (39 / 100 : ℝ) (2 / 5)) (hl : lambda ∈ Icc (0 : ℝ) (1 / 5)) :
    lambda / 600 ≤ Phi (P39NoiseGate.noiseArgument p 10 lambda) -
      Phi (P39NoiseGate.noiseArgument p 10 0) := by
  have hm := P39ModeNoiseUpperBounds.noise_loss_le_of_slope p 10 (-(1 / 600)) lambda hp hl.1
    (by
      intro x hx
      have hd := negative_gaussianSlope_lower hp (show x ∈ Icc (0 : ℝ) (1 / 5) from
        ⟨hx.1, hx.2.trans hl.2⟩)
      linarith only [hd])
  nlinarith only [hm]

theorem count10_zero_baseline_upper {p : ℝ}
    (hp : p ∈ Icc (39 / 100 : ℝ) (2 / 5)) : zeroBaseline p ≤ -(1 / 9000 : ℝ) := by
  have hf := P39Count10Coarse.upper_phase_face hp
  have hp0 : 0 ≤ p := by linarith only [hp.1]
  have hp1 : p ≤ 1 := by linarith only [hp.2]
  have heta := N26P39Count10Prices.eta_nonneg hp0 hp1
  have hQ := StopLossShape.Q_nonneg N26P39Count10Prices.reference (N26P39Count10Prices.A p)
  have hterm := mul_nonneg heta hQ
  have harg : N26P39Count10Prices.argument p 0 = P39NoiseGate.noiseArgument p 10 0 := by
    simp only [N26P39Count10Prices.argument, P39NoiseGate.noiseArgument,
      variance, P39Reference.v, add_zero, mul_assoc]
  have hprice : N26P39Count10Prices.price p 0 = zeroBaseline p +
      N26P39Count10Prices.eta p * StopLossShape.Q N26P39Count10Prices.reference
        (N26P39Count10Prices.A p) := by
    unfold N26P39Count10Prices.price zeroBaseline
    rw [harg]
    simp only [add_zero, zero_add, N26P39Count10Prices.ci, N26P39Count10Prices.ciQ,
      Rat.cast_div, Rat.cast_ofNat]
    ring
  rw [hprice] at hf
  linarith only [hf, hterm]

theorem count10_noisy_baseline_upper {p lambda : ℝ}
    (hp : p ∈ Icc (39 / 100 : ℝ) (2 / 5)) (hl : lambda ∈ Icc (0 : ℝ) (1 / 5)) :
    BinomialWeights.lowerPrefix 26 10 p - Phi (P39NoiseGate.noiseArgument p 10 lambda) -
      (803 / 10000) * P39Reference.rho0 p ≤ -(1 / 9000 : ℝ) - lambda / 600 := by
  have hb := count10_zero_baseline_upper hp
  have hc := count10_gaussian_credit hp hl
  unfold zeroBaseline at hb
  linarith only [hb, hc]

end BerryEsseen.P39LeftGaussianCredit

#print axioms BerryEsseen.P39LeftGaussianCredit.count10_argument_abs_le
#print axioms BerryEsseen.P39LeftGaussianCredit.count10_phi_lower
#print axioms BerryEsseen.P39LeftGaussianCredit.negative_gaussianSlope_lower
#print axioms BerryEsseen.P39LeftGaussianCredit.count10_gaussian_credit
#print axioms BerryEsseen.P39LeftGaussianCredit.count10_zero_baseline_upper
#print axioms BerryEsseen.P39LeftGaussianCredit.count10_noisy_baseline_upper
