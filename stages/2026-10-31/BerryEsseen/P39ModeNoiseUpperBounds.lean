module

public import BerryEsseen.P39NoiseGate
public import BerryEsseen.PositivePhasePriceConvex
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

@[expose] public section

/-! 2026-10-30: Gaussian noise losses for the two endpoints of the
count-11 mode-price phase interval. This is only the Gaussian component;
the original law's third-moment noise credit is acquired separately. -/

noncomputable section

open Set

namespace BerryEsseen.P39ModeNoiseUpperBounds

open GaussianTools MomentBudgetNoise

lemma variance_bounds {p : ℝ} (hp : p ∈ Icc (39 / 100 : ℝ) (2 / 5)) :
    (2379 / 10000 : ℝ) ≤ variance p ∧ variance p ≤ (6 : ℝ) / 25 := by
  have hlow := mul_nonneg (sub_nonneg.mpr hp.1)
    (show 0 ≤ (61 / 100 : ℝ) - p by linarith only [hp.2])
  have hhigh := mul_nonneg (sub_nonneg.mpr hp.2)
    (show 0 ≤ (3 / 5 : ℝ) - p by linarith only [hp.2])
  unfold variance P39Reference.v
  constructor <;> nlinarith only [hlow, hhigh]

lemma variance_sqrt_lower {p l : ℝ}
    (hp : p ∈ Icc (39 / 100 : ℝ) (2 / 5)) (hl : 0 ≤ l) :
    (30927 / 5000 : ℝ) ≤ 26 * variance p + l ∧
      (2487 / 1000 : ℝ) ≤ Real.sqrt (26 * variance p + l) := by
  have hV : (30927 / 5000 : ℝ) ≤ 26 * variance p + l := by
    nlinarith only [(variance_bounds hp).1, hl]
  refine ⟨hV, ?_⟩
  apply Real.le_sqrt_of_sq_le
  nlinarith only [hV]

lemma count11_argument_lower {p l : ℝ}
    (hp : p ∈ Icc (39 / 100 : ℝ) (2 / 5))
    (hl : l ∈ Icc (0 : ℝ) (17 / 50)) :
    (23 : ℝ) / 100 ≤ P39NoiseGate.noiseArgument p 11 l := by
  have hVpos := P39NoiseGate.actual_variance_pos hp hl.1
  have hV : 26 * variance p + l ≤ (329 : ℝ) / 50 := by
    nlinarith only [(variance_bounds hp).2, hl.2]
  have hs : Real.sqrt (26 * variance p + l) ≤ (257 : ℝ) / 100 := by
    have hs2 := Real.sq_sqrt hVpos.le
    nlinarith only [hs2, hV, Real.sqrt_nonneg (26 * variance p + l)]
  unfold P39NoiseGate.noiseArgument
  apply (le_div_iff₀ (Real.sqrt_pos.mpr hVpos)).mpr
  nlinarith only [hs, hp.2]

lemma phi_count11_upper {p l : ℝ}
    (hp : p ∈ Icc (39 / 100 : ℝ) (2 / 5))
    (hl : l ∈ Icc (0 : ℝ) (17 / 50)) :
    phi (P39NoiseGate.noiseArgument p 11 l) ≤ (39 : ℝ) / 100 := by
  have hexp : (40 : ℝ) / 39 ≤ Real.exp ((23 / 100 : ℝ) ^ 2 / 2) := by
    nlinarith only [Real.add_one_le_exp ((23 / 100 : ℝ) ^ 2 / 2)]
  have hphi := GaussianPrices.phi_lt_of_exp_lower (23 / 100) (39 / 100) (40 / 39)
    (by norm_num) hexp (by norm_num)
  have ha := count11_argument_lower hp hl
  exact (PositivePhasePriceConvex.phi_antitoneOn_nonnegative (by norm_num)
    (show (0 : ℝ) ≤ P39NoiseGate.noiseArgument p 11 l by linarith only [ha]) ha).trans hphi.le

lemma phi_upper (x : ℝ) : phi x ≤ (2 : ℝ) / 5 := by
  rw [GaussianPrices.phi_eq_phi_zero_mul_exp]
  have he : Real.exp (-(x ^ 2 / 2)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith only [sq_nonneg x])
  exact (mul_le_mul_of_nonneg_left he (phi_nonneg 0)).trans
    (by simpa only [mul_one] using GaussianPrices.phi_zero_lt_2_5.le)

theorem count11_noiseSlope_upper {p l : ℝ}
    (hp : p ∈ Icc (39 / 100 : ℝ) (2 / 5))
    (hl : l ∈ Icc (0 : ℝ) (17 / 50)) :
    P39NoiseGate.gaussianSlope p 11 l ≤ (11 : ℝ) / 1000 := by
  have hVpos := P39NoiseGate.actual_variance_pos hp hl.1
  obtain ⟨hV, hs⟩ := variance_sqrt_lower hp hl.1
  have hden := mul_le_mul hV hs (by norm_num : (0 : ℝ) ≤ 2487 / 1000) hVpos.le
  have hnum : phi (P39NoiseGate.noiseArgument p 11 l) * (11 - 26 * p) ≤
      (39 / 100 : ℝ) * (43 / 50) := by
    exact mul_le_mul (phi_count11_upper hp hl) (by linarith only [hp.1])
      (by linarith only [hp.2]) (by norm_num)
  unfold P39NoiseGate.gaussianSlope
  apply (div_le_iff₀ (by positivity : 0 < 2 * (26 * variance p + l) * Real.sqrt (26 * variance p + l))).mpr
  nlinarith only [hden, hnum]

theorem count12_noiseSlope_upper {p l : ℝ}
    (hp : p ∈ Icc (39 / 100 : ℝ) (2 / 5)) (hl : 0 ≤ l) :
    P39NoiseGate.gaussianSlope p 12 l ≤ (1 : ℝ) / 40 := by
  have hVpos := P39NoiseGate.actual_variance_pos hp hl
  obtain ⟨hV, hs⟩ := variance_sqrt_lower hp hl
  have hden := mul_le_mul hV hs (by norm_num : (0 : ℝ) ≤ 2487 / 1000) hVpos.le
  have hnum : phi (P39NoiseGate.noiseArgument p 12 l) * (12 - 26 * p) ≤
      (2 / 5 : ℝ) * (93 / 50) := by
    exact mul_le_mul (phi_upper _) (by linarith only [hp.1])
      (by linarith only [hp.2]) (by norm_num)
  unfold P39NoiseGate.gaussianSlope
  apply (div_le_iff₀ (by positivity : 0 < 2 * (26 * variance p + l) * Real.sqrt (26 * variance p + l))).mpr
  nlinarith only [hden, hnum]

theorem noise_loss_le_of_slope (p r K l : ℝ)
    (hp : p ∈ Icc (39 / 100 : ℝ) (2 / 5)) (hl : 0 ≤ l)
    (hSlope : ∀ x ∈ Icc (0 : ℝ) l, P39NoiseGate.gaussianSlope p r x ≤ K) :
    Phi (P39NoiseGate.noiseArgument p r 0) - Phi (P39NoiseGate.noiseArgument p r l) ≤ K * l := by
  let f := fun x : ℝ => -Phi (P39NoiseGate.noiseArgument p r x) - K * x
  have hd : ∀ x ∈ Icc (0 : ℝ) l,
      HasDerivAt f (P39NoiseGate.gaussianSlope p r x - K) x := by
    intro x hx
    have harg := P39NoiseGate.hasDerivAt_noiseArgument (p := p) (r := r) (l := x)
      (P39NoiseGate.actual_variance_pos hp hx.1)
    have hG := ((hasDerivAt_Phi (P39NoiseGate.noiseArgument p r x)).comp x harg).neg
    convert hG.sub ((hasDerivAt_id x).const_mul K) using 1
    · funext y
      rfl
    · unfold P39NoiseGate.gaussianSlope
      ring
  have hm : AntitoneOn f (Icc (0 : ℝ) l) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 l)
    · exact fun x hx => (hd x hx).continuousAt.continuousWithinAt
    · exact fun x hx => (hd x (interior_subset hx)).hasDerivWithinAt
    · intro x hx
      exact sub_nonpos.mpr (hSlope x (interior_subset hx))
  have h := hm ⟨le_rfl, hl⟩ ⟨hl, le_rfl⟩ hl
  dsimp only [f] at h
  nlinarith only [h]

theorem count11_noise_loss {p l : ℝ}
    (hp : p ∈ Icc (39 / 100 : ℝ) (2 / 5))
    (hl : l ∈ Icc (0 : ℝ) (17 / 50)) :
    Phi (P39NoiseGate.noiseArgument p 11 0) - Phi (P39NoiseGate.noiseArgument p 11 l) ≤
      (11 / 1000 : ℝ) * l :=
  noise_loss_le_of_slope p 11 (11 / 1000) l hp hl.1
    (fun x hx => count11_noiseSlope_upper hp ⟨hx.1, hx.2.trans hl.2⟩)

theorem count12_noise_loss {p l : ℝ}
    (hp : p ∈ Icc (39 / 100 : ℝ) (2 / 5)) (hl : 0 ≤ l) :
    Phi (P39NoiseGate.noiseArgument p 12 0) - Phi (P39NoiseGate.noiseArgument p 12 l) ≤ (1 / 40 : ℝ) * l :=
  noise_loss_le_of_slope p 12 (1 / 40) l hp hl (fun x hx => count12_noiseSlope_upper hp hx.1)

end BerryEsseen.P39ModeNoiseUpperBounds

#print axioms BerryEsseen.P39ModeNoiseUpperBounds.count11_noiseSlope_upper
#print axioms BerryEsseen.P39ModeNoiseUpperBounds.count12_noiseSlope_upper
#print axioms BerryEsseen.P39ModeNoiseUpperBounds.count11_noise_loss
#print axioms BerryEsseen.P39ModeNoiseUpperBounds.count12_noise_loss
