module

public import BerryEsseen.P39ModeEtaEndpointPrices
public import BerryEsseen.P39Count11Face

@[expose] public section

/-! 2026-10-30: probability monotonicity of the same zero-noise baselines
whose actual Gaussian/binomial endpoint prices were proved separately.
The count-12 Gaussian numerator belongs to base1 throughout the strip. -/

namespace BerryEsseen.P39ModeBaselineMonotonicity

open Set MeasureTheory
open P39ModeEtaEndpointPrices
open scoped BigOperators

noncomputable section

set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

theorem base0_eq_old (p : ℝ) : base0 p = P39Count11Face.base p 0 := by
  simp only [base0, P39Count11Face.base, argument, P39NoiseGate.noiseArgument,
    MomentBudgetNoise.variance, P39Reference.v, add_zero, mul_assoc]

theorem base0_monotone : MonotoneOn base0 strip := by
  intro a ha b hb hab
  rw [base0_eq_old, base0_eq_old]
  exact P39Count11Face.base_zero_monotone ha hb hab

lemma variance_bounds {p : ℝ} (hp : p ∈ strip) :
    (2379 / 10000 : ℝ) ≤ P39Reference.v p ∧ P39Reference.v p ≤ 6 / 25 := by
  have hlo := mul_nonneg (sub_nonneg.mpr hp.1)
    (show (0 : ℝ) ≤ 61 / 100 - p by linarith only [hp.2])
  have hhi := mul_nonneg (sub_nonneg.mpr hp.2)
    (show (0 : ℝ) ≤ 3 / 5 - p by linarith only [hp.2])
  unfold P39Reference.v
  constructor <;> nlinarith only [hlo, hhi]

lemma sum_variance_bounds {p : ℝ} (hp : p ∈ strip) :
    (30927 / 5000 : ℝ) ≤ 26 * P39Reference.v p ∧
      26 * P39Reference.v p ≤ 156 / 25 := by
  have h := variance_bounds hp
  constructor <;> linarith only [h.1, h.2]

lemma sum_sqrt_bounds {p : ℝ} (hp : p ∈ strip) :
    (2487 / 1000 : ℝ) ≤ Real.sqrt (26 * P39Reference.v p) ∧
      Real.sqrt (26 * P39Reference.v p) ≤ 5 / 2 := by
  have h := sum_variance_bounds hp
  constructor
  · apply Real.le_sqrt_of_sq_le
    nlinarith only [h.1]
  · apply Real.sqrt_le_iff.mpr
    constructor
    · norm_num
    · nlinarith only [h.2]

lemma numerator_bounds {p : ℝ} (hp : p ∈ strip) :
    (8 / 5 : ℝ) ≤ 12 - 26 * p ∧ 12 - 26 * p ≤ 93 / 50 := by
  constructor <;> linarith only [hp.1, hp.2]

lemma probability_slope_bounds {p : ℝ} (hp : p ∈ strip) :
    (0 : ℝ) ≤ 1 - 2 * p ∧ 1 - 2 * p ≤ 11 / 50 := by
  constructor <;> linarith only [hp.1, hp.2]

theorem argument_eq (k : ℕ) (p : ℝ) :
    ProbabilityGaussianPrice.argument 26 k 0 0 p = argument (k : ℝ) p := by
  simp only [ProbabilityGaussianPrice.argument, ProbabilityGaussianPrice.numerator,
    ProbabilityGaussianPrice.variance, argument, Nat.cast_ofNat, add_zero, mul_assoc]

lemma argument1_lower {p : ℝ} (hp : p ∈ strip) :
    (16 / 25 : ℝ) ≤ ProbabilityGaussianPrice.argument 26 12 0 0 p := by
  have hN := numerator_bounds hp
  have hs := sum_sqrt_bounds hp
  have hs0 : (0 : ℝ) < Real.sqrt (26 * P39Reference.v p) := by linarith only [hs.1]
  simp only [ProbabilityGaussianPrice.argument, ProbabilityGaussianPrice.numerator,
    ProbabilityGaussianPrice.variance, Nat.cast_ofNat, add_zero]
  change 16 / 25 ≤ (12 - 26 * p) / Real.sqrt (26 * P39Reference.v p)
  apply (le_div_iff₀ hs0).mpr
  nlinarith only [hN.1, hs.2]

lemma phi_at_lower_upper : GaussianTools.phi (16 / 25) ≤ (163 / 500 : ℝ) := by
  apply (GaussianPrices.phi_lt_of_exp_lower (16 / 25) (163 / 500) (200 / 163)
    (by norm_num) ?_ (by norm_num)).le
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 128 / 625) 4
  have hc : (200 / 163 : ℝ) ≤
      ∑ i ∈ Finset.range 4, (128 / 625 : ℝ) ^ i / (i.factorial : ℝ) := by
    norm_num [Finset.sum_range_succ]
  convert hc.trans h using 1 <;> norm_num

lemma phi1_upper {p : ℝ} (hp : p ∈ strip) :
    GaussianTools.phi (ProbabilityGaussianPrice.argument 26 12 0 0 p) ≤ (163 / 500 : ℝ) := by
  have hz := argument1_lower hp
  have hz0 : (0 : ℝ) ≤ ProbabilityGaussianPrice.argument 26 12 0 0 p := by linarith only [hz]
  have hsq := (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 16 / 25) hz0).mpr hz
  have he : Real.exp (-(ProbabilityGaussianPrice.argument 26 12 0 0 p ^ 2 / 2)) ≤
      Real.exp (-((16 / 25 : ℝ) ^ 2 / 2)) := Real.exp_le_exp.mpr (by nlinarith only [hsq])
  have hphi : GaussianTools.phi (ProbabilityGaussianPrice.argument 26 12 0 0 p) ≤
      GaussianTools.phi (16 / 25) := by
    rw [GaussianPrices.phi_eq_phi_zero_mul_exp (ProbabilityGaussianPrice.argument 26 12 0 0 p),
      GaussianPrices.phi_eq_phi_zero_mul_exp (16 / 25)]
    exact mul_le_mul_of_nonneg_left he (GaussianTools.phi_nonneg 0)
  exact hphi.trans phi_at_lower_upper

def argumentSlopeUpper : ℝ :=
  26 / (2487 / 1000) + (93 / 50) * 26 * (11 / 50) /
    (2 * (30927 / 5000) * (2487 / 1000))

lemma negative_argumentSlope_bounds {p : ℝ} (hp : p ∈ strip) :
    0 ≤ -ProbabilityGaussianPrice.argumentSlope 26 12 0 0 p ∧
      -ProbabilityGaussianPrice.argumentSlope 26 12 0 0 p ≤ argumentSlopeUpper := by
  have hV := sum_variance_bounds hp
  have hs := sum_sqrt_bounds hp
  have hN := numerator_bounds hp
  have hP := probability_slope_bounds hp
  have hV0 : (0 : ℝ) < 26 * P39Reference.v p := by linarith only [hV.1]
  have hs0 : (0 : ℝ) < Real.sqrt (26 * P39Reference.v p) := by linarith only [hs.1]
  have hfirst : 26 / Real.sqrt (26 * P39Reference.v p) ≤ (26 : ℝ) / (2487 / 1000) := by
    apply (div_le_iff₀ hs0).mpr
    nlinarith only [hs.1]
  have hnum := mul_le_mul hN.2 hP.2 hP.1 (by norm_num : (0 : ℝ) ≤ 93 / 50)
  have hden := mul_le_mul hV.1 hs.1 (by norm_num : (0 : ℝ) ≤ 2487 / 1000) hV0.le
  have hsecond : (12 - 26 * p) * (26 * (1 - 2 * p)) /
      (2 * (26 * P39Reference.v p) * Real.sqrt (26 * P39Reference.v p)) ≤
      (93 / 50 : ℝ) * 26 * (11 / 50) / (2 * (30927 / 5000) * (2487 / 1000)) := by
    apply (div_le_iff₀ (by positivity :
      (0 : ℝ) < 2 * (26 * P39Reference.v p) * Real.sqrt (26 * P39Reference.v p))).mpr
    nlinarith only [hnum, hden]
  have hsecond0 : (0 : ℝ) ≤ (12 - 26 * p) * (26 * (1 - 2 * p)) /
      (2 * (26 * P39Reference.v p) * Real.sqrt (26 * P39Reference.v p)) := by
    apply div_nonneg
    · exact mul_nonneg (by linarith only [hN.1]) (mul_nonneg (by norm_num) hP.1)
    · positivity
  have heq : -ProbabilityGaussianPrice.argumentSlope 26 12 0 0 p =
      26 / Real.sqrt (26 * P39Reference.v p) + (12 - 26 * p) * (26 * (1 - 2 * p)) /
        (2 * (26 * P39Reference.v p) * Real.sqrt (26 * P39Reference.v p)) := by
    simp only [ProbabilityGaussianPrice.argumentSlope, ProbabilityGaussianPrice.numerator,
      ProbabilityGaussianPrice.variance, ProbabilityGaussianPrice.varianceSlope,
      Nat.cast_ofNat, add_zero, P39Reference.v]
    ring
  rw [heq]
  constructor
  · exact add_nonneg (div_nonneg (by norm_num) hs0.le) hsecond0
  · unfold argumentSlopeUpper
    linarith only [hfirst, hsecond]

lemma negative_rhoSlope_upper {p : ℝ} (hp : p ∈ strip) : -P39Reference.e1 p ≤ (141 / 100 : ℝ) := by
  have hv := variance_bounds hp
  have hv0 : (0 : ℝ) < P39Reference.v p := by linarith only [hv.1]
  have hs : (487 / 1000 : ℝ) ≤ Real.sqrt (P39Reference.v p) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith only [hv.1]
  have hP := probability_slope_bounds hp
  have hnum := mul_le_mul hP.2 (show P39Reference.v p + 1 / 2 ≤ (37 / 50 : ℝ) by
    linarith only [hv.2]) (by linarith only [hv.1] : (0 : ℝ) ≤ P39Reference.v p + 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 11 / 50)
  have hden := mul_le_mul hv.1 hs (by norm_num : (0 : ℝ) ≤ 487 / 1000) hv0.le
  have heq : -P39Reference.e1 p = (1 - 2 * p) * (P39Reference.v p + 1 / 2) /
      (P39Reference.v p * Real.sqrt (P39Reference.v p)) := by
    unfold P39Reference.e1
    ring
  rw [heq]
  apply (div_le_iff₀ (mul_pos hv0 (Real.sqrt_pos.mpr hv0))).mpr
  nlinarith only [hnum, hden]

lemma mass11_lower {p : ℝ} (hp : p ∈ strip) :
    (14778 / 100000 : ℝ) ≤ BinomialWeights.mass 26 11 p := by
  have hrat : (14778 / 100000 : ℚ) ≤ massQ 26 11 (39 / 100) := by decide +kernel
  have he : (14778 / 100000 : ℝ) ≤ BinomialWeights.mass 26 11 (39 / 100) := by
    have h := (Rat.cast_le (K := ℝ)).mpr hrat
    simpa only [massQ, BinomialWeights.mass, Rat.cast_mul, Rat.cast_pow,
      Rat.cast_natCast, Rat.cast_sub, Rat.cast_one, Rat.cast_div, Rat.cast_ofNat] using h
  exact he.trans (P39Count11Face.mass_monotone 11 (by norm_num) (by norm_num)
    (by norm_num [P39Count11Face.strip]) hp hp.1)

lemma prefixSlope_upper {p : ℝ} (hp : p ∈ strip) :
    BinomialWeights.prefixSlope 26 11 p ≤ -(15 : ℝ) / (61 / 100) * (14778 / 100000) := by
  have hm := mass11_lower hp
  have hq0 : (0 : ℝ) < 1 - p := sub_pos.mpr (domain hp).2
  change -15 * BinomialWeights.mass 26 11 p / (1 - p) ≤ _
  apply (div_le_iff₀ hq0).mpr
  nlinarith only [hm, hp.1]

def base1Slope (p : ℝ) : ℝ := BinomialWeights.prefixSlope 26 11 p -
  ProbabilityGaussianPrice.gaussianPriceSlope 26 12 0 0 p - (2 / 25) * P39Reference.e1 p

theorem hasDerivAt_base1 {p : ℝ} (hp : p ∈ strip) : HasDerivAt base1 (base1Slope p) p := by
  have hd := domain hp
  have hF := BinomialWeights.hasDerivAt_prefix 26 11 p hd.1 hd.2 (by norm_num)
  have hG := ProbabilityGaussianPrice.gaussianPrice_hasDerivAt (n := 26) (k := 12) (t := 0) (s := 0)
    (by norm_num) (by norm_num) ⟨hd.1, hd.2⟩
  have hR := (P39Reference.hasDerivAt_rho0 hd.1 hd.2).const_mul ((2 : ℝ) / 25)
  convert (hF.fun_sub hG).fun_sub hR using 1
  · funext q
    simp only [base1, ProbabilityGaussianPrice.gaussianPrice, argument_eq, Nat.cast_ofNat]
  · rfl

lemma derivative_rational_gate : -(15 : ℝ) / (61 / 100) * (14778 / 100000) +
    (163 / 500) * argumentSlopeUpper + (2 / 25) * (141 / 100) < 0 := by
  norm_num [argumentSlopeUpper]

theorem base1Slope_neg {p : ℝ} (hp : p ∈ strip) : base1Slope p < 0 := by
  have hF := prefixSlope_upper hp
  have hS := negative_argumentSlope_bounds hp
  have hG := mul_le_mul (phi1_upper hp) hS.2 hS.1 (by norm_num : (0 : ℝ) ≤ 163 / 500)
  have hR := negative_rhoSlope_upper hp
  unfold base1Slope ProbabilityGaussianPrice.gaussianPriceSlope
  nlinarith only [hF, hG, hR, derivative_rational_gate]

theorem base1_antitone : AntitoneOn base1 strip := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
  · intro p hp
    exact (hasDerivAt_base1 hp).continuousAt.continuousWithinAt
  · intro p hp
    exact (hasDerivAt_base1 (interior_subset hp)).differentiableAt.differentiableWithinAt
  · intro p hp
    rw [(hasDerivAt_base1 (interior_subset hp)).deriv]
    exact (base1Slope_neg (interior_subset hp)).le

theorem base0_strip_upper {p : ℝ} (hp : p ∈ strip) : base0 p ≤ -(3 / 500 : ℝ) :=
  (base0_monotone hp (by norm_num [strip]) hp.2).trans base0_endpoint

theorem base1_strip_upper {p : ℝ} (hp : p ∈ strip) : base1 p ≤ -(147 / 1000 : ℝ) :=
  (base1_antitone (by norm_num [strip]) hp hp.1).trans base1_endpoint

end

end BerryEsseen.P39ModeBaselineMonotonicity

#print axioms BerryEsseen.P39ModeBaselineMonotonicity.base0_monotone
#print axioms BerryEsseen.P39ModeBaselineMonotonicity.phi1_upper
#print axioms BerryEsseen.P39ModeBaselineMonotonicity.negative_argumentSlope_bounds
#print axioms BerryEsseen.P39ModeBaselineMonotonicity.negative_rhoSlope_upper
#print axioms BerryEsseen.P39ModeBaselineMonotonicity.mass11_lower
#print axioms BerryEsseen.P39ModeBaselineMonotonicity.hasDerivAt_base1
#print axioms BerryEsseen.P39ModeBaselineMonotonicity.base1Slope_neg
#print axioms BerryEsseen.P39ModeBaselineMonotonicity.base1_antitone
#print axioms BerryEsseen.P39ModeBaselineMonotonicity.base0_strip_upper
#print axioms BerryEsseen.P39ModeBaselineMonotonicity.base1_strip_upper
