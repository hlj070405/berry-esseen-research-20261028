module

public import BerryEsseen.RationalReferencePrice
public import BerryEsseen.BinomialWeights
public import BerryEsseen.RationalGaussianPrices
public import BerryEsseen.P39Reference
public import BerryEsseen.AnalyticConstants

@[expose] public section

/-! 2026-10-29: Four original corners of the remaining count-10 box.
The reference is the actual 16+10 double-binomial law from pieces[3],
boxes[0] of result_b0_n26_p39_complete_merged_fresh_20261027.json.
Only point prices are proved here; no curvature or whole-box bound is assumed. -/

namespace BerryEsseen.N26P39Count10Prices

open MeasureTheory
open scoped BigOperators

set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

def b0Q : ℚ := 28411442497 / 500000000000
def z0Q : ℚ := 615144231 / 250000000000
def b1Q : ℚ := 119001 / 200000
def z1Q : ℚ := 47318787 / 50000000000
def deltaQ : ℚ := 5769 / 100000
def ciQ : ℚ := 803 / 10000
def pLQ : ℚ := 39 / 100
def pUQ : ℚ := 2 / 5
def tLQ : ℚ := -(1 / 8)
def tUQ : ℚ := 0

noncomputable def reference : Measure ℝ :=
  DoubleBinomialReference.law (b0Q : ℝ) (z0Q : ℝ) 16 (b1Q : ℝ) (z1Q : ℝ) 10
noncomputable def delta : ℝ := deltaQ
noncomputable def ci : ℝ := ciQ
noncomputable def eta (p : ℝ) : ℝ := BinomialWeights.mass 26 11 p / (1 - delta)
noncomputable def A (p : ℝ) : ℝ := (1 - delta) * (11 / 16) * (1 - p) / p
noncomputable def argument (p t : ℝ) : ℝ :=
  (10 + t - 26 * p) / Real.sqrt (26 * p * (1 - p))
noncomputable def price (p t : ℝ) : ℝ :=
  BinomialWeights.lowerPrefix 26 10 p + eta p * (t + StopLossShape.Q reference (A p + t)) -
    GaussianTools.Phi (argument p t) - ci * P39Reference.rho0 p

instance reference_isProbability : IsProbabilityMeasure reference :=
  DoubleBinomialReference.law_isProbabilityMeasure _ _ _ _ _ _
    (by norm_num [b0Q]) (by norm_num [z0Q]) (by norm_num [b1Q]) (by norm_num [z1Q])

theorem reference_integrable_sq : Integrable (fun z : ℝ => z ^ 2) reference :=
  DoubleBinomialReference.integrable_law _ _ _ _ _ _
    (by norm_num [b0Q]) (by norm_num [z0Q]) (by norm_num [b1Q]) (by norm_num [z1Q]) _

theorem reference_memLp_two : MemLp (fun z : ℝ => z) 2 reference :=
  DoubleBinomialReference.law_memLp_two _ _ _ _ _ _
    (by norm_num [b0Q]) (by norm_num [z0Q]) (by norm_num [b1Q]) (by norm_num [z1Q])

theorem ci_pos : 0 < ci := by norm_num [ci, ciQ]

theorem ci_le_target : ci ≤ esseenConstant / Real.sqrt (26 : ℝ) := by
  have hspos : 0 < Real.sqrt (26 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hs : Real.sqrt (26 : ℝ) ≤ (12749 / 2500 : ℝ) := by
    calc
      _ ≤ Real.sqrt ((12749 / 2500 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = _ := Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 12749 / 2500)
  apply (le_div_iff₀ hspos).mpr
  calc
    ci * Real.sqrt (26 : ℝ) ≤ ci * (12749 / 2500) := mul_le_mul_of_nonneg_left hs ci_pos.le
    _ ≤ (819 / 2000 : ℝ) := by norm_num [ci, ciQ]
    _ ≤ esseenConstant := AnalyticConstants.esseenConstant_gt_819_2000.le

theorem eta_nonneg {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) : 0 ≤ eta p :=
  div_nonneg (BinomialWeights.mass_nonneg _ _ p hp hp1) (by norm_num [delta, deltaQ])

def massQ (n k : ℕ) (p : ℚ) : ℚ := (n.choose k : ℚ) * p ^ k * (1 - p) ^ (n - k)
def prefixQ (p : ℚ) : ℚ := ∑ j ∈ Finset.range (10 + 1), massQ 26 j p
def etaQ (p : ℚ) : ℚ := massQ 26 11 p / (1 - deltaQ)
def thresholdQ (p t : ℚ) : ℚ := (1 - deltaQ) * (11 / 16) * (1 - p) / p + t
def varianceQ (p : ℚ) : ℚ := p * (1 - p)
def numeratorQ (p t : ℚ) : ℚ := 10 + t - 26 * p
def bernoulliNumeratorQ (p : ℚ) : ℚ := 1 - 2 * varianceQ p
def pointUpperQ (p t u z r : ℚ) : ℚ := prefixQ p + etaQ p * (t + u) -
  RationalGaussianPrices.PhiLower 8 z - ciQ * r

private theorem cast_massQ (n k : ℕ) (p : ℚ) :
    (massQ n k p : ℝ) = BinomialWeights.mass n k (p : ℝ) := by
  simp only [massQ, BinomialWeights.mass, Rat.cast_mul, Rat.cast_pow,
    Rat.cast_natCast, Rat.cast_sub, Rat.cast_one]

private theorem prefix_cast (p : ℚ) : (prefixQ p : ℝ) = BinomialWeights.lowerPrefix 26 10 (p : ℝ) := by
  unfold prefixQ BinomialWeights.lowerPrefix
  calc
    _ = ∑ j ∈ Finset.range (10 + 1), (massQ 26 j p : ℝ) := map_sum (Rat.castHom ℝ) _ _
    _ = _ := Finset.sum_congr rfl (fun j _ => cast_massQ 26 j p)

private theorem eta_cast (p : ℚ) : (etaQ p : ℝ) = eta (p : ℝ) := by
  simp only [etaQ, eta, delta, Rat.cast_div, Rat.cast_sub, Rat.cast_one, cast_massQ]

theorem threshold_cast (p t : ℚ) : (thresholdQ p t : ℝ) = A (p : ℝ) + (t : ℝ) := by
  simp only [thresholdQ, A, delta, Rat.cast_add, Rat.cast_mul, Rat.cast_sub,
    Rat.cast_div, Rat.cast_ofNat, Rat.cast_one]

private theorem variance_cast (p : ℚ) : (varianceQ p : ℝ) = P39Reference.v (p : ℝ) := by
  simp only [varianceQ, P39Reference.v, Rat.cast_mul, Rat.cast_sub, Rat.cast_one]

private theorem bernoulli_numerator_cast (p : ℚ) :
    (bernoulliNumeratorQ p : ℝ) = 1 - 2 * P39Reference.v (p : ℝ) := by
  simp only [bernoulliNumeratorQ, Rat.cast_sub, Rat.cast_mul,
    Rat.cast_one, Rat.cast_ofNat, variance_cast]

/-- A negative Gaussian argument uses a square comparison with the correct
sign, not a square-root upper bound that would reverse the desired inequality. -/
private theorem argument_lower_checked (p t z : ℚ) (hp0 : 0 < p) (hp1 : p < 1)
    (hz : z ≤ 0) (hn : numeratorQ p t ≤ 0)
    (hc : numeratorQ p t ^ 2 ≤ 26 * varianceQ p * z ^ 2) :
    (z : ℝ) ≤ argument (p : ℝ) (t : ℝ) := by
  have hp0R : (0 : ℝ) < p := by exact_mod_cast hp0
  have hp1R : (p : ℝ) < 1 := by exact_mod_cast hp1
  have hv : 0 < (26 : ℝ) * (p : ℝ) * (1 - (p : ℝ)) := by positivity
  have hzR : (z : ℝ) ≤ 0 := by exact_mod_cast hz
  have hnR : 10 + (t : ℝ) - 26 * (p : ℝ) ≤ 0 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hn
    simpa only [numeratorQ, Rat.cast_add, Rat.cast_sub, Rat.cast_mul,
      Rat.cast_ofNat, Rat.cast_zero] using h
  have hcheck := (Rat.cast_le (K := ℝ)).mpr hc
  simp only [numeratorQ, varianceQ, Rat.cast_pow, Rat.cast_mul, Rat.cast_add,
    Rat.cast_sub, Rat.cast_ofNat, Rat.cast_one] at hcheck
  have hsq : (-(10 + (t : ℝ) - 26 * (p : ℝ))) ^ 2 ≤
      (-(z : ℝ) * Real.sqrt (26 * (p : ℝ) * (1 - (p : ℝ)))) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hv.le]
    nlinarith only [hcheck]
  have hmag := (sq_le_sq₀ (neg_nonneg.mpr hnR)
    (mul_nonneg (neg_nonneg.mpr hzR) (Real.sqrt_nonneg _))).mp hsq
  unfold argument
  apply (le_div_iff₀ (Real.sqrt_pos.mpr hv)).mpr
  nlinarith only [hmag]

private theorem rho_lower_checked (p r : ℚ) (hp0 : 0 < p) (hp1 : p < 1)
    (hr : 0 ≤ r) (hk : 0 ≤ bernoulliNumeratorQ p)
    (hc : varianceQ p * r ^ 2 ≤ bernoulliNumeratorQ p ^ 2) :
    (r : ℝ) ≤ P39Reference.rho0 (p : ℝ) := by
  have hp0R : (0 : ℝ) < p := by exact_mod_cast hp0
  have hp1R : (p : ℝ) < 1 := by exact_mod_cast hp1
  have hv := P39Reference.v_pos hp0R hp1R
  have hrR : (0 : ℝ) ≤ r := by exact_mod_cast hr
  have hkR := (Rat.cast_nonneg (K := ℝ)).mpr hk
  rw [bernoulli_numerator_cast] at hkR
  have hcheck := (Rat.cast_le (K := ℝ)).mpr hc
  simp only [Rat.cast_mul, Rat.cast_pow, variance_cast, bernoulli_numerator_cast] at hcheck
  have hsq : ((r : ℝ) * Real.sqrt (P39Reference.v (p : ℝ))) ^ 2 ≤
      (1 - 2 * P39Reference.v (p : ℝ)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hv.le]
    nlinarith only [hcheck]
  unfold P39Reference.rho0
  apply (le_div_iff₀ (Real.sqrt_pos.mpr hv)).mpr
  exact (sq_le_sq₀ (mul_nonneg hrR (Real.sqrt_nonneg _)) hkR).mp hsq

private theorem Q_le_checked (p t h u : ℚ) (hh : 0 < h)
    (hc : RationalReferencePrice.rationalPrice b0Q z0Q 16 b1Q z1Q 10 (thresholdQ p t) h ≤ u) :
    StopLossShape.Q reference (A (p : ℝ) + (t : ℝ)) ≤ (u : ℝ) := by
  have hq := RationalReferencePrice.Q_le_of_rational_bound b0Q z0Q 16 b1Q z1Q 10
    (thresholdQ p t) h u (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) hh hc
  rw [threshold_cast] at hq
  exact hq

/-- All arithmetic obligations of a point, including the literal reference
price, are rational and hence directly decidable in the kernel. -/
def NumericChecks (p t h u z r bound : ℚ) : Prop :=
  0 < p ∧ p < 1 ∧ 0 < h ∧ z ≤ 0 ∧ numeratorQ p t ≤ 0 ∧
    numeratorQ p t ^ 2 ≤ 26 * varianceQ p * z ^ 2 ∧
    0 ≤ r ∧ 0 ≤ bernoulliNumeratorQ p ∧
    varianceQ p * r ^ 2 ≤ bernoulliNumeratorQ p ^ 2 ∧
    RationalReferencePrice.rationalPrice b0Q z0Q 16 b1Q z1Q 10 (thresholdQ p t) h ≤ u ∧
    pointUpperQ p t u z r ≤ bound

private theorem price_le_checked (p t h u z r bound : ℚ) (hc : NumericChecks p t h u z r bound) :
    price (p : ℝ) (t : ℝ) ≤ (bound : ℝ) := by
  rcases hc with ⟨hp0, hp1, hh, hz, hn, hgauss, hr, hk, hrho, hq, hbound⟩
  have hp0R : (0 : ℝ) < p := by exact_mod_cast hp0
  have hp1R : (p : ℝ) < 1 := by exact_mod_cast hp1
  have hQ := mul_le_mul_of_nonneg_left (Q_le_checked p t h u hh hq)
    (eta_nonneg hp0R.le hp1R.le)
  have harg := argument_lower_checked p t z hp0 hp1 hz hn hgauss
  have hm : Monotone GaussianTools.Phi := fun a b hab => measureReal_mono (Set.Iic_subset_Iic.mpr hab)
  have hPhi := (RationalGaussianPrices.Phi_rational_bounds 8 z).1.trans (hm harg)
  have hRho := mul_le_mul_of_nonneg_left (rho_lower_checked p r hp0 hp1 hr hk hrho) ci_pos.le
  have hreal := (Rat.cast_le (K := ℝ)).mpr hbound
  have hcast : (pointUpperQ p t u z r : ℝ) = BinomialWeights.lowerPrefix 26 10 (p : ℝ) +
      eta (p : ℝ) * ((t : ℝ) + (u : ℝ)) - (RationalGaussianPrices.PhiLower 8 z : ℝ) - ci * (r : ℝ) := by
    simp only [pointUpperQ, ci, Rat.cast_add, Rat.cast_sub, Rat.cast_mul, prefix_cast, eta_cast]
  rw [hcast] at hreal
  unfold price
  linarith only [hQ, hPhi, hRho, hreal]

theorem thresholds_exact :
    thresholdQ pLQ tLQ = 55429001 / 62400000 ∧ thresholdQ pUQ tLQ = 2709623 / 3200000 ∧
    thresholdQ pLQ tUQ = 63229001 / 62400000 ∧ thresholdQ pUQ tUQ = 3109623 / 3200000 := by
  decide +kernel

theorem checks_lower_left : NumericChecks pLQ tLQ (124763 / 1000000) (327 / 1000000)
    (-(106553 / 1000000)) (1074731 / 1000000) (-(28 / 100000)) := by
  unfold NumericChecks
  decide +kernel
theorem checks_lower_right : NumericChecks pUQ tLQ (63623 / 500000) (57 / 125000)
    (-(210169 / 1000000)) (212289 / 200000) (-(82 / 100000)) := by
  unfold NumericChecks
  decide +kernel
theorem checks_upper_left : NumericChecks pLQ tUQ (33159 / 250000) (123 / 1000000)
    (-(14073 / 250000)) (1074731 / 1000000) (-(69 / 100000)) := by
  unfold NumericChecks
  decide +kernel
theorem checks_upper_right : NumericChecks pUQ tUQ (124427 / 1000000) (17 / 100000)
    (-(160129 / 1000000)) (212289 / 200000) (-(28 / 100000)) := by
  unfold NumericChecks
  decide +kernel

theorem corner_lower_left : price (39 / 100) (-(1 / 8)) ≤ -(28 / 100000) := by
  have h := price_le_checked _ _ _ _ _ _ _ checks_lower_left
  simpa only [pLQ, tLQ, Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using h

theorem corner_lower_right : price (2 / 5) (-(1 / 8)) ≤ -(82 / 100000) := by
  have h := price_le_checked _ _ _ _ _ _ _ checks_lower_right
  simpa only [pUQ, tLQ, Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using h

theorem corner_upper_left : price (39 / 100) 0 ≤ -(69 / 100000) := by
  have h := price_le_checked _ _ _ _ _ _ _ checks_upper_left
  simpa only [pLQ, tUQ, Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero] using h

theorem corner_upper_right : price (2 / 5) 0 ≤ -(28 / 100000) := by
  have h := price_le_checked _ _ _ _ _ _ _ checks_upper_right
  simpa only [pUQ, tUQ, Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero] using h

theorem Q_at_lower_right : StopLossShape.Q reference (A (2 / 5) - 1 / 8) ≤ (57 / 125000) := by
  rcases checks_lower_right with ⟨_, _, hh, _, _, _, _, _, _, hq, _⟩
  have h := Q_le_checked pUQ tLQ (63623 / 500000) (57 / 125000) hh hq
  simpa only [pUQ, tLQ, Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one,
    sub_eq_add_neg, neg_div] using h

theorem Q_le_mill_of_threshold {a : ℝ} (ha : A (2 / 5) - 1 / 8 ≤ a) :
    StopLossShape.Q reference a ≤ 1 / 1000 := by
  have hanti := StopLossShape.Q_antitone reference reference_integrable_sq
  exact ((hanti ha).trans Q_at_lower_right).trans (by norm_num)

end BerryEsseen.N26P39Count10Prices

#print axioms BerryEsseen.N26P39Count10Prices.reference_integrable_sq
#print axioms BerryEsseen.N26P39Count10Prices.ci_le_target
#print axioms BerryEsseen.N26P39Count10Prices.checks_lower_left
#print axioms BerryEsseen.N26P39Count10Prices.checks_lower_right
#print axioms BerryEsseen.N26P39Count10Prices.checks_upper_left
#print axioms BerryEsseen.N26P39Count10Prices.checks_upper_right
#print axioms BerryEsseen.N26P39Count10Prices.corner_lower_left
#print axioms BerryEsseen.N26P39Count10Prices.corner_lower_right
#print axioms BerryEsseen.N26P39Count10Prices.corner_upper_left
#print axioms BerryEsseen.N26P39Count10Prices.corner_upper_right
#print axioms BerryEsseen.N26P39Count10Prices.Q_le_mill_of_threshold
