module

public import BerryEsseen.N26P39Price
public import BerryEsseen.BinomialWeights
public import BerryEsseen.ProbabilityGaussianPrice
public import BerryEsseen.P39NoiseGate

@[expose] public section

/-! 2026-10-29: continuous count-11, t=0 scalar face on the original
P39 probability/noise strip. The reference measure is exactly the frozen
N26P39Price.reference. Probability and noise are controlled analytically;
only the previously proved one-width reference price is used. Original
law support acquisition and inward budgets are not replaced by reference caps. -/

namespace BerryEsseen.P39Count11Face

open MeasureTheory Set Filter
open GaussianTools BinomialWeights
open scoped BigOperators Topology

noncomputable section

def strip : Set ℝ := Icc (39 / 100) (2 / 5)
def delta : ℝ := (N26P39Price.inward : ℝ)
def lambdaUpper : ℝ := 7677 / 200000
def eta (p : ℝ) : ℝ := (3 : ℝ) / 2 * mass 26 12 p / (1 - delta)
def threshold (p : ℝ) : ℝ := (N26P39Price.CA : ℝ) * (1 - p) / p
def base (p l : ℝ) : ℝ :=
  lowerPrefix 26 11 p - Phi (P39NoiseGate.noiseArgument p 11 l) - (2 : ℝ) / 25 * P39Reference.rho0 p
def face (p l : ℝ) : ℝ :=
  base p l + eta p * StopLossShape.Q N26P39Price.reference (threshold p)

lemma domain {p : ℝ} (hp : p ∈ strip) : 0 < p ∧ p < 1 := P39Reference.positive_domain hp

lemma delta_lt_one : delta < 1 := by norm_num [delta, N26P39Price.inward]

lemma numerator_bounds {p : ℝ} (hp : p ∈ strip) :
    (3 : ℝ) / 5 ≤ 11 - 26 * p ∧ 11 - 26 * p ≤ 43 / 50 := by
  constructor <;> linarith only [hp.1, hp.2]

lemma zero_variance_bounds {p : ℝ} (hp : p ∈ strip) :
    (91 : ℝ) / 15 ≤ 26 * P39Reference.v p ∧ 26 * P39Reference.v p ≤ 156 / 25 := by
  have hv := P39NoiseGate.variance_bounds hp
  constructor <;> linarith only [hv.1, hv.2]

lemma zero_sqrt_bounds {p : ℝ} (hp : p ∈ strip) :
    (86 : ℝ) / 35 ≤ Real.sqrt (26 * P39Reference.v p) ∧
      Real.sqrt (26 * P39Reference.v p) ≤ 5 / 2 := by
  have hv := zero_variance_bounds hp
  have hv0 : 0 ≤ 26 * P39Reference.v p := by linarith only [hv.1]
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num
    linarith only [hv.1]
  · have hs := Real.sq_sqrt hv0
    nlinarith only [hs, Real.sqrt_nonneg (26 * P39Reference.v p), hv.2]

lemma zero_argument_bounds {p : ℝ} (hp : p ∈ strip) :
    (6 : ℝ) / 25 ≤ P39NoiseGate.noiseArgument p 11 0 ∧
      P39NoiseGate.noiseArgument p 11 0 ≤ 7 / 20 := by
  have hN := numerator_bounds hp
  have hs := zero_sqrt_bounds hp
  have hs0 : 0 < Real.sqrt (26 * P39Reference.v p) := by linarith only [hs.1]
  simp only [P39NoiseGate.noiseArgument, add_zero]
  constructor
  · apply (le_div_iff₀ hs0).mpr
    linarith only [hs.2, hN.1]
  · apply (div_le_iff₀ hs0).mpr
    linarith only [hs.1, hN.2]

lemma zero_phi_lower {p : ℝ} (hp : p ∈ strip) :
    (183 : ℝ) / 500 ≤ phi (P39NoiseGate.noiseArgument p 11 0) := by
  have hz := zero_argument_bounds hp
  have hz0 : 0 ≤ P39NoiseGate.noiseArgument p 11 0 := by linarith only [hz.1]
  have h := GaussianPrices.phi_lower_on_unit _ hz0 (by linarith only [hz.2])
  have hsq := (sq_le_sq₀ hz0 (by norm_num : (0 : ℝ) ≤ 7 / 20)).mpr hz.2
  nlinarith only [h, hsq]

lemma argument_zero_eq (p : ℝ) :
    ProbabilityGaussianPrice.argument 26 11 0 0 p = P39NoiseGate.noiseArgument p 11 0 := by
  simp only [ProbabilityGaussianPrice.argument, ProbabilityGaussianPrice.numerator,
    ProbabilityGaussianPrice.variance, P39NoiseGate.noiseArgument, P39Reference.v,
    Nat.cast_ofNat, add_zero]

lemma negative_argumentSlope_lower {p : ℝ} (hp : p ∈ strip) :
    (52 : ℝ) / 5 ≤ -ProbabilityGaussianPrice.argumentSlope 26 11 0 0 p := by
  have hN := numerator_bounds hp
  have hv := zero_variance_bounds hp
  have hs := zero_sqrt_bounds hp
  have hv0 : 0 < 26 * P39Reference.v p := by linarith only [hv.1]
  have hs0 : 0 < Real.sqrt (26 * P39Reference.v p) := by linarith only [hs.1]
  have hfirst : (52 : ℝ) / 5 ≤ 26 / Real.sqrt (26 * P39Reference.v p) := by
    apply (le_div_iff₀ hs0).mpr
    linarith only [hs.2]
  have hsecond : 0 ≤ (11 - 26 * p) * (26 * (1 - 2 * p)) /
      (2 * (26 * P39Reference.v p) * Real.sqrt (26 * P39Reference.v p)) := by
    apply div_nonneg
    · exact mul_nonneg (by linarith only [hN.1]) (by linarith only [hp.2])
    · positivity
  have hfinal : (52 : ℝ) / 5 ≤ -(-26 / Real.sqrt (26 * P39Reference.v p) -
      (11 - 26 * p) * (26 * (1 - 2 * p)) /
        (2 * (26 * P39Reference.v p) * Real.sqrt (26 * P39Reference.v p))) := by
    calc
      _ ≤ 26 / Real.sqrt (26 * P39Reference.v p) := hfirst
      _ ≤ 26 / Real.sqrt (26 * P39Reference.v p) +
          (11 - 26 * p) * (26 * (1 - 2 * p)) /
            (2 * (26 * P39Reference.v p) * Real.sqrt (26 * P39Reference.v p)) :=
        le_add_of_nonneg_right hsecond
      _ = _ := by ring
  simpa only [ProbabilityGaussianPrice.argumentSlope, ProbabilityGaussianPrice.numerator,
    ProbabilityGaussianPrice.variance, ProbabilityGaussianPrice.varianceSlope,
    Nat.cast_ofNat, add_zero, P39Reference.v] using hfinal

theorem mass_monotone (k : ℕ) (hk : k ≤ 26) (hmode : (52 : ℝ) / 5 ≤ k) :
    MonotoneOn (mass 26 k) strip := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
  · intro p hp
    exact (hasDerivAt_mass 26 k p (domain hp).1 (domain hp).2 hk).continuousAt.continuousWithinAt
  · intro p hp
    have hd := domain (interior_subset hp)
    exact (hasDerivAt_mass 26 k p hd.1 hd.2 hk).differentiableAt.differentiableWithinAt
  · intro p hp
    have hi := interior_subset hp
    have hd := domain hi
    rw [(hasDerivAt_mass 26 k p hd.1 hd.2 hk).deriv]
    unfold massSlope
    apply div_nonneg
    · exact mul_nonneg (mass_nonneg 26 k p hd.1.le hd.2.le) (by norm_num; linarith only [hmode, hi.2])
    · exact mul_nonneg hd.1.le (sub_nonneg.mpr hd.2.le)

private def rationalMass (k : ℕ) : ℚ := ((26 : ℕ).choose k : ℚ) * (2 / 5) ^ k * (3 / 5) ^ (26 - k)
private def rationalPrefix : ℚ := ∑ j ∈ Finset.range 12, rationalMass j

private lemma cast_rationalMass (k : ℕ) : (rationalMass k : ℝ) = mass 26 k (2 / 5) := by
  simp only [rationalMass, mass, Rat.cast_mul, Rat.cast_natCast, Rat.cast_pow, Rat.cast_div, Rat.cast_ofNat]
  norm_num

private lemma cast_rationalPrefix : (rationalPrefix : ℝ) = lowerPrefix 26 11 (2 / 5) := by
  unfold rationalPrefix lowerPrefix
  rw [show ((∑ j ∈ Finset.range 12, rationalMass j : ℚ) : ℝ) =
    ∑ j ∈ Finset.range 12, (rationalMass j : ℝ) from map_sum (Rat.castHom ℝ) _ _]
  simp only [cast_rationalMass]

private lemma rationalMass11_upper : rationalMass 11 ≤ (381 : ℚ) / 2500 := by
  norm_num [rationalMass, Nat.choose_eq_factorial_div_factorial]

lemma mass11_upper {p : ℝ} (hp : p ∈ strip) : mass 26 11 p ≤ (381 : ℝ) / 2500 := by
  have he : mass 26 11 (2 / 5) ≤ (381 : ℝ) / 2500 := by
    rw [← cast_rationalMass]
    simpa only [Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr rationalMass11_upper
  exact ((mass_monotone 11 (by norm_num) (by norm_num)) hp (by norm_num [strip]) hp.2).trans he

lemma prefixSlope_lower {p : ℝ} (hp : p ∈ strip) : (-381 : ℝ) / 100 ≤ prefixSlope 26 11 p := by
  have hq : 0 < 1 - p := sub_pos.mpr (domain hp).2
  have hm := mass11_upper hp
  change (-381 : ℝ) / 100 ≤ -15 * mass 26 11 p / (1 - p)
  apply (le_div_iff₀ hq).mpr
  linarith only [hm, hp.2]

def baseSlope (p : ℝ) : ℝ := prefixSlope 26 11 p -
  ProbabilityGaussianPrice.gaussianPriceSlope 26 11 0 0 p - (2 : ℝ) / 25 * P39Reference.e1 p

theorem hasDerivAt_base_zero {p : ℝ} (hp : p ∈ strip) :
    HasDerivAt (fun q => base q 0) (baseSlope p) p := by
  have hd := domain hp
  have hF := hasDerivAt_prefix 26 11 p hd.1 hd.2 (by norm_num)
  have hG := ProbabilityGaussianPrice.gaussianPrice_hasDerivAt (n := 26) (k := 11) (t := 0) (s := 0)
    (by norm_num) (by norm_num) ⟨hd.1, hd.2⟩
  have hR := (P39Reference.hasDerivAt_rho0 hd.1 hd.2).const_mul ((2 : ℝ) / 25)
  convert (hF.fun_sub hG).fun_sub hR using 1
  · funext q
    simp only [base, ProbabilityGaussianPrice.gaussianPrice, argument_zero_eq]
  · rfl

theorem baseSlope_lower {p : ℝ} (hp : p ∈ strip) : (9 : ℝ) / 100 ≤ baseSlope p := by
  have hF := prefixSlope_lower hp
  have hG := mul_le_mul (zero_phi_lower hp) (negative_argumentSlope_lower hp)
    (by norm_num : (0 : ℝ) ≤ 52 / 5) (phi_nonneg (P39NoiseGate.noiseArgument p 11 0))
  have hR := (P39Reference.e1_bounds hp).2
  unfold baseSlope ProbabilityGaussianPrice.gaussianPriceSlope
  rw [argument_zero_eq]
  nlinarith only [hF, hG, hR]

theorem base_zero_monotone : MonotoneOn (fun p => base p 0) strip := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
  · intro p hp
    exact (hasDerivAt_base_zero hp).continuousAt.continuousWithinAt
  · intro p hp
    exact (hasDerivAt_base_zero (interior_subset hp)).differentiableAt.differentiableWithinAt
  · intro p hp
    rw [(hasDerivAt_base_zero (interior_subset hp)).deriv]
    linarith only [baseSlope_lower (interior_subset hp)]

lemma phi_upper (x : ℝ) : phi x ≤ (2 : ℝ) / 5 := by
  calc
    _ ≤ phi 0 := by
      rw [GaussianPrices.phi_eq_phi_zero_mul_exp]
      have he : Real.exp (-(x ^ 2 / 2)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith only [sq_nonneg x])
      simpa only [mul_one] using mul_le_mul_of_nonneg_left he (phi_nonneg 0)
    _ ≤ 2 / 5 := GaussianPrices.phi_zero_lt_2_5.le

/-- The count is 11 here. The older noise gate for counts at most 10.5
is not used; this larger positive Gaussian slope is bounded directly. -/
lemma noiseSlope_upper {p l : ℝ} (hp : p ∈ strip) (hl : 0 ≤ l) :
    P39NoiseGate.gaussianSlope p 11 l ≤ (1 : ℝ) / 80 := by
  let V := 26 * P39Reference.v p + l
  have hV : 6 ≤ V := by dsimp only [V]; linarith only [(zero_variance_bounds hp).1, hl]
  have hV0 : 0 < V := by linarith only [hV]
  have hs : (12 : ℝ) / 5 ≤ Real.sqrt V := by
    apply Real.le_sqrt_of_sq_le
    norm_num
    linarith only [hV]
  have hnum : phi (P39NoiseGate.noiseArgument p 11 l) * (11 - 26 * p) ≤ (43 : ℝ) / 125 := by
    calc
      _ ≤ phi (P39NoiseGate.noiseArgument p 11 l) * (43 / 50) :=
        mul_le_mul_of_nonneg_left (numerator_bounds hp).2 (phi_nonneg _)
      _ ≤ (2 / 5) * (43 / 50) := mul_le_mul_of_nonneg_right (phi_upper _) (by norm_num)
      _ = _ := by norm_num
  have hden : (144 : ℝ) / 5 ≤ 2 * V * Real.sqrt V := by
    have hh := mul_le_mul hV hs (by norm_num : (0 : ℝ) ≤ 12 / 5) hV0.le
    nlinarith only [hh]
  change phi (P39NoiseGate.noiseArgument p 11 l) * (11 - 26 * p) /
    (2 * V * Real.sqrt V) ≤ (1 : ℝ) / 80
  apply (div_le_iff₀ (by positivity : 0 < 2 * V * Real.sqrt V)).mpr
  nlinarith only [hnum, hden]

def noisePart (p l : ℝ) : ℝ := -Phi (P39NoiseGate.noiseArgument p 11 l)

lemma hasDerivAt_noisePart {p l : ℝ} (hp : p ∈ strip) (hl : 0 ≤ l) :
    HasDerivAt (noisePart p) (P39NoiseGate.gaussianSlope p 11 l) l := by
  have hV := P39NoiseGate.actual_variance_pos hp hl
  have h := ((hasDerivAt_Phi (P39NoiseGate.noiseArgument p 11 l)).comp l
    (P39NoiseGate.hasDerivAt_noiseArgument hV)).neg
  convert h using 1
  · funext z; rfl
  · unfold P39NoiseGate.gaussianSlope
    ring

theorem base_noise_increment {p l : ℝ} (hp : p ∈ strip) (hl : 0 ≤ l) :
    base p l ≤ base p 0 + l / 80 := by
  have hd : ∀ x ∈ Icc (0 : ℝ) l,
      HasDerivAt (fun u => noisePart p u - u / 80)
        (P39NoiseGate.gaussianSlope p 11 x - 1 / 80) x := by
    intro x hx
    exact (hasDerivAt_noisePart hp hx.1).fun_sub ((hasDerivAt_id' x).div_const 80)
  have hm : AntitoneOn (fun u => noisePart p u - u / 80) (Icc (0 : ℝ) l) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
    · exact fun x hx => (hd x hx).continuousAt.continuousWithinAt
    · exact fun x hx => (hd x (interior_subset hx)).hasDerivWithinAt
    · intro x hx
      exact sub_nonpos.mpr (noiseSlope_upper hp (interior_subset hx).1)
  have h := hm ⟨le_rfl, hl⟩ ⟨hl, le_rfl⟩ hl
  change noisePart p l - l / 80 ≤ noisePart p 0 - 0 / 80 at h
  unfold base
  unfold noisePart at h
  linarith only [h]

lemma eta_nonneg {p : ℝ} (hp : p ∈ strip) : 0 ≤ eta p :=
  div_nonneg (mul_nonneg (by norm_num) (mass_nonneg 26 12 p (domain hp).1.le (domain hp).2.le))
    (sub_nonneg.mpr delta_lt_one.le)

lemma eta_endpoint_upper {p : ℝ} (hp : p ∈ strip) : eta p ≤ eta (2 / 5) := by
  have hm := (mass_monotone 12 (by norm_num) (by norm_num)) hp (by norm_num [strip]) hp.2
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hm (by norm_num))
    (sub_nonneg.mpr delta_lt_one.le)

lemma CA_nonneg : 0 ≤ (N26P39Price.CA : ℝ) := by
  norm_num [N26P39Price.CA, N26P39Price.inward, N26P39Price.slopeMultiplier]

lemma threshold_endpoint : threshold (2 / 5) = (N26P39Price.threshold : ℝ) := by
  norm_num [threshold, N26P39Price.threshold, N26P39Price.pUpper]

lemma threshold_endpoint_lower {p : ℝ} (hp : p ∈ strip) : threshold (2 / 5) ≤ threshold p := by
  have hp0 := (domain hp).1
  unfold threshold
  apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2 / 5) hp0).mpr
  nlinarith only [mul_nonneg CA_nonneg (sub_nonneg.mpr hp.2)]

lemma reference_probability : IsProbabilityMeasure N26P39Price.reference := by
  exact DoubleBinomialReference.law_isProbabilityMeasure _ _ _ _ _ _
    (by norm_num [N26P39Price.b0]) (by norm_num [N26P39Price.z0])
    (by norm_num [N26P39Price.b1]) (by norm_num [N26P39Price.z1])

lemma reference_square_integrable : Integrable (fun z : ℝ => z ^ 2) N26P39Price.reference := by
  exact DoubleBinomialReference.integrable_law _ _ _ _ _ _
    (by norm_num [N26P39Price.b0]) (by norm_num [N26P39Price.z0])
    (by norm_num [N26P39Price.b1]) (by norm_num [N26P39Price.z1]) _

theorem frozen_Q_term_upper {p : ℝ} (hp : p ∈ strip) :
    eta p * StopLossShape.Q N26P39Price.reference (threshold p) ≤
      eta (2 / 5) * (N26P39Price.upper : ℝ) := by
  have := reference_probability
  have hQ := (StopLossShape.Q_antitone N26P39Price.reference reference_square_integrable
    (threshold_endpoint_lower hp)).trans (by simpa only [threshold_endpoint] using N26P39Price.actual_Q_upper)
  exact mul_le_mul (eta_endpoint_upper hp) hQ
    (StopLossShape.Q_nonneg _ _) (eta_nonneg (by norm_num [strip]))

private def gaussianFloor : ℚ := 1 / 2 + (39 : ℚ) / 100 * (6 / 25 - (6 / 25) ^ 3 / 6)
private def rhoFloor : ℚ := 530722777603 / 500000000000
private def endpointResidual : ℚ := rationalPrefix - gaussianFloor - (2 : ℚ) / 25 * rhoFloor +
  ((3 : ℚ) / 2 * rationalMass 12 / (1 - N26P39Price.inward)) * N26P39Price.upper +
  (7677 : ℚ) / 200000 / 80

set_option maxRecDepth 20000 in
private lemma endpoint_certificate : endpointResidual ≤ (-1 : ℚ) / 400 := by
  unfold endpointResidual rationalPrefix rationalMass gaussianFloor rhoFloor N26P39Price.inward N26P39Price.upper
  decide +kernel

private lemma endpoint_Phi_lower : (gaussianFloor : ℝ) ≤ Phi (P39NoiseGate.noiseArgument (2 / 5) 11 0) := by
  have h := GaussianPrices.Phi_lower_on_unit (6 / 25 : ℝ) (by norm_num) (by norm_num)
  have hm : Phi (6 / 25) ≤ Phi (P39NoiseGate.noiseArgument (2 / 5) 11 0) :=
    measureReal_mono (Iic_subset_Iic.mpr (zero_argument_bounds (by norm_num [strip])).1)
  have heq : (gaussianFloor : ℝ) = (1 : ℝ) / 2 + (39 : ℝ) / 100 * (6 / 25 - (6 / 25) ^ 3 / 6) := by
    norm_num [gaussianFloor]
  rw [heq]
  exact h.trans hm

private lemma endpoint_numeric_bound : lowerPrefix 26 11 (2 / 5) - (gaussianFloor : ℝ) -
    (2 : ℝ) / 25 * (rhoFloor : ℝ) + eta (2 / 5) * (N26P39Price.upper : ℝ) + lambdaUpper / 80 ≤
      (-1 : ℝ) / 400 := by
  have h := (Rat.cast_le (K := ℝ)).mpr endpoint_certificate
  have heq : (endpointResidual : ℝ) = lowerPrefix 26 11 (2 / 5) - (gaussianFloor : ℝ) -
      (2 : ℝ) / 25 * (rhoFloor : ℝ) + eta (2 / 5) * (N26P39Price.upper : ℝ) + lambdaUpper / 80 := by
    simp only [endpointResidual, Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div,
      Rat.cast_ofNat, Rat.cast_one, cast_rationalPrefix, cast_rationalMass, eta, delta, lambdaUpper]
  rw [heq] at h
  simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_one, Rat.cast_ofNat] using h

/-- The whole continuous scalar face uses the same frozen reference
measure at every p and l. No original-law acquisition premise is inferred. -/
theorem whole_face {p l : ℝ} (hp : p ∈ strip) (hl : l ∈ Icc (0 : ℝ) lambdaUpper) :
    face p l ≤ (-1 : ℝ) / 400 := by
  have hb := base_noise_increment hp hl.1
  have hmono := base_zero_monotone hp (by norm_num [strip]) hp.2
  change base p 0 ≤ base (2 / 5) 0 at hmono
  have hQ := frozen_Q_term_upper hp
  have hPhi := endpoint_Phi_lower
  have hρ : (rhoFloor : ℝ) ≤ P39Reference.rho0 (2 / 5) := by
    simpa only [rhoFloor, Rat.cast_div, Rat.cast_ofNat] using P39Reference.endpoint_floor
  have hnum := endpoint_numeric_bound
  unfold face base at *
  linarith only [hb, hmono, hQ, hPhi, hρ, hnum, hl.2]

/-- Literal expanded form of the count-11, t=0 continuous price. -/
theorem whole_face_explicit {p l : ℝ}
    (hp : p ∈ Icc (39 / 100 : ℝ) (2 / 5)) (hl : l ∈ Icc (0 : ℝ) (7677 / 200000)) :
    lowerPrefix 26 11 p - Phi ((11 - 26 * p) / Real.sqrt (26 * (p * (1 - p)) + l)) -
      (2 : ℝ) / 25 * P39Reference.rho0 p +
      ((3 : ℝ) / 2 * mass 26 12 p / (1 - 5769 / 100000)) *
        StopLossShape.Q N26P39Price.reference ((N26P39Price.CA : ℝ) * (1 - p) / p) ≤
          (-1 : ℝ) / 400 := by
  simpa only [face, base, eta, threshold, delta, N26P39Price.inward, Rat.cast_div, Rat.cast_ofNat,
    P39NoiseGate.noiseArgument, P39Reference.v] using whole_face hp hl

/-! Wider reusable baseline statements. The reference price is not varied
here, and no new comparison with a common-cap reference is asserted. -/

lemma scaled_variance (p l : ℝ) :
    ProbabilityGaussianPrice.variance 26 (l / 26) p = 26 * P39Reference.v p + l := by
  unfold ProbabilityGaussianPrice.variance P39Reference.v
  norm_num only [Nat.cast_ofNat]
  ring

lemma argument_noise_eq (p l : ℝ) :
    ProbabilityGaussianPrice.argument 26 11 0 (l / 26) p = P39NoiseGate.noiseArgument p 11 l := by
  unfold ProbabilityGaussianPrice.argument
  rw [scaled_variance]
  simp only [ProbabilityGaussianPrice.numerator, P39NoiseGate.noiseArgument, Nat.cast_ofNat, add_zero]

lemma noisy_phi_lower {p l : ℝ} (hp : p ∈ strip) (hl : 0 ≤ l) :
    (183 : ℝ) / 500 ≤ phi (P39NoiseGate.noiseArgument p 11 l) := by
  have hV : (91 : ℝ) / 15 ≤ 26 * P39Reference.v p + l :=
    (zero_variance_bounds hp).1.trans (le_add_of_nonneg_right hl)
  have hs : (86 : ℝ) / 35 ≤ Real.sqrt (26 * P39Reference.v p + l) := by
    apply Real.le_sqrt_of_sq_le
    norm_num
    linarith only [hV]
  have hs0 : 0 < Real.sqrt (26 * P39Reference.v p + l) := by linarith only [hs]
  have hz0 : 0 ≤ P39NoiseGate.noiseArgument p 11 l :=
    div_nonneg (by linarith only [(numerator_bounds hp).1]) hs0.le
  have hz : P39NoiseGate.noiseArgument p 11 l ≤ (7 : ℝ) / 20 := by
    apply (div_le_iff₀ hs0).mpr
    linarith only [hs, (numerator_bounds hp).2]
  have h := GaussianPrices.phi_lower_on_unit _ hz0 (by linarith only [hz])
  have hsq := (sq_le_sq₀ hz0 (by norm_num : (0 : ℝ) ≤ 7 / 20)).mpr hz
  nlinarith only [h, hsq]

lemma wide_negative_argumentSlope_lower {p l : ℝ} (hp : p ∈ strip) (hl : l ∈ Icc (0 : ℝ) (1 / 4)) :
    (520 : ℝ) / 51 ≤ -ProbabilityGaussianPrice.argumentSlope 26 11 0 (l / 26) p := by
  let V := 26 * P39Reference.v p + l
  have hV : (91 : ℝ) / 15 ≤ V ∧ V ≤ 649 / 100 := by
    dsimp only [V]
    constructor <;> linarith only [(zero_variance_bounds hp).1, (zero_variance_bounds hp).2, hl.1, hl.2]
  have hV0 : 0 < V := by linarith only [hV.1]
  have hs0 : 0 < Real.sqrt V := Real.sqrt_pos.mpr hV0
  have hs : Real.sqrt V ≤ (51 : ℝ) / 20 := by
    nlinarith only [Real.sq_sqrt hV0.le, Real.sqrt_nonneg V, hV.2]
  have hfirst : (520 : ℝ) / 51 ≤ 26 / Real.sqrt V := by
    apply (le_div_iff₀ hs0).mpr
    linarith only [hs]
  have hsecond : 0 ≤ (11 - 26 * p) * (26 * (1 - 2 * p)) / (2 * V * Real.sqrt V) := by
    apply div_nonneg
    · exact mul_nonneg (by linarith only [(numerator_bounds hp).1]) (by linarith only [hp.2])
    · positivity
  have hfinal : (520 : ℝ) / 51 ≤ -(-26 / Real.sqrt V -
      (11 - 26 * p) * (26 * (1 - 2 * p)) / (2 * V * Real.sqrt V)) := by
    calc
      _ ≤ 26 / Real.sqrt V := hfirst
      _ ≤ 26 / Real.sqrt V + (11 - 26 * p) * (26 * (1 - 2 * p)) / (2 * V * Real.sqrt V) :=
        le_add_of_nonneg_right hsecond
      _ = _ := by ring
  simpa only [ProbabilityGaussianPrice.argumentSlope, ProbabilityGaussianPrice.numerator,
    ProbabilityGaussianPrice.varianceSlope, scaled_variance, Nat.cast_ofNat, add_zero, V] using hfinal

def probabilitySlope (l p : ℝ) : ℝ := prefixSlope 26 11 p -
  ProbabilityGaussianPrice.gaussianPriceSlope 26 11 0 (l / 26) p - (2 : ℝ) / 25 * P39Reference.e1 p

theorem hasDerivAt_base_probability {p l : ℝ} (hp : p ∈ strip) (hl : 0 ≤ l) :
    HasDerivAt (fun q => base q l) (probabilitySlope l p) p := by
  have hd := domain hp
  have hF := hasDerivAt_prefix 26 11 p hd.1 hd.2 (by norm_num)
  have hG := ProbabilityGaussianPrice.gaussianPrice_hasDerivAt (n := 26) (k := 11) (t := 0) (s := l / 26)
    (by norm_num) (div_nonneg hl (by norm_num)) ⟨hd.1, hd.2⟩
  have hR := (P39Reference.hasDerivAt_rho0 hd.1 hd.2).const_mul ((2 : ℝ) / 25)
  convert (hF.fun_sub hG).fun_sub hR using 1
  · funext q
    simp only [base, ProbabilityGaussianPrice.gaussianPrice, argument_noise_eq]
  · rfl

theorem probabilitySlope_lower {p l : ℝ} (hp : p ∈ strip) (hl : l ∈ Icc (0 : ℝ) (1 / 4)) :
    (33 : ℝ) / 2000 ≤ probabilitySlope l p := by
  have hF := prefixSlope_lower hp
  have hG := mul_le_mul (noisy_phi_lower hp hl.1) (wide_negative_argumentSlope_lower hp hl)
    (by norm_num : (0 : ℝ) ≤ 520 / 51) (phi_nonneg (P39NoiseGate.noiseArgument p 11 l))
  have hR := (P39Reference.e1_bounds hp).2
  unfold probabilitySlope ProbabilityGaussianPrice.gaussianPriceSlope
  rw [argument_noise_eq]
  nlinarith only [hF, hG, hR]

theorem base_probability_monotone {l : ℝ} (hl : l ∈ Icc (0 : ℝ) (1 / 4)) :
    MonotoneOn (fun p => base p l) strip := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
  · intro p hp
    exact (hasDerivAt_base_probability hp hl.1).continuousAt.continuousWithinAt
  · intro p hp
    exact (hasDerivAt_base_probability (interior_subset hp) hl.1).differentiableAt.differentiableWithinAt
  · intro p hp
    rw [(hasDerivAt_base_probability (interior_subset hp) hl.1).deriv]
    linarith only [probabilitySlope_lower (interior_subset hp) hl]

lemma endpoint_noiseSlope_upper {l : ℝ} (hl : 0 ≤ l) :
    P39NoiseGate.gaussianSlope (2 / 5) 11 l ≤ (1 : ℝ) / 125 := by
  let V := 26 * P39Reference.v (2 / 5) + l
  have hV : (156 : ℝ) / 25 ≤ V := by
    dsimp only [V, P39Reference.v]
    linarith only [hl]
  have hV0 : 0 < V := by linarith only [hV]
  have hs : (249 : ℝ) / 100 ≤ Real.sqrt V := by
    apply Real.le_sqrt_of_sq_le
    norm_num
    linarith only [hV]
  have hnum : phi (P39NoiseGate.noiseArgument (2 / 5) 11 l) * (11 - 26 * (2 / 5)) ≤ (6 : ℝ) / 25 := by
    have h := mul_le_mul_of_nonneg_right (phi_upper (P39NoiseGate.noiseArgument (2 / 5) 11 l))
      (by norm_num : (0 : ℝ) ≤ 3 / 5)
    nlinarith only [h]
  have hden : (19422 : ℝ) / 625 ≤ 2 * V * Real.sqrt V := by
    have h := mul_le_mul hV hs (by norm_num : (0 : ℝ) ≤ 249 / 100) hV0.le
    nlinarith only [h]
  change phi (P39NoiseGate.noiseArgument (2 / 5) 11 l) * (11 - 26 * (2 / 5)) /
    (2 * V * Real.sqrt V) ≤ (1 : ℝ) / 125
  apply (div_le_iff₀ (by positivity : 0 < 2 * V * Real.sqrt V)).mpr
  nlinarith only [hnum, hden]

theorem base_endpoint_noise_increment {l : ℝ} (hl : 0 ≤ l) :
    base (2 / 5) l ≤ base (2 / 5) 0 + l / 125 := by
  have hp : (2 / 5 : ℝ) ∈ strip := by norm_num [strip]
  have hd : ∀ x ∈ Icc (0 : ℝ) l,
      HasDerivAt (fun u => noisePart (2 / 5) u - u / 125)
        (P39NoiseGate.gaussianSlope (2 / 5) 11 x - 1 / 125) x := by
    intro x hx
    exact (hasDerivAt_noisePart hp hx.1).fun_sub ((hasDerivAt_id' x).div_const 125)
  have hm : AntitoneOn (fun u => noisePart (2 / 5) u - u / 125) (Icc (0 : ℝ) l) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
    · exact fun x hx => (hd x hx).continuousAt.continuousWithinAt
    · exact fun x hx => (hd x (interior_subset hx)).hasDerivWithinAt
    · intro x hx
      exact sub_nonpos.mpr (endpoint_noiseSlope_upper (interior_subset hx).1)
  have h := hm ⟨le_rfl, hl⟩ ⟨hl, le_rfl⟩ hl
  change noisePart (2 / 5) l - l / 125 ≤ noisePart (2 / 5) 0 - 0 / 125 at h
  unfold base
  unfold noisePart at h
  linarith only [h]

theorem baseline_endpoint {p l : ℝ} (hp : p ∈ strip) (hl : l ∈ Icc (0 : ℝ) (1 / 4)) :
    base p l ≤ base (2 / 5) 0 + l / 125 :=
  ((base_probability_monotone hl) hp (by norm_num [strip]) hp.2).trans
    (base_endpoint_noise_increment hl.1)

end

end BerryEsseen.P39Count11Face

#print axioms BerryEsseen.P39Count11Face.mass11_upper
#print axioms BerryEsseen.P39Count11Face.baseSlope_lower
#print axioms BerryEsseen.P39Count11Face.base_zero_monotone
#print axioms BerryEsseen.P39Count11Face.base_noise_increment
#print axioms BerryEsseen.P39Count11Face.frozen_Q_term_upper
#print axioms BerryEsseen.P39Count11Face.whole_face_explicit
#print axioms BerryEsseen.P39Count11Face.base_probability_monotone
#print axioms BerryEsseen.P39Count11Face.probabilitySlope_lower
#print axioms BerryEsseen.P39Count11Face.baseline_endpoint
