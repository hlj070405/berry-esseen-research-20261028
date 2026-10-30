module

public import BerryEsseen.BinomialPrefixGate
public import BerryEsseen.RationalReferencePrice
public import BerryEsseen.RationalGaussianPrices
public import BerryEsseen.P39Reference

@[expose] public section

/-! 2026-10-30: exact tail-mode eta and two actual Gaussian/reference
endpoint prices. The reference variance is a fixed parameter; acquisition
of that budget from an original law is a separate statement. -/

namespace BerryEsseen.P39ModeEtaEndpointPrices

open MeasureTheory Set
open scoped BigOperators

noncomputable section

set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

def strip : Set ℝ := Icc (39 / 100) (2 / 5)
def deltaBar : ℝ := 7 / 80
def gap : ℝ := 73 / 80
def eta (p : ℝ) : ℝ := BinomialWeights.mass 26 12 p / gap

lemma domain {p : ℝ} (hp : p ∈ strip) : 0 < p ∧ p < 1 := by
  constructor <;> linarith only [hp.1, hp.2]

theorem eta_eq_tailEta (p : ℝ) : eta p = BinomialPrefixGate.tailEta 26 11 deltaBar p := by
  norm_num [eta, gap, deltaBar, BinomialPrefixGate.tailEta]

theorem eta_pos {p : ℝ} (hp : p ∈ strip) : 0 < eta p := by
  exact div_pos (BinomialWeights.mass_pos 26 12 p (domain hp).1 (domain hp).2
    (by norm_num)) (by norm_num [gap])

theorem mode_condition {p : ℝ} (hp : p ∈ strip) : (27 : ℝ) * p ≤ 13 := by
  linarith only [hp.2]

theorem eta_prefix_gate {p : ℝ} (hp : p ∈ strip) :
    ∀ r : ℕ, 1 ≤ r → r ≤ 26 - 11 →
      Staircase.prefixMass (fun j => BinomialWeights.mass 26 (11 + j) p) r ≤
        eta p * ((r : ℝ) * (1 - deltaBar)) := by
  rw [eta_eq_tailEta]
  exact BinomialPrefixGate.eta_prefix_gate 26 11 deltaBar p (domain hp).1 (domain hp).2
    (by simpa using mode_condition hp) (by norm_num [deltaBar])

/-- The first prefix already forces this eta; the tail-mode gate is exact. -/
theorem eta_minimal {p e : ℝ} (_hp : p ∈ strip)
    (he : ∀ r : ℕ, 1 ≤ r → r ≤ 26 - 11 →
      Staircase.prefixMass (fun j => BinomialWeights.mass 26 (11 + j) p) r ≤
        e * ((r : ℝ) * (1 - deltaBar))) : eta p ≤ e := by
  have h := he 1 (by norm_num) (by norm_num)
  norm_num [Staircase.prefixMass, deltaBar] at h
  unfold eta gap
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 73 / 80)).mpr
  linarith only [h]

private theorem mass12_monotone : MonotoneOn (BinomialWeights.mass 26 12) strip := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
  · intro p hp
    exact (BinomialWeights.hasDerivAt_mass 26 12 p (domain hp).1 (domain hp).2
      (by norm_num)).continuousAt.continuousWithinAt
  · intro p hp
    have hd := domain (interior_subset hp)
    exact (BinomialWeights.hasDerivAt_mass 26 12 p hd.1 hd.2
      (by norm_num)).differentiableAt.differentiableWithinAt
  · intro p hp
    have hi := interior_subset hp
    have hd := domain hi
    rw [(BinomialWeights.hasDerivAt_mass 26 12 p hd.1 hd.2 (by norm_num)).deriv]
    unfold BinomialWeights.massSlope
    apply div_nonneg
    · exact mul_nonneg (BinomialWeights.mass_nonneg 26 12 p hd.1.le hd.2.le)
        (by norm_num; linarith only [hi.2])
    · exact mul_nonneg hd.1.le (sub_nonneg.mpr hd.2.le)

def massQ (n k : ℕ) (p : ℚ) : ℚ :=
  (n.choose k : ℚ) * p ^ k * (1 - p) ^ (n - k)

private theorem cast_massQ (n k : ℕ) (p : ℚ) :
    (massQ n k p : ℝ) = BinomialWeights.mass n k (p : ℝ) := by
  simp only [massQ, BinomialWeights.mass, Rat.cast_mul, Rat.cast_pow,
    Rat.cast_natCast, Rat.cast_sub, Rat.cast_one]

private theorem eta_endpoint_rational : massQ 26 12 (2 / 5) / (73 / 80) ≤ (7 / 50 : ℚ) := by
  decide +kernel

theorem eta_le_seven_fiftieths {p : ℝ} (hp : p ∈ strip) : eta p ≤ 7 / 50 := by
  have he : eta (2 / 5) ≤ 7 / 50 := by
    have h := (Rat.cast_le (K := ℝ)).mpr eta_endpoint_rational
    simpa only [Rat.cast_div, Rat.cast_ofNat, cast_massQ, eta, gap] using h
  exact (div_le_div_of_nonneg_right
    (mass12_monotone hp (by norm_num [strip]) hp.2) (by norm_num [gap])).trans he

theorem mass_div_eta_eq {p : ℝ} (hp : p ∈ strip) :
    BinomialWeights.mass 26 11 p / eta p = gap * (12 * (1 - p)) / (15 * p) := by
  have hflux := BinomialPrefixGate.adjacent_mass_flux 26 11 p (by norm_num)
  norm_num only [Nat.reduceAdd, Nat.reduceSub, Nat.cast_ofNat] at hflux
  have hm := BinomialWeights.mass_pos 26 12 p (domain hp).1 (domain hp).2 (by norm_num)
  have hp0 := (domain hp).1.ne'
  unfold eta gap
  field_simp [hm.ne', hp0]
  nlinarith only [hflux]

theorem mass_div_eta_lower {p : ℝ} (hp : p ∈ strip) :
    (219 / 200 : ℝ) ≤ BinomialWeights.mass 26 11 p / eta p := by
  rw [mass_div_eta_eq hp]
  apply (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 15) (domain hp).1)).mpr
  unfold gap
  linarith only [hp.2]

def capQ : ℚ := 5 / 8
def totalVarianceQ : ℚ := 8 / 25
def perVarianceQ : ℚ := 4 / 325
def widthQ : ℚ := 1 / 5
def threshold0Q : ℚ := 219 / 200
def threshold1Q : ℚ := 419 / 200
def upper0Q : ℚ := 143 / 5000
def upper1Q : ℚ := 7 / 5000

def reference : Measure ℝ := TwoMoment.uniformReferenceSumLaw (5 / 8) 26 (8 / 25)

theorem perVariance_cast : (perVarianceQ : ℝ) = (totalVarianceQ : ℝ) / 26 := by
  norm_num [perVarianceQ, totalVarianceQ]

theorem uniform_eq_double : reference =
    DoubleBinomialReference.law (capQ : ℝ) (perVarianceQ : ℝ) 26 (capQ : ℝ) ((0 : ℚ) : ℝ) 0 := by
  rw [DoubleBinomialReference.law_empty_right]
  unfold reference TwoMoment.uniformReferenceSumLaw
  rw [TwoMoment.finiteIndependentSumLaw_const_eq_convPower, perVariance_cast]
  norm_num [capQ, totalVarianceQ]

theorem reference_probability : IsProbabilityMeasure reference :=
  TwoMoment.uniformReferenceSumLaw_isProbabilityMeasure _ _ _ (by norm_num) (by norm_num)

theorem reference_memLp_two : MemLp (fun x : ℝ => x) 2 reference := by
  rw [uniform_eq_double]
  exact DoubleBinomialReference.law_memLp_two _ _ _ _ _ _
    (by norm_num [capQ]) (by norm_num [perVarianceQ])
    (by norm_num [capQ]) (by norm_num)

theorem reference_square_integrable : Integrable (fun x : ℝ => x ^ 2) reference :=
  (TwoMoment.uniformReferenceSumLaw_moments _ 26 _ (by norm_num) (by norm_num)
    (by norm_num)).2.1

theorem reference_moments : (∫ x, x ∂reference) = 0 ∧
    (∫ x, x ^ 2 ∂reference) = (8 / 25 : ℝ) :=
  (TwoMoment.uniformReferenceSumLaw_moments _ 26 _ (by norm_num) (by norm_num)
    (by norm_num)).2.2

theorem rational_price_upper0 :
    RationalReferencePrice.rationalPrice capQ perVarianceQ 26 capQ 0 0 threshold0Q widthQ ≤ upper0Q := by
  decide +kernel

theorem rational_price_upper1 :
    RationalReferencePrice.rationalPrice capQ perVarianceQ 26 capQ 0 0 threshold1Q widthQ ≤ upper1Q := by
  decide +kernel

theorem actual_price_eq (A : ℚ) : StopLossShape.price reference (A : ℝ) (widthQ : ℝ) =
    (RationalReferencePrice.rationalPrice capQ perVarianceQ 26 capQ 0 0 A widthQ : ℝ) := by
  rw [uniform_eq_double]
  exact RationalReferencePrice.price_eq_cast capQ perVarianceQ 26 capQ 0 0 A widthQ
    (by norm_num [capQ]) (by norm_num [perVarianceQ]) (by norm_num [capQ]) (by norm_num)

theorem actual_Q_upper0 : StopLossShape.Q reference (219 / 200) ≤ (143 / 5000 : ℝ) := by
  have h := (StopLossShape.Q_le_price reference (threshold0Q : ℝ) (widthQ : ℝ)
    (by norm_num [widthQ]))
  rw [actual_price_eq] at h
  have h' := h.trans (Rat.cast_le.mpr rational_price_upper0)
  simpa only [threshold0Q, upper0Q, Rat.cast_div, Rat.cast_ofNat] using h'

theorem actual_Q_upper1 : StopLossShape.Q reference (419 / 200) ≤ (7 / 5000 : ℝ) := by
  have h := (StopLossShape.Q_le_price reference (threshold1Q : ℝ) (widthQ : ℝ)
    (by norm_num [widthQ]))
  rw [actual_price_eq] at h
  have h' := h.trans (Rat.cast_le.mpr rational_price_upper1)
  simpa only [threshold1Q, upper1Q, Rat.cast_div, Rat.cast_ofNat] using h'

def argument (k : ℝ) (p : ℝ) : ℝ :=
  (k - 26 * p) / Real.sqrt (26 * p * (1 - p))
def base0 (p : ℝ) : ℝ := BinomialWeights.lowerPrefix 26 11 p -
  GaussianTools.Phi (argument 11 p) - (2 / 25) * P39Reference.rho0 p
def base1 (p : ℝ) : ℝ := BinomialWeights.lowerPrefix 26 11 p -
  GaussianTools.Phi (argument 12 p) - (2 / 25) * P39Reference.rho0 p

theorem argument0_lower : (6 / 25 : ℝ) ≤ argument 11 (2 / 5) := by
  have hv : (0 : ℝ) < 26 * (2 / 5) * (1 - 2 / 5) := by norm_num
  have hs : Real.sqrt ((26 : ℝ) * (2 / 5) * (1 - 2 / 5)) ≤ 5 / 2 := by
    apply (Real.sqrt_le_iff).mpr
    norm_num
  unfold argument
  apply (le_div_iff₀ (Real.sqrt_pos.mpr hv)).mpr
  nlinarith only [hs]

theorem argument1_lower : (747 / 1000 : ℝ) ≤ argument 12 (39 / 100) := by
  have hv : (0 : ℝ) < 26 * (39 / 100) * (1 - 39 / 100) := by norm_num
  have hs : Real.sqrt ((26 : ℝ) * (39 / 100) * (1 - 39 / 100)) ≤ 311 / 125 := by
    apply (Real.sqrt_le_iff).mpr
    norm_num
  unfold argument
  apply (le_div_iff₀ (Real.sqrt_pos.mpr hv)).mpr
  nlinarith only [hs]

private theorem rho0_endpoint_lower : (52 / 49 : ℝ) ≤ P39Reference.rho0 (2 / 5) := by
  have hv : (0 : ℝ) < (2 / 5) * (1 - 2 / 5) := by norm_num
  have hs : Real.sqrt ((2 / 5 : ℝ) * (1 - 2 / 5)) ≤ 49 / 100 := by
    apply (Real.sqrt_le_iff).mpr
    norm_num
  unfold P39Reference.rho0 P39Reference.v
  apply (le_div_iff₀ (Real.sqrt_pos.mpr hv)).mpr
  nlinarith only [hs]

private theorem rho1_endpoint_lower : (537 / 500 : ℝ) ≤ P39Reference.rho0 (39 / 100) := by
  have hv : (0 : ℝ) < (39 / 100) * (1 - 39 / 100) := by norm_num
  have hs : Real.sqrt ((39 / 100 : ℝ) * (1 - 39 / 100)) ≤ 61 / 125 := by
    apply (Real.sqrt_le_iff).mpr
    norm_num
  unfold P39Reference.rho0 P39Reference.v
  apply (le_div_iff₀ (Real.sqrt_pos.mpr hv)).mpr
  nlinarith only [hs]

def prefixQ (p : ℚ) : ℚ := ∑ j ∈ Finset.range 12, massQ 26 j p

private theorem cast_prefixQ (p : ℚ) :
    (prefixQ p : ℝ) = BinomialWeights.lowerPrefix 26 11 (p : ℝ) := by
  unfold prefixQ BinomialWeights.lowerPrefix
  rw [show ((∑ j ∈ Finset.range 12, massQ 26 j p : ℚ) : ℝ) =
    ∑ j ∈ Finset.range 12, (massQ 26 j p : ℝ) from map_sum (Rat.castHom ℝ) _ _]
  exact Finset.sum_congr rfl (fun j _ => cast_massQ 26 j p)

private theorem baseline_rational0 : prefixQ (2 / 5) -
    RationalGaussianPrices.PhiLower 8 (6 / 25) - (2 / 25) * (52 / 49) ≤ -(3 / 500 : ℚ) := by
  decide +kernel

private theorem baseline_rational1 : prefixQ (39 / 100) -
    RationalGaussianPrices.PhiLower 8 (747 / 1000) - (2 / 25) * (537 / 500) ≤ -(147 / 1000 : ℚ) := by
  decide +kernel

theorem base0_endpoint : base0 (2 / 5) ≤ -(3 / 500 : ℝ) := by
  have hm : Monotone GaussianTools.Phi := fun a b hab =>
    measureReal_mono (Iic_subset_Iic.mpr hab)
  have hPhi := (RationalGaussianPrices.Phi_rational_bounds 8 (6 / 25)).1
  have harg := hm argument0_lower
  have hcheck := (Rat.cast_le (K := ℝ)).mpr baseline_rational0
  simp only [Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg,
    cast_prefixQ] at hcheck hPhi
  unfold base0
  linarith only [hcheck, hPhi, harg, rho0_endpoint_lower]

theorem base1_endpoint : base1 (39 / 100) ≤ -(147 / 1000 : ℝ) := by
  have hm : Monotone GaussianTools.Phi := fun a b hab =>
    measureReal_mono (Iic_subset_Iic.mpr hab)
  have hPhi := (RationalGaussianPrices.Phi_rational_bounds 8 (747 / 1000)).1
  have harg := hm argument1_lower
  have hcheck := (Rat.cast_le (K := ℝ)).mpr baseline_rational1
  simp only [Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg,
    cast_prefixQ] at hcheck hPhi
  unfold base1
  linarith only [hcheck, hPhi, harg, rho1_endpoint_lower]

/-- Scalar arithmetic only: the noise slope and total budget are inputs elsewhere. -/
theorem arithmetic_gate0 :
    -(3 / 500 : ℝ) + (11 / 1000 - (2 / 25) * (19 / 10) / 26) * (17 / 50) +
      (7 / 50) * (143 / 5000) ≤ -(1 / 5000 : ℝ) := by norm_num

theorem arithmetic_gate1 :
    -(147 / 1000 : ℝ) + (1 / 40 - (2 / 25) * (19 / 10) / 26) * (17 / 50) +
      (7 / 50) * (1 + 7 / 5000) ≤ -(1 / 5000 : ℝ) := by norm_num

end

end BerryEsseen.P39ModeEtaEndpointPrices

#print axioms BerryEsseen.P39ModeEtaEndpointPrices.eta_prefix_gate
#print axioms BerryEsseen.P39ModeEtaEndpointPrices.eta_minimal
#print axioms BerryEsseen.P39ModeEtaEndpointPrices.eta_le_seven_fiftieths
#print axioms BerryEsseen.P39ModeEtaEndpointPrices.mass_div_eta_lower
#print axioms BerryEsseen.P39ModeEtaEndpointPrices.uniform_eq_double
#print axioms BerryEsseen.P39ModeEtaEndpointPrices.reference_memLp_two
#print axioms BerryEsseen.P39ModeEtaEndpointPrices.reference_moments
#print axioms BerryEsseen.P39ModeEtaEndpointPrices.actual_price_eq
#print axioms BerryEsseen.P39ModeEtaEndpointPrices.actual_Q_upper0
#print axioms BerryEsseen.P39ModeEtaEndpointPrices.actual_Q_upper1
#print axioms BerryEsseen.P39ModeEtaEndpointPrices.base0_endpoint
#print axioms BerryEsseen.P39ModeEtaEndpointPrices.base1_endpoint
#print axioms BerryEsseen.P39ModeEtaEndpointPrices.arithmetic_gate0
#print axioms BerryEsseen.P39ModeEtaEndpointPrices.arithmetic_gate1
