module

public import BerryEsseen.P39ModeTailExclusion

@[expose] public section

/-! 2026-10-30: one probability-monotone baseline family for counts
12 through 14, and one Gaussian noise-loss bound for the entire right
side. The finite rational rows are integer-count certificates, not a
probability, noise or phase grid. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace BerryEsseen.P39RightCountBaselines

open GaussianTools P39ModeEtaEndpointPrices

set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

def argumentUpperQ (k : ℕ) : ℚ := if k = 12 then 3 / 4 else if k = 13 then 29 / 25 else 39 / 25
def phiFloorQ (k : ℕ) : ℚ := if k = 12 then 3 / 10 else if k = 13 then 1 / 5 else 117 / 1000
def massUpperQ (k : ℕ) : ℚ := if k = 12 then 127 / 1000 else if k = 13 then 57 / 625 else 113 / 2000
def argumentLowerQ (k : ℕ) : ℚ := (2 / 5) * ((k : ℚ) - 52 / 5)
def densityCertQ (k : ℕ) : ℚ := RationalGaussianPrices.densityLower *
  ∑ j ∈ Finset.range 8, (-1 : ℚ) ^ j * ((argumentUpperQ k) ^ 2 / 2) ^ j / (j.factorial : ℚ)
def prefixQ (k : ℕ) : ℚ := ∑ j ∈ Finset.range (k + 1), P39ModeEtaEndpointPrices.massQ 26 j (2 / 5)
def slopeFloorQ (k : ℕ) : ℚ := -((26 - k : ℕ) : ℚ) * massUpperQ k / (3 / 5) +
  (52 / 5) * phiFloorQ k + (2 / 25) * (6 / 5)

private lemma count_cases {k : ℕ} (hlo : 12 ≤ k) (hhi : k ≤ 14) : k = 12 ∨ k = 13 ∨ k = 14 := by omega

theorem rational_rows (k : ℕ) (hlo : 12 ≤ k) (hhi : k ≤ 14) :
    0 ≤ argumentUpperQ k ∧ 0 ≤ phiFloorQ k ∧ 0 ≤ massUpperQ k ∧
      phiFloorQ k ≤ densityCertQ k ∧
      P39ModeEtaEndpointPrices.massQ 26 k (2 / 5) ≤ massUpperQ k ∧
      (k : ℚ) - 26 * (39 / 100) ≤ argumentUpperQ k * (2487 / 1000) ∧
      (9 / 50 : ℚ) ≤ slopeFloorQ k ∧
      prefixQ k - RationalGaussianPrices.PhiLower 8 (argumentLowerQ k) -
        (2 / 25) * (530722777603 / 500000000000) ≤ -(23 / 1000 : ℚ) := by
  rcases count_cases hlo hhi with rfl | rfl | rfl <;> decide +kernel

private theorem cast_massQ (n k : ℕ) (p : ℚ) :
    (P39ModeEtaEndpointPrices.massQ n k p : ℝ) = BinomialWeights.mass n k (p : ℝ) := by
  simp only [P39ModeEtaEndpointPrices.massQ, BinomialWeights.mass, Rat.cast_mul,
    Rat.cast_pow, Rat.cast_natCast, Rat.cast_sub, Rat.cast_one]

private theorem cast_prefixQ (k : ℕ) : (prefixQ k : ℝ) = BinomialWeights.lowerPrefix 26 k (2 / 5) := by
  unfold prefixQ BinomialWeights.lowerPrefix
  rw [show ((∑ j ∈ Finset.range (k + 1), P39ModeEtaEndpointPrices.massQ 26 j (2 / 5) : ℚ) : ℝ) =
      ∑ j ∈ Finset.range (k + 1), (P39ModeEtaEndpointPrices.massQ 26 j (2 / 5) : ℝ) from
    map_sum (Rat.castHom ℝ) _ _]
  apply Finset.sum_congr rfl
  intro j _
  simpa only [Rat.cast_div, Rat.cast_ofNat] using cast_massQ 26 j (2 / 5)

theorem phi_at_upper_lower (k : ℕ) (hlo : 12 ≤ k) (hhi : k ≤ 14) :
    (phiFloorQ k : ℝ) ≤ phi (argumentUpperQ k : ℝ) := by
  have hr := (rational_rows k hlo hhi).2.2.2.1
  have hcast : (densityCertQ k : ℝ) = (RationalGaussianPrices.densityLower : ℝ) *
      GaussianEnclosures.expTaylor 7 (((argumentUpperQ k : ℝ)) ^ 2 / 2) := by
    unfold densityCertQ GaussianEnclosures.expTaylor
    push_cast
    rfl
  have ht := GaussianEnclosures.exp_neg_taylor_lower 7 (by decide)
    ((argumentUpperQ k : ℝ) ^ 2 / 2) (by positivity)
  have hm := mul_le_mul_of_nonneg_left ht
    (show (0 : ℝ) ≤ RationalGaussianPrices.densityLower by norm_num [RationalGaussianPrices.densityLower])
  have hd := mul_le_mul_of_nonneg_right RationalGaussianPrices.densityLower_lt_phi_zero.le
    (Real.exp_nonneg (-((argumentUpperQ k : ℝ) ^ 2 / 2)))
  have hc : (phiFloorQ k : ℝ) ≤ (densityCertQ k : ℝ) := Rat.cast_le.mpr hr
  rw [hcast] at hc
  rw [GaussianPrices.phi_eq_phi_zero_mul_exp]
  exact hc.trans (hm.trans hd)

theorem mass_upper {p : ℝ} (hp : p ∈ strip) (k : ℕ) (hlo : 12 ≤ k) (hhi : k ≤ 14) :
    BinomialWeights.mass 26 k p ≤ (massUpperQ k : ℝ) := by
  have hr := (rational_rows k hlo hhi).2.2.2.2.1
  have he : BinomialWeights.mass 26 k (2 / 5) ≤ (massUpperQ k : ℝ) := by
    have hc : (P39ModeEtaEndpointPrices.massQ 26 k (2 / 5) : ℝ) ≤ (massUpperQ k : ℝ) := Rat.cast_le.mpr hr
    simpa only [cast_massQ, Rat.cast_div, Rat.cast_ofNat] using hc
  have hkR : (12 : ℝ) ≤ k := by exact_mod_cast hlo
  have hm := P39Count11Face.mass_monotone k (by omega) (by linarith only [hkR])
  exact (hm hp (by norm_num [P39Count11Face.strip]) hp.2).trans he

theorem argument_bounds {p : ℝ} (hp : p ∈ strip) (k : ℕ) (hlo : 12 ≤ k) (hhi : k ≤ 14) :
    0 ≤ ProbabilityGaussianPrice.argument 26 k 0 0 p ∧
      ProbabilityGaussianPrice.argument 26 k 0 0 p ≤ (argumentUpperQ k : ℝ) := by
  have hs := P39ModeBaselineMonotonicity.sum_sqrt_bounds hp
  have hs0 : 0 < Real.sqrt (26 * P39Reference.v p) := by linarith only [hs.1]
  have hkR : (12 : ℝ) ≤ k := by exact_mod_cast hlo
  have hn : 0 ≤ (k : ℝ) - 26 * p := by linarith only [hkR, hp.2]
  have hrow := (rational_rows k hlo hhi).2.2.2.2.2.1
  have hrowR : (k : ℝ) - 26 * (39 / 100) ≤ (argumentUpperQ k : ℝ) * (2487 / 1000) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hrow
    simpa only [Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc
  have hA : (0 : ℝ) ≤ argumentUpperQ k := Rat.cast_nonneg.mpr (rational_rows k hlo hhi).1
  have hprod := mul_le_mul_of_nonneg_left hs.1 hA
  simp only [ProbabilityGaussianPrice.argument, ProbabilityGaussianPrice.numerator,
    ProbabilityGaussianPrice.variance, Nat.cast_ofNat, add_zero]
  change 0 ≤ ((k : ℝ) - 26 * p) / Real.sqrt (26 * P39Reference.v p) ∧
    ((k : ℝ) - 26 * p) / Real.sqrt (26 * P39Reference.v p) ≤ (argumentUpperQ k : ℝ)
  refine ⟨div_nonneg hn hs0.le, (div_le_iff₀ hs0).mpr ?_⟩
  nlinarith only [hrowR, hprod, hp.1]

theorem phi_argument_lower {p : ℝ} (hp : p ∈ strip) (k : ℕ) (hlo : 12 ≤ k) (hhi : k ≤ 14) :
    (phiFloorQ k : ℝ) ≤ phi (ProbabilityGaussianPrice.argument 26 k 0 0 p) := by
  have hz := argument_bounds hp k hlo hhi
  have hA : (0 : ℝ) ≤ argumentUpperQ k := Rat.cast_nonneg.mpr (rational_rows k hlo hhi).1
  exact (phi_at_upper_lower k hlo hhi).trans
    (PositivePhasePriceConvex.phi_antitoneOn_nonnegative hz.1 hA hz.2)

theorem negative_argumentSlope_lower {p : ℝ} (hp : p ∈ strip) (k : ℕ) (hlo : 12 ≤ k) :
    (52 : ℝ) / 5 ≤ -ProbabilityGaussianPrice.argumentSlope 26 k 0 0 p := by
  have hv := P39ModeBaselineMonotonicity.sum_variance_bounds hp
  have hs := P39ModeBaselineMonotonicity.sum_sqrt_bounds hp
  have hv0 : 0 < 26 * P39Reference.v p := by linarith only [hv.1]
  have hs0 : 0 < Real.sqrt (26 * P39Reference.v p) := by linarith only [hs.1]
  have hkR : (12 : ℝ) ≤ k := by exact_mod_cast hlo
  have hfirst : (52 : ℝ) / 5 ≤ 26 / Real.sqrt (26 * P39Reference.v p) := by
    apply (le_div_iff₀ hs0).mpr
    linarith only [hs.2]
  have hsecond : 0 ≤ ((k : ℝ) - 26 * p) * (26 * (1 - 2 * p)) /
      (2 * (26 * P39Reference.v p) * Real.sqrt (26 * P39Reference.v p)) := by
    apply div_nonneg
    · exact mul_nonneg (by linarith only [hkR, hp.2]) (by linarith only [hp.2])
    · positivity
  have hf : (52 : ℝ) / 5 ≤ -(-26 / Real.sqrt (26 * P39Reference.v p) -
      ((k : ℝ) - 26 * p) * (26 * (1 - 2 * p)) /
        (2 * (26 * P39Reference.v p) * Real.sqrt (26 * P39Reference.v p))) := by
    calc
      _ ≤ 26 / Real.sqrt (26 * P39Reference.v p) := hfirst
      _ ≤ 26 / Real.sqrt (26 * P39Reference.v p) +
          ((k : ℝ) - 26 * p) * (26 * (1 - 2 * p)) /
            (2 * (26 * P39Reference.v p) * Real.sqrt (26 * P39Reference.v p)) :=
        le_add_of_nonneg_right hsecond
      _ = _ := by ring
  simpa only [ProbabilityGaussianPrice.argumentSlope, ProbabilityGaussianPrice.numerator,
    ProbabilityGaussianPrice.variance, ProbabilityGaussianPrice.varianceSlope,
    Nat.cast_ofNat, add_zero, P39Reference.v] using hf

theorem prefixSlope_lower {p : ℝ} (hp : p ∈ strip) (k : ℕ) (hlo : 12 ≤ k) (hhi : k ≤ 14) :
    -((26 - k : ℕ) : ℝ) * (massUpperQ k : ℝ) / (3 / 5) ≤ BinomialWeights.prefixSlope 26 k p := by
  have hq : (3 : ℝ) / 5 ≤ 1 - p := by linarith only [hp.2]
  have hq0 : 0 < 1 - p := sub_pos.mpr (domain hp).2
  have hM0 : (0 : ℝ) ≤ massUpperQ k := Rat.cast_nonneg.mpr (rational_rows k hlo hhi).2.2.1
  have hd : BinomialWeights.mass 26 k p / (1 - p) ≤ (massUpperQ k : ℝ) / (3 / 5) :=
    (div_le_div_of_nonneg_right (mass_upper hp k hlo hhi) hq0.le).trans
      (div_le_div_of_nonneg_left hM0 (by norm_num) hq)
  have hm := mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg (26 - k) : (0 : ℝ) ≤ (26 - k : ℕ))
  calc
    _ = -(((26 - k : ℕ) : ℝ) * ((massUpperQ k : ℝ) / (3 / 5))) := by ring
    _ ≤ -(((26 - k : ℕ) : ℝ) * (BinomialWeights.mass 26 k p / (1 - p))) := neg_le_neg hm
    _ = _ := by unfold BinomialWeights.prefixSlope; ring

def baseline (k : ℕ) (p : ℝ) : ℝ := BinomialWeights.lowerPrefix 26 k p -
  ProbabilityGaussianPrice.gaussianPrice 26 k 0 0 p - (2 / 25) * P39Reference.rho0 p
def baselineSlope (k : ℕ) (p : ℝ) : ℝ := BinomialWeights.prefixSlope 26 k p -
  ProbabilityGaussianPrice.gaussianPriceSlope 26 k 0 0 p - (2 / 25) * P39Reference.e1 p

theorem hasDerivAt_baseline {p : ℝ} (hp : p ∈ strip) (k : ℕ) (hhi : k ≤ 14) :
    HasDerivAt (baseline k) (baselineSlope k p) p := by
  have hd := domain hp
  have hF := BinomialWeights.hasDerivAt_prefix 26 k p hd.1 hd.2 (by omega)
  have hG := ProbabilityGaussianPrice.gaussianPrice_hasDerivAt (n := 26) (k := k) (t := 0) (s := 0)
    (by norm_num) (by norm_num) ⟨hd.1, hd.2⟩
  have hR := (P39Reference.hasDerivAt_rho0 hd.1 hd.2).const_mul ((2 : ℝ) / 25)
  convert (hF.fun_sub hG).fun_sub hR using 1
  · rfl
  · rfl

theorem baselineSlope_lower {p : ℝ} (hp : p ∈ strip) (k : ℕ) (hlo : 12 ≤ k) (hhi : k ≤ 14) :
    (9 : ℝ) / 50 ≤ baselineSlope k p := by
  have hF := prefixSlope_lower hp k hlo hhi
  have hG := mul_le_mul (phi_argument_lower hp k hlo hhi) (negative_argumentSlope_lower hp k hlo)
    (by norm_num : (0 : ℝ) ≤ 52 / 5) (phi_nonneg _)
  have hR := (P39Reference.e1_bounds hp).2
  have hr : (9 : ℝ) / 50 ≤ -((26 - k : ℕ) : ℝ) * (massUpperQ k : ℝ) / (3 / 5) +
      (52 / 5) * (phiFloorQ k : ℝ) + (2 / 25) * (6 / 5) := by
    have hq := (Rat.cast_le (K := ℝ)).mpr (rational_rows k hlo hhi).2.2.2.2.2.2.1
    simpa only [slopeFloorQ, Rat.cast_add, Rat.cast_mul, Rat.cast_neg, Rat.cast_div,
      Rat.cast_natCast, Rat.cast_ofNat] using hq
  unfold baselineSlope ProbabilityGaussianPrice.gaussianPriceSlope
  nlinarith only [hF, hG, hR, hr]

theorem baseline_monotone (k : ℕ) (hlo : 12 ≤ k) (hhi : k ≤ 14) : MonotoneOn (baseline k) strip := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
  · intro p hp
    exact (hasDerivAt_baseline hp k hhi).continuousAt.continuousWithinAt
  · intro p hp
    exact (hasDerivAt_baseline (interior_subset hp) k hhi).differentiableAt.differentiableWithinAt
  · intro p hp
    rw [(hasDerivAt_baseline (interior_subset hp) k hhi).deriv]
    exact (by linarith only [baselineSlope_lower (interior_subset hp) k hlo hhi])

theorem endpoint_argument_lower (k : ℕ) (hlo : 12 ≤ k) :
    (argumentLowerQ k : ℝ) ≤ ProbabilityGaussianPrice.argument 26 k 0 0 (2 / 5) := by
  have hs := (P39ModeBaselineMonotonicity.sum_sqrt_bounds (p := (2 / 5)) (by norm_num [strip])).2
  have hv0 : 0 < 26 * P39Reference.v (2 / 5) := by norm_num [P39Reference.v]
  have hA : (0 : ℝ) ≤ argumentLowerQ k := by
    unfold argumentLowerQ
    push_cast
    have hkR : (12 : ℝ) ≤ k := by exact_mod_cast hlo
    linarith only [hkR]
  have hm := mul_le_mul_of_nonneg_left hs hA
  have he : (argumentLowerQ k : ℝ) * (5 / 2) = (k : ℝ) - 26 * (2 / 5) := by
    unfold argumentLowerQ
    push_cast
    ring
  simp only [ProbabilityGaussianPrice.argument, ProbabilityGaussianPrice.numerator,
    ProbabilityGaussianPrice.variance, Nat.cast_ofNat, add_zero]
  change (argumentLowerQ k : ℝ) ≤ ((k : ℝ) - 26 * (2 / 5)) / Real.sqrt (26 * P39Reference.v (2 / 5))
  apply (le_div_iff₀ (Real.sqrt_pos.mpr hv0)).mpr
  linarith only [hm, he]

theorem baseline_endpoint_upper (k : ℕ) (hlo : 12 ≤ k) (hhi : k ≤ 14) :
    baseline k (2 / 5) ≤ -(23 / 1000 : ℝ) := by
  have hmono : Monotone Phi := fun a b hab => measureReal_mono (Iic_subset_Iic.mpr hab)
  have hPhi := (RationalGaussianPrices.Phi_rational_bounds 8 (argumentLowerQ k)).1.trans
    (hmono (endpoint_argument_lower k hlo))
  have hcheck : (prefixQ k : ℝ) - (RationalGaussianPrices.PhiLower 8 (argumentLowerQ k) : ℝ) -
      (2 / 25) * (530722777603 / 500000000000) ≤ -(23 / 1000 : ℝ) := by
    have hr := (Rat.cast_le (K := ℝ)).mpr (rational_rows k hlo hhi).2.2.2.2.2.2.2
    simpa only [Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hr
  rw [cast_prefixQ] at hcheck
  unfold baseline ProbabilityGaussianPrice.gaussianPrice
  nlinarith only [hcheck, hPhi, P39Reference.endpoint_floor]

theorem baseline_strip_upper {p : ℝ} (hp : p ∈ strip) (k : ℕ) (hlo : 12 ≤ k) (hhi : k ≤ 14) :
    baseline k p ≤ -(23 / 1000 : ℝ) :=
  ((baseline_monotone k hlo hhi) hp (by norm_num [strip]) hp.2).trans (baseline_endpoint_upper k hlo hhi)

theorem baseline_noise_form (k : ℕ) (p : ℝ) : baseline k p =
    BinomialWeights.lowerPrefix 26 k p - Phi (P39NoiseGate.noiseArgument p (k : ℝ) 0) -
      (2 / 25) * P39Reference.rho0 p := by
  rw [baseline, ProbabilityGaussianPrice.gaussianPrice, P39ModeBaselineMonotonicity.argument_eq,
    P39ModeTailExclusion.argument_eq_zero_noise]

theorem x_mul_phi_le (x : ℝ) (hx : 0 ≤ x) : x * phi x ≤ (3 : ℝ) / 10 := by
  have he : (4 / 3 : ℝ) * x ≤ Real.exp (x ^ 2 / 2) := by
    nlinarith only [Real.add_one_le_exp (x ^ 2 / 2), sq_nonneg (x - (4 / 3 : ℝ))]
  have hm := mul_le_mul_of_nonneg_right he (Real.exp_nonneg (-(x ^ 2 / 2)))
  have hprod : Real.exp (x ^ 2 / 2) * Real.exp (-(x ^ 2 / 2)) = 1 := by rw [← Real.exp_add]; simp
  rw [hprod] at hm
  have hd := mul_le_mul_of_nonneg_right GaussianPrices.phi_zero_lt_2_5.le
    (mul_nonneg hx (Real.exp_nonneg (-(x ^ 2 / 2))))
  rw [GaussianPrices.phi_eq_phi_zero_mul_exp]
  nlinarith only [hm, hd]

theorem gaussianSlope_right_upper {p r lambda : ℝ} (hp : p ∈ strip) (hl : 0 ≤ lambda)
    (hr : 26 * p ≤ r) : P39NoiseGate.gaussianSlope p r lambda ≤ (1 : ℝ) / 40 := by
  let V := 26 * MomentBudgetNoise.variance p + lambda
  let x := P39NoiseGate.noiseArgument p r lambda
  have hV0 : 0 < V := P39NoiseGate.actual_variance_pos hp hl
  have hV6 : (6 : ℝ) ≤ V := by
    have hv := (P39ModeNoiseUpperBounds.variance_bounds hp).1
    dsimp only [V]
    linarith only [hv, hl]
  have hs0 := Real.sqrt_pos.mpr hV0
  have hx : 0 ≤ x := div_nonneg (sub_nonneg.mpr hr) (Real.sqrt_nonneg _)
  have hxmul : x * Real.sqrt V = r - 26 * p := by
    dsimp only [x, P39NoiseGate.noiseArgument, V]
    exact div_mul_cancel₀ _ hs0.ne'
  have hn : phi x * (r - 26 * p) ≤ (3 / 10 : ℝ) * Real.sqrt V := by
    calc
      _ = (x * phi x) * Real.sqrt V := by rw [← hxmul]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (x_mul_phi_le x hx) hs0.le
  have hd := mul_le_mul_of_nonneg_right hV6 hs0.le
  change phi x * (r - 26 * p) / (2 * V * Real.sqrt V) ≤ (1 : ℝ) / 40
  apply (div_le_iff₀ (by positivity : 0 < 2 * V * Real.sqrt V)).mpr
  nlinarith only [hn, hd]

theorem right_noise_loss {p r lambda : ℝ} (hp : p ∈ strip) (hl : 0 ≤ lambda)
    (hr : 26 * p ≤ r) :
    Phi (P39NoiseGate.noiseArgument p r 0) - Phi (P39NoiseGate.noiseArgument p r lambda) ≤
      (1 / 40 : ℝ) * lambda :=
  P39ModeNoiseUpperBounds.noise_loss_le_of_slope p r (1 / 40) lambda hp hl
    (fun _ hx => gaussianSlope_right_upper hp hx.1 hr)

end BerryEsseen.P39RightCountBaselines

#print axioms BerryEsseen.P39RightCountBaselines.rational_rows
#print axioms BerryEsseen.P39RightCountBaselines.baselineSlope_lower
#print axioms BerryEsseen.P39RightCountBaselines.baseline_strip_upper
#print axioms BerryEsseen.P39RightCountBaselines.x_mul_phi_le
#print axioms BerryEsseen.P39RightCountBaselines.right_noise_loss
