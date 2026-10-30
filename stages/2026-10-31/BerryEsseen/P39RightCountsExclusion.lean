module

public import BerryEsseen.P39RightCountBaselines
public import BerryEsseen.P39RightRayExclusion
public import BerryEsseen.P39HeightLocalization

@[expose] public section

/-! 2026-10-30: one actual-law exclusion family for counts 12 and 13.
The same acquired resource pays all count variances from 11 to 13.
Exact eta is retained through the prefix identity before it is bounded.
Both closed phase endpoints and every interior phase use the same
reference, law, actual noise and original maximum. -/

noncomputable section
open MeasureTheory Set

namespace BerryEsseen.P39RightCountsExclusion

open CanonicalSign CentralGap NoiseCoordinates GaussianTools
open CentralGapReferenceSquareBounds P39Count11VarianceAcquisition
open P39ModeEtaEndpointPrices (strip reference reference_probability reference_square_integrable deltaBar gap)

local instance : IsProbabilityMeasure reference := reference_probability

def eta (k : ℕ) (p : ℝ) : ℝ := BinomialPrefixGate.tailEta 26 k deltaBar p
def threshold (k : ℕ) (p : ℝ) : ℝ := BinomialWeights.mass 26 k p / eta k p
def envelope (k : ℕ) (p lambda t : ℝ) : ℝ :=
  PositivePhasePriceConvex.phasePrice reference (BinomialWeights.lowerPrefix 26 k p)
    (eta k p) (threshold k p) ((k : ℝ) - 26 * p)
    (26 * MomentBudgetNoise.variance p + lambda)
    ((2 / 25) * (P39Reference.rho0 p + (19 / 10) * lambda / 26)) t

theorem original_actualCountVariance_le (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (H C : ℝ) (hm : ContactVariation.PositiveClosedMaximum μ 26 H C)
    (hprev : Extremizer.fixedNSup 25 ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10)
    (hp : p μ ∈ Icc (39 / 100 : ℝ) (2 / 5)) (k : ℕ) (hk0 : 11 ≤ k) (hk1 : k ≤ 13) :
    StaircasePrices.actualCountVariance (residual0 μ h : Measure ℝ)
      (residual1 μ h : Measure ℝ) 26 k ≤ (8 : ℝ) / 25 := by
  obtain ⟨hcap0, hcap1⟩ := original_residual_variance_caps μ h H C hm hprev hC hρ hp
  obtain ⟨hs0, hs1⟩ := noise_allocation_split μ h
  have hdelta := (CanonicalInwardBudget.original_inward_lt_seven_eightieths μ h
    26 (by decide) H C hm hprev hC hρ).le
  have hq : (3 : ℝ) / 5 ≤ q μ := by unfold q; linarith only [hp.2]
  have hpayed := (retainedCost_ge_weighted_variances (p μ) (q μ) (a0 μ h) (a1 μ h)
    (noiseLevel μ h 26) (ConditionalResidual.actualAllocation μ h) (variance0 μ h) (variance1 μ h)
    hp.1 hq (a0_nonneg μ h) (a1_nonneg μ h) hdelta (variance0_nonneg μ h) (variance1_nonneg μ h)
    hcap0 hcap1 hs0 hs1).trans (original_retained_budget μ h H C hm hprev hC hρ)
  have hc := (scale_and_outward_caps μ h hρ hp).1
  have hu := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (scale_pos μ h).le hc 3)
    (by norm_num : (0 : ℝ) ≤ 92 / 75)
  have hn0 : ((26 - k : ℕ) : ℝ) ≤ 15 := by exact_mod_cast (show 26 - k ≤ 15 by omega)
  have hn1 : (k : ℝ) ≤ 13 := by exact_mod_cast hk1
  have hprice0 := (mul_le_mul_of_nonneg_left hn0 (by norm_num : (0 : ℝ) ≤ 113 / 200)).trans
    coefficient_gates.1.le
  have hprice1 := (mul_le_mul_of_nonneg_left hn1 (by norm_num : (0 : ℝ) ≤ 113 / 200)).trans
    (show (113 / 200 : ℝ) * 13 ≤ coefficient1 by norm_num [coefficient1, ConservedTransfer.kappa])
  have hm0 := mul_le_mul_of_nonneg_right hprice0 (variance0_nonneg μ h)
  have hm1 := mul_le_mul_of_nonneg_right hprice1 (variance1_nonneg μ h)
  change ((26 - k : ℕ) : ℝ) * variance0 μ h + (k : ℝ) * variance1 μ h ≤ (8 : ℝ) / 25
  nlinarith only [hpayed, hu, hm0, hm1, coefficient_gates.2.2]

theorem eta_pos {p : ℝ} (hp : p ∈ strip) (k : ℕ) (hk : k ≤ 13) : 0 < eta k p :=
  BinomialPrefixGate.tailEta_pos 26 k deltaBar p (P39ModeEtaEndpointPrices.domain hp).1
    (P39ModeEtaEndpointPrices.domain hp).2 (by omega) (by norm_num [deltaBar])

theorem eta_le_tenth {p : ℝ} (hp : p ∈ strip) (k : ℕ) (hk0 : 12 ≤ k) (hk1 : k ≤ 13) :
    eta k p ≤ (1 : ℝ) / 10 := by
  have hm := BinomialPrefixGate.mass_tail_le 26 12 (k + 1) p
    (P39ModeEtaEndpointPrices.domain hp).1 (P39ModeEtaEndpointPrices.domain hp).2
    (by norm_num; linarith only [hp.2]) (by omega) (by omega)
  have hb := P39RightCountBaselines.mass_upper hp 13 (by decide) (by decide)
  norm_num [P39RightCountBaselines.massUpperQ] at hb
  norm_num only [Nat.reduceAdd] at hm
  unfold eta BinomialPrefixGate.tailEta
  apply (div_le_iff₀ (by norm_num [deltaBar] : (0 : ℝ) < 1 - deltaBar)).mpr
  norm_num only [deltaBar]
  nlinarith only [hm, hb]

theorem threshold_eq_ratio {p : ℝ} (hp : p ∈ strip) (k : ℕ) (hk : k ≤ 13) :
    threshold k p = gap * ((k + 1 : ℕ) : ℝ) * (1 - p) / (((26 - k : ℕ) : ℝ) * p) := by
  have hf := BinomialPrefixGate.adjacent_mass_flux 26 k p (by omega)
  have hm := BinomialWeights.mass_pos 26 (k + 1) p (P39ModeEtaEndpointPrices.domain hp).1
    (P39ModeEtaEndpointPrices.domain hp).2 (by omega)
  have hp0 := (P39ModeEtaEndpointPrices.domain hp).1.ne'
  have hn0 : ((26 - k : ℕ) : ℝ) ≠ 0 := (Nat.cast_pos.mpr (show 0 < 26 - k by omega)).ne'
  unfold threshold eta BinomialPrefixGate.tailEta
  norm_num only [deltaBar, gap]
  field_simp [hm.ne', hp0, hn0]
  nlinarith only [hf]

theorem threshold_lower {p : ℝ} (hp : p ∈ strip) (k : ℕ) (hk0 : 12 ≤ k) (hk1 : k ≤ 13) :
    (219 : ℝ) / 200 ≤ threshold k p := by
  rw [threshold_eq_ratio hp k hk1]
  have hp0 := (P39ModeEtaEndpointPrices.domain hp).1
  have hn0 : (0 : ℝ) < (26 - k : ℕ) := Nat.cast_pos.mpr (by omega)
  apply (le_div_iff₀ (mul_pos hn0 hp0)).mpr
  have hcount : ((26 - k : ℕ) : ℝ) ≤ 15 := by exact_mod_cast (show 26 - k ≤ 15 by omega)
  have hnext : (12 : ℝ) ≤ (k + 1 : ℕ) := by exact_mod_cast (show 12 ≤ k + 1 by omega)
  have hq : (3 : ℝ) / 5 ≤ 1 - p := by linarith only [hp.2]
  have hd := mul_le_mul hcount hp.2 hp0.le (by norm_num : (0 : ℝ) ≤ 15)
  have hn := mul_le_mul hnext hq (by norm_num : (0 : ℝ) ≤ 3 / 5) (Nat.cast_nonneg (k + 1))
  have hng := mul_le_mul_of_nonneg_left hn (by norm_num [gap] : (0 : ℝ) ≤ gap)
  norm_num only [gap] at hng ⊢
  nlinarith only [hd, hng]

theorem prefix_eta_identity (k : ℕ) (p : ℝ) :
    BinomialWeights.lowerPrefix 26 k p + eta k p =
      BinomialWeights.lowerPrefix 26 (k + 1) p + deltaBar * eta k p := by
  have he : eta k p * gap = BinomialWeights.mass 26 (k + 1) p := by
    unfold eta BinomialPrefixGate.tailEta gap deltaBar
    ring
  have hpref : BinomialWeights.lowerPrefix 26 (k + 1) p =
      BinomialWeights.lowerPrefix 26 k p + BinomialWeights.mass 26 (k + 1) p := by
    unfold BinomialWeights.lowerPrefix
    rw [Finset.sum_range_succ]
  norm_num only [gap, deltaBar] at he ⊢
  linarith only [he, hpref]

theorem envelope_noise_form (k : ℕ) (p lambda t : ℝ) :
    envelope k p lambda t = BinomialWeights.lowerPrefix 26 k p +
      eta k p * (t + StopLossShape.Q reference (threshold k p + t)) -
      Phi (P39NoiseGate.noiseArgument p ((k : ℝ) + t) lambda) -
      (2 / 25) * (P39Reference.rho0 p + (19 / 10) * lambda / 26) := by
  have ha : (((k : ℝ) - 26 * p) + t) / Real.sqrt (26 * MomentBudgetNoise.variance p + lambda) =
      P39NoiseGate.noiseArgument p ((k : ℝ) + t) lambda := by
    unfold P39NoiseGate.noiseArgument
    congr 1
    ring
  unfold envelope PositivePhasePriceConvex.phasePrice
  rw [ha]

theorem endpoint_arithmetic :
    -(23 / 1000 : ℝ) + (1 / 40 - (2 / 25) * (19 / 10) / 26) * (17 / 50) +
        (1 / 10) * (143 / 5000) ≤ -(7 / 1000) ∧
      -(23 / 1000 : ℝ) + (1 / 40 - (2 / 25) * (19 / 10) / 26) * (17 / 50) +
        (1 / 10) * (deltaBar + 7 / 5000) ≤ -(7 / 1000) := by norm_num [deltaBar]

theorem envelope_zero_upper {p lambda : ℝ} (hp : p ∈ strip)
    (hl : lambda ∈ Icc (0 : ℝ) (17 / 50)) (k : ℕ) (hk0 : 12 ≤ k) (hk1 : k ≤ 13) :
    envelope k p lambda 0 ≤ -(7 / 1000 : ℝ) := by
  have hb := P39RightCountBaselines.baseline_strip_upper hp k hk0 (by omega)
  rw [P39RightCountBaselines.baseline_noise_form] at hb
  have hkR : (12 : ℝ) ≤ k := by exact_mod_cast hk0
  have hn := P39RightCountBaselines.right_noise_loss hp hl.1
    (show 26 * p ≤ (k : ℝ) by linarith only [hkR, hp.2])
  have hQ := ((StopLossShape.Q_antitone reference reference_square_integrable)
    (threshold_lower hp k hk0 hk1)).trans P39ModeEtaEndpointPrices.actual_Q_upper0
  have hQprice := mul_le_mul (eta_le_tenth hp k hk0 hk1) hQ
    (StopLossShape.Q_nonneg reference _) (by norm_num : (0 : ℝ) ≤ 1 / 10)
  have hL := mul_le_mul_of_nonneg_left hl.2
    (by norm_num : (0 : ℝ) ≤ 1 / 40 - (2 / 25) * (19 / 10) / 26)
  rw [envelope_noise_form]
  simp only [add_zero, zero_add]
  nlinarith only [hb, hn, hQprice, hL, endpoint_arithmetic.1]

theorem envelope_one_upper {p lambda : ℝ} (hp : p ∈ strip)
    (hl : lambda ∈ Icc (0 : ℝ) (17 / 50)) (k : ℕ) (hk0 : 12 ≤ k) (hk1 : k ≤ 13) :
    envelope k p lambda 1 ≤ -(7 / 1000 : ℝ) := by
  have hb := P39RightCountBaselines.baseline_strip_upper hp (k + 1) (by omega) (by omega)
  rw [P39RightCountBaselines.baseline_noise_form] at hb
  norm_num only [Nat.cast_add, Nat.cast_one] at hb
  have hkR : (12 : ℝ) ≤ k := by exact_mod_cast hk0
  have hn := P39RightCountBaselines.right_noise_loss hp hl.1
    (show 26 * p ≤ (k : ℝ) + 1 by linarith only [hkR, hp.2])
  have hA : (419 / 200 : ℝ) ≤ threshold k p + 1 := by
    linarith only [threshold_lower hp k hk0 hk1]
  have hQ := ((StopLossShape.Q_antitone reference reference_square_integrable) hA).trans
    P39ModeEtaEndpointPrices.actual_Q_upper1
  have hdelta0 : (0 : ℝ) ≤ deltaBar := by norm_num [deltaBar]
  have hQ0 := StopLossShape.Q_nonneg reference (threshold k p + 1)
  have hQprice := mul_le_mul (eta_le_tenth hp k hk0 hk1) (add_le_add_left hQ deltaBar)
    (by linarith only [hdelta0, hQ0])
    (by norm_num : (0 : ℝ) ≤ 1 / 10)
  have hL := mul_le_mul_of_nonneg_left hl.2
    (by norm_num : (0 : ℝ) ≤ 1 / 40 - (2 / 25) * (19 / 10) / 26)
  have he := prefix_eta_identity k p
  rw [envelope_noise_form]
  nlinarith only [hb, hn, hQprice, hL, he, endpoint_arithmetic.2]

theorem envelope_phase_upper {p lambda t : ℝ} (hp : p ∈ strip)
    (hl : lambda ∈ Icc (0 : ℝ) (17 / 50)) (k : ℕ) (hk0 : 12 ≤ k) (hk1 : k ≤ 13)
    (ht : t ∈ Icc (0 : ℝ) 1) : envelope k p lambda t ≤ -(7 / 1000 : ℝ) := by
  have hkR : (12 : ℝ) ≤ k := by exact_mod_cast hk0
  exact PositivePhasePriceConvex.phasePrice_le_of_endpoints reference reference_square_integrable
    (BinomialWeights.lowerPrefix 26 k p) (eta k p) (threshold k p) ((k : ℝ) - 26 * p)
    (26 * MomentBudgetNoise.variance p + lambda)
    ((2 / 25) * (P39Reference.rho0 p + (19 / 10) * lambda / 26)) 0 1 (-(7 / 1000))
    (P39NoiseGate.actual_variance_pos hp hl.1) (eta_pos hp k hk1).le
    (by linarith only [hkR, hp.2]) (by norm_num)
    (envelope_zero_upper hp hl k hk0 hk1) (envelope_one_upper hp hl k hk0 hk1) t ht

theorem original_closedCDF_le_uniform (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (H C : ℝ) (hm : ContactVariation.PositiveClosedMaximum μ 26 H C)
    (hprev : Extremizer.fixedNSup 25 ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) (hp : p μ ∈ Icc (39 / 100 : ℝ) (2 / 5))
    (k : ℕ) (hk0 : 12 ≤ k) (hk1 : k ≤ 13) (t : ℝ) :
    (normalizedIidSumLaw μ 26).real (Iic (ConditionalResidual.canonicalThreshold μ h 26 k t)) ≤
      BinomialWeights.lowerPrefix 26 k (p μ) + eta k (p μ) *
        (t + StopLossShape.Q reference (threshold k (p μ) + t)) := by
  have hs0 := RefinedLowMomentSupport.original_support μ h 26 (by decide) H C hm hprev hC hρ
  have hs : (μ : Measure ℝ).support ⊆ Icc (-(37 / 16 : ℝ)) (37 / 16) :=
    fun x hx => ⟨(hs0 hx).1.le, (hs0 hx).2.le⟩
  have hO := (scale_and_outward_caps μ h hρ hp).2.2
  have houter : ∀ᵐ u ∂(residual1 μ h : Measure ℝ), u ≤ (5 : ℝ) / 8 :=
    (CanonicalResidualMomentBounds.residual1_upper_of_support μ h (37 / 16) hs).mono (fun _ hu => hu.trans hO)
  have hdelta := (CanonicalInwardBudget.original_inward_lt_seven_eightieths μ h
    26 (by decide) H C hm hprev hC hρ).le
  have haB : a0 μ h ≤ (5 : ℝ) / 8 := by linarith only [hdelta, a1_nonneg μ h]
  have hkR : (12 : ℝ) ≤ k := by exact_mod_cast hk0
  have hmode : ((26 + 1 : ℕ) : ℝ) * p μ ≤ ((k + 2 : ℕ) : ℝ) := by
    norm_num only [Nat.cast_add, Nat.cast_ofNat]
    linarith only [hp.2, hkR]
  have hCDF := BinomialPrefixGate.canonical_normalized_closedCDF_le_Q μ h 26 k (by decide) (by omega)
    (a0 μ h) (a1 μ h) (5 / 8) deltaBar t (a0_nonneg μ h) (a1_nonneg μ h) (by norm_num)
    hdelta (by norm_num [deltaBar]) (CentralGap.residual0_upper μ h) (CentralGap.residual1_lower μ h)
    houter hmode
  dsimp only at hCDF
  change (normalizedIidSumLaw μ 26).real (Iic (ConditionalResidual.canonicalThreshold μ h 26 k t)) ≤
    Staircase.lowerMass (CoupledPrice.canonicalBinomialWeight μ 26) k + eta k (p μ) *
      (t + StopLossShape.Q (TwoMoment.coupledReferenceLaw (residual0 μ h : Measure ℝ)
        (residual1 μ h : Measure ℝ) (a0 μ h) (5 / 8) 26 k)
        (t + CoupledPrice.canonicalBinomialWeight μ 26 k / eta k (p μ))) at hCDF
  rw [← BinomialWeights.prefix_at_canonical μ 26 k] at hCDF
  have harg : t + CoupledPrice.canonicalBinomialWeight μ 26 k / eta k (p μ) = threshold k (p μ) + t := by
    rw [← BinomialWeights.mass_at_canonical μ 26 k]
    unfold threshold
    ring
  rw [harg] at hCDF
  have hQ : StopLossShape.Q (TwoMoment.coupledReferenceLaw (residual0 μ h : Measure ℝ)
      (residual1 μ h : Measure ℝ) (a0 μ h) (5 / 8) 26 k) (threshold k (p μ) + t) ≤
      StopLossShape.Q reference (threshold k (p μ) + t) :=
    UniformCoupledReference.coupledReference_Q_le_uniform
      (residual0 μ h : Measure ℝ) (residual1 μ h : Measure ℝ) (a0 μ h) (5 / 8) (5 / 8) (8 / 25)
      26 k (by decide) (by omega) (a0_nonneg μ h) (by norm_num) (by norm_num) haB le_rfl
      (original_actualCountVariance_le μ h H C hm hprev hC hρ hp k (by omega) hk1) _
  have hprice := mul_le_mul_of_nonneg_left (add_le_add_left hQ t) (eta_pos hp k hk1).le
  nlinarith only [hCDF, hprice]

theorem original_residual_le_envelope (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (H C : ℝ) (hm : ContactVariation.PositiveClosedMaximum μ 26 H C)
    (hprev : Extremizer.fixedNSup 25 ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) (hp : p μ ∈ Icc (39 / 100 : ℝ) (2 / 5))
    (k : ℕ) (hk0 : 12 ≤ k) (hk1 : k ≤ 13) (t : ℝ) :
    ConditionalResidual.positiveTargetResidual μ 26 (ConditionalResidual.canonicalThreshold μ h 26 k t) ≤
      envelope k (p μ) (noiseLevel μ h 26) t := by
  have hCDF := original_closedCDF_le_uniform μ h H C hm hprev hC hρ hp k hk0 hk1 t
  have hr := P39CoarseNoiseIncrement.original_thirdMoment_ge_rho0_add_noise μ h H C hm hprev hC hρ hp
  have hρ0 : 0 ≤ thirdAbsoluteMoment μ :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (Extremizer.thirdAbsoluteMoment_ge_one μ h)
  have hc := mul_le_mul_of_nonneg_right P39NoiseGate.actual_cost_lower hρ0
  have hcredit := mul_le_mul_of_nonneg_left hr (by norm_num : (0 : ℝ) ≤ 2 / 25)
  have hLambda : noiseLevel μ h 26 = 26 * noiseVariance μ h := rfl
  have hcharge : (2 / 25 : ℝ) * (P39Reference.rho0 (p μ) + (19 / 10) * noiseLevel μ h 26 / 26) ≤
      esseenConstant * thirdAbsoluteMoment μ / Real.sqrt 26 := by
    have hl : (2 / 25 : ℝ) * (P39Reference.rho0 (p μ) + (19 / 10) * noiseLevel μ h 26 / 26) ≤
        (2 / 25) * thirdAbsoluteMoment μ := by
      rw [hLambda]
      convert hcredit using 1
      ring
    exact hl.trans (by simpa only [div_mul_eq_mul_div] using hc)
  have ht : ConditionalResidual.canonicalThreshold μ h 26 k t =
      P39NoiseGate.noiseArgument (p μ) ((k : ℝ) + t) (noiseLevel μ h 26) := by
    simpa only [noiseLevel, Nat.cast_ofNat] using P39FrozenNoise.canonical_threshold_eq_noiseArgument μ h k t
  have hPhi := congrArg Phi ht
  rw [envelope_noise_form]
  unfold ConditionalResidual.positiveTargetResidual
  norm_num only [Nat.cast_ofNat]
  nlinarith only [hCDF, hcharge, hPhi]

theorem original_count_phase_upper (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (H C : ℝ) (hm : ContactVariation.PositiveClosedMaximum μ 26 H C)
    (hprev : Extremizer.fixedNSup 25 ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) (hp : p μ ∈ Icc (39 / 100 : ℝ) (2 / 5))
    (k : ℕ) (hk0 : 12 ≤ k) (hk1 : k ≤ 13) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ConditionalResidual.positiveTargetResidual μ 26 (ConditionalResidual.canonicalThreshold μ h 26 k t) ≤
      -(7 / 1000 : ℝ) := by
  have hl0 : 0 ≤ noiseLevel μ h 26 := mul_nonneg (Nat.cast_nonneg 26) (noiseVariance_nonneg μ h)
  have hl1 := P39Count11VarianceAcquisition.original_noiseLevel_le μ h H C hm hprev hC hρ hp
  exact (original_residual_le_envelope μ h H C hm hprev hC hρ hp k hk0 hk1 t).trans
    (envelope_phase_upper hp ⟨hl0, hl1⟩ k hk0 hk1 ht)

theorem original_not_height_interval (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (H C : ℝ) (hm : ContactVariation.PositiveClosedMaximum μ 26 H C)
    (hprev : Extremizer.fixedNSup 25 ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) (hp : p μ ∈ Icc (39 / 100 : ℝ) (2 / 5))
    (k : ℕ) (hk0 : 12 ≤ k) (hk1 : k ≤ 13) :
    CentralGapConditionalIntegral.canonicalHeight μ h 26 H ∉ Icc (k : ℝ) ((k : ℝ) + 1) := by
  intro hheight
  let t := CentralGapConditionalIntegral.canonicalHeight μ h 26 H - (k : ℝ)
  have ht : t ∈ Icc (0 : ℝ) 1 := by
    dsimp only [t]
    constructor <;> linarith only [hheight.1, hheight.2]
  have hu := original_count_phase_upper μ h H C hm hprev hC hρ hp k hk0 hk1 t ht
  have hnum : (k : ℝ) + t - 26 * p μ = scale μ h * H := by
    dsimp only [t, CentralGapConditionalIntegral.canonicalHeight]
    norm_num only [Nat.cast_ofNat]
    ring
  have hthreshold : ConditionalResidual.canonicalThreshold μ h 26 k t = H / Real.sqrt 26 := by
    unfold ConditionalResidual.canonicalThreshold
    norm_num only [Nat.cast_ofNat]
    rw [hnum]
    exact mul_div_mul_left H (Real.sqrt 26) (scale_pos μ h).ne'
  rw [hthreshold] at hu
  have hs : Real.sqrt (26 : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 26)).ne'
  have hcdf : (normalizedIidSumLaw μ 26).real (Iic (H / Real.sqrt 26)) =
      (MixtureSum.iidSumLaw (μ : Measure ℝ) 26).real (Iic H) := by
    rw [Reflection.normalized_closedCDF_eq_raw μ 26 (by decide) (H / Real.sqrt 26)]
    norm_num only [Nat.cast_ofNat]
    have he : Real.sqrt (26 : ℝ) * (H / Real.sqrt 26) = H := by field_simp [hs]
    rw [he]
  unfold ConditionalResidual.positiveTargetResidual at hu
  norm_num only [Nat.cast_ofNat] at hu
  rw [hcdf] at hu
  have ha := hm.attainment
  norm_num only [Nat.cast_ofNat] at ha
  rw [ha] at hu
  have hρ0 : 0 ≤ thirdAbsoluteMoment μ :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (Extremizer.thirdAbsoluteMoment_ge_one μ h)
  have he : 0 ≤ (C - esseenConstant) * thirdAbsoluteMoment μ / Real.sqrt 26 :=
    div_nonneg (mul_nonneg (sub_nonneg.mpr hC) hρ0) (Real.sqrt_nonneg _)
  have heq : (C - esseenConstant) * thirdAbsoluteMoment μ / Real.sqrt 26 =
      C * thirdAbsoluteMoment μ / Real.sqrt 26 - esseenConstant * thirdAbsoluteMoment μ / Real.sqrt 26 := by ring
  rw [heq] at he
  linarith only [hu, he]

theorem original_height_lt_eleven (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (H C : ℝ) (hm : ContactVariation.PositiveClosedMaximum μ 26 H C)
    (hprev : Extremizer.fixedNSup 25 ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) (hp : p μ ∈ Icc (39 / 100 : ℝ) (2 / 5)) :
    CentralGapConditionalIntegral.canonicalHeight μ h 26 H < (11 : ℝ) := by
  have h14 := P39RightRayExclusion.original_height_lt_fourteen μ h H C hm hprev hC hρ hp
  by_contra hnot
  have h11 := le_of_not_gt hnot
  by_cases h12 : CentralGapConditionalIntegral.canonicalHeight μ h 26 H ≤ (12 : ℝ)
  · exact P39ModeTailExclusion.original_not_height_interval μ h H C hm hprev hC hρ hp ⟨h11, h12⟩
  · by_cases h13 : CentralGapConditionalIntegral.canonicalHeight μ h 26 H ≤ (13 : ℝ)
    · exact original_not_height_interval μ h H C hm hprev hC hρ hp 12 (by decide) (by decide)
        ⟨(lt_of_not_ge h12).le, by norm_num only [Nat.cast_ofNat]; exact h13⟩
    · exact original_not_height_interval μ h H C hm hprev hC hρ hp 13 (by decide) (by decide)
        ⟨(lt_of_not_ge h13).le, by norm_num only [Nat.cast_ofNat]; exact h14.le⟩

theorem original_height_window (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (H C : ℝ) (hm : ContactVariation.PositiveClosedMaximum μ 26 H C)
    (hprev : Extremizer.fixedNSup 25 ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) (hp : p μ ∈ Icc (39 / 100 : ℝ) (2 / 5)) :
    CentralGapConditionalIntegral.canonicalHeight μ h 26 H ∈ Ioo (17 / 2 : ℝ) 11 :=
  ⟨P39HeightLocalization.original_height_gt_half_seventeen μ h H C hm hprev hC hρ hp,
    original_height_lt_eleven μ h H C hm hprev hC hρ hp⟩

end BerryEsseen.P39RightCountsExclusion

#print axioms BerryEsseen.P39RightCountsExclusion.original_actualCountVariance_le
#print axioms BerryEsseen.P39RightCountsExclusion.threshold_lower
#print axioms BerryEsseen.P39RightCountsExclusion.prefix_eta_identity
#print axioms BerryEsseen.P39RightCountsExclusion.envelope_phase_upper
#print axioms BerryEsseen.P39RightCountsExclusion.original_closedCDF_le_uniform
#print axioms BerryEsseen.P39RightCountsExclusion.original_count_phase_upper
#print axioms BerryEsseen.P39RightCountsExclusion.original_not_height_interval
#print axioms BerryEsseen.P39RightCountsExclusion.original_height_lt_eleven
#print axioms BerryEsseen.P39RightCountsExclusion.original_height_window
