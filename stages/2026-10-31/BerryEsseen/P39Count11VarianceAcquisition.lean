module

public import BerryEsseen.CanonicalInwardBudget
public import BerryEsseen.RefinedLowMomentSupport
public import BerryEsseen.CentralGapReferenceSquareBounds
public import BerryEsseen.P39CountVariance

@[expose] public section

/-! 2026-10-30: acquire the actual P39 count-11 variance and total noise.
The count law has 26 coordinates, with 15 negative-group and 11
positive-group residuals. Original support, inward caps and the shared
allocation resource are acquired before the numerical variance ceiling.
No old resource plane or independent variance profile is an input. -/

noncomputable section

open MeasureTheory Set

namespace BerryEsseen.P39Count11VarianceAcquisition

open CanonicalSign CentralGap NoiseCoordinates CentralGapReferenceSquareBounds

def count11Variance (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) : ℝ :=
  15 * variance0 μ h + 11 * variance1 μ h

/-- This is the original CDF's 26-coordinate conditional count law. -/
def count11Law (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) : Measure ℝ :=
  CentralGapConditionalIntegral.residualCountLaw μ h 26 11

theorem count11Law_eq_map_W (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    count11Law μ h =
      (CommonProduct.pairProduct (residual0 μ h : Measure ℝ) (residual1 μ h : Measure ℝ) 26).map
        (CommonProduct.W 26 11) :=
  CentralGapConditionalIntegral.residualCountLaw_eq_map_W μ h 26 11 (by decide)

theorem count11Variance_eq_actualCountVariance (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    count11Variance μ h = StaircasePrices.actualCountVariance
      (residual0 μ h : Measure ℝ) (residual1 μ h : Measure ℝ) 26 11 := rfl

theorem count11Law_moments (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    Integrable (fun x : ℝ => x) (count11Law μ h) ∧
      Integrable (fun x : ℝ => x ^ 2) (count11Law μ h) ∧
      (∫ x : ℝ, x ∂count11Law μ h) = 0 ∧
      (∫ x : ℝ, x ^ 2 ∂count11Law μ h) = count11Variance μ h := by
  have h0 := residual0_centered μ h
  have h1 := residual1_centered μ h
  have hm := CommonProductMoments.moments_W
    (residual0 μ h : Measure ℝ) (residual1 μ h : Measure ℝ)
    h0.integrable_first h0.integrable_second h1.integrable_first h1.integrable_second
    h0.mean_zero h1.mean_zero 26 11 (by decide)
  have hW : AEMeasurable (CommonProduct.W 26 11)
      (CommonProduct.pairProduct (residual0 μ h : Measure ℝ) (residual1 μ h : Measure ℝ) 26) :=
    (CommonProduct.measurable_W 26 11 (by decide)).aemeasurable
  simp only [count11Law_eq_map_W]
  refine ⟨(integrable_map_measure measurable_id.aestronglyMeasurable hW).mpr hm.1,
    (integrable_map_measure (by fun_prop) hW).mpr hm.2.1, ?_, ?_⟩
  · rw [integral_map (f := fun x : ℝ => x) hW measurable_id.aestronglyMeasurable]
    exact hm.2.2.1
  · rw [integral_map hW (by fun_prop)]
    simpa only [count11Variance, variance0, variance1, Nat.reduceSub, Nat.cast_ofNat] using hm.2.2.2

/-- Integrating the true bounded centered source gives its second moment.
Neither endpoint needs to be strictly positive. -/
theorem centered_second_le_product (ν : ProbabilityMeasure ℝ)
    (hν : MomentBudget.CenteredResidualLaw ν) (a O : ℝ)
    (hbound : ∀ᵐ u ∂(ν : Measure ℝ), -O ≤ u ∧ u ≤ a) :
    (∫ u : ℝ, u ^ 2 ∂(ν : Measure ℝ)) ≤ a * O := by
  have hi : Integrable (fun u : ℝ => (a - O) * u + a * O) (ν : Measure ℝ) :=
    (hν.integrable_first.const_mul (a - O)).add (integrable_const (a * O))
  have hp : ∀ᵐ u ∂(ν : Measure ℝ), u ^ 2 ≤ (a - O) * u + a * O := by
    filter_upwards [hbound] with u hu
    have hz := mul_nonneg (sub_nonneg.mpr hu.2) (show 0 ≤ u + O by linarith only [hu.1])
    nlinarith only [hz]
  have hb := integral_mono_ae hν.integrable_second hi hp
  rw [integral_add (hν.integrable_first.const_mul (a - O)) (integrable_const (a * O)),
    integral_const_mul, hν.mean_zero, integral_const, probReal_univ, one_smul] at hb
  simpa only [mul_zero, zero_add] using hb

theorem outward0_polynomial_cap (p : ℝ) :
    (407 / 80 : ℝ) * p * (1 - p) - p ≤ (106929 : ℝ) / 130240 := by
  nlinarith only [sq_nonneg ((814 : ℝ) * p - 327)]

theorem outward1_polynomial_cap (p : ℝ) (hp : p ≤ (2 : ℝ) / 5) :
    (407 / 80 : ℝ) * p * (1 - p) - (1 - p) ≤ (621 : ℝ) / 1000 := by
  have hf := mul_nonneg (sub_nonneg.mpr hp)
    (show 0 ≤ (1621 / 400 : ℝ) - (407 / 80) * p by linarith only [hp])
  nlinarith only [hf]

theorem scale_and_outward_caps (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10)
    (hp : p μ ∈ Icc (39 / 100 : ℝ) (2 / 5)) :
    scale μ h ≤ (66 : ℝ) / 125 ∧ O0 μ h (37 / 16) ≤ (33 : ℝ) / 40 ∧
      O1 μ h (37 / 16) ≤ (5 : ℝ) / 8 := by
  have hp0 := (p_pos μ h).le
  have hq0 := (q_pos μ h).le
  have hc := CanonicalHeightLocalization.scale_le_two_rho_mul_pq μ h
  have hr := mul_le_mul_of_nonneg_right hρ (show 0 ≤ 2 * p μ * q μ by positivity)
  have hscale : scale μ h ≤ (11 / 5 : ℝ) * (p μ * q μ) := by nlinarith only [hc, hr]
  have hpq : p μ * q μ ≤ (6 : ℝ) / 25 := by
    have hz := mul_nonneg (sub_nonneg.mpr hp.2)
      (show 0 ≤ (3 / 5 : ℝ) - p μ by linarith only [hp.2])
    unfold q
    nlinarith only [hz]
  have hsc : scale μ h ≤ (66 : ℝ) / 125 := by
    have hh := mul_le_mul_of_nonneg_left hpq (by norm_num : (0 : ℝ) ≤ 11 / 5)
    nlinarith only [hscale, hh]
  have hR := mul_le_mul_of_nonneg_right hscale (by norm_num : (0 : ℝ) ≤ 37 / 16)
  have hO0 : O0 μ h (37 / 16) ≤ (106929 : ℝ) / 130240 := by
    have hb := outward0_polynomial_cap (p μ)
    unfold O0 q at *
    nlinarith only [hR, hb]
  have hO1 : O1 μ h (37 / 16) ≤ (621 : ℝ) / 1000 := by
    have hb := outward1_polynomial_cap (p μ) hp.2
    unfold O1 q at *
    nlinarith only [hR, hb]
  exact ⟨hsc, hO0.trans (by norm_num), hO1.trans (by norm_num)⟩

theorem original_residual_variance_caps (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (H C : ℝ) (hm : ContactVariation.PositiveClosedMaximum μ 26 H C)
    (hprev : Extremizer.fixedNSup 25 ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10)
    (hp : p μ ∈ Icc (39 / 100 : ℝ) (2 / 5)) :
    variance0 μ h ≤ a0 μ h * (33 / 40 : ℝ) ∧
      variance1 μ h ≤ a1 μ h * (5 / 8 : ℝ) := by
  have hs0 := RefinedLowMomentSupport.original_support μ h 26 (by decide) H C hm hprev hC hρ
  have hs : (μ : Measure ℝ).support ⊆ Icc (-(37 / 16 : ℝ)) (37 / 16) :=
    fun x hx => ⟨(hs0 hx).1.le, (hs0 hx).2.le⟩
  obtain ⟨_, hO0, hO1⟩ := scale_and_outward_caps μ h hρ hp
  have hlow := CanonicalResidualMomentBounds.residual0_lower_of_support μ h (37 / 16) hs
  have hupp := CanonicalResidualMomentBounds.residual1_upper_of_support μ h (37 / 16) hs
  constructor
  · apply centered_second_le_product (residual0 μ h) (residual0_centered μ h) (a0 μ h) (33 / 40)
    filter_upwards [hlow, CentralGap.residual0_upper μ h] with u hl hu
    exact ⟨by linarith only [hl, hO0], hu⟩
  · have hb := centered_second_le_product (residual1 μ h) (residual1_centered μ h)
      (5 / 8) (a1 μ h) (by
        filter_upwards [CentralGap.residual1_lower μ h, hupp] with u hl hu
        exact ⟨hl, hu.trans hO1⟩)
    simpa only [variance1, mul_comm] using hb

/-- Both allocation identities are multiplicative and retain zero noise. -/
theorem noise_allocation_split (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    noiseLevel μ h 26 * (1 - ConditionalResidual.actualAllocation μ h) = 26 * q μ * variance0 μ h ∧
      noiseLevel μ h 26 * ConditionalResidual.actualAllocation μ h = 26 * p μ * variance1 μ h := by
  obtain ⟨hm, hp⟩ := CanonicalJointDefectCoordinates.scaled_theta_parts μ h 26
  have hv0 := residualSecondMoment0_eq μ h
  have hv1 := residualSecondMoment1_eq μ h
  change variance0 μ h = scale μ h ^ 2 * conditionalVariance0 μ h at hv0
  change variance1 μ h = scale μ h ^ 2 * conditionalVariance1 μ h at hv1
  unfold thetaMinus at hm
  unfold thetaPlus at hp
  norm_num only [Nat.cast_ofNat] at hm hp
  constructor
  · rw [hv0]
    calc
      _ = 26 * scale μ h ^ 2 * (q μ * conditionalVariance0 μ h) := hm.symm
      _ = _ := by ring
  · rw [hv1]
    calc
      _ = 26 * scale μ h ^ 2 * (p μ * conditionalVariance1 μ h) := hp.symm
      _ = _ := by ring

def retainedCost (p q a b lambda alpha : ℝ) : ℝ :=
  ConservedTransfer.kappa *
    (6 * 26 * p * q * CanonicalInwardBudget.gapMass a b +
      3 * lambda * ((Real.sqrt 10 + 3) * (p - a) * (1 - alpha) +
        (Real.sqrt 10 + 1) * (q - b) * alpha))

def coefficient0 : ℝ := ConservedTransfer.kappa * 26 * (3 / 5) *
  (6 * (39 / 100) * (73 / 80) / (33 / 40) + 3 * (154 / 25) * (121 / 400))

def coefficient1 : ℝ := ConservedTransfer.kappa * 26 * (39 / 100) *
  (6 * (3 / 5) * (73 / 80) / (5 / 8) + 3 * (104 / 25) * (41 / 80))

theorem coefficient_gates :
    (113 / 200 : ℝ) * 15 < coefficient0 ∧ (113 / 200 : ℝ) * 11 < coefficient1 ∧
      (92 / 75 : ℝ) * (66 / 125) ^ 3 < (113 / 200) * (8 / 25) := by
  norm_num [coefficient0, coefficient1, ConservedTransfer.kappa]

theorem sqrt_ten_lower : (79 : ℝ) / 25 ≤ Real.sqrt 10 := by
  nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 10), Real.sqrt_nonneg (10 : ℝ)]

theorem retainedCost_ge_weighted_variances (p q a b lambda alpha v0 v1 : ℝ)
    (hp : (39 : ℝ) / 100 ≤ p) (hq : (3 : ℝ) / 5 ≤ q)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hdelta : a + b ≤ (7 : ℝ) / 80)
    (hv0 : 0 ≤ v0) (hv1 : 0 ≤ v1) (hcap0 : v0 ≤ a * (33 / 40 : ℝ))
    (hcap1 : v1 ≤ b * (5 / 8 : ℝ))
    (hsplit0 : lambda * (1 - alpha) = 26 * q * v0) (hsplit1 : lambda * alpha = 26 * p * v1) :
    coefficient0 * v0 + coefficient1 * v1 ≤ retainedCost p q a b lambda alpha := by
  have hp0 : 0 ≤ p := by linarith only [hp]
  have hq0 : 0 ≤ q := by linarith only [hq]
  have hk := ConservedTransfer.kappa_pos.le
  have hquad := mul_nonneg (add_nonneg ha hb) (sub_nonneg.mpr hdelta)
  have hf : (73 / 80 : ℝ) * (a + b) ≤ CanonicalInwardBudget.gapMass a b := by
    unfold CanonicalInwardBudget.gapMass
    nlinarith only [hquad, mul_nonneg ha hb]
  have hv0a : v0 / (33 / 40 : ℝ) ≤ a := (div_le_iff₀ (by norm_num)).mpr hcap0
  have hv1b : v1 / (5 / 8 : ℝ) ≤ b := (div_le_iff₀ (by norm_num)).mpr hcap1
  have hfv := (mul_le_mul_of_nonneg_left (add_le_add hv0a hv1b)
    (by norm_num : (0 : ℝ) ≤ 73 / 80)).trans hf
  have hpa := mul_le_mul hp hq (by norm_num : (0 : ℝ) ≤ 3 / 5) hp0
  have hga := mul_le_mul_of_nonneg_left hfv
    (show 0 ≤ ConservedTransfer.kappa * 6 * 26 * p * q by positivity)
  have hgc := mul_le_mul_of_nonneg_right hpa
    (show 0 ≤ ConservedTransfer.kappa * 6 * 26 * (73 / 80) *
      (v0 / (33 / 40 : ℝ) + v1 / (5 / 8 : ℝ)) by positivity)
  have hgap :
      ConservedTransfer.kappa * 26 * (3 / 5) * (6 * (39 / 100) * (73 / 80) / (33 / 40)) * v0 +
        ConservedTransfer.kappa * 26 * (39 / 100) * (6 * (3 / 5) * (73 / 80) / (5 / 8)) * v1 ≤
      ConservedTransfer.kappa * 6 * 26 * p * q * CanonicalInwardBudget.gapMass a b := by
    nlinarith only [hga, hgc]
  have hA : (121 : ℝ) / 400 ≤ p - a := by linarith only [hp, hdelta, hb]
  have hB : (41 : ℝ) / 80 ≤ q - b := by linarith only [hq, hdelta, ha]
  have hT0 := mul_le_mul
    (show (154 : ℝ) / 25 ≤ Real.sqrt 10 + 3 by linarith only [sqrt_ten_lower]) hA
    (by norm_num : (0 : ℝ) ≤ 121 / 400) (by positivity : 0 ≤ Real.sqrt 10 + 3)
  have hT1 := mul_le_mul
    (show (104 : ℝ) / 25 ≤ Real.sqrt 10 + 1 by linarith only [sqrt_ten_lower]) hB
    (by norm_num : (0 : ℝ) ≤ 41 / 80) (by positivity : 0 ≤ Real.sqrt 10 + 1)
  have hQ0 := mul_le_mul hq hT0 (by norm_num : (0 : ℝ) ≤ (154 / 25) * (121 / 400)) hq0
  have hP1 := mul_le_mul hp hT1 (by norm_num : (0 : ℝ) ≤ (104 / 25) * (41 / 80)) hp0
  have hN0 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hQ0 hv0)
    (show 0 ≤ ConservedTransfer.kappa * 3 * 26 by positivity)
  have hN1 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hP1 hv1)
    (show 0 ≤ ConservedTransfer.kappa * 3 * 26 by positivity)
  have hnoise : ConservedTransfer.kappa *
      (3 * lambda * ((Real.sqrt 10 + 3) * (p - a) * (1 - alpha) +
        (Real.sqrt 10 + 1) * (q - b) * alpha)) =
      ConservedTransfer.kappa * 3 * 26 *
        (q * (Real.sqrt 10 + 3) * (p - a) * v0 + p * (Real.sqrt 10 + 1) * (q - b) * v1) := by
    calc
      _ = ConservedTransfer.kappa * 3 *
          ((Real.sqrt 10 + 3) * (p - a) * (lambda * (1 - alpha)) +
            (Real.sqrt 10 + 1) * (q - b) * (lambda * alpha)) := by ring
      _ = _ := by rw [hsplit0, hsplit1]; ring
  unfold retainedCost coefficient0 coefficient1
  nlinarith only [hgap, hN0, hN1, hnoise]

theorem weighted_variance_lt_of_budget (p q c a b lambda alpha v0 v1 : ℝ)
    (hp : (39 : ℝ) / 100 ≤ p) (hq : (3 : ℝ) / 5 ≤ q)
    (hc0 : 0 ≤ c) (hc1 : c ≤ (66 : ℝ) / 125)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hdelta : a + b ≤ (7 : ℝ) / 80)
    (hv0 : 0 ≤ v0) (hv1 : 0 ≤ v1) (hcap0 : v0 ≤ a * (33 / 40 : ℝ))
    (hcap1 : v1 ≤ b * (5 / 8 : ℝ))
    (hsplit0 : lambda * (1 - alpha) = 26 * q * v0) (hsplit1 : lambda * alpha = 26 * p * v1)
    (hbudget : retainedCost p q a b lambda alpha ≤ (92 / 75 : ℝ) * c ^ 3) :
    15 * v0 + 11 * v1 < (8 : ℝ) / 25 := by
  have hc := retainedCost_ge_weighted_variances p q a b lambda alpha v0 v1
    hp hq ha hb hdelta hv0 hv1 hcap0 hcap1 hsplit0 hsplit1
  have hu := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hc0 hc1 3)
    (by norm_num : (0 : ℝ) ≤ 92 / 75)
  have hg0 := mul_le_mul_of_nonneg_right coefficient_gates.1.le hv0
  have hg1 := mul_le_mul_of_nonneg_right coefficient_gates.2.1.le hv1
  nlinarith only [hc, hbudget, hu, hg0, hg1, coefficient_gates.2.2]

theorem original_retained_budget (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (H C : ℝ) (hm : ContactVariation.PositiveClosedMaximum μ 26 H C)
    (hprev : Extremizer.fixedNSup 25 ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) :
    retainedCost (p μ) (q μ) (a0 μ h) (a1 μ h) (noiseLevel μ h 26)
      (ConditionalResidual.actualAllocation μ h) ≤ (92 / 75 : ℝ) * scale μ h ^ 3 := by
  have hu := CanonicalJointDefectCoordinates.original_canonical_resource_bound μ h
    26 (by decide) H C hm hprev hC hρ
  have hs := UniformLowMomentFourierInitial.original_support μ h 26 (by decide) H C hm hprev hC hρ
  have hL := ContactGapSum.actualL_nonneg μ h (12 / 5) (by norm_num) hs 26 (by decide) H C hm
  have hp0 := (p_pos μ h).le
  have hq0 := (q_pos μ h).le
  have hk := ConservedTransfer.kappa_pos.le
  have hc0 := (scale_pos μ h).le
  have hbias : 0 ≤ ConservedTransfer.kappa * 26 * p μ * q μ *
      ((6 + 2 * Real.sqrt 10) * (p μ - JointDefect.pStar) ^ 2) := by positivity
  have hgap : 0 ≤ scale μ h ^ 3 * (26 * Real.sqrt 26 * ContactGapSum.actualL μ 26 H) := by positivity
  unfold retainedCost CanonicalJointDefectCoordinates.jointPolynomial CanonicalInwardBudget.gapMass at *
  unfold q at *
  nlinarith only [hu, hbias, hgap]

theorem original_count11Variance_lt (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (H C : ℝ) (hm : ContactVariation.PositiveClosedMaximum μ 26 H C)
    (hprev : Extremizer.fixedNSup 25 ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10)
    (hp : p μ ∈ Icc (39 / 100 : ℝ) (2 / 5)) : count11Variance μ h < (8 : ℝ) / 25 := by
  have hc := (scale_and_outward_caps μ h hρ hp).1
  obtain ⟨hv0, hv1⟩ := original_residual_variance_caps μ h H C hm hprev hC hρ hp
  obtain ⟨hs0, hs1⟩ := noise_allocation_split μ h
  have hdelta := (CanonicalInwardBudget.original_inward_lt_seven_eightieths μ h
    26 (by decide) H C hm hprev hC hρ).le
  have hq : (3 : ℝ) / 5 ≤ q μ := by unfold q; linarith only [hp.2]
  exact weighted_variance_lt_of_budget (p μ) (q μ) (scale μ h) (a0 μ h) (a1 μ h)
    (noiseLevel μ h 26) (ConditionalResidual.actualAllocation μ h) (variance0 μ h) (variance1 μ h)
    hp.1 hq (scale_pos μ h).le hc (a0_nonneg μ h) (a1_nonneg μ h) hdelta
    (variance0_nonneg μ h) (variance1_nonneg μ h) hv0 hv1 hs0 hs1
    (original_retained_budget μ h H C hm hprev hC hρ)

theorem original_count11Variance_le (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (H C : ℝ) (hm : ContactVariation.PositiveClosedMaximum μ 26 H C)
    (hprev : Extremizer.fixedNSup 25 ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10)
    (hp : p μ ∈ Icc (39 / 100 : ℝ) (2 / 5)) : count11Variance μ h ≤ (8 : ℝ) / 25 :=
  (original_count11Variance_lt μ h H C hm hprev hC hρ hp).le

theorem original_actualCountVariance_le (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (H C : ℝ) (hm : ContactVariation.PositiveClosedMaximum μ 26 H C)
    (hprev : Extremizer.fixedNSup 25 ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10)
    (hp : p μ ∈ Icc (39 / 100 : ℝ) (2 / 5)) :
    StaircasePrices.actualCountVariance (residual0 μ h : Measure ℝ)
      (residual1 μ h : Measure ℝ) 26 11 ≤ (8 : ℝ) / 25 := by
  rw [← count11Variance_eq_actualCountVariance]
  exact original_count11Variance_le μ h H C hm hprev hC hρ hp

theorem original_count11Law_second_moment_le (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (H C : ℝ) (hm : ContactVariation.PositiveClosedMaximum μ 26 H C)
    (hprev : Extremizer.fixedNSup 25 ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10)
    (hp : p μ ∈ Icc (39 / 100 : ℝ) (2 / 5)) :
    (∫ x : ℝ, x ^ 2 ∂count11Law μ h) ≤ (8 : ℝ) / 25 := by
  rw [(count11Law_moments μ h).2.2.2]
  exact original_count11Variance_le μ h H C hm hprev hC hρ hp

theorem noiseLevel_eq_weighted_variances (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    noiseLevel μ h 26 = 26 * (q μ * variance0 μ h + p μ * variance1 μ h) := rfl

theorem original_noiseLevel_le (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (H C : ℝ) (hm : ContactVariation.PositiveClosedMaximum μ 26 H C)
    (hprev : Extremizer.fixedNSup 25 ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10)
    (hp : p μ ∈ Icc (39 / 100 : ℝ) (2 / 5)) : noiseLevel μ h 26 ≤ (17 : ℝ) / 50 := by
  have hv := original_count11Variance_le μ h H C hm hprev hC hρ hp
  have hq : q μ ≤ (61 : ℝ) / 100 := by unfold q; linarith only [hp.1]
  have hqv := mul_le_mul_of_nonneg_right hq (variance0_nonneg μ h)
  have hpv := mul_le_mul_of_nonneg_right hp.2 (variance1_nonneg μ h)
  have he := noiseLevel_eq_weighted_variances μ h
  have hv1 := variance1_nonneg μ h
  have hcomparison : noiseLevel μ h 26 ≤ (793 / 750 : ℝ) * count11Variance μ h := by
    unfold count11Variance
    nlinarith only [hqv, hpv, he, hv1]
  nlinarith only [hcomparison, hv]

theorem original_noiseVariance_le (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (H C : ℝ) (hm : ContactVariation.PositiveClosedMaximum μ 26 H C)
    (hprev : Extremizer.fixedNSup 25 ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10)
    (hp : p μ ∈ Icc (39 / 100 : ℝ) (2 / 5)) : noiseVariance μ h ≤ (17 : ℝ) / 1300 := by
  have hb := original_noiseLevel_le μ h H C hm hprev hC hρ hp
  change 26 * noiseVariance μ h ≤ (17 : ℝ) / 50 at hb
  linarith only [hb]

end BerryEsseen.P39Count11VarianceAcquisition

#print axioms BerryEsseen.P39Count11VarianceAcquisition.count11Law_moments
#print axioms BerryEsseen.P39Count11VarianceAcquisition.centered_second_le_product
#print axioms BerryEsseen.P39Count11VarianceAcquisition.scale_and_outward_caps
#print axioms BerryEsseen.P39Count11VarianceAcquisition.original_residual_variance_caps
#print axioms BerryEsseen.P39Count11VarianceAcquisition.noise_allocation_split
#print axioms BerryEsseen.P39Count11VarianceAcquisition.coefficient_gates
#print axioms BerryEsseen.P39Count11VarianceAcquisition.retainedCost_ge_weighted_variances
#print axioms BerryEsseen.P39Count11VarianceAcquisition.original_count11Variance_le
#print axioms BerryEsseen.P39Count11VarianceAcquisition.original_actualCountVariance_le
#print axioms BerryEsseen.P39Count11VarianceAcquisition.original_count11Law_second_moment_le
#print axioms BerryEsseen.P39Count11VarianceAcquisition.original_noiseLevel_le
#print axioms BerryEsseen.P39Count11VarianceAcquisition.original_noiseVariance_le
