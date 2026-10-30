module

public import BerryEsseen.P39InwardBudget
public import BerryEsseen.P39Count11VarianceAcquisition

@[expose] public section

/-! 2026-10-30: the acquired delta<1/16 pays a common variance ceiling
for all actual N26 conditional counts 10 through 14. The combination
16*v0+14*v1 is only a resource comparison; it is not an N26 count law or
an assertion about an original maximum at sample size 30. Actual total
noise follows from the same multiplicative allocation coordinates.
-/

noncomputable section

open MeasureTheory Set

namespace BerryEsseen.P39LowCountVarianceAcquisition

open CanonicalSign CentralGap NoiseCoordinates CentralGapReferenceSquareBounds
open P39Count11VarianceAcquisition (retainedCost)

def coefficient0 : ℝ := ConservedTransfer.kappa * 26 * (3 / 5) *
  (6 * (39 / 100) * (15 / 16) / (33 / 40) + 3 * (154 / 25) * (131 / 400))

def coefficient1 : ℝ := ConservedTransfer.kappa * 26 * (39 / 100) *
  (6 * (3 / 5) * (15 / 16) / (5 / 8) + 3 * (104 / 25) * (43 / 80))

theorem coefficient_values : coefficient0 = (6209887281 : ℝ) / 687500000 ∧
    coefficient1 = (510028311 : ℝ) / 62500000 := by
  norm_num [coefficient0, coefficient1, ConservedTransfer.kappa]

theorem coefficient_gates :
    (1129 / 2000 : ℝ) * 16 < coefficient0 ∧
      (1129 / 2000 : ℝ) * 14 < coefficient1 ∧
      (92 / 75 : ℝ) * (66 / 125) ^ 3 < (1129 / 2000) * (8 / 25) := by
  norm_num [coefficient0, coefficient1, ConservedTransfer.kappa]

theorem retainedCost_ge_weighted_variances (p q a b lambda alpha v0 v1 : ℝ)
    (hp : (39 : ℝ) / 100 ≤ p) (hq : (3 : ℝ) / 5 ≤ q)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hdelta : a + b ≤ (1 : ℝ) / 16)
    (hv0 : 0 ≤ v0) (hv1 : 0 ≤ v1) (hcap0 : v0 ≤ a * (33 / 40 : ℝ))
    (hcap1 : v1 ≤ b * (5 / 8 : ℝ))
    (hsplit0 : lambda * (1 - alpha) = 26 * q * v0)
    (hsplit1 : lambda * alpha = 26 * p * v1) :
    coefficient0 * v0 + coefficient1 * v1 ≤ retainedCost p q a b lambda alpha := by
  have hp0 : 0 ≤ p := by linarith only [hp]
  have hq0 : 0 ≤ q := by linarith only [hq]
  have hk := ConservedTransfer.kappa_pos.le
  have hquad := mul_nonneg (add_nonneg ha hb) (sub_nonneg.mpr hdelta)
  have hf : (15 / 16 : ℝ) * (a + b) ≤ CanonicalInwardBudget.gapMass a b := by
    unfold CanonicalInwardBudget.gapMass
    nlinarith only [hquad, mul_nonneg ha hb]
  have hv0a : v0 / (33 / 40 : ℝ) ≤ a := (div_le_iff₀ (by norm_num)).mpr hcap0
  have hv1b : v1 / (5 / 8 : ℝ) ≤ b := (div_le_iff₀ (by norm_num)).mpr hcap1
  have hfv := (mul_le_mul_of_nonneg_left (add_le_add hv0a hv1b)
    (by norm_num : (0 : ℝ) ≤ 15 / 16)).trans hf
  have hpa := mul_le_mul hp hq (by norm_num : (0 : ℝ) ≤ 3 / 5) hp0
  have hga := mul_le_mul_of_nonneg_left hfv
    (show 0 ≤ ConservedTransfer.kappa * 6 * 26 * p * q by positivity)
  have hgc := mul_le_mul_of_nonneg_right hpa
    (show 0 ≤ ConservedTransfer.kappa * 6 * 26 * (15 / 16) *
      (v0 / (33 / 40 : ℝ) + v1 / (5 / 8 : ℝ)) by positivity)
  have hgap :
      ConservedTransfer.kappa * 26 * (3 / 5) * (6 * (39 / 100) * (15 / 16) / (33 / 40)) * v0 +
        ConservedTransfer.kappa * 26 * (39 / 100) * (6 * (3 / 5) * (15 / 16) / (5 / 8)) * v1 ≤
      ConservedTransfer.kappa * 6 * 26 * p * q * CanonicalInwardBudget.gapMass a b := by
    nlinarith only [hga, hgc]
  have hA : (131 : ℝ) / 400 ≤ p - a := by linarith only [hp, hdelta, hb]
  have hB : (43 : ℝ) / 80 ≤ q - b := by linarith only [hq, hdelta, ha]
  have hT0 := mul_le_mul
    (show (154 : ℝ) / 25 ≤ Real.sqrt 10 + 3 by linarith only [P39InwardBudget.sqrt_ten_lower]) hA
    (by norm_num : (0 : ℝ) ≤ 131 / 400) (by positivity : 0 ≤ Real.sqrt 10 + 3)
  have hT1 := mul_le_mul
    (show (104 : ℝ) / 25 ≤ Real.sqrt 10 + 1 by linarith only [P39InwardBudget.sqrt_ten_lower]) hB
    (by norm_num : (0 : ℝ) ≤ 43 / 80) (by positivity : 0 ≤ Real.sqrt 10 + 1)
  have hQ0 := mul_le_mul hq hT0 (by norm_num : (0 : ℝ) ≤ (154 / 25) * (131 / 400)) hq0
  have hP1 := mul_le_mul hp hT1 (by norm_num : (0 : ℝ) ≤ (104 / 25) * (43 / 80)) hp0
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

theorem variance_combination_lt_of_budget (p q c a b lambda alpha v0 v1 : ℝ)
    (hp : (39 : ℝ) / 100 ≤ p) (hq : (3 : ℝ) / 5 ≤ q)
    (hc0 : 0 ≤ c) (hc1 : c ≤ (66 : ℝ) / 125)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hdelta : a + b ≤ (1 : ℝ) / 16)
    (hv0 : 0 ≤ v0) (hv1 : 0 ≤ v1) (hcap0 : v0 ≤ a * (33 / 40 : ℝ))
    (hcap1 : v1 ≤ b * (5 / 8 : ℝ))
    (hsplit0 : lambda * (1 - alpha) = 26 * q * v0)
    (hsplit1 : lambda * alpha = 26 * p * v1)
    (hbudget : retainedCost p q a b lambda alpha ≤ (92 / 75 : ℝ) * c ^ 3) :
    16 * v0 + 14 * v1 < (8 : ℝ) / 25 := by
  have hc := retainedCost_ge_weighted_variances p q a b lambda alpha v0 v1
    hp hq ha hb hdelta hv0 hv1 hcap0 hcap1 hsplit0 hsplit1
  have hu := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hc0 hc1 3)
    (by norm_num : (0 : ℝ) ≤ 92 / 75)
  have hg0 := mul_le_mul_of_nonneg_right coefficient_gates.1.le hv0
  have hg1 := mul_le_mul_of_nonneg_right coefficient_gates.2.1.le hv1
  nlinarith only [hc, hbudget, hu, hg0, hg1, coefficient_gates.2.2]

/-- A resource combination of the same two source variances. This is not
the variance identity of a 26-coordinate conditional count. -/
def varianceCombination (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) : ℝ :=
  16 * variance0 μ h + 14 * variance1 μ h

theorem original_varianceCombination_lt (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (H C : ℝ) (hm : ContactVariation.PositiveClosedMaximum μ 26 H C)
    (hprev : Extremizer.fixedNSup 25 ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10)
    (hp : p μ ∈ Icc (39 / 100 : ℝ) (2 / 5)) : varianceCombination μ h < (8 : ℝ) / 25 := by
  have hc := (P39Count11VarianceAcquisition.scale_and_outward_caps μ h hρ hp).1
  obtain ⟨hv0, hv1⟩ := P39Count11VarianceAcquisition.original_residual_variance_caps
    μ h H C hm hprev hC hρ hp
  obtain ⟨hs0, hs1⟩ := P39Count11VarianceAcquisition.noise_allocation_split μ h
  have hdelta := (P39InwardBudget.original_inward_lt_sixteenth μ h H C hm hprev hC hρ hp).le
  have hq : (3 : ℝ) / 5 ≤ q μ := by unfold q; linarith only [hp.2]
  exact variance_combination_lt_of_budget (p μ) (q μ) (scale μ h) (a0 μ h) (a1 μ h)
    (noiseLevel μ h 26) (ConditionalResidual.actualAllocation μ h) (variance0 μ h) (variance1 μ h)
    hp.1 hq (scale_pos μ h).le hc (a0_nonneg μ h) (a1_nonneg μ h) hdelta
    (variance0_nonneg μ h) (variance1_nonneg μ h) hv0 hv1 hs0 hs1
    (P39Count11VarianceAcquisition.original_retained_budget μ h H C hm hprev hC hρ)

/-- Every actual N26 count in 10..14 is dominated by the resource combination. -/
theorem original_actualCountVariance_lt (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (H C : ℝ) (hm : ContactVariation.PositiveClosedMaximum μ 26 H C)
    (hprev : Extremizer.fixedNSup 25 ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10)
    (hp : p μ ∈ Icc (39 / 100 : ℝ) (2 / 5)) (k : ℕ) (hk0 : 10 ≤ k) (hk1 : k ≤ 14) :
    StaircasePrices.actualCountVariance (residual0 μ h : Measure ℝ) (residual1 μ h : Measure ℝ)
      26 k < (8 : ℝ) / 25 := by
  have h0 : ((26 - k : ℕ) : ℝ) ≤ 16 := by exact_mod_cast (show 26 - k ≤ 16 by omega)
  have h1 : (k : ℝ) ≤ 14 := by exact_mod_cast hk1
  have hm0 := mul_le_mul_of_nonneg_right h0 (variance0_nonneg μ h)
  have hm1 := mul_le_mul_of_nonneg_right h1 (variance1_nonneg μ h)
  have hu := original_varianceCombination_lt μ h H C hm hprev hC hρ hp
  change ((26 - k : ℕ) : ℝ) * variance0 μ h + (k : ℝ) * variance1 μ h < (8 : ℝ) / 25
  exact (add_le_add hm0 hm1).trans_lt hu

theorem original_actualCountVariance_le (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (H C : ℝ) (hm : ContactVariation.PositiveClosedMaximum μ 26 H C)
    (hprev : Extremizer.fixedNSup 25 ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10)
    (hp : p μ ∈ Icc (39 / 100 : ℝ) (2 / 5)) (k : ℕ) (hk0 : 10 ≤ k) (hk1 : k ≤ 14) :
    StaircasePrices.actualCountVariance (residual0 μ h : Measure ℝ) (residual1 μ h : Measure ℝ)
      26 k ≤ (8 : ℝ) / 25 :=
  (original_actualCountVariance_lt μ h H C hm hprev hC hρ hp k hk0 hk1).le

theorem countLaw_secondMoment_eq (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (k : ℕ) (hk : k ≤ 26) :
    (∫ x : ℝ, x ^ 2 ∂CentralGapConditionalIntegral.residualCountLaw μ h 26 k) =
      StaircasePrices.actualCountVariance (residual0 μ h : Measure ℝ) (residual1 μ h : Measure ℝ) 26 k := by
  rw [CentralGapConditionalIntegral.residualCountLaw_eq_map_W μ h 26 k hk,
    integral_map (CommonProduct.measurable_W 26 k hk).aemeasurable (by fun_prop)]
  exact CommonProductMoments.integral_W_sq_of_centered (residual0 μ h) (residual1 μ h)
    (residual0_centered μ h) (residual1_centered μ h) 26 k hk

theorem original_countLaw_secondMoment_lt (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (H C : ℝ) (hm : ContactVariation.PositiveClosedMaximum μ 26 H C)
    (hprev : Extremizer.fixedNSup 25 ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10)
    (hp : p μ ∈ Icc (39 / 100 : ℝ) (2 / 5)) (k : ℕ) (hk0 : 10 ≤ k) (hk1 : k ≤ 14) :
    (∫ x : ℝ, x ^ 2 ∂CentralGapConditionalIntegral.residualCountLaw μ h 26 k) < (8 : ℝ) / 25 := by
  rw [countLaw_secondMoment_eq μ h k (by omega)]
  exact original_actualCountVariance_lt μ h H C hm hprev hC hρ hp k hk0 hk1

/-- Actual total noise, retaining the true weights q and p. No division
by the noise or by the allocation is used at the zero-noise boundary. -/
theorem original_noiseLevel_lt (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (H C : ℝ) (hm : ContactVariation.PositiveClosedMaximum μ 26 H C)
    (hprev : Extremizer.fixedNSup 25 ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10)
    (hp : p μ ∈ Icc (39 / 100 : ℝ) (2 / 5)) : noiseLevel μ h 26 < (793 : ℝ) / 2500 := by
  have hq : q μ ≤ (61 : ℝ) / 100 := by unfold q; linarith only [hp.1]
  have hv0 := variance0_nonneg μ h
  have hv1 := variance1_nonneg μ h
  have hqv := mul_le_mul_of_nonneg_right hq hv0
  have hpv := mul_le_mul_of_nonneg_right hp.2 hv1
  have he := P39Count11VarianceAcquisition.noiseLevel_eq_weighted_variances μ h
  have hcomp : noiseLevel μ h 26 ≤ (793 / 800 : ℝ) * varianceCombination μ h := by
    unfold varianceCombination
    nlinarith only [hqv, hpv, he, hv1]
  have hu := original_varianceCombination_lt μ h H C hm hprev hC hρ hp
  nlinarith only [hcomp, hu]

theorem original_noiseVariance_lt (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (H C : ℝ) (hm : ContactVariation.PositiveClosedMaximum μ 26 H C)
    (hprev : Extremizer.fixedNSup 25 ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10)
    (hp : p μ ∈ Icc (39 / 100 : ℝ) (2 / 5)) : noiseVariance μ h < (793 : ℝ) / 65000 := by
  have hu := original_noiseLevel_lt μ h H C hm hprev hC hρ hp
  change 26 * noiseVariance μ h < (793 : ℝ) / 2500 at hu
  linarith only [hu]

end BerryEsseen.P39LowCountVarianceAcquisition

#print axioms BerryEsseen.P39LowCountVarianceAcquisition.coefficient_gates
#print axioms BerryEsseen.P39LowCountVarianceAcquisition.variance_combination_lt_of_budget
#print axioms BerryEsseen.P39LowCountVarianceAcquisition.original_varianceCombination_lt
#print axioms BerryEsseen.P39LowCountVarianceAcquisition.original_actualCountVariance_lt
#print axioms BerryEsseen.P39LowCountVarianceAcquisition.original_countLaw_secondMoment_lt
#print axioms BerryEsseen.P39LowCountVarianceAcquisition.original_noiseLevel_lt
#print axioms BerryEsseen.P39LowCountVarianceAcquisition.original_noiseVariance_lt
