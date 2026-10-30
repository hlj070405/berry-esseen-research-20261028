module

public import BerryEsseen.P39RefinedResidualCaps
public import BerryEsseen.BinomialPrefixGate
public import BerryEsseen.P39FrozenNoise
public import BerryEsseen.N26P39Count10Prices

@[expose] public section

/-! 2026-10-31: remove allocation from the actual N26 left-count price.
The original law supplies its true count variance and moment floor,
including zero noise. The upper reference uses V0=(26-k)*s/q, rather
than a fixed count-variance ceiling. Exact eta and its threshold remain
unchanged for every real phase. No phase exclusion is asserted here. -/

noncomputable section

open MeasureTheory Set

namespace BerryEsseen.P39LeftAllocationReduction

open CanonicalSign CentralGap NoiseCoordinates GaussianTools

def cost : ℝ := 803 / 10000
def leftVariance (p lambda : ℝ) (k : ℕ) : ℝ :=
  ((26 - k : ℕ) : ℝ) * (lambda / 26) / (1 - p)
def leftReference (p lambda : ℝ) (k : ℕ) : Measure ℝ :=
  TwoMoment.uniformReferenceSumLaw (9 / 16) 26 (leftVariance p lambda k)
def eta (p delta : ℝ) (k : ℕ) : ℝ := BinomialPrefixGate.tailEta 26 k delta p
def threshold (p delta : ℝ) (k : ℕ) : ℝ := BinomialWeights.mass 26 k p / eta p delta k

/-- This envelope has no allocation argument. The reference still keeps
the original law's actual p, lambda and count k. -/
def leftEnvelope (p lambda delta t : ℝ) (k : ℕ) : ℝ :=
  BinomialWeights.lowerPrefix 26 k p + eta p delta k *
      (t + StopLossShape.Q (leftReference p lambda k) (threshold p delta k + t)) -
    Phi (P39NoiseGate.noiseArgument p ((k : ℝ) + t) lambda) -
    cost * MomentBudget.gDelta p (lambda / 26) delta 0

theorem cost_pos : 0 < cost := by norm_num [cost]

theorem cost_le_target : cost ≤ esseenConstant / Real.sqrt (26 : ℝ) := by
  simpa only [cost, N26P39Count10Prices.ci, N26P39Count10Prices.ciQ,
    Rat.cast_div, Rat.cast_ofNat] using N26P39Count10Prices.ci_le_target

theorem allocationVariance_le_zero (p s : ℝ) (k : ℕ) (alpha : ℝ)
    (hp : 0 < p) (hp1 : p < 1) (hs : 0 ≤ s) (hk : k ≤ 26)
    (hcount : (k : ℝ) ≤ 26 * p) (ha : alpha ∈ Icc (0 : ℝ) 1) :
    AllocationEnvelope.allocationVariance p s 26 k alpha ≤
      AllocationEnvelope.allocationVariance p s 26 k 0 := by
  have hd : AllocationEnvelope.varianceSlope p s 26 k ≤ 0 := by
    unfold AllocationEnvelope.varianceSlope
    norm_num only [Nat.cast_ofNat]
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos hs (sub_nonpos.mpr hcount))
      (mul_nonneg hp.le (sub_pos.mpr hp1).le)
  have he := AllocationEnvelope.allocationVariance_sub p s 26 k 0 alpha hp hp1 hk
  simp only [sub_zero] at he
  have hm := mul_nonpos_of_nonpos_of_nonneg hd ha.1
  linarith only [he, hm]

/-- The allocation formula is identified with the actual count moments
before its monotonicity is used. At zero noise both source moments are
proved zero; no ratio by zero noise is introduced. -/
theorem actualCountVariance_eq_allocation (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (k : ℕ) :
    StaircasePrices.actualCountVariance (residual0 μ h : Measure ℝ)
        (residual1 μ h : Measure ℝ) 26 k =
      AllocationEnvelope.allocationVariance (p μ) (noiseVariance μ h) 26 k
        (ConditionalResidual.actualAllocation μ h) := by
  by_cases hs : noiseVariance μ h = 0
  · obtain ⟨h0, h1, _⟩ := ConditionalResidual.canonical_zero_noise_moments μ h hs
    change ((26 - k : ℕ) : ℝ) * MomentBudget.residualSecondMoment (residual0 μ h) +
      (k : ℝ) * MomentBudget.residualSecondMoment (residual1 μ h) = _
    rw [h0, h1, hs]
    simp only [AllocationEnvelope.allocationVariance, zero_mul, mul_zero, add_zero]
  · change ((26 - k : ℕ) : ℝ) * MomentBudget.residualSecondMoment (residual0 μ h) +
      (k : ℝ) * MomentBudget.residualSecondMoment (residual1 μ h) = _
    exact MomentBudget.allocation_count_variance (p μ) _ _ (noiseVariance μ h)
      (ConditionalResidual.actualAllocation μ h) ((26 - k : ℕ) : ℝ) (k : ℝ)
      (p_pos μ h) (p_lt_one μ h)
      (lt_of_le_of_ne (noiseVariance_nonneg μ h) (Ne.symm hs)) rfl rfl

theorem noiseLevel_div_twenty_six (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    noiseLevel μ h 26 / 26 = noiseVariance μ h := by
  unfold noiseLevel
  norm_num

theorem actualCountVariance_le_leftVariance (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (k : ℕ) (hk : k ≤ 26) (hcount : (k : ℝ) ≤ 26 * p μ) :
    StaircasePrices.actualCountVariance (residual0 μ h : Measure ℝ)
        (residual1 μ h : Measure ℝ) 26 k ≤ leftVariance (p μ) (noiseLevel μ h 26) k := by
  rw [actualCountVariance_eq_allocation]
  have hv := allocationVariance_le_zero (p μ) (noiseVariance μ h) k
    (ConditionalResidual.actualAllocation μ h) (p_pos μ h) (p_lt_one μ h)
    (noiseVariance_nonneg μ h) hk hcount (PhysicalResourcePlane.actualAllocation_mem_Icc μ h)
  have he : AllocationEnvelope.allocationVariance (p μ) (noiseVariance μ h) 26 k 0 =
      leftVariance (p μ) (noiseLevel μ h 26) k := by
    unfold leftVariance
    rw [noiseLevel_div_twenty_six]
    simp only [AllocationEnvelope.allocationVariance, sub_zero, mul_zero, zero_div, add_zero, mul_one]
    ring
  exact hv.trans he.le

theorem actual_zero_allocation_floor (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hpHalf : p μ ≤ (1 : ℝ) / 2) (delta : ℝ) (hdelta : 0 < delta)
    (hcap : a0 μ h + a1 μ h ≤ delta) :
    MomentBudget.gDelta (p μ) (noiseVariance μ h) delta 0 ≤ thirdAbsoluteMoment μ := by
  have ha := PhysicalResourcePlane.actualAllocation_mem_Icc μ h
  have hm := MomentBudgetShape.monotoneOn_gDelta_constant (p μ) (noiseVariance μ h) delta
    (p_pos μ h) hpHalf (noiseVariance_nonneg μ h) hdelta
  have hfloor := ConditionalResidual.canonical_actual_allocation_floor μ h (a0 μ h) (a1 μ h)
    delta (a0_nonneg μ h) (a1_nonneg μ h) hdelta hcap
    (CentralGap.residual0_upper μ h) (CentralGap.residual1_lower μ h)
  exact (hm (by constructor <;> norm_num) ha ha.1).trans hfloor

theorem actual_zero_allocation_floor_lambda (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hpHalf : p μ ≤ (1 : ℝ) / 2) (delta : ℝ) (hdelta : 0 < delta)
    (hcap : a0 μ h + a1 μ h ≤ delta) :
    MomentBudget.gDelta (p μ) (noiseLevel μ h 26 / 26) delta 0 ≤ thirdAbsoluteMoment μ := by
  rw [noiseLevel_div_twenty_six]
  exact actual_zero_allocation_floor μ h hpHalf delta hdelta hcap

theorem eta_pos {p delta : ℝ} (hp : p ∈ Icc (39 / 100 : ℝ) (2 / 5))
    (hd : delta < 1) (k : ℕ) (hk : k ≤ 10) : 0 < eta p delta k :=
  BinomialPrefixGate.tailEta_pos 26 k delta p (by linarith only [hp.1])
    (by linarith only [hp.2]) (by omega) hd

/-- The common reference is licensed by actual source caps and V0.
There is deliberately no fixed 8/25 variance premise for count 9. -/
theorem original_reference_Q_le_leftReference (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (H C : ℝ) (hm : ContactVariation.PositiveClosedMaximum μ 26 H C)
    (hprev : Extremizer.fixedNSup 25 ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10)
    (hp : p μ ∈ Icc (39 / 100 : ℝ) (2 / 5)) (k : ℕ) (hk : k ≤ 10) (x : ℝ) :
    StopLossShape.Q (TwoMoment.coupledReferenceLaw (residual0 μ h : Measure ℝ)
      (residual1 μ h : Measure ℝ) (a0 μ h) (9 / 16) 26 k) x ≤
      StopLossShape.Q (leftReference (p μ) (noiseLevel μ h 26) k) x := by
  have hd := P39InwardBudget.original_inward_lt_sixteenth μ h H C hm hprev hC hρ hp
  have haB : a0 μ h ≤ (9 : ℝ) / 16 := by linarith only [hd, a1_nonneg μ h]
  have hkR : (k : ℝ) ≤ 10 := by exact_mod_cast hk
  have hcount : (k : ℝ) ≤ 26 * p μ := by linarith only [hkR, hp.1]
  have hV := actualCountVariance_le_leftVariance μ h k (by omega) hcount
  exact UniformCoupledReference.coupledReference_Q_le_uniform
    (residual0 μ h : Measure ℝ) (residual1 μ h : Measure ℝ)
    (a0 μ h) (9 / 16) (9 / 16) (leftVariance (p μ) (noiseLevel μ h 26) k)
    26 k (by decide) (by omega) (a0_nonneg μ h) (by norm_num) (by norm_num) haB le_rfl hV x

theorem original_closedCDF_le_leftReference (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (H C : ℝ) (hm : ContactVariation.PositiveClosedMaximum μ 26 H C)
    (hprev : Extremizer.fixedNSup 25 ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10)
    (hp : p μ ∈ Icc (39 / 100 : ℝ) (2 / 5)) (delta : ℝ) (hd : delta < 1)
    (hcap : a0 μ h + a1 μ h ≤ delta) (k : ℕ) (hk0 : 9 ≤ k) (hk1 : k ≤ 10) (t : ℝ) :
    (normalizedIidSumLaw μ 26).real (Iic (ConditionalResidual.canonicalThreshold μ h 26 k t)) ≤
      BinomialWeights.lowerPrefix 26 k (p μ) + eta (p μ) delta k *
        (t + StopLossShape.Q (leftReference (p μ) (noiseLevel μ h 26) k) (threshold (p μ) delta k + t)) := by
  have houter : ∀ᵐ u ∂(residual1 μ h : Measure ℝ), u ≤ (9 : ℝ) / 16 :=
    (P39RefinedResidualCaps.original_residual1_upper μ h H C hm hprev hC hρ hp).mono (fun _ hu => hu.le)
  have hkR : (9 : ℝ) ≤ k := by exact_mod_cast hk0
  have hmode : ((26 + 1 : ℕ) : ℝ) * p μ ≤ ((k + 2 : ℕ) : ℝ) := by
    norm_num only [Nat.cast_add, Nat.cast_ofNat]
    linarith only [hp.2, hkR]
  have hCDF := BinomialPrefixGate.canonical_normalized_closedCDF_le_Q μ h 26 k (by decide) (by omega)
    (a0 μ h) (a1 μ h) (9 / 16) delta t (a0_nonneg μ h) (a1_nonneg μ h) (by norm_num)
    hcap hd (CentralGap.residual0_upper μ h) (CentralGap.residual1_lower μ h) houter hmode
  dsimp only at hCDF
  change (normalizedIidSumLaw μ 26).real (Iic (ConditionalResidual.canonicalThreshold μ h 26 k t)) ≤
    Staircase.lowerMass (CoupledPrice.canonicalBinomialWeight μ 26) k + eta (p μ) delta k *
      (t + StopLossShape.Q (TwoMoment.coupledReferenceLaw (residual0 μ h : Measure ℝ)
        (residual1 μ h : Measure ℝ) (a0 μ h) (9 / 16) 26 k)
        (t + CoupledPrice.canonicalBinomialWeight μ 26 k / eta (p μ) delta k)) at hCDF
  rw [← BinomialWeights.prefix_at_canonical μ 26 k] at hCDF
  have harg : t + CoupledPrice.canonicalBinomialWeight μ 26 k / eta (p μ) delta k =
      threshold (p μ) delta k + t := by
    rw [← BinomialWeights.mass_at_canonical μ 26 k]
    unfold threshold
    ring
  rw [harg] at hCDF
  have hQ := original_reference_Q_le_leftReference μ h H C hm hprev hC hρ hp k hk1
    (threshold (p μ) delta k + t)
  have hprice := mul_le_mul_of_nonneg_left (add_le_add_left hQ t) (eta_pos hp hd k hk1).le
  nlinarith only [hCDF, hprice]

/-- All allocation has disappeared from the right-hand side. Phase t
remains arbitrary and the positive cap delta remains a licensed input. -/
theorem original_residual_le_leftEnvelope (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (H C : ℝ) (hm : ContactVariation.PositiveClosedMaximum μ 26 H C)
    (hprev : Extremizer.fixedNSup 25 ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10)
    (hp : p μ ∈ Icc (39 / 100 : ℝ) (2 / 5)) (delta : ℝ) (hd0 : 0 < delta) (hd1 : delta < 1)
    (hcap : a0 μ h + a1 μ h ≤ delta) (k : ℕ) (hk0 : 9 ≤ k) (hk1 : k ≤ 10) (t : ℝ) :
    ConditionalResidual.positiveTargetResidual μ 26 (ConditionalResidual.canonicalThreshold μ h 26 k t) ≤
      leftEnvelope (p μ) (noiseLevel μ h 26) delta t k := by
  have hCDF := original_closedCDF_le_leftReference μ h H C hm hprev hC hρ hp delta hd1 hcap k hk0 hk1 t
  have hfloor := actual_zero_allocation_floor_lambda μ h (by linarith only [hp.2]) delta hd0 hcap
  have hcredit := mul_le_mul_of_nonneg_left hfloor cost_pos.le
  have hρ0 : 0 ≤ thirdAbsoluteMoment μ :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (Extremizer.thirdAbsoluteMoment_ge_one μ h)
  have hc := mul_le_mul_of_nonneg_right cost_le_target hρ0
  have hcost : cost * MomentBudget.gDelta (p μ) (noiseLevel μ h 26 / 26) delta 0 ≤
      esseenConstant * thirdAbsoluteMoment μ / Real.sqrt 26 :=
    hcredit.trans (by simpa only [div_mul_eq_mul_div] using hc)
  have ht : ConditionalResidual.canonicalThreshold μ h 26 k t =
      P39NoiseGate.noiseArgument (p μ) ((k : ℝ) + t) (noiseLevel μ h 26) := by
    simpa only [noiseLevel, Nat.cast_ofNat] using P39FrozenNoise.canonical_threshold_eq_noiseArgument μ h k t
  have hPhi := congrArg Phi ht
  unfold leftEnvelope ConditionalResidual.positiveTargetResidual
  norm_num only [Nat.cast_ofNat]
  nlinarith only [hCDF, hcost, hPhi]

/-- The actual consumer includes the reduced moment-feasibility
constraint and the independently acquired actual lambda domain. -/
theorem original_left_reduction (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (H C : ℝ) (hm : ContactVariation.PositiveClosedMaximum μ 26 H C)
    (hprev : Extremizer.fixedNSup 25 ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10)
    (hp : p μ ∈ Icc (39 / 100 : ℝ) (2 / 5)) (delta : ℝ) (hd0 : 0 < delta) (hd1 : delta < 1)
    (hcap : a0 μ h + a1 μ h ≤ delta) (k : ℕ) (hk0 : 9 ≤ k) (hk1 : k ≤ 10) (t : ℝ) :
    ConditionalResidual.positiveTargetResidual μ 26 (ConditionalResidual.canonicalThreshold μ h 26 k t) ≤
        leftEnvelope (p μ) (noiseLevel μ h 26) delta t k ∧
      MomentBudget.gDelta (p μ) (noiseLevel μ h 26 / 26) delta 0 ≤ thirdAbsoluteMoment μ ∧
      thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10 ∧
      noiseLevel μ h 26 ∈ Icc (0 : ℝ) (17 / 50) := by
  refine ⟨original_residual_le_leftEnvelope μ h H C hm hprev hC hρ hp delta hd0 hd1 hcap k hk0 hk1 t,
    actual_zero_allocation_floor_lambda μ h (by linarith only [hp.2]) delta hd0 hcap, hρ, ?_⟩
  exact ⟨mul_nonneg (Nat.cast_nonneg 26) (noiseVariance_nonneg μ h),
    P39Count11VarianceAcquisition.original_noiseLevel_le μ h H C hm hprev hC hρ hp⟩

theorem original_floor_le_cap (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10)
    (hp : p μ ∈ Icc (39 / 100 : ℝ) (2 / 5)) (delta : ℝ) (hd : 0 < delta)
    (hcap : a0 μ h + a1 μ h ≤ delta) :
    MomentBudget.gDelta (p μ) (noiseLevel μ h 26 / 26) delta 0 ≤ (11 : ℝ) / 10 :=
  (actual_zero_allocation_floor_lambda μ h (by linarith only [hp.2]) delta hd hcap).trans hρ

end BerryEsseen.P39LeftAllocationReduction

#print axioms BerryEsseen.P39LeftAllocationReduction.cost_le_target
#print axioms BerryEsseen.P39LeftAllocationReduction.allocationVariance_le_zero
#print axioms BerryEsseen.P39LeftAllocationReduction.actualCountVariance_eq_allocation
#print axioms BerryEsseen.P39LeftAllocationReduction.actualCountVariance_le_leftVariance
#print axioms BerryEsseen.P39LeftAllocationReduction.actual_zero_allocation_floor
#print axioms BerryEsseen.P39LeftAllocationReduction.original_reference_Q_le_leftReference
#print axioms BerryEsseen.P39LeftAllocationReduction.original_closedCDF_le_leftReference
#print axioms BerryEsseen.P39LeftAllocationReduction.original_residual_le_leftEnvelope
#print axioms BerryEsseen.P39LeftAllocationReduction.original_left_reduction
#print axioms BerryEsseen.P39LeftAllocationReduction.original_floor_le_cap
