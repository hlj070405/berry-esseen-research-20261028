module

public import BerryEsseen.P39LowCountVarianceAcquisition
public import BerryEsseen.UniformCoupledReference

@[expose] public section

/-! 2026-10-30: acquired noise tightens the canonical scale and residual
caps. The same original maximum then licenses a common 9/16 reference
for all counts 10..14; no separate source caps or variance plane are input. -/

noncomputable section

open MeasureTheory Set

namespace BerryEsseen.P39RefinedResidualCaps

open CanonicalSign CentralGap

theorem original_scale_lt (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (H C : ℝ) (hm : ContactVariation.PositiveClosedMaximum μ 26 H C)
    (hprev : Extremizer.fixedNSup 25 ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10)
    (hp : p μ ∈ Icc (39 / 100 : ℝ) (2 / 5)) : scale μ h < (201 : ℝ) / 400 := by
  have hs := P39LowCountVarianceAcquisition.original_noiseVariance_lt μ h H C hm hprev hC hρ hp
  have hv := (P39InwardBudget.probability_variance_bounds (p μ) hp).2
  change p μ * q μ ≤ (6 : ℝ) / 25 at hv
  have hc := CanonicalSign.scale_sq μ h
  have hc0 := scale_pos μ h
  nlinarith only [hs, hv, hc, hc0]

theorem original_outward_caps (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (H C : ℝ) (hm : ContactVariation.PositiveClosedMaximum μ 26 H C)
    (hprev : Extremizer.fixedNSup 25 ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10)
    (hp : p μ ∈ Icc (39 / 100 : ℝ) (2 / 5)) :
    O0 μ h (37 / 16) < (31 : ℝ) / 40 ∧ O1 μ h (37 / 16) < (9 : ℝ) / 16 := by
  have hc := original_scale_lt μ h H C hm hprev hC hρ hp
  have hr := mul_lt_mul_of_pos_left hc (by norm_num : (0 : ℝ) < 37 / 16)
  unfold O0 O1 q
  constructor <;> linarith only [hr, hp.1, hp.2]

theorem original_residual1_upper (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (H C : ℝ) (hm : ContactVariation.PositiveClosedMaximum μ 26 H C)
    (hprev : Extremizer.fixedNSup 25 ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10)
    (hp : p μ ∈ Icc (39 / 100 : ℝ) (2 / 5)) :
    ∀ᵐ u ∂(residual1 μ h : Measure ℝ), u < (9 : ℝ) / 16 := by
  have hs0 := RefinedLowMomentSupport.original_support μ h 26 (by decide) H C hm hprev hC hρ
  have hs : (μ : Measure ℝ).support ⊆ Icc (-(37 / 16 : ℝ)) (37 / 16) :=
    fun _ hx => ⟨(hs0 hx).1.le, (hs0 hx).2.le⟩
  have hu := CanonicalResidualMomentBounds.residual1_upper_of_support μ h (37 / 16) hs
  have hc := (original_outward_caps μ h H C hm hprev hC hρ hp).2
  exact hu.mono (fun _ hh => hh.trans_lt hc)

theorem original_reference_Q_le_uniform (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (H C : ℝ) (hm : ContactVariation.PositiveClosedMaximum μ 26 H C)
    (hprev : Extremizer.fixedNSup 25 ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10)
    (hp : p μ ∈ Icc (39 / 100 : ℝ) (2 / 5)) (k : ℕ) (hk0 : 10 ≤ k) (hk1 : k ≤ 14)
    (x : ℝ) :
    StopLossShape.Q (TwoMoment.coupledReferenceLaw
      (residual0 μ h : Measure ℝ) (residual1 μ h : Measure ℝ) (a0 μ h) (9 / 16) 26 k) x ≤
      StopLossShape.Q (TwoMoment.uniformReferenceSumLaw (9 / 16) 26 (8 / 25)) x := by
  have hd := P39InwardBudget.original_inward_lt_sixteenth μ h H C hm hprev hC hρ hp
  have ha : a0 μ h ≤ (9 : ℝ) / 16 := by linarith only [hd, a1_nonneg μ h]
  have hv := P39LowCountVarianceAcquisition.original_actualCountVariance_le
    μ h H C hm hprev hC hρ hp k hk0 hk1
  exact UniformCoupledReference.coupledReference_Q_le_uniform
    (residual0 μ h : Measure ℝ) (residual1 μ h : Measure ℝ)
    (a0 μ h) (9 / 16) (9 / 16) (8 / 25) 26 k (by decide) (by omega)
    (a0_nonneg μ h) (by norm_num) (by norm_num) ha le_rfl hv x

end BerryEsseen.P39RefinedResidualCaps

#print axioms BerryEsseen.P39RefinedResidualCaps.original_scale_lt
#print axioms BerryEsseen.P39RefinedResidualCaps.original_outward_caps
#print axioms BerryEsseen.P39RefinedResidualCaps.original_residual1_upper
#print axioms BerryEsseen.P39RefinedResidualCaps.original_reference_Q_le_uniform
