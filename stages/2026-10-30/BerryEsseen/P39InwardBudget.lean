module

public import BerryEsseen.CanonicalInwardBudget

@[expose] public section

/-! 2026-10-30: the actual N26/P39 joint resource sharpens the acquired
inward cap sum to 1/16. The scale/noise identity is used at the original
law. The two rational scale branches retain the uniform 92/75 budget;
no old profile, improved raw constant, or gap-cost lower price is used.
-/

noncomputable section

namespace BerryEsseen.P39InwardBudget

open MeasureTheory Set
open CanonicalSign CentralGap NoiseCoordinates

theorem probability_variance_bounds (p : ℝ) (hp : p ∈ Icc (39 / 100 : ℝ) (2 / 5)) :
    (2379 : ℝ) / 10000 ≤ p * (1 - p) ∧ p * (1 - p) ≤ (6 : ℝ) / 25 := by
  have hlow := mul_nonneg (sub_nonneg.mpr hp.1)
    (show 0 ≤ (61 / 100 : ℝ) - p by linarith only [hp.2])
  have hupp := mul_nonneg (sub_nonneg.mpr hp.2)
    (show 0 ≤ (3 / 5 : ℝ) - p by linarith only [hp.2])
  constructor <;> nlinarith only [hlow, hupp]

lemma sqrt_ten_lower : (79 : ℝ) / 25 ≤ Real.sqrt 10 := by
  nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 10), Real.sqrt_nonneg (10 : ℝ)]

theorem noise_bracket_lower (p a b alpha : ℝ)
    (hp : p ∈ Icc (39 / 100 : ℝ) (2 / 5)) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hdelta : a + b ≤ (7 : ℝ) / 80) (halpha : alpha ∈ Icc (0 : ℝ) 1) :
    (9 : ℝ) / 5 ≤ (Real.sqrt 10 + 3) * (p - a) * (1 - alpha) +
      (Real.sqrt 10 + 1) * ((1 - p) - b) * alpha := by
  have hA : (121 : ℝ) / 400 ≤ p - a := by linarith only [hp.1, hdelta, hb]
  have hB : (41 : ℝ) / 80 ≤ (1 - p) - b := by linarith only [hp.2, hdelta, ha]
  have hT0 := mul_le_mul
    (show (154 : ℝ) / 25 ≤ Real.sqrt 10 + 3 by linarith only [sqrt_ten_lower]) hA
    (by norm_num : (0 : ℝ) ≤ 121 / 400) (by positivity : 0 ≤ Real.sqrt 10 + 3)
  have hT1 := mul_le_mul
    (show (104 : ℝ) / 25 ≤ Real.sqrt 10 + 1 by linarith only [sqrt_ten_lower]) hB
    (by norm_num : (0 : ℝ) ≤ 41 / 80) (by positivity : 0 ≤ Real.sqrt 10 + 1)
  have h0 : (9 : ℝ) / 5 ≤ (Real.sqrt 10 + 3) * (p - a) :=
    (by norm_num : (9 : ℝ) / 5 ≤ (154 / 25) * (121 / 400)).trans hT0
  have h1 : (9 : ℝ) / 5 ≤ (Real.sqrt 10 + 1) * ((1 - p) - b) :=
    (by norm_num : (9 : ℝ) / 5 ≤ (104 / 25) * (41 / 80)).trans hT1
  have hw0 := mul_le_mul_of_nonneg_right h0 (sub_nonneg.mpr halpha.2)
  have hw1 := mul_le_mul_of_nonneg_right h1 halpha.1
  nlinarith only [hw0, hw1]

theorem rational_gates :
    (92 / 75 : ℝ) * (49 / 100) ^ 3 <
        ConservedTransfer.kappa * 26 * (45 / 128) * (2379 / 10000) ∧
      (92 / 75 : ℝ) * 3 * (66 / 125) ^ 2 <
        ConservedTransfer.kappa * 26 * (27 / 5) * (49 / 50) := by
  norm_num [ConservedTransfer.kappa]

/-- This scalar implication uses only actual-coordinate identities and
the retained joint polynomial. Its original-law acquisition follows below. -/
theorem inward_lt_sixteenth_of_joint_budget (p c a b lambda alpha : ℝ)
    (hp : p ∈ Icc (39 / 100 : ℝ) (2 / 5))
    (hc0 : 0 ≤ c) (hc1 : c ≤ (66 : ℝ) / 125) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hdelta : a + b ≤ (7 : ℝ) / 80) (hlambda : 0 ≤ lambda)
    (halpha : alpha ∈ Icc (0 : ℝ) 1)
    (hscale : lambda = 26 * (c ^ 2 - p * (1 - p)))
    (hbudget : ConservedTransfer.kappa *
        CanonicalJointDefectCoordinates.jointPolynomial 26 p a b lambda alpha ≤
      (92 / 75 : ℝ) * c ^ 3) : a + b < (1 : ℝ) / 16 := by
  by_contra hnot
  have hlarge : (1 : ℝ) / 16 ≤ a + b := le_of_not_gt hnot
  have hk : 0 ≤ ConservedTransfer.kappa := ConservedTransfer.kappa_pos.le
  obtain ⟨hpq0, hpq1⟩ := probability_variance_bounds p hp
  have hp0 : 0 ≤ p := by linarith only [hp.1]
  have hq0 : 0 ≤ 1 - p := by linarith only [hp.2]
  have hquad := mul_nonneg (sub_nonneg.mpr hlarge)
    (show 0 ≤ (15 / 16 : ℝ) - (a + b) by linarith only [hdelta])
  have hgap : (15 : ℝ) / 256 ≤ (a + b) * (1 - (a + b)) + a * b := by
    nlinarith only [hquad, mul_nonneg ha hb]
  have hnoise := noise_bracket_lower p a b alpha hp ha hb hdelta halpha
  have hG := mul_le_mul_of_nonneg_left hgap
    (show 0 ≤ 6 * 26 * p * (1 - p) by positivity)
  have hN := mul_le_mul_of_nonneg_left hnoise (show 0 ≤ 3 * lambda by positivity)
  have hBias : 0 ≤ 26 * p * (1 - p) *
      ((6 + 2 * Real.sqrt 10) * (p - JointDefect.pStar) ^ 2) := by positivity
  have hraw : 26 * (p * (1 - p)) * (45 / 128) + (27 / 5) * lambda ≤
      CanonicalJointDefectCoordinates.jointPolynomial 26 p a b lambda alpha := by
    unfold CanonicalJointDefectCoordinates.jointPolynomial
    norm_num only [Nat.cast_ofNat]
    nlinarith only [hG, hN, hBias]
  have hcheap := (mul_le_mul_of_nonneg_left hraw ConservedTransfer.kappa_pos.le).trans hbudget
  have hbase : ConservedTransfer.kappa * 26 * (45 / 128) * (2379 / 10000) ≤
      ConservedTransfer.kappa * (26 * (p * (1 - p)) * (45 / 128)) := by
    have hh := mul_le_mul_of_nonneg_left hpq0
      (show 0 ≤ ConservedTransfer.kappa * 26 * (45 / 128) by positivity)
    nlinarith only [hh]
  by_cases hsmall : c ≤ (49 : ℝ) / 100
  · have hcub := pow_le_pow_left₀ hc0 hsmall 3
    have hn0 : 0 ≤ ConservedTransfer.kappa * (27 / 5) * lambda := by positivity
    norm_num only [ConservedTransfer.kappa] at hcheap hbase hn0
    nlinarith only [hcheap, hbase, hn0, hcub]
  · have hd : 0 ≤ c - (49 : ℝ) / 100 := by linarith only [hsmall]
    have hlower : 26 * (c ^ 2 - (6 : ℝ) / 25) ≤ lambda := by
      nlinarith only [hscale, hpq1]
    have hnprice := mul_le_mul_of_nonneg_left hlower
      (show 0 ≤ ConservedTransfer.kappa * (27 / 5) by positivity)
    have hupper : ConservedTransfer.kappa * 26 * (45 / 128) * (2379 / 10000) +
        ConservedTransfer.kappa * 26 * (27 / 5) * (c ^ 2 - 6 / 25) ≤
        (92 / 75 : ℝ) * c ^ 3 := by
      nlinarith only [hcheap, hbase, hnprice]
    have hc2 := pow_le_pow_left₀ hc0 hc1 2
    have hpoly : c ^ 2 + (49 / 100 : ℝ) * c + (49 / 100 : ℝ) ^ 2 ≤
        3 * (66 / 125 : ℝ) ^ 2 := by nlinarith only [hc2, hc1]
    have hprod := mul_le_mul_of_nonneg_right hpoly hd
    have hcub : c ^ 3 - (49 / 100 : ℝ) ^ 3 ≤ 3 * (66 / 125 : ℝ) ^ 2 * (c - 49 / 100) := by
      nlinarith only [hprod]
    have hquadprice : (49 / 50 : ℝ) * (c - 49 / 100) ≤ c ^ 2 - 6 / 25 := by
      nlinarith only [sq_nonneg (c - (49 / 100 : ℝ))]
    have hnprice2 := mul_le_mul_of_nonneg_left hquadprice
      (show 0 ≤ ConservedTransfer.kappa * 26 * (27 / 5) by positivity)
    norm_num only [ConservedTransfer.kappa] at hupper hnprice2
    nlinarith only [hupper, hnprice2, hcub, hd]

/-- The actual original N26 maximum supplies every scalar premise. The
sample count, full C25 predecessor, original H/C and actual rho remain. -/
theorem original_inward_lt_sixteenth (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (H C : ℝ) (hm : ContactVariation.PositiveClosedMaximum μ 26 H C)
    (hprev : Extremizer.fixedNSup 25 ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10)
    (hp : p μ ∈ Icc (39 / 100 : ℝ) (2 / 5)) : a0 μ h + a1 μ h < (1 : ℝ) / 16 := by
  have hc := CanonicalHeightLocalization.scale_le_two_rho_mul_pq μ h
  have hρscaled := mul_le_mul_of_nonneg_right hρ (show 0 ≤ 2 * p μ * q μ by
    exact mul_nonneg (mul_nonneg (by norm_num) (p_pos μ h).le) (q_pos μ h).le)
  obtain ⟨_, hpq1⟩ := probability_variance_bounds (p μ) hp
  have hccap : scale μ h ≤ (66 : ℝ) / 125 := by
    change p μ * q μ ≤ (6 : ℝ) / 25 at hpq1
    nlinarith only [hc, hρscaled, hpq1]
  have hdelta := (CanonicalInwardBudget.original_inward_lt_seven_eightieths μ h
    26 (by decide) H C hm hprev hC hρ).le
  have hlambda : 0 ≤ noiseLevel μ h 26 :=
    mul_nonneg (Nat.cast_nonneg 26) (noiseVariance_nonneg μ h)
  have hscale : noiseLevel μ h 26 = 26 * (scale μ h ^ 2 - p μ * (1 - p μ)) := by
    unfold noiseLevel
    rw [CanonicalSign.scale_sq]
    unfold q
    ring
  have hu := CanonicalJointDefectCoordinates.original_canonical_resource_bound μ h
    26 (by decide) H C hm hprev hC hρ
  have hs := UniformLowMomentFourierInitial.original_support μ h 26 (by decide) H C hm hprev hC hρ
  have hL := ContactGapSum.actualL_nonneg μ h (12 / 5) (by norm_num) hs 26 (by decide) H C hm
  have hc0 : 0 ≤ scale μ h := (scale_pos μ h).le
  have hcost : 0 ≤ scale μ h ^ 3 * (26 * Real.sqrt 26 * ContactGapSum.actualL μ 26 H) := by positivity
  have hbudget : ConservedTransfer.kappa *
      CanonicalJointDefectCoordinates.jointPolynomial 26 (p μ) (a0 μ h) (a1 μ h)
        (noiseLevel μ h 26) (ConditionalResidual.actualAllocation μ h) ≤
      (92 / 75 : ℝ) * scale μ h ^ 3 := by
    norm_num only [Nat.cast_ofNat] at hu
    nlinarith only [hu, hcost]
  exact inward_lt_sixteenth_of_joint_budget (p μ) (scale μ h) (a0 μ h) (a1 μ h)
    (noiseLevel μ h 26) (ConditionalResidual.actualAllocation μ h) hp (scale_pos μ h).le hccap
    (a0_nonneg μ h) (a1_nonneg μ h) hdelta hlambda
    (PhysicalResourcePlane.actualAllocation_mem_Icc μ h) hscale hbudget

end BerryEsseen.P39InwardBudget

#print axioms BerryEsseen.P39InwardBudget.probability_variance_bounds
#print axioms BerryEsseen.P39InwardBudget.noise_bracket_lower
#print axioms BerryEsseen.P39InwardBudget.inward_lt_sixteenth_of_joint_budget
#print axioms BerryEsseen.P39InwardBudget.original_inward_lt_sixteenth
