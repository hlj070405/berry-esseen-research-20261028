module

public import BerryEsseen.CanonicalJointDefectCoordinates
public import BerryEsseen.CanonicalHeightLocalization

@[expose] public section

/-! 2026-10-30: acquire a uniform budget for the two actual canonical
inward caps. The scalar exclusion first rules out delta>=1/10; only then
is the stronger scale/pq identity used for the linear n*delta budget.
The original-law endpoints supply every sign, allocation and resource
premise, including zero noise. No inward-cap bound is an incoming profile. -/

noncomputable section

open MeasureTheory Set

namespace BerryEsseen.CanonicalInwardBudget

open CanonicalSign CentralGap NoiseCoordinates GapDefect

def gapMass (a b : ℝ) : ℝ := (a + b) * (1 - (a + b)) + a * b

theorem gapMass_lower_of_large (p q a b : ℝ)
    (hp : (37 : ℝ) / 100 ≤ p) (hq : (37 : ℝ) / 100 ≤ q)
    (hsum : p + q = 1) (hpq : p * q ≤ (1 : ℝ) / 4)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hap : a ≤ p) (hbq : b ≤ q)
    (hlarge : (1 : ℝ) / 10 ≤ a + b) :
    (9 : ℝ) / 100 ≤ gapMass a b := by
  have hsumab : a + b ≤ 1 := by linarith only [hap, hbq, hsum]
  have hab := mul_nonneg ha hb
  by_cases hmid : a + b ≤ (9 : ℝ) / 10
  · have hf := mul_nonneg (sub_nonneg.mpr hlarge) (sub_nonneg.mpr hmid)
    unfold gapMass
    nlinarith only [hf, hab]
  · have hhigh : (9 : ℝ) / 10 ≤ a + b := (le_of_not_ge hmid)
    have hend := mul_nonneg (sub_nonneg.mpr hap) (sub_nonneg.mpr hbq)
    have hpb := mul_le_mul_of_nonneg_right hp hb
    have hqa := mul_le_mul_of_nonneg_right hq ha
    have hf := mul_nonneg (sub_nonneg.mpr hsumab)
      (show 0 ≤ a + b - (37 : ℝ) / 100 by linarith only [hhigh])
    unfold gapMass
    nlinarith only [hend, hpb, hqa, hpq, hf]

theorem inward_lt_tenth_of_budget (n p q c a b : ℝ) (hn : 26 ≤ n)
    (hp : (37 : ℝ) / 100 ≤ p) (hq : (37 : ℝ) / 100 ≤ q) (hsum : p + q = 1)
    (hpq0 : (2331 : ℝ) / 10000 ≤ p * q) (hpq1 : p * q ≤ (1 : ℝ) / 4)
    (hc0 : 0 ≤ c) (hc1 : c ≤ (11 : ℝ) / 20)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hap : a ≤ p) (hbq : b ≤ q)
    (hbudget : ConservedTransfer.kappa * 6 * n * p * q * gapMass a b ≤ (92 / 75 : ℝ) * c ^ 3) :
    a + b < (1 : ℝ) / 10 := by
  by_contra hnot
  have hlarge : (1 : ℝ) / 10 ≤ a + b := le_of_not_gt hnot
  have hf := gapMass_lower_of_large p q a b hp hq hsum hpq1 ha hb hap hbq hlarge
  have hn0 : 0 ≤ n := by linarith only [hn]
  have hpq : 0 ≤ p * q := by linarith only [hpq0]
  have hnpq := mul_le_mul hn hpq0 (by norm_num : (0 : ℝ) ≤ 2331 / 10000) hn0
  have hall := mul_le_mul hnpq hf (by norm_num : (0 : ℝ) ≤ 9 / 100) (mul_nonneg hn0 hpq)
  have hscaled := mul_le_mul_of_nonneg_left hall
    (show 0 ≤ ConservedTransfer.kappa * 6 by norm_num [ConservedTransfer.kappa])
  have hcub := pow_le_pow_left₀ hc0 hc1 3
  have hupper := mul_le_mul_of_nonneg_left hcub (by norm_num : (0 : ℝ) ≤ 92 / 75)
  unfold ConservedTransfer.kappa at hscaled hbudget
  nlinarith only [hscaled, hbudget, hupper]

/-- A scalar implication with the entire varying-n resource as input.
The small-delta license is proved inside this theorem before use. -/
theorem scalar_inward_budget (n p q c a b : ℝ) (hn : 26 ≤ n)
    (hp : (37 : ℝ) / 100 ≤ p) (hq : (37 : ℝ) / 100 ≤ q) (hsum : p + q = 1)
    (hpq0 : (2331 : ℝ) / 10000 ≤ p * q) (hpq1 : p * q ≤ (1 : ℝ) / 4)
    (hc0 : 0 ≤ c) (hscale : c ≤ (11 / 5 : ℝ) * (p * q))
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hap : a ≤ p) (hbq : b ≤ q)
    (hbudget : ConservedTransfer.kappa * 6 * n * p * q * gapMass a b ≤ (92 / 75 : ℝ) * c ^ 3) :
    a + b < (1 : ℝ) / 10 ∧ n * (a + b) ≤ (61226 : ℝ) / 26919 := by
  have hscaleCap : c ≤ (11 : ℝ) / 20 := by
    have hm := mul_le_mul_of_nonneg_left hpq1 (by norm_num : (0 : ℝ) ≤ 11 / 5)
    nlinarith only [hscale, hm]
  have hsmall := inward_lt_tenth_of_budget n p q c a b hn hp hq hsum hpq0 hpq1
    hc0 hscaleCap ha hb hap hbq hbudget
  refine ⟨hsmall, ?_⟩
  have hn0 : 0 ≤ n := by linarith only [hn]
  have hp0 : 0 ≤ p := by linarith only [hp]
  have hq0 : 0 ≤ q := by linarith only [hq]
  have hpqpos : 0 < p * q := by linarith only [hpq0]
  have hdelta := add_nonneg ha hb
  have hquad := mul_nonneg hdelta (sub_nonneg.mpr hsmall.le)
  have hf : (9 / 10 : ℝ) * (a + b) ≤ gapMass a b := by
    unfold gapMass
    nlinarith only [hquad, mul_nonneg ha hb]
  have hcoef : 0 ≤ ConservedTransfer.kappa * 6 * n * p * q := by
    have hk := ConservedTransfer.kappa_pos.le
    positivity
  have hscaled := mul_le_mul_of_nonneg_left hf hcoef
  have hcub := pow_le_pow_left₀ hc0 hscale 3
  have hupper := mul_le_mul_of_nonneg_left hcub (by norm_num : (0 : ℝ) ≤ 92 / 75)
  have hfactor : (p * q) * (ConservedTransfer.kappa * (27 / 5 : ℝ) * n * (a + b)) ≤
      (p * q) * ((92 / 75 : ℝ) * (1331 / 125) * (p * q) ^ 2) := by
    nlinarith only [hscaled, hbudget, hupper]
  have hcancel := (mul_le_mul_iff_of_pos_left hpqpos).mp hfactor
  have hsq := (sq_le_sq₀ hpqpos.le (by norm_num : (0 : ℝ) ≤ 1 / 4)).mpr hpq1
  have hsqprice := mul_le_mul_of_nonneg_left hsq
    (by norm_num : (0 : ℝ) ≤ (92 / 75) * (1331 / 125))
  unfold ConservedTransfer.kappa at hcancel
  nlinarith only [hcancel, hsqprice]

private theorem actual_cap_bounds (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    0 ≤ a0 μ h ∧ 0 ≤ a1 μ h ∧ a0 μ h ≤ p μ ∧ a1 μ h ≤ q μ := by
  have hm : 0 ≤ p μ - a0 μ h := by
    rw [← CanonicalJointDefectCoordinates.scale_mul_Aminus]
    exact mul_nonneg (scale_pos μ h).le (Aminus_nonneg μ h)
  have hp : 0 ≤ q μ - a1 μ h := by
    rw [← CanonicalJointDefectCoordinates.scale_mul_Aplus]
    exact mul_nonneg (scale_pos μ h).le (Aplus_nonneg μ h)
  exact ⟨a0_nonneg μ h, a1_nonneg μ h, sub_nonneg.mp hm, sub_nonneg.mp hp⟩

private theorem gap_part_le_jointPolynomial (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) :
    6 * (n : ℝ) * p μ * q μ * gapMass (a0 μ h) (a1 μ h) ≤
      CanonicalJointDefectCoordinates.jointPolynomial n (p μ) (a0 μ h) (a1 μ h)
        (noiseLevel μ h n) (ConditionalResidual.actualAllocation μ h) := by
  obtain ⟨_, _, hm, hp⟩ := actual_cap_bounds μ h
  have hA := sub_nonneg.mpr hm
  have hB := sub_nonneg.mpr hp
  have halloc := PhysicalResourcePlane.actualAllocation_mem_Icc μ h
  have ha := halloc.1
  have hb := sub_nonneg.mpr halloc.2
  have hp0 := (p_pos μ h).le
  have hq0 := (q_pos μ h).le
  have hl : 0 ≤ noiseLevel μ h n :=
    mul_nonneg (Nat.cast_nonneg n) (noiseVariance_nonneg μ h)
  have hnb : 0 ≤ (n : ℝ) * p μ * q μ *
      ((6 + 2 * Real.sqrt 10) * (p μ - JointDefect.pStar) ^ 2) := by positivity
  have hnn : 0 ≤ 3 * noiseLevel μ h n *
      ((Real.sqrt 10 + 3) * (p μ - a0 μ h) * (1 - ConditionalResidual.actualAllocation μ h) +
        (Real.sqrt 10 + 1) * (q μ - a1 μ h) * ConditionalResidual.actualAllocation μ h) := by
    positivity
  change 6 * (n : ℝ) * p μ * q μ * gapMass (a0 μ h) (a1 μ h) ≤
    (n : ℝ) * p μ * q μ *
      ((6 + 2 * Real.sqrt 10) * (p μ - JointDefect.pStar) ^ 2 +
        6 * gapMass (a0 μ h) (a1 μ h)) +
      3 * noiseLevel μ h n *
        ((Real.sqrt 10 + 3) * (p μ - a0 μ h) * (1 - ConditionalResidual.actualAllocation μ h) +
          (Real.sqrt 10 + 1) * (q μ - a1 μ h) * ConditionalResidual.actualAllocation μ h)
  nlinarith only [hnb, hnn]

/-- Every discarded term is an actual nonnegative cost of this same law,
including the zero-noise branch of its canonical allocation. -/
theorem original_gap_budget (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (hn : 26 ≤ n) (H C : ℝ)
    (hm : ContactVariation.PositiveClosedMaximum μ n H C)
    (hprev : Extremizer.fixedNSup (n - 1) ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) :
    ConservedTransfer.kappa * 6 * (n : ℝ) * p μ * q μ * gapMass (a0 μ h) (a1 μ h) ≤
      (92 / 75 : ℝ) * scale μ h ^ 3 := by
  have hp := mul_le_mul_of_nonneg_left (gap_part_le_jointPolynomial μ h n)
    ConservedTransfer.kappa_pos.le
  have hu := CanonicalJointDefectCoordinates.original_canonical_resource_bound μ h
    n hn H C hm hprev hC hρ
  have hL := ContactGapSum.actualL_nonneg μ h (12 / 5) (by norm_num)
    (UniformLowMomentFourierInitial.original_support μ h n hn H C hm hprev hC hρ)
    n (by omega) H C hm
  have hc0 := (scale_pos μ h).le
  have hgap : 0 ≤ scale μ h ^ 3 * ((n : ℝ) * Real.sqrt n * ContactGapSum.actualL μ n H) := by
    positivity
  nlinarith only [hp, hu, hgap]

private theorem original_scalar_budget (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (hn : 26 ≤ n) (H C : ℝ)
    (hm : ContactVariation.PositiveClosedMaximum μ n H C)
    (hprev : Extremizer.fixedNSup (n - 1) ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) :
    a0 μ h + a1 μ h < (1 : ℝ) / 10 ∧
      (n : ℝ) * (a0 μ h + a1 μ h) ≤ (61226 : ℝ) / 26919 := by
  have hp := LowMomentSignProbabilityBand.p_mem_Icc_37_100_63_100 μ h hρ
  have hq := LowMomentSignProbabilityBand.q_mem_Icc_37_100_63_100 μ h hρ
  have hsum : p μ + q μ = 1 := by unfold q; ring
  have hpq0 : (2331 : ℝ) / 10000 ≤ p μ * q μ := by
    have hm := mul_nonneg (sub_nonneg.mpr hp.1) (sub_nonneg.mpr hp.2)
    unfold q
    nlinarith only [hm]
  have hpq1 : p μ * q μ ≤ (1 : ℝ) / 4 := by
    unfold q
    nlinarith only [sq_nonneg (p μ - (1 / 2 : ℝ))]
  have hc := CanonicalHeightLocalization.scale_le_two_rho_mul_pq μ h
  have hp0 := (p_pos μ h).le
  have hq0 := (q_pos μ h).le
  have hρprice := mul_le_mul_of_nonneg_right hρ
    (show 0 ≤ 2 * p μ * q μ by positivity)
  have hscale : scale μ h ≤ (11 / 5 : ℝ) * (p μ * q μ) := by
    nlinarith only [hc, hρprice]
  obtain ⟨ha, hb, hap, hbq⟩ := actual_cap_bounds μ h
  exact scalar_inward_budget (n : ℝ) (p μ) (q μ) (scale μ h) (a0 μ h) (a1 μ h)
    (by exact_mod_cast hn) hp.1 hq.1 hsum hpq0 hpq1 (scale_pos μ h).le hscale ha hb hap hbq
    (original_gap_budget μ h n hn H C hm hprev hC hρ)

theorem original_inward_lt_tenth (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (hn : 26 ≤ n) (H C : ℝ)
    (hm : ContactVariation.PositiveClosedMaximum μ n H C)
    (hprev : Extremizer.fixedNSup (n - 1) ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) :
    a0 μ h + a1 μ h < (1 : ℝ) / 10 :=
  (original_scalar_budget μ h n hn H C hm hprev hC hρ).1

theorem original_scaled_inward_le (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (hn : 26 ≤ n) (H C : ℝ)
    (hm : ContactVariation.PositiveClosedMaximum μ n H C)
    (hprev : Extremizer.fixedNSup (n - 1) ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) :
    (n : ℝ) * (a0 μ h + a1 μ h) ≤ (61226 : ℝ) / 26919 :=
  (original_scalar_budget μ h n hn H C hm hprev hC hρ).2

theorem original_inward_lt_seven_eightieths (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (hn : 26 ≤ n) (H C : ℝ)
    (hm : ContactVariation.PositiveClosedMaximum μ n H C)
    (hprev : Extremizer.fixedNSup (n - 1) ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) :
    a0 μ h + a1 μ h < (7 : ℝ) / 80 := by
  have hb := original_scaled_inward_le μ h n hn H C hm hprev hC hρ
  have hnR : (26 : ℝ) ≤ n := by exact_mod_cast hn
  have hp := mul_le_mul_of_nonneg_right hnR (add_nonneg (a0_nonneg μ h) (a1_nonneg μ h))
  have hc : (61226 : ℝ) / 26919 < 26 * (7 / 80) := by norm_num
  nlinarith only [hb, hp, hc]

end BerryEsseen.CanonicalInwardBudget

#print axioms BerryEsseen.CanonicalInwardBudget.gapMass_lower_of_large
#print axioms BerryEsseen.CanonicalInwardBudget.inward_lt_tenth_of_budget
#print axioms BerryEsseen.CanonicalInwardBudget.scalar_inward_budget
#print axioms BerryEsseen.CanonicalInwardBudget.original_gap_budget
#print axioms BerryEsseen.CanonicalInwardBudget.original_inward_lt_tenth
#print axioms BerryEsseen.CanonicalInwardBudget.original_scaled_inward_le
#print axioms BerryEsseen.CanonicalInwardBudget.original_inward_lt_seven_eightieths
