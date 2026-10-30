module

public import BerryEsseen.ConservedTransfer

@[expose] public section

/-! 2026-10-29: retain the Gaussian phase cost in the original resource.
The defect ceiling and phase floor are incoming bounds for the same law.
The phase curvature is added once, with its actual-n normalization. -/

noncomputable section

open MeasureTheory Set
open BerryEsseen.GaussianTools BerryEsseen.GapDefect BerryEsseen.ContactGapSum
open BerryEsseen.ConservedTransfer

namespace BerryEsseen.ConservedPhaseBudget

def coefficient (eLower rhoLower dD : ℝ) : ℝ :=
  eLower * ((819 / 2000 : ℝ) * rhoLower - dD / 15) / 2

theorem exp_phase_cost (w : ℝ) : w * Real.exp (-w) ≤ 1 - Real.exp (-w) := by
  have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp w) (Real.exp_pos (-w)).le
  have he : Real.exp (-w) * Real.exp w = 1 := by rw [← Real.exp_add]; simp
  rw [he] at h
  nlinarith only [h]

lemma actual_coefficient_lower (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (rhoLower dD : ℝ) (hρ : rhoLower ≤ thirdAbsoluteMoment μ)
    (hD : actualPhysicalDefect μ ≤ dD) :
    (819 / 2000 : ℝ) * rhoLower - dD / 15 ≤
      esseenConstant * thirdAbsoluteMoment μ - phi 0 / 6 * actualPhysicalDefect μ := by
  have hρ0 : 0 ≤ thirdAbsoluteMoment μ := by
    linarith [Extremizer.thirdAbsoluteMoment_ge_one μ h]
  have hD0 := PhysicalDefect.actualPhysicalDefect_nonneg μ h
  have hCE := mul_le_mul_of_nonneg_right AnalyticConstants.esseenConstant_gt_819_2000.le hρ0
  have hρprice := mul_le_mul_of_nonneg_left hρ (by norm_num : (0 : ℝ) ≤ 819 / 2000)
  have hphi : phi 0 / 6 ≤ (1 : ℝ) / 15 := by linarith [GaussianPrices.phi_zero_lt_2_5]
  have hDprice := mul_le_mul_of_nonneg_right hphi hD0
  nlinarith only [hCE, hρprice, hDprice, hD]

theorem phase_curvature_le_actual_cost (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (hn : 0 < n) (H eLower rhoLower dD : ℝ)
    (hρ : rhoLower ≤ thirdAbsoluteMoment μ) (hD : actualPhysicalDefect μ ≤ dD)
    (he : eLower ≤ phase n H)
    (hA : 0 ≤ (819 / 2000 : ℝ) * rhoLower - dD / 15) :
    coefficient eLower rhoLower dD * H ^ 2 ≤
      (n : ℝ) * (1 - phase n H) *
        (esseenConstant * thirdAbsoluteMoment μ - phi 0 / 6 * actualPhysicalDefect μ) := by
  let w : ℝ := H ^ 2 / (2 * (n : ℝ))
  have hw : 0 ≤ w := div_nonneg (sq_nonneg H) (by positivity)
  have hEW : eLower * w ≤ 1 - phase n H := by
    calc
      _ ≤ phase n H * w := mul_le_mul_of_nonneg_right he hw
      _ ≤ _ := by simpa only [phase, w, mul_comm] using exp_phase_cost w
  have hstep := mul_le_mul_of_nonneg_right hEW hA
  have hactual := mul_le_mul_of_nonneg_left (actual_coefficient_lower μ h rhoLower dD hρ hD)
    (sub_nonneg.mpr (phase_le_one n H))
  have hmul := mul_le_mul_of_nonneg_left (hstep.trans hactual) (Nat.cast_nonneg n)
  have hleft : (n : ℝ) * (eLower * w * ((819 / 2000 : ℝ) * rhoLower - dD / 15)) =
      coefficient eLower rhoLower dD * H ^ 2 := by
    unfold coefficient w
    field_simp [(Nat.cast_pos.mpr hn).ne']
  rw [hleft] at hmul
  nlinarith only [hmul]

theorem resource_with_phase_curvature (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (R : ℝ) (hR : 0 ≤ R) (hbound : (μ : Measure ℝ).support ⊆ Icc (-R) R)
    (n : ℕ) (hn : 0 < n) (H C eLower rhoLower dD : ℝ)
    (hm : ContactVariation.PositiveClosedMaximum μ n H C)
    (hρ : rhoLower ≤ thirdAbsoluteMoment μ) (hD : actualPhysicalDefect μ ≤ dD)
    (he : eLower ≤ phase n H)
    (hA : 0 ≤ (819 / 2000 : ℝ) * rhoLower - dD / 15) :
    (n : ℝ) * (C - esseenConstant) * thirdAbsoluteMoment μ +
      kappa * n * actualPhysicalDefect μ + (n : ℝ) * Real.sqrt n * actualL μ n H +
      coefficient eLower rhoLower dD * H ^ 2 ≤ ConservedResource.raw μ n H C := by
  have hw := ConservedResource.conserved_identity μ h R hR hbound n hn H C hm
  change (n : ℝ) * (C - esseenConstant) * thirdAbsoluteMoment μ +
    (n : ℝ) * esseenConstant * thirdAbsoluteMoment μ * (1 - phase n H) +
    (n : ℝ) * phi 0 * phase n H * actualPhysicalDefect μ / 6 +
    (n : ℝ) * Real.sqrt n * actualL μ n H = ConservedResource.raw μ n H C at hw
  have hcurv := phase_curvature_le_actual_cost μ h n hn H eLower rhoLower dD hρ hD he hA
  have hD0 := PhysicalDefect.actualPhysicalDefect_nonneg μ h
  have hk := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right kappa_le_phi_zero_div_six hD0) (Nat.cast_nonneg n)
  nlinarith only [hw, hcurv, hk]

theorem defect_phase_budget (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (R : ℝ) (hR : 0 ≤ R) (hbound : (μ : Measure ℝ).support ⊆ Icc (-R) R)
    (n : ℕ) (hn : 0 < n) (H C eLower rhoLower dD : ℝ)
    (hm : ContactVariation.PositiveClosedMaximum μ n H C) (hC : esseenConstant ≤ C)
    (hρ : rhoLower ≤ thirdAbsoluteMoment μ) (hD : actualPhysicalDefect μ ≤ dD)
    (he : eLower ≤ phase n H)
    (hA : 0 ≤ (819 / 2000 : ℝ) * rhoLower - dD / 15) :
    kappa * n * actualPhysicalDefect μ ≤ ConservedResource.raw μ n H C -
      coefficient eLower rhoLower dD * H ^ 2 := by
  have ht := resource_with_phase_curvature μ h R hR hbound n hn H C
    eLower rhoLower dD hm hρ hD he hA
  have hL := actualL_nonneg μ h R hR hbound n hn H C hm
  have hρ0 : 0 ≤ thirdAbsoluteMoment μ := by linarith [Extremizer.thirdAbsoluteMoment_ge_one μ h]
  have hfirst : 0 ≤ (n : ℝ) * (C - esseenConstant) * thirdAbsoluteMoment μ :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg n) (sub_nonneg.mpr hC)) hρ0
  have hgap : 0 ≤ (n : ℝ) * Real.sqrt n * actualL μ n H := by positivity
  nlinarith only [ht, hfirst, hgap]

theorem resource_with_phase_curvature_of_raw_bound (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (R : ℝ) (hR : 0 ≤ R) (hbound : (μ : Measure ℝ).support ⊆ Icc (-R) R)
    (n : ℕ) (hn : 0 < n) (H C r0 rhoLower dD : ℝ)
    (hm : ContactVariation.PositiveClosedMaximum μ n H C) (hC : esseenConstant ≤ C)
    (hraw : ConservedResource.raw μ n H C ≤ r0)
    (hρ : rhoLower ≤ thirdAbsoluteMoment μ) (hD : actualPhysicalDefect μ ≤ dD)
    (hA : 0 ≤ (819 / 2000 : ℝ) * rhoLower - dD / 15) :
    (n : ℝ) * (C - esseenConstant) * thirdAbsoluteMoment μ +
      kappa * n * actualPhysicalDefect μ + (n : ℝ) * Real.sqrt n * actualL μ n H +
      coefficient (1 - 5 * r0 / (2 * (n : ℝ))) rhoLower dD * H ^ 2 ≤
        ConservedResource.raw μ n H C :=
  resource_with_phase_curvature μ h R hR hbound n hn H C _ rhoLower dD hm hρ hD
    (phase_lower_bound μ h R hR hbound n hn H C r0 hm hC hraw) hA

end BerryEsseen.ConservedPhaseBudget

#print axioms BerryEsseen.ConservedPhaseBudget.exp_phase_cost
#print axioms BerryEsseen.ConservedPhaseBudget.actual_coefficient_lower
#print axioms BerryEsseen.ConservedPhaseBudget.resource_with_phase_curvature
#print axioms BerryEsseen.ConservedPhaseBudget.defect_phase_budget
#print axioms BerryEsseen.ConservedPhaseBudget.resource_with_phase_curvature_of_raw_bound
