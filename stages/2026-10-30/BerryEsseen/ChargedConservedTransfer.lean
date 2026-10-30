module

public import BerryEsseen.ConservedPhaseBudget

@[expose] public section

/-! 2026-10-30: charge the original conserved resource at its actual n.
The charged remainder, its floor-n capped charge, and every conclusion
refer to the same original law and positive closed maximum. A strict
charged first pass licenses removal of the Gaussian weight; the second
pass uses only the defect ceiling acquired in that independent first pass. -/

noncomputable section

open MeasureTheory Set
open BerryEsseen.GaussianTools BerryEsseen.GapDefect BerryEsseen.ContactGapSum
open BerryEsseen.ConservedTransfer

namespace BerryEsseen.ChargedConservedTransfer

/-- Remove exactly the actual-n excess-score term from the original raw resource. -/
def chargedRaw (μ : ProbabilityMeasure ℝ) (n : ℕ) (H C : ℝ) : ℝ :=
  ConservedResource.raw μ n H C -
    (n : ℝ) * (C - esseenConstant) * thirdAbsoluteMoment μ

/-- A floor-n price with an upper score threshold: the raw term is still
evaluated at the actual n, H, C, and original law. -/
def floorChargedRaw (μ : ProbabilityMeasure ℝ) (n N : ℕ) (H C cup : ℝ) : ℝ :=
  ConservedResource.raw μ n H C -
    (N : ℝ) * max 0 (C - cup) * thirdAbsoluteMoment μ

theorem charged_identity (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (R : ℝ) (hR : 0 ≤ R) (hbound : (μ : Measure ℝ).support ⊆ Icc (-R) R)
    (n : ℕ) (hn : 0 < n) (H C : ℝ)
    (hm : ContactVariation.PositiveClosedMaximum μ n H C) :
    (n : ℝ) * esseenConstant * thirdAbsoluteMoment μ * (1 - phase n H) +
      (n : ℝ) * phi 0 * phase n H * actualPhysicalDefect μ / 6 +
      (n : ℝ) * Real.sqrt n * actualL μ n H = chargedRaw μ n H C := by
  have hw := ConservedResource.conserved_identity μ h R hR hbound n hn H C hm
  change (n : ℝ) * (C - esseenConstant) * thirdAbsoluteMoment μ +
    (n : ℝ) * esseenConstant * thirdAbsoluteMoment μ * (1 - phase n H) +
    (n : ℝ) * phi 0 * phase n H * actualPhysicalDefect μ / 6 +
    (n : ℝ) * Real.sqrt n * actualL μ n H = ConservedResource.raw μ n H C at hw
  unfold chargedRaw
  linarith only [hw]

/-- The correct strict score threshold after the exact charge is n CE ρ. -/
theorem raw_lt_score_of_charged_lt (μ : ProbabilityMeasure ℝ) (n : ℕ) (H C : ℝ)
    (hfirst : chargedRaw μ n H C < (n : ℝ) * (esseenConstant * thirdAbsoluteMoment μ)) :
    ConservedResource.raw μ n H C < (n : ℝ) * (C * thirdAbsoluteMoment μ) := by
  unfold chargedRaw at hfirst
  nlinarith only [hfirst]

theorem gamma_threeJ_pos_of_charged_lt (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (R : ℝ) (hR : 0 ≤ R) (hbound : (μ : Measure ℝ).support ⊆ Icc (-R) R)
    (n : ℕ) (hn : 0 < n) (H C : ℝ)
    (hm : ContactVariation.PositiveClosedMaximum μ n H C)
    (hfirst : chargedRaw μ n H C < (n : ℝ) * (esseenConstant * thirdAbsoluteMoment μ)) :
    0 < ZeroBias.gamma μ + 3 * actualJ μ :=
  gamma_threeJ_pos_of_raw_lt_score μ h R hR hbound n hn H C hm
    (raw_lt_score_of_charged_lt μ n H C hfirst)

/-- An independently acquired sign also licenses the unweighted charged resource. -/
theorem unweighted_charged_resource_of_gamma_pos
    (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (R : ℝ) (hR : 0 ≤ R) (hbound : (μ : Measure ℝ).support ⊆ Icc (-R) R)
    (n : ℕ) (hn : 0 < n) (H C : ℝ)
    (hm : ContactVariation.PositiveClosedMaximum μ n H C)
    (ht : 0 < ZeroBias.gamma μ + 3 * actualJ μ) :
    kappa * n * actualPhysicalDefect μ +
      (n : ℝ) * Real.sqrt n * actualL μ n H ≤ chargedRaw μ n H C := by
  have hw := charged_identity μ h R hR hbound n hn H C hm
  have hD := PhysicalDefect.actualPhysicalDefect_nonneg μ h
  have hcoef : 0 ≤ esseenConstant * thirdAbsoluteMoment μ -
      phi 0 / 6 * actualPhysicalDefect μ := by
    rw [ConservedResource.esseenConstant_eq_phi_zero]
    unfold actualPhysicalDefect
    nlinarith [mul_nonneg (phi_nonneg 0) ht.le]
  have hmix := mul_nonneg (Nat.cast_nonneg n)
    (mul_nonneg (sub_nonneg.mpr (phase_le_one n H)) hcoef)
  have hk := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right kappa_le_phi_zero_div_six hD) (Nat.cast_nonneg n)
  nlinarith only [hw, hmix, hk]

/-- Equivalently, subtract the same exact charge from both sides of the
already proved unweighted raw resource. -/
theorem unweighted_charged_resource
    (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (R : ℝ) (hR : 0 ≤ R) (hbound : (μ : Measure ℝ).support ⊆ Icc (-R) R)
    (n : ℕ) (hn : 0 < n) (H C : ℝ)
    (hm : ContactVariation.PositiveClosedMaximum μ n H C)
    (hfirst : chargedRaw μ n H C < (n : ℝ) * (esseenConstant * thirdAbsoluteMoment μ)) :
    kappa * n * actualPhysicalDefect μ +
      (n : ℝ) * Real.sqrt n * actualL μ n H ≤ chargedRaw μ n H C := by
  have hu := unweighted_resource μ h R hR hbound n hn H C hm
    (raw_lt_score_of_charged_lt μ n H C hfirst)
  unfold chargedRaw
  linarith only [hu]

theorem defect_bound_of_gamma_pos (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (R : ℝ) (hR : 0 ≤ R) (hbound : (μ : Measure ℝ).support ⊆ Icc (-R) R)
    (n : ℕ) (hn : 0 < n) (H C r : ℝ)
    (hm : ContactVariation.PositiveClosedMaximum μ n H C)
    (hprice : chargedRaw μ n H C ≤ r)
    (ht : 0 < ZeroBias.gamma μ + 3 * actualJ μ) :
    actualPhysicalDefect μ ≤ r / (kappa * n) := by
  have hu := unweighted_charged_resource_of_gamma_pos μ h R hR hbound n hn H C hm ht
  have hL := actualL_nonneg μ h R hR hbound n hn H C hm
  have hgap : 0 ≤ (n : ℝ) * Real.sqrt n * actualL μ n H := by positivity
  apply (le_div_iff₀ (mul_pos kappa_pos (Nat.cast_pos.mpr hn))).mpr
  nlinarith only [hu, hprice, hgap]

theorem defect_bound (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (R : ℝ) (hR : 0 ≤ R) (hbound : (μ : Measure ℝ).support ⊆ Icc (-R) R)
    (n : ℕ) (hn : 0 < n) (H C r : ℝ)
    (hm : ContactVariation.PositiveClosedMaximum μ n H C)
    (hprice : chargedRaw μ n H C ≤ r)
    (hfirst : r < (n : ℝ) * (esseenConstant * thirdAbsoluteMoment μ)) :
    actualPhysicalDefect μ ≤ r / (kappa * n) :=
  defect_bound_of_gamma_pos μ h R hR hbound n hn H C r hm hprice
    (gamma_threeJ_pos_of_charged_lt μ h R hR hbound n hn H C hm
      (hprice.trans_lt hfirst))

/-- The floor charge never exceeds the exact actual-n excess-score charge.
Both inequalities on score thresholds are used in the max comparison. -/
theorem chargedRaw_le_floorChargedRaw (μ : ProbabilityMeasure ℝ) (n N : ℕ)
    (H C cup : ℝ) (hN : N ≤ n) (hC : esseenConstant ≤ C) (hcup : esseenConstant ≤ cup)
    (hρ : 0 ≤ thirdAbsoluteMoment μ) :
    chargedRaw μ n H C ≤ floorChargedRaw μ n N H C cup := by
  have hmax : max 0 (C - cup) ≤ C - esseenConstant :=
    max_le (sub_nonneg.mpr hC) (by linarith only [hcup])
  have hfee : (N : ℝ) * max 0 (C - cup) ≤ (n : ℝ) * (C - esseenConstant) :=
    (mul_le_mul_of_nonneg_left hmax (Nat.cast_nonneg N)).trans
      (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hN) (sub_nonneg.mpr hC))
  have hfeeρ := mul_le_mul_of_nonneg_right hfee hρ
  unfold chargedRaw floorChargedRaw
  linarith only [hfeeρ]

theorem floor_defect_bound (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (R : ℝ) (hR : 0 ≤ R) (hbound : (μ : Measure ℝ).support ⊆ Icc (-R) R)
    (n N : ℕ) (hn : 0 < n) (hN : N ≤ n) (H C cup r : ℝ)
    (hm : ContactVariation.PositiveClosedMaximum μ n H C)
    (hC : esseenConstant ≤ C) (hcup : esseenConstant ≤ cup)
    (hprice : floorChargedRaw μ n N H C cup ≤ r)
    (hfirst : r < (n : ℝ) * (esseenConstant * thirdAbsoluteMoment μ)) :
    actualPhysicalDefect μ ≤ r / (kappa * n) := by
  have hρ : 0 ≤ thirdAbsoluteMoment μ := by
    linarith [Extremizer.thirdAbsoluteMoment_ge_one μ h]
  exact defect_bound μ h R hR hbound n hn H C r hm
    ((chargedRaw_le_floorChargedRaw μ n N H C cup hN hC hcup hρ).trans hprice) hfirst

/-- The exact charged identity supplies the first phase floor directly. -/
theorem phase_lower_bound (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (R : ℝ) (hR : 0 ≤ R) (hbound : (μ : Measure ℝ).support ⊆ Icc (-R) R)
    (n : ℕ) (hn : 0 < n) (H C r : ℝ)
    (hm : ContactVariation.PositiveClosedMaximum μ n H C)
    (hprice : chargedRaw μ n H C ≤ r) :
    1 - 5 * r / (2 * (n : ℝ)) ≤ phase n H := by
  have hw := charged_identity μ h R hR hbound n hn H C hm
  have hρ1 := Extremizer.thirdAbsoluteMoment_ge_one μ h
  have hρ : 0 ≤ thirdAbsoluteMoment μ := by linarith
  have hCE : 0 ≤ esseenConstant := by linarith [AnalyticConstants.esseenConstant_gt_819_2000]
  have hCEρ : (2 : ℝ) / 5 ≤ esseenConstant * thirdAbsoluteMoment μ := by
    nlinarith [AnalyticConstants.esseenConstant_gt_819_2000,
      mul_nonneg hCE (sub_nonneg.mpr hρ1)]
  have hL := actualL_nonneg μ h R hR hbound n hn H C hm
  have hD := PhysicalDefect.actualPhysicalDefect_nonneg μ h
  have hPhi : 0 ≤ phi 0 := phi_nonneg 0
  have hPhase : 0 ≤ phase n H := (phase_pos n H).le
  have hDterm : 0 ≤ (n : ℝ) * phi 0 * phase n H * actualPhysicalDefect μ / 6 := by
    positivity
  have hgap : 0 ≤ (n : ℝ) * Real.sqrt n * actualL μ n H := by positivity
  have hmultiply := mul_le_mul_of_nonneg_left hCEρ
    (mul_nonneg (Nat.cast_nonneg n) (sub_nonneg.mpr (phase_le_one n H)))
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hratio : 1 - phase n H ≤ 5 * r / (2 * (n : ℝ)) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * (n : ℝ))).mpr
    nlinarith only [hw, hprice, hDterm, hgap, hmultiply]
  linarith only [hratio]

/-- Subtract the exact charge from the retained-phase resource; the defect
ceiling and phase floor must already have been acquired independently. -/
theorem resource_with_phase_curvature
    (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (R : ℝ) (hR : 0 ≤ R) (hbound : (μ : Measure ℝ).support ⊆ Icc (-R) R)
    (n : ℕ) (hn : 0 < n) (H C eLower rhoLower dD : ℝ)
    (hm : ContactVariation.PositiveClosedMaximum μ n H C)
    (hρ : rhoLower ≤ thirdAbsoluteMoment μ) (hD : actualPhysicalDefect μ ≤ dD)
    (he : eLower ≤ phase n H)
    (hA : 0 ≤ (819 / 2000 : ℝ) * rhoLower - dD / 15) :
    kappa * n * actualPhysicalDefect μ + (n : ℝ) * Real.sqrt n * actualL μ n H +
      ConservedPhaseBudget.coefficient eLower rhoLower dD * H ^ 2 ≤ chargedRaw μ n H C := by
  have hu := ConservedPhaseBudget.resource_with_phase_curvature μ h R hR hbound n hn H C
    eLower rhoLower dD hm hρ hD he hA
  unfold chargedRaw
  linarith only [hu]

theorem defect_bound_with_phase_curvature
    (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (R : ℝ) (hR : 0 ≤ R) (hbound : (μ : Measure ℝ).support ⊆ Icc (-R) R)
    (n : ℕ) (hn : 0 < n) (H C eLower rhoLower dD : ℝ)
    (hm : ContactVariation.PositiveClosedMaximum μ n H C)
    (hρ : rhoLower ≤ thirdAbsoluteMoment μ) (hD : actualPhysicalDefect μ ≤ dD)
    (he : eLower ≤ phase n H)
    (hA : 0 ≤ (819 / 2000 : ℝ) * rhoLower - dD / 15) :
    actualPhysicalDefect μ ≤
      (chargedRaw μ n H C - ConservedPhaseBudget.coefficient eLower rhoLower dD * H ^ 2) /
        (kappa * n) := by
  have hu := resource_with_phase_curvature μ h R hR hbound n hn H C
    eLower rhoLower dD hm hρ hD he hA
  have hL := actualL_nonneg μ h R hR hbound n hn H C hm
  have hgap : 0 ≤ (n : ℝ) * Real.sqrt n * actualL μ n H := by positivity
  apply (le_div_iff₀ (mul_pos kappa_pos (Nat.cast_pos.mpr hn))).mpr
  nlinarith only [hu, hgap]

/-- Keep the actual third absolute moment in an affine curvature price;
the incoming defect ceiling is an independent, already proved bound. -/
theorem defect_bound_with_phase_curvature_actual_rho
    (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (R : ℝ) (hR : 0 ≤ R) (hbound : (μ : Measure ℝ).support ⊆ Icc (-R) R)
    (n : ℕ) (hn : 0 < n) (H C eLower dIncoming : ℝ)
    (hm : ContactVariation.PositiveClosedMaximum μ n H C)
    (hD : actualPhysicalDefect μ ≤ dIncoming) (he : eLower ≤ phase n H)
    (hA : 0 ≤ (819 / 2000 : ℝ) * thirdAbsoluteMoment μ - dIncoming / 15) :
    actualPhysicalDefect μ ≤
      (chargedRaw μ n H C -
        ConservedPhaseBudget.coefficient eLower (thirdAbsoluteMoment μ) dIncoming * H ^ 2) /
          (kappa * n) :=
  defect_bound_with_phase_curvature μ h R hR hbound n hn H C eLower
    (thirdAbsoluteMoment μ) dIncoming hm le_rfl hD he hA

/-- A forward second pass: the charged price first acquires a defect ceiling
and phase floor, then retains curvature using precisely those two bounds. -/
theorem second_pass_defect_bound (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (R : ℝ) (hR : 0 ≤ R) (hbound : (μ : Measure ℝ).support ⊆ Icc (-R) R)
    (n : ℕ) (hn : 0 < n) (H C r rhoLower : ℝ)
    (hm : ContactVariation.PositiveClosedMaximum μ n H C)
    (hprice : chargedRaw μ n H C ≤ r)
    (hfirst : r < (n : ℝ) * (esseenConstant * thirdAbsoluteMoment μ))
    (hρ : rhoLower ≤ thirdAbsoluteMoment μ)
    (hA : 0 ≤ (819 / 2000 : ℝ) * rhoLower - (r / (kappa * n)) / 15) :
    actualPhysicalDefect μ ≤
      (chargedRaw μ n H C -
        ConservedPhaseBudget.coefficient (1 - 5 * r / (2 * (n : ℝ)))
          rhoLower (r / (kappa * n)) * H ^ 2) / (kappa * n) :=
  defect_bound_with_phase_curvature μ h R hR hbound n hn H C _ rhoLower _ hm hρ
    (defect_bound μ h R hR hbound n hn H C r hm hprice hfirst)
    (phase_lower_bound μ h R hR hbound n hn H C r hm hprice) hA

theorem floor_second_pass_defect_bound (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (R : ℝ) (hR : 0 ≤ R) (hbound : (μ : Measure ℝ).support ⊆ Icc (-R) R)
    (n N : ℕ) (hn : 0 < n) (hN : N ≤ n) (H C cup r rhoLower : ℝ)
    (hm : ContactVariation.PositiveClosedMaximum μ n H C)
    (hC : esseenConstant ≤ C) (hcup : esseenConstant ≤ cup)
    (hprice : floorChargedRaw μ n N H C cup ≤ r)
    (hfirst : r < (n : ℝ) * (esseenConstant * thirdAbsoluteMoment μ))
    (hρ : rhoLower ≤ thirdAbsoluteMoment μ)
    (hA : 0 ≤ (819 / 2000 : ℝ) * rhoLower - (r / (kappa * n)) / 15) :
    actualPhysicalDefect μ ≤
      (floorChargedRaw μ n N H C cup -
        ConservedPhaseBudget.coefficient (1 - 5 * r / (2 * (n : ℝ)))
          rhoLower (r / (kappa * n)) * H ^ 2) / (kappa * n) := by
  have hρ0 : 0 ≤ thirdAbsoluteMoment μ := by
    linarith [Extremizer.thirdAbsoluteMoment_ge_one μ h]
  have hcharge := chargedRaw_le_floorChargedRaw μ n N H C cup hN hC hcup hρ0
  have hsecond := second_pass_defect_bound μ h R hR hbound n hn H C r rhoLower hm
    (hcharge.trans hprice) hfirst hρ hA
  exact hsecond.trans (div_le_div_of_nonneg_right (sub_le_sub_right hcharge _)
    (mul_pos kappa_pos (Nat.cast_pos.mpr hn)).le)

end BerryEsseen.ChargedConservedTransfer

#print axioms BerryEsseen.ChargedConservedTransfer.charged_identity
#print axioms BerryEsseen.ChargedConservedTransfer.gamma_threeJ_pos_of_charged_lt
#print axioms BerryEsseen.ChargedConservedTransfer.unweighted_charged_resource
#print axioms BerryEsseen.ChargedConservedTransfer.defect_bound
#print axioms BerryEsseen.ChargedConservedTransfer.chargedRaw_le_floorChargedRaw
#print axioms BerryEsseen.ChargedConservedTransfer.floor_defect_bound
#print axioms BerryEsseen.ChargedConservedTransfer.phase_lower_bound
#print axioms BerryEsseen.ChargedConservedTransfer.resource_with_phase_curvature
#print axioms BerryEsseen.ChargedConservedTransfer.defect_bound_with_phase_curvature_actual_rho
#print axioms BerryEsseen.ChargedConservedTransfer.second_pass_defect_bound
#print axioms BerryEsseen.ChargedConservedTransfer.floor_second_pass_defect_bound
