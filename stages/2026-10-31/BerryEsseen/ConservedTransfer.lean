module

public import BerryEsseen.ConservedResource
public import BerryEsseen.PhysicalDefect
public import BerryEsseen.AnalyticConstants

@[expose] public section

/-! 2026-10-28: forward acquisition from the actual conserved resource.
The first strict raw-price bound licenses removal of the Gaussian weight;
the resulting defect bound is never assumed to license its own first pass. -/

noncomputable section

open MeasureTheory Set
open BerryEsseen.GaussianTools BerryEsseen.GapDefect BerryEsseen.ContactGapSum

namespace BerryEsseen.ConservedTransfer

def kappa : ℝ := 997 / 15000

lemma kappa_pos : 0 < kappa := by norm_num [kappa]

theorem kappa_le_phi_zero_div_six : kappa ≤ phi 0 / 6 := by
  have hr : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hs := Real.sq_sqrt (show 0 ≤ 2 * Real.pi by positivity)
  have hp := Real.pi_lt_d4
  have hu : Real.sqrt (2 * Real.pi) < (2500 : ℝ) / 997 := by nlinarith
  have hd : (997 : ℝ) / 2500 < phi 0 := by
    rw [GaussianPrices.phi_zero_eq]
    apply (lt_div_iff₀ hr).mpr
    nlinarith
  unfold kappa
  linarith

def phase (n : ℕ) (H : ℝ) : ℝ := Real.exp (-(H ^ 2 / (2 * (n : ℝ))))

theorem phase_pos (n : ℕ) (H : ℝ) : 0 < phase n H := Real.exp_pos _

theorem phase_le_one (n : ℕ) (H : ℝ) : phase n H ≤ 1 := by
  unfold phase
  apply Real.exp_le_one_iff.mpr
  exact neg_nonpos.mpr (div_nonneg (sq_nonneg H) (by positivity))

theorem gamma_threeJ_pos_of_raw_lt_score (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (R : ℝ) (hR : 0 ≤ R) (hbound : (μ : Measure ℝ).support ⊆ Icc (-R) R)
    (n : ℕ) (hn : 0 < n) (H C : ℝ)
    (hm : ContactVariation.PositiveClosedMaximum μ n H C)
    (hraw : ConservedResource.raw μ n H C < (n : ℝ) * (C * thirdAbsoluteMoment μ)) :
    0 < ZeroBias.gamma μ + 3 * actualJ μ := by
  have hb := ConservedResource.balanced_identity μ h R hR hbound n hn H C hm
  have hL := actualL_nonneg μ h R hR hbound n hn H C hm
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hquot : ConservedResource.raw μ n H C / n < C * thirdAbsoluteMoment μ :=
    (div_lt_iff₀ hnR).mpr (by nlinarith only [hraw])
  have hp := phi_pos (H / Real.sqrt n)
  have hprice : 0 < phi (H / Real.sqrt n) * (ZeroBias.gamma μ + 3 * actualJ μ) := by
    nlinarith [mul_nonneg (Real.sqrt_nonneg (n : ℝ)) hL]
  exact pos_of_mul_pos_right hprice hp.le

theorem unweighted_resource (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (R : ℝ) (hR : 0 ≤ R) (hbound : (μ : Measure ℝ).support ⊆ Icc (-R) R)
    (n : ℕ) (hn : 0 < n) (H C : ℝ)
    (hm : ContactVariation.PositiveClosedMaximum μ n H C)
    (hraw : ConservedResource.raw μ n H C < (n : ℝ) * (C * thirdAbsoluteMoment μ)) :
    (n : ℝ) * (C - esseenConstant) * thirdAbsoluteMoment μ +
      kappa * n * actualPhysicalDefect μ + (n : ℝ) * Real.sqrt n * actualL μ n H ≤
        ConservedResource.raw μ n H C := by
  have hw := ConservedResource.conserved_identity μ h R hR hbound n hn H C hm
  change (n : ℝ) * (C - esseenConstant) * thirdAbsoluteMoment μ +
    (n : ℝ) * esseenConstant * thirdAbsoluteMoment μ * (1 - phase n H) +
    (n : ℝ) * phi 0 * phase n H * actualPhysicalDefect μ / 6 +
    (n : ℝ) * Real.sqrt n * actualL μ n H = ConservedResource.raw μ n H C at hw
  have ht := gamma_threeJ_pos_of_raw_lt_score μ h R hR hbound n hn H C hm hraw
  have hD := PhysicalDefect.actualPhysicalDefect_nonneg μ h
  have hcoef : 0 ≤ esseenConstant * thirdAbsoluteMoment μ - phi 0 / 6 * actualPhysicalDefect μ := by
    rw [ConservedResource.esseenConstant_eq_phi_zero]
    unfold actualPhysicalDefect
    nlinarith [mul_nonneg (phi_nonneg 0) ht.le]
  have hmix := mul_nonneg (sub_nonneg.mpr (phase_le_one n H)) hcoef
  have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hmixn := mul_nonneg hnR hmix
  have hk := mul_le_mul_of_nonneg_right kappa_le_phi_zero_div_six hD
  have hkn := mul_le_mul_of_nonneg_left hk hnR
  nlinarith only [hw, hmixn, hkn]

theorem defect_bound (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (R : ℝ) (hR : 0 ≤ R) (hbound : (μ : Measure ℝ).support ⊆ Icc (-R) R)
    (n : ℕ) (hn : 0 < n) (H C r : ℝ)
    (hm : ContactVariation.PositiveClosedMaximum μ n H C) (hC : esseenConstant ≤ C)
    (hprice : ConservedResource.raw μ n H C ≤ r)
    (hfirst : r < (n : ℝ) * (C * thirdAbsoluteMoment μ)) :
    actualPhysicalDefect μ ≤ r / (kappa * n) := by
  have hu := unweighted_resource μ h R hR hbound n hn H C hm (hprice.trans_lt hfirst)
  have hL := actualL_nonneg μ h R hR hbound n hn H C hm
  have hρ : 0 ≤ thirdAbsoluteMoment μ := (Extremizer.thirdAbsoluteMoment_ge_one μ h).trans' (by norm_num)
  have hA : 0 ≤ (n : ℝ) * (C - esseenConstant) * thirdAbsoluteMoment μ :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg n) (sub_nonneg.mpr hC)) hρ
  have hB : 0 ≤ (n : ℝ) * Real.sqrt n * actualL μ n H :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg n) (Real.sqrt_nonneg _)) hL
  apply (le_div_iff₀ (mul_pos kappa_pos (Nat.cast_pos.mpr hn))).mpr
  nlinarith only [hu, hprice, hA, hB]

theorem phase_lower_bound (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (R : ℝ) (hR : 0 ≤ R) (hbound : (μ : Measure ℝ).support ⊆ Icc (-R) R)
    (n : ℕ) (hn : 0 < n) (H C r : ℝ)
    (hm : ContactVariation.PositiveClosedMaximum μ n H C) (hC : esseenConstant ≤ C)
    (hprice : ConservedResource.raw μ n H C ≤ r) :
    1 - 5 * r / (2 * (n : ℝ)) ≤ phase n H := by
  have hw := ConservedResource.conserved_identity μ h R hR hbound n hn H C hm
  change (n : ℝ) * (C - esseenConstant) * thirdAbsoluteMoment μ +
    (n : ℝ) * esseenConstant * thirdAbsoluteMoment μ * (1 - phase n H) +
    (n : ℝ) * phi 0 * phase n H * actualPhysicalDefect μ / 6 +
    (n : ℝ) * Real.sqrt n * actualL μ n H = ConservedResource.raw μ n H C at hw
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
  have hA : 0 ≤ (n : ℝ) * (C - esseenConstant) * thirdAbsoluteMoment μ :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg n) (sub_nonneg.mpr hC)) hρ
  have hB : 0 ≤ (n : ℝ) * phi 0 * phase n H * actualPhysicalDefect μ / 6 := by
    positivity
  have hE : 0 ≤ (n : ℝ) * Real.sqrt n * actualL μ n H := by positivity
  have hmultiply := mul_le_mul_of_nonneg_left hCEρ
    (mul_nonneg (Nat.cast_nonneg n) (sub_nonneg.mpr (phase_le_one n H)))
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hratio : 1 - phase n H ≤ 5 * r / (2 * (n : ℝ)) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * (n : ℝ))).mpr
    nlinarith only [hw, hprice, hA, hB, hE, hmultiply]
  linarith

end BerryEsseen.ConservedTransfer

#print axioms BerryEsseen.ConservedTransfer.kappa_le_phi_zero_div_six
#print axioms BerryEsseen.ConservedTransfer.gamma_threeJ_pos_of_raw_lt_score
#print axioms BerryEsseen.ConservedTransfer.unweighted_resource
#print axioms BerryEsseen.ConservedTransfer.defect_bound
#print axioms BerryEsseen.ConservedTransfer.phase_lower_bound
