module

public import BerryEsseen.CentralGapConditionalIntegral
public import BerryEsseen.UniformLowMomentRawAcquisition
public import BerryEsseen.LowMomentSignProbabilityBand
public import BerryEsseen.PhysicalSkewnessLower
public import Mathlib.Algebra.Order.Floor.Semiring

@[expose] public section

/-! 2026-10-30: acquire a genuine interior adjacent-count decomposition
for every low-moment original maximum at its actual n>=26. The height is
cH+np; the floor does not change either the sample count or the law. -/

noncomputable section

open MeasureTheory Set
open BerryEsseen.CanonicalSign BerryEsseen.NoiseCoordinates

namespace BerryEsseen.CanonicalHeightLocalization

theorem scale_le_two_rho_mul_pq (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    scale μ h ≤ 2 * thirdAbsoluteMoment μ * p μ * q μ := by
  have hf := SignedMoment.first_mul_third_ge_one_add_signed_sq μ h
  rw [PhysicalSkewnessLower.firstAbsoluteMoment_eq_twice_positive μ h] at hf
  have hf1 : (1 : ℝ) ≤ 2 * positiveFirstMoment μ * thirdAbsoluteMoment μ := by
    nlinarith only [hf, sq_nonneg (SignedMoment.signedSecondMoment μ)]
  have hp := mul_le_mul_of_nonneg_right hf1 (scale_pos μ h).le
  have he : (2 * positiveFirstMoment μ * thirdAbsoluteMoment μ) * scale μ h =
      2 * thirdAbsoluteMoment μ * p μ * q μ := by
    calc
      _ = 2 * thirdAbsoluteMoment μ * (positiveFirstMoment μ * scale μ h) := by ring
      _ = _ := by rw [positiveFirstMoment_mul_scale μ h]; ring
  nlinarith only [hp, he]

theorem scale_le_eleven_twentieths (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) : scale μ h ≤ (11 : ℝ) / 20 := by
  have hf := SignedMoment.first_mul_third_ge_one_add_signed_sq μ h
  rw [PhysicalSkewnessLower.firstAbsoluteMoment_eq_twice_positive μ h] at hf
  have hm0 := positiveFirstMoment_pos μ h
  have hcap := mul_le_mul_of_nonneg_left hρ (show 0 ≤ 2 * positiveFirstMoment μ by positivity)
  have hm : (5 : ℝ) / 11 ≤ positiveFirstMoment μ := by
    nlinarith only [hf, hcap, sq_nonneg (SignedMoment.signedSecondMoment μ)]
  have hv : p μ * q μ ≤ (1 : ℝ) / 4 := by
    unfold q
    nlinarith only [sq_nonneg (p μ - (1 / 2 : ℝ))]
  have hp := mul_le_mul_of_nonneg_right hm (scale_pos μ h).le
  have he := positiveFirstMoment_mul_scale μ h
  nlinarith only [hp, he, hv]

theorem threshold_square_le_of_phase (n : ℕ) (hn : 0 < n) (H : ℝ)
    (he : (5 : ℝ) / 6 ≤ ConservedTransfer.phase n H) :
    H ^ 2 ≤ (2 / 5 : ℝ) * n := by
  let w := H ^ 2 / (2 * (n : ℝ))
  have hw0 : 0 ≤ w := by dsimp [w]; positivity
  have hcost := ConservedPhaseBudget.exp_phase_cost w
  change w * ConservedTransfer.phase n H ≤ 1 - ConservedTransfer.phase n H at hcost
  have hp := mul_le_mul_of_nonneg_right he hw0
  have hw : w ≤ (1 : ℝ) / 5 := by nlinarith only [hcost, hp, he]
  have hmul := (div_le_iff₀ (by positivity : 0 < 2 * (n : ℝ))).mp hw
  nlinarith only [hmul]

theorem height_bounds_of_phase (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) (n : ℕ) (hn : 26 ≤ n) (H : ℝ)
    (he : (5 : ℝ) / 6 ≤ ConservedTransfer.phase n H) :
    (13 / 50 : ℝ) * n ≤ CentralGapConditionalIntegral.canonicalHeight μ h n H ∧
      CentralGapConditionalIntegral.canonicalHeight μ h n H ≤ (37 / 50 : ℝ) * n := by
  have hnR : (26 : ℝ) ≤ n := by exact_mod_cast hn
  have hs0 := Real.sqrt_nonneg (n : ℝ)
  have hs2 := Real.sq_sqrt (Nat.cast_nonneg n)
  have hs5 : (5 : ℝ) ≤ Real.sqrt (n : ℝ) := by nlinarith only [hnR, hs0, hs2]
  have hprod := mul_nonneg (sub_nonneg.mpr hs5) hs0
  have hsN : Real.sqrt (n : ℝ) ≤ (n : ℝ) / 5 := by nlinarith only [hprod, hs2]
  have hH2 := threshold_square_le_of_phase n (by omega) H he
  have hH : |H| ≤ Real.sqrt (n : ℝ) := by
    apply (sq_le_sq₀ (abs_nonneg H) hs0).mp
    rw [sq_abs, Real.sq_sqrt (Nat.cast_nonneg n)]
    nlinarith only [hH2, hnR]
  have hc := scale_le_eleven_twentieths μ h hρ
  have hCH : |scale μ h * H| ≤ (11 / 100 : ℝ) * n := by
    rw [abs_mul, abs_of_pos (scale_pos μ h)]
    have hp := mul_le_mul hc hH (abs_nonneg H) (by norm_num : (0 : ℝ) ≤ 11 / 20)
    have hq := mul_le_mul_of_nonneg_left hsN (by norm_num : (0 : ℝ) ≤ 11 / 20)
    nlinarith only [hp, hq]
  have hp := LowMomentSignProbabilityBand.p_mem_Icc_37_100_63_100 μ h hρ
  have hpl := mul_le_mul_of_nonneg_left hp.1 (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hpu := mul_le_mul_of_nonneg_left hp.2 (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  obtain ⟨hcl, hcu⟩ := abs_le.mp hCH
  unfold CentralGapConditionalIntegral.canonicalHeight
  constructor <;> nlinarith only [hpl, hpu, hcl, hcu]

/-- The two adjacent predecessor counts are genuinely in range, including
for every original maximum; no separately assumed count cell is needed. -/
theorem exists_adjacent_phase_of_phase (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) (n : ℕ) (hn : 26 ≤ n) (H : ℝ)
    (he : (5 : ℝ) / 6 ≤ ConservedTransfer.phase n H) :
    ∃ (j : ℕ) (t : ℝ), 1 ≤ j ∧ j ≤ n - 1 ∧ t ∈ Ico (0 : ℝ) 1 ∧
      CentralGapConditionalIntegral.canonicalHeight μ h n H = (j : ℝ) + t := by
  let T := CentralGapConditionalIntegral.canonicalHeight μ h n H
  have hb := height_bounds_of_phase μ h hρ n hn H he
  have hnR : (26 : ℝ) ≤ n := by exact_mod_cast hn
  have hT1 : (1 : ℝ) ≤ T := by dsimp [T]; nlinarith only [hb.1, hnR]
  have hT0 : 0 ≤ T := by linarith only [hT1]
  have hTn : T ≤ ((n - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
    dsimp [T]
    nlinarith only [hb.2, hnR]
  let j : ℕ := ⌊T⌋₊
  have hj : 1 ≤ j := (Nat.le_floor_iff' (by decide : (1 : ℕ) ≠ 0)).mpr
    (by simpa only [Nat.cast_one] using hT1)
  have hjn : j ≤ n - 1 := Nat.floor_le_of_le hTn
  refine ⟨j, T - (j : ℝ), hj, hjn, ⟨?_, ?_⟩, ?_⟩
  · exact sub_nonneg.mpr (Nat.floor_le hT0)
  · have ht := Nat.lt_floor_add_one T
    change T < (j : ℝ) + 1 at ht
    linarith only [ht]
  · dsimp [T]
    ring

theorem original_exists_adjacent_phase (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (hn : 26 ≤ n) (H C : ℝ)
    (hm : ContactVariation.PositiveClosedMaximum μ n H C)
    (hprev : Extremizer.fixedNSup (n - 1) ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) :
    ∃ (j : ℕ) (t : ℝ), 1 ≤ j ∧ j ≤ n - 1 ∧ t ∈ Ico (0 : ℝ) 1 ∧
      CentralGapConditionalIntegral.canonicalHeight μ h n H = (j : ℝ) + t :=
  exists_adjacent_phase_of_phase μ h hρ n hn H
    (UniformLowMomentRawAcquisition.original_phase_lower_bound μ h n hn H C hm hprev hC hρ)

end BerryEsseen.CanonicalHeightLocalization

#print axioms BerryEsseen.CanonicalHeightLocalization.scale_le_two_rho_mul_pq
#print axioms BerryEsseen.CanonicalHeightLocalization.scale_le_eleven_twentieths
#print axioms BerryEsseen.CanonicalHeightLocalization.threshold_square_le_of_phase
#print axioms BerryEsseen.CanonicalHeightLocalization.height_bounds_of_phase
#print axioms BerryEsseen.CanonicalHeightLocalization.original_exists_adjacent_phase
