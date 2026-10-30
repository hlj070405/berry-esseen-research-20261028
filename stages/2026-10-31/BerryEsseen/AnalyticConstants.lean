module

public import BerryEsseen.Target
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp

@[expose] public section

/-! 2026-10-28: exact analytic gates for the support-ray comparison.
All decimals in the manuscript are represented by rational constants here.
-/

noncomputable section

namespace BerryEsseen.AnalyticConstants

theorem esseenConstant_gt_819_2000 : (819 : ℝ) / 2000 < esseenConstant := by
  have hs10 := Real.sq_sqrt (show (0 : ℝ) ≤ 10 by norm_num)
  have h10 : (79 : ℝ) / 25 < Real.sqrt 10 := by
    nlinarith [Real.sqrt_nonneg (10 : ℝ)]
  have hp := Real.pi_lt_d4
  have hs2 := Real.sq_sqrt (show 0 ≤ 2 * Real.pi by positivity)
  have h2 : Real.sqrt (2 * Real.pi) < (2507 : ℝ) / 1000 := by
    nlinarith [Real.sqrt_nonneg (2 * Real.pi)]
  have hden : 0 < 6 * Real.sqrt (2 * Real.pi) := by positivity
  unfold esseenConstant
  apply (lt_div_iff₀ hden).mpr
  nlinarith

def scaleExcess (n : ℝ) : ℝ := n * (Real.sqrt (n / (n - 1)) - 1) - 1 / 2

theorem scaleExcess_lt (n : ℝ) (hn : 25 ≤ n) : scaleExcess n < 2 / (5 * n) := by
  have hnpos : 0 < n := by linarith
  have hnm : 0 < n - 1 := by linarith
  let z := 1 / n
  let s := Real.sqrt (n / (n - 1))
  let T := 1 + z / 2 + 2 * z ^ 2 / 5
  have hzpos : 0 < z := one_div_pos.mpr hnpos
  have hz : z ≤ (1 : ℝ) / 25 := by
    dsimp [z]
    apply (div_le_iff₀ hnpos).mpr
    linarith
  have hz2 : z ^ 2 ≤ ((1 : ℝ) / 25) ^ 2 :=
    (sq_le_sq₀ hzpos.le (by norm_num)).mpr hz
  have hz3 : z ^ 3 ≤ ((1 : ℝ) / 25) ^ 3 := by
    have h := mul_le_mul hz2 hz hzpos.le (sq_nonneg ((1 : ℝ) / 25))
    simpa only [pow_succ] using h
  have hbracket : 0 < (1 : ℝ) / 20 - 13 * z / 20 - 6 * z ^ 2 / 25 - 4 * z ^ 3 / 25 := by
    nlinarith
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hT : 0 < T := by dsimp [T]; nlinarith [sq_nonneg z]
  have hden : 0 < 1 - z := by linarith
  have hss : (1 - z) * s ^ 2 = 1 := by
    dsimp [s]
    rw [Real.sq_sqrt (div_nonneg hnpos.le hnm.le)]
    dsimp [z]
    field_simp [hnpos.ne', hnm.ne']
  have hpoly : (1 - z) * T ^ 2 - 1 =
      z ^ 2 * (1 / 20 - 13 * z / 20 - 6 * z ^ 2 / 25 - 4 * z ^ 3 / 25) := by
    dsimp [T]
    ring
  have hstrict : 0 < (1 - z) * (T ^ 2 - s ^ 2) := by
    have hmul := mul_pos (sq_pos_of_pos hzpos) hbracket
    nlinarith [hpoly, hss]
  have hdiff : 0 < T ^ 2 - s ^ 2 := (mul_pos_iff_of_pos_left hden).mp hstrict
  have hsT : s < T := by nlinarith
  have hmul := mul_lt_mul_of_pos_left hsT hnpos
  have heq : n * (T - 1) - 1 / 2 = 2 / (5 * n) := by
    dsimp [T, z]
    field_simp [hnpos.ne']
    ring
  change n * (s - 1) - 1 / 2 < _
  calc
    _ < n * (T - 1) - 1 / 2 := by linarith
    _ = _ := heq

theorem scaleExcess_lt_two_125 (n : ℝ) (hn : 25 ≤ n) : scaleExcess n < (2 : ℝ) / 125 := by
  have hnpos : 0 < n := by linarith
  have h := scaleExcess_lt n hn
  apply h.trans_le
  apply (div_le_iff₀ (mul_pos (by norm_num) hnpos)).mpr
  linarith

end BerryEsseen.AnalyticConstants

#print axioms BerryEsseen.AnalyticConstants.esseenConstant_gt_819_2000
#print axioms BerryEsseen.AnalyticConstants.scaleExcess_lt
