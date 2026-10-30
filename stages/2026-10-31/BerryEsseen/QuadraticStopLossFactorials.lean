module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

@[expose] public section

/-! 2026-10-31: a quadratic stop-loss at an integer count is controlled
by its second and third falling factorials. The majorant is exact at
counts 0,1,2,3 when the threshold lies in [1,2]. -/

noncomputable section

namespace BerryEsseen.QuadraticStopLossFactorials

def coefficient2 (d : ℝ) : ℝ := (2 - d) ^ 2 / 2
def coefficient3 (d : ℝ) : ℝ := (-3 + 6 * d - 2 * d ^ 2) / 6
def falling2 (x : ℝ) : ℝ := x * (x - 1)
def falling3 (x : ℝ) : ℝ := x * (x - 1) * (x - 2)
def majorant (d x : ℝ) : ℝ := coefficient2 d * falling2 x + coefficient3 d * falling3 x

theorem coefficient3_identity (d : ℝ) :
    coefficient3 d = 1 / 6 + (d - 1) * (2 - d) / 3 := by
  unfold coefficient3
  ring

theorem coefficient3_nonneg {d : ℝ} (hd : d ∈ Set.Icc (1 : ℝ) 2) :
    0 ≤ coefficient3 d := by
  rw [coefficient3_identity]
  have hp := mul_nonneg (sub_nonneg.mpr hd.1) (sub_nonneg.mpr hd.2)
  linarith only [hp]

theorem remainder_identity (d x : ℝ) :
    majorant d x - (x - d) ^ 2 =
      (x - 2) * (x - 3) * (coefficient3 d * x - d ^ 2 / 6) := by
  unfold majorant coefficient2 coefficient3 falling2 falling3
  ring

theorem fourth_count_gate (d : ℝ) :
    4 * coefficient3 d - d ^ 2 / 6 = (2 - d) * (3 * d - 2) / 2 := by
  unfold coefficient3
  ring

theorem squared_positive_part_le (k : ℕ) (d : ℝ) (hd : d ∈ Set.Icc (1 : ℝ) 2) :
    (max ((k : ℝ) - d) 0) ^ 2 ≤ majorant d k := by
  by_cases hk : k < 4
  · have hcases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hcases with rfl | rfl | rfl | rfl
    · rw [show ((0 : ℕ) : ℝ) - d = -d by norm_num,
        max_eq_right (by linarith only [hd.1] : -d ≤ (0 : ℝ))]
      norm_num [majorant, falling2, falling3]
    · rw [max_eq_right (by norm_num; linarith only [hd.1] : ((1 : ℕ) : ℝ) - d ≤ 0)]
      norm_num [majorant, falling2, falling3]
    · rw [max_eq_left (by norm_num; linarith only [hd.2] : 0 ≤ ((2 : ℕ) : ℝ) - d)]
      norm_num [majorant, falling2, falling3, coefficient2]
    · rw [max_eq_left (by norm_num; linarith only [hd.2] : 0 ≤ ((3 : ℕ) : ℝ) - d)]
      unfold majorant coefficient2 coefficient3 falling2 falling3
      norm_num only [Nat.cast_ofNat]
      nlinarith only []
  · have hk4 : (4 : ℝ) ≤ k := by exact_mod_cast (show 4 ≤ k by omega)
    rw [max_eq_left (by linarith only [hk4, hd.2] : 0 ≤ (k : ℝ) - d)]
    have hb := coefficient3_nonneg hd
    have hg0 : 0 ≤ 4 * coefficient3 d - d ^ 2 / 6 := by
      rw [fourth_count_gate]
      exact div_nonneg (mul_nonneg (sub_nonneg.mpr hd.2)
        (by linarith only [hd.1])) (by norm_num)
    have hkg := mul_le_mul_of_nonneg_left hk4 hb
    have hg : 0 ≤ coefficient3 d * (k : ℝ) - d ^ 2 / 6 := by
      nlinarith only [hg0, hkg]
    have hr : 0 ≤ ((k : ℝ) - 2) * ((k : ℝ) - 3) *
        (coefficient3 d * (k : ℝ) - d ^ 2 / 6) :=
      mul_nonneg (mul_nonneg (by linarith only [hk4]) (by linarith only [hk4])) hg
    linarith only [remainder_identity d k, hr]

end BerryEsseen.QuadraticStopLossFactorials

#print axioms BerryEsseen.QuadraticStopLossFactorials.squared_positive_part_le
