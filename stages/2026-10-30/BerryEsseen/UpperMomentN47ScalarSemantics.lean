module

public import BerryEsseen.UpperMomentN47ScalarChecks
public import Mathlib.Data.List.GetD

@[expose] public section

/-! 2026-10-30: semantic licenses for the fixed n47 scalar witnesses.
The getters read the checked tables themselves. Their index theorems use
the kernel-checked table order, and all analytic bounds concern the same
actual spectrum G U U on the complete closed cells. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace BerryEsseen.UpperMomentN47ScalarSemantics

open Set
open FixedPointEnclosure FixedPointArithmetic FixedPointUpperMomentRate
open FixedPointUpperMomentCoarseW
open FixedFourierConstants (scale scale_positive)
open UpperMomentN47ScalarData UpperMomentN47ScalarChecks

def firstDefault : FirstRow := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩
def secondDefault : T2Row := ⟨0, 0, 0, 0, 0⟩

def firstRow (j : ℕ) : FirstRow := firstData.getD j firstDefault
def secondRow (j : ℕ) : T2Row := T2data.getD j secondDefault

theorem firstRow_mem (j : ℕ) (hj : j < 1024) : firstRow j ∈ firstData := by
  have hj' : j < firstData.length := by simpa only [firstData_length] using hj
  rw [firstRow, List.getD_eq_getElem firstData firstDefault hj']
  exact List.getElem_mem hj'

theorem secondRow_mem (j : ℕ) (hj : j < 1024) : secondRow j ∈ T2data := by
  have hj' : j < T2data.length := by simpa only [T2data_length] using hj
  rw [secondRow, List.getD_eq_getElem T2data secondDefault hj']
  exact List.getElem_mem hj'

theorem firstRow_index (j : ℕ) (hj : j < 1024) : (firstRow j).index = j := by
  change FirstRow.index (firstData.getD j firstDefault) = j
  rw [← List.getD_map firstData firstDefault FirstRow.index, firstData_indices]
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_range] using hj)]
  exact List.getElem_range _

theorem secondRow_index (j : ℕ) (hj : j < 1024) : (secondRow j).index = j := by
  change T2Row.index (T2data.getD j secondDefault) = j
  rw [← List.getD_map T2data secondDefault T2Row.index, T2data_indices]
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_range] using hj)]
  exact List.getElem_range _

noncomputable section

def U : ℝ := 7361 / 4000
def s : ℝ := 752000000 / 54184321
def d : ℝ := 1 / U ^ 2

def v1 (j : ℕ) : ℝ := (j : ℝ) / 1280
def v2 (j : ℕ) : ℝ := ((256 + j : ℕ) : ℝ) / 320

def H (j : ℕ) : ℝ := ((firstRow j).H : ℝ) / 10 ^ 18
def D (j : ℕ) : ℝ := ((firstRow j).D : ℝ) / 10 ^ 18
def G1 (j : ℕ) : ℝ := ((firstRow j).G : ℝ) / 10 ^ 18
def G2 (j : ℕ) : ℝ := ((secondRow j).G : ℝ) / 10 ^ 18

theorem val_lift18 (z : ℤ) : val (lift18 z) = (z : ℝ) / 10 ^ 18 := by
  norm_num [val, qval, lift18, FixedFourierConstants.scale]
  ring

theorem contains_U : Contains scale ub U := by
  simpa only [ub, U, Int.cast_ofNat] using
    rat_contains scale scale_positive 7361 4000 (by decide)

theorem contains_s : Contains scale sb s := by
  simpa only [sb, s, Int.cast_ofNat] using
    rat_contains scale scale_positive 752000000 54184321 (by decide)

theorem contains_firstLeft (j : ℕ) : Contains scale (firstLeft j) (v1 j) := by
  simpa only [firstLeft, v1, Int.cast_natCast, Int.cast_ofNat] using
    rat_contains scale scale_positive (j : ℤ) 1280 (by decide)

theorem contains_firstRight (j : ℕ) : Contains scale (firstRight j) (v1 (j + 1)) := by
  simpa only [firstRight, v1, Int.cast_natCast, Int.cast_ofNat] using
    rat_contains scale scale_positive ((j + 1 : ℕ) : ℤ) 1280 (by decide)

theorem contains_T2left (j : ℕ) : Contains scale (T2left j) (v2 j) := by
  simpa only [T2left, v2, Int.cast_natCast, Int.cast_ofNat] using
    rat_contains scale scale_positive ((256 + j : ℕ) : ℤ) 320 (by decide)

theorem contains_T2right (j : ℕ) : Contains scale (T2right j) (v2 (j + 1)) := by
  have hindex : 256 + (j + 1) = 257 + j := by omega
  simpa only [T2right, v2, hindex, Int.cast_natCast, Int.cast_ofNat] using
    rat_contains scale scale_positive ((257 + j : ℕ) : ℤ) 320 (by decide)

theorem U_pos : 0 < U := by norm_num [U]
theorem s_pos : 0 < s := by norm_num [s]
theorem d_eq : d = UpperMomentSpectrumPrice.d U := rfl
theorem s_eq_47_mul_d : s = 47 * d := by norm_num [s, d, U]

theorem v1_nonneg (j : ℕ) : 0 ≤ v1 j := by unfold v1; positivity
theorem v2_nonneg (j : ℕ) : 0 ≤ v2 j := by unfold v2; positivity

theorem v1_width (j : ℕ) : v1 (j + 1) - v1 j = 1 / 1280 := by
  simp only [v1, Nat.cast_add, Nat.cast_one]
  ring

theorem v2_width (j : ℕ) : v2 (j + 1) - v2 j = 1 / 320 := by
  simp only [v2, Nat.cast_add, Nat.cast_one]
  ring

theorem actual_G1_cell_le (j : ℕ) (hj : j < 1024) {v : ℝ}
    (hv : v ∈ Icc (v1 j) (v1 (j + 1))) :
    UpperMomentDamping.G U U v ≤ G1 j := by
  have hc := first_rate_checked (firstRow_mem j hj)
  rw [firstRow_index j hj] at hc
  have hh := rateCheck_sound contains_U (contains_firstLeft j) (contains_firstRight j) hv hc
  simpa only [val_lift18, G1] using hh

theorem actual_forcing_cell_le (j : ℕ) (hj : j < 1024) {v : ℝ}
    (hv : v ∈ Icc (v1 j) (v1 (j + 1))) :
    s * Real.exp ((s - d) * UpperMomentDamping.G U U v) *
      UpperMomentSpectrumPrice.W U v ≤ H j := by
  have hc := first_forcing_cell_checked (firstRow_mem j hj)
  rw [firstRow_index j hj] at hc
  have hh := coarseForcingCellCheck_sound contains_U contains_s
    (contains_firstLeft j) (contains_firstRight j) hv hc
  simpa only [val_lift18, H, d_eq] using hh

theorem actual_decay_le (j : ℕ) (hj : j < 1024) :
    Real.exp (-s * (v1 (j + 1) ^ 2 - v1 j ^ 2) / 2) ≤ D j := by
  have hc := first_decay_checked (firstRow_mem j hj)
  rw [firstRow_index j hj] at hc
  have hh := decayCheck_sound contains_s (contains_firstLeft j) (contains_firstRight j) hc
  simpa only [val_lift18, D] using hh

theorem actual_G2_cell_le (j : ℕ) (hj : j < 1024) {v : ℝ}
    (hv : v ∈ Icc (v2 j) (v2 (j + 1))) :
    UpperMomentDamping.G U U v ≤ G2 j := by
  have hc := T2_row_checked (secondRow_mem j hj)
  change rateCheck ub (T2left (secondRow j).index) (T2right (secondRow j).index) gc
    (lift18 (secondRow j).norm) (lift18 (secondRow j).M4)
    (lift18 (secondRow j).MR) (lift18 (secondRow j).G) = true at hc
  rw [secondRow_index j hj] at hc
  have hh := rateCheck_sound contains_U (contains_T2left j) (contains_T2right j) hv hc
  simpa only [val_lift18, G2] using hh

theorem D_pos (j : ℕ) (hj : j < 1024) : 0 < D j :=
  (Real.exp_pos _).trans_le (actual_decay_le j hj)

theorem H_nonneg (j : ℕ) (hj : j < 1024) : 0 ≤ H j := by
  have hc := first_forcing_checked (firstRow_mem j hj)
  unfold forcingCheck at hc
  split_ifs at hc with hU
  · rcases of_decide_eq_true (Bool.and_eq_true_iff.mp hc).2 with
      ⟨_hS, _hdiff, _hG, _hW, _hP, hH, _hprod⟩
    simpa only [val_lift18, H] using val_nonneg hH

theorem D_le_one (j : ℕ) (hj : j < 1024) : D j ≤ 1 := by
  have hc := first_decay_checked (firstRow_mem j hj)
  have hD := (of_decide_eq_true (Bool.and_eq_true_iff.mp hc).1).2.2.2
  have hscale : val scale = 1 := by norm_num [val, qval, FixedFourierConstants.scale]
  simpa only [val_lift18, hscale, D] using val_mono hD

end

end BerryEsseen.UpperMomentN47ScalarSemantics

#print axioms BerryEsseen.UpperMomentN47ScalarSemantics.firstRow_index
#print axioms BerryEsseen.UpperMomentN47ScalarSemantics.secondRow_index
#print axioms BerryEsseen.UpperMomentN47ScalarSemantics.actual_G1_cell_le
#print axioms BerryEsseen.UpperMomentN47ScalarSemantics.actual_forcing_cell_le
#print axioms BerryEsseen.UpperMomentN47ScalarSemantics.actual_decay_le
#print axioms BerryEsseen.UpperMomentN47ScalarSemantics.actual_G2_cell_le
