module

public import BerryEsseen.UpperMomentNu235Checks
public import BerryEsseen.UpperMomentSharedSpectrum
public import BerryEsseen.UpperMomentN47FirstIntegral

@[expose] public section

/-! 2026-10-30: deterministic first absolute integral at real nu=235/4.
The fixed spectrum, grid and kernel licenses are shared with n47. Only the
new exponential, forcing, decay, recurrence and integral-row witnesses are
used for the new s. No noninteger iid sum is introduced. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

noncomputable section

open MeasureTheory Set
open scoped Interval BigOperators

namespace BerryEsseen.UpperMomentNu235FirstIntegral

open UpperMomentNu235Data
open FixedPointEnclosure FixedPointArithmetic
open FixedFourierConstants (scale scale_positive)
open UpperMomentN47ScalarSemantics (U_pos v1_nonneg v1_width)

abbrev U : ℝ := UpperMomentN47ScalarSemantics.U
def s : ℝ := 940000000 / 54184321
abbrev v1 : ℕ → ℝ := UpperMomentN47ScalarSemantics.v1

def H (j : ℕ) : ℝ := ((firstRow j).H : ℝ) / 10 ^ 18
def D (j : ℕ) : ℝ := ((firstRow j).D : ℝ) / 10 ^ 18
def r (j : ℕ) : ℝ := (R18.getD j 0 : ℝ) / 10 ^ 18
abbrev K : ℕ → ℝ := UpperMomentN47FirstIntegral.K
def row (j : ℕ) : ℝ := (row118.getD j 0 : ℝ) / 10 ^ 18

theorem s_pos : 0 < s := by norm_num [s]

private lemma val_lift (z : ℤ) :
    FixedPointUpperMomentRate.val (UpperMomentNu235Checks.lift18 z) =
      (z : ℝ) / 10 ^ 18 := by
  norm_num [FixedPointUpperMomentRate.val, qval, UpperMomentNu235Checks.lift18,
    factor, FixedFourierConstants.scale]
  ring

private lemma contains_s : Contains scale UpperMomentNu235Checks.sb s := by
  simpa only [UpperMomentNu235Checks.sb, s, Int.cast_ofNat] using
    rat_contains scale scale_positive 940000000 54184321 (by decide)

private lemma contains_dt : Contains scale UpperMomentNu235Checks.dt1 (1 / 1280 : ℝ) := by
  simpa only [UpperMomentNu235Checks.dt1, Int.cast_one, Int.cast_ofNat] using
    rat_contains scale scale_positive 1 1280 (by decide)

lemma grid_order (j : ℕ) : v1 j ≤ v1 (j + 1) := UpperMomentN47FirstIntegral.grid_order j

/-- The zipped member reads both frozen and new rows at the same grid index. -/
private lemma scalar_pair_mem (j : ℕ) (hj : j < 1024) :
    (UpperMomentN47ScalarSemantics.firstRow j, firstRow j) ∈
      UpperMomentNu235Checks.scalarPairs := by
  have hp : j < UpperMomentNu235Checks.scalarPairs.length := by
    simpa only [UpperMomentNu235Checks.scalarPairs_length] using hj
  have hm := List.getElem_mem hp
  have ho : j < UpperMomentN47ScalarData.firstData.length := by
    simpa only [UpperMomentN47ScalarData.firstData_length] using hj
  have hn : j < firstData.length := by simpa only [firstData_length] using hj
  simp only [UpperMomentNu235Checks.scalarPairs, List.getElem_zip] at hm
  simpa only [UpperMomentNu235Checks.scalarPairs, UpperMomentN47ScalarSemantics.firstRow, firstRow,
    List.getD_eq_getElem _ _ ho, List.getD_eq_getElem _ _ hn] using hm

theorem actual_forcing_cell_le (j : ℕ) (hj : j < 1024) {v : ℝ}
    (hv : v ∈ Icc (v1 j) (v1 (j + 1))) :
    UpperMomentSpectralCells.forcing U (UpperMomentDamping.G U U) s v ≤ H j := by
  have hc := UpperMomentNu235Checks.forcing_checked (scalar_pair_mem j hj)
  have hh := UpperMomentSharedSpectrum.actual_forcing_cell_le j hj contains_s hv hc
  simpa only [UpperMomentSpectralCells.forcing, UpperMomentN47ScalarSemantics.d_eq,
    val_lift, H] using hh

theorem actual_decay_le (j : ℕ) (hj : j < 1024) :
    Real.exp (-s * (v1 (j + 1) ^ 2 - v1 j ^ 2) / 2) ≤ D j := by
  have hc := UpperMomentNu235Checks.decay_checked (scalar_pair_mem j hj)
  rw [firstRow_index j hj] at hc
  have hh := UpperMomentSharedSpectrum.actual_decay_le j contains_s hc
  simpa only [val_lift, D] using hh

/-- Both the recurrence and row multiplication read this same new R18 list. -/
theorem recurrence_step (j : ℕ) (hj : j < 1024) :
    D j * r j + UpperMomentGridPrice.cellWidth v1 j * H j ≤ r (j + 1) := by
  have hc := UpperMomentNu235Checks.recurrence_table_checked
  unfold UpperMomentNu235Checks.recurrenceTableCheck at hc
  have hh := FixedPointRecurrence.chainCheck_row _ _ _ _ hc j
    (by simpa only [List.length_map, firstData_length] using hj)
  have hR (k : ℕ) : (R18.map UpperMomentNu235Checks.lift18).getD k 0 =
      UpperMomentNu235Checks.lift18 (R18.getD k 0) := by
    simpa only [UpperMomentNu235Checks.lift18, zero_mul] using
      List.getD_map R18 0 UpperMomentNu235Checks.lift18 (n := k)
  have hH : (firstData.map (fun x => UpperMomentNu235Checks.lift18 x.H)).getD j 0 =
      UpperMomentNu235Checks.lift18 (firstRow j).H := by
    simpa only [firstRow, firstDefault, UpperMomentNu235Checks.lift18, zero_mul] using
      List.getD_map firstData firstDefault (fun x => UpperMomentNu235Checks.lift18 x.H) (n := j)
  have hD : (firstData.map (fun x => UpperMomentNu235Checks.lift18 x.D)).getD j 0 =
      UpperMomentNu235Checks.lift18 (firstRow j).D := by
    simpa only [firstRow, firstDefault, UpperMomentNu235Checks.lift18, zero_mul] using
      List.getD_map firstData firstDefault (fun x => UpperMomentNu235Checks.lift18 x.D) (n := j)
  rw [hR j, hR (j + 1), hH, hD] at hh
  have hs := FixedPointRecurrence.updateCheck_sound contains_dt _ _ _ _ hh
  simpa only [val_lift, D, H, r, UpperMomentGridPrice.cellWidth, v1_width] using hs

/-- All nodes bound the actual defining global R for the new s. -/
theorem actual_R_nodes :
    ∀ j ≤ 1024, UpperMomentSpectralCells.R U (UpperMomentDamping.G U U) s (v1 j) ≤ r j := by
  apply UpperMomentGridPrice.R_grid_endpoints U (UpperMomentDamping.G U U)
    (UpperMomentDamping.continuous_G U U) s U_pos s_pos v1 H D r 1024
    (v1_nonneg 0) (fun j _ => grid_order j)
  · norm_num [v1, UpperMomentN47ScalarSemantics.v1, r, R18]
  · exact fun j hj v hv => actual_forcing_cell_le j hj hv
  · exact actual_decay_le
  · exact recurrence_step

theorem r_nonneg (j : ℕ) (hj : j ≤ 1024) : 0 ≤ r j :=
  (UpperMomentSpectralCells.R_nonneg U (UpperMomentDamping.G U U) s (v1 j)
    U_pos s_pos.le (v1_nonneg j)).trans (actual_R_nodes j hj)

theorem row_arithmetic (j : ℕ) (hj0 : 0 < j) (hj : j < 1024) :
    (1 / 1280 : ℝ) * K j * (r j + (1 / 1280 : ℝ) * H j) ≤ row j := by
  have hc := UpperMomentNu235Checks.first_table_checked
  change UpperMomentNu235Checks.firstPairs.zipIdx.all _ = true at hc
  have hjp : j < UpperMomentNu235Checks.firstPairs.length := by
    simpa only [UpperMomentNu235Checks.firstPairs_length] using hj
  have hh := (List.forall_mem_zipIdx'.mp (List.all_eq_true.mp hc)) j hjp
  unfold UpperMomentNu235Checks.firstPairCheck at hh
  have hg := (Bool.and_eq_true_iff.mp hh).2
  simp only [ite_eq_right (Nat.ne_of_gt hj0)] at hg
  simp only [UpperMomentNu235Checks.firstPairs, List.getElem_zip] at hg
  have hs := FixedPointUpperMomentExp.firstRowCheck_sound contains_dt hg
  have hd : j < firstData.length := by simpa only [firstData_length] using hj
  have hr : j < R18.length := by rw [R18_length]; omega
  have hk : j < UpperMomentN47KernelWitnesses.kernel118.length := by
    simpa only [UpperMomentN47KernelWitnesses.kernel118_length] using hj
  have hw : j < row118.length := by simpa only [row118_length] using hj
  simpa only [val_lift, K, UpperMomentN47FirstIntegral.K, r, H, row, firstRow,
    UpperMomentN47KernelTables.kernel1Upper, List.getD_eq_getElem _ _ hd,
    List.getD_eq_getElem _ _ hr, List.getD_eq_getElem _ _ hk,
    List.getD_eq_getElem _ _ hw] using hs

theorem regular_cell_integral (j : ℕ) (hj0 : 0 < j) (hj : j < 1024) :
    (∫ v in v1 j..v1 (j + 1), UpperMomentAbsoluteProfile.first U
      (UpperMomentDamping.G U U) 4 s v) ≤ row j := by
  apply UpperMomentFirstRows.cell_integral_le_row U (UpperMomentDamping.G U U)
    (UpperMomentDamping.continuous_G U U) 4 s (v1 j) (v1 (j + 1)) (H j) (r j) (K j)
    (row j) U_pos s_pos (v1_nonneg j) (grid_order j)
    (fun v hv => actual_forcing_cell_le j hj hv) (r_nonneg j (by omega))
    (actual_R_nodes j (by omega)) (UpperMomentN47FirstIntegral.K_nonneg j hj0 hj)
    (UpperMomentFirstRows.kernel_le_ae_of_Ioo 4 (v1 j) (v1 (j + 1)) (K j)
      (fun v hv => UpperMomentN47FirstIntegral.actual_kernel_open j hj0 hj hv))
  simpa only [v1_width] using row_arithmetic j hj0 hj

private lemma d_le_s : UpperMomentSpectrumPrice.d U ≤ s := by
  norm_num [UpperMomentSpectrumPrice.d, U, UpperMomentN47ScalarSemantics.U, s]

theorem head_arithmetic :
    s * ((v1 1) ^ 4 / 48 + UpperMomentSpectrumPrice.d U * (v1 1) ^ 5 / 120 +
      4 * (v1 1) ^ 3 / (36 * Real.pi) +
      4 * UpperMomentSpectrumPrice.d U * (v1 1) ^ 4 / (96 * Real.pi)) ≤ row 0 := by
  have hp : (314159265358979323846 : ℝ) / 10 ^ 20 ≤ Real.pi := by
    simpa only [PrawitzRationalGate.piNum, PrawitzRationalGate.piDen,
      Int.cast_ofNat, Int.cast_pow] using PrawitzRationalGate.pi_lower.le
  have hi := one_div_le_one_div_of_le (by norm_num :
      (0 : ℝ) < 314159265358979323846 / 10 ^ 20) hp
  norm_num [s, v1, UpperMomentN47ScalarSemantics.v1, U, UpperMomentN47ScalarSemantics.U,
    UpperMomentSpectrumPrice.d, row, row118, div_eq_mul_inv] at hi ⊢
  nlinarith only [hi]

theorem head_cell_integral :
    (∫ v in v1 0..v1 1, UpperMomentAbsoluteProfile.first U
      (UpperMomentDamping.G U U) 4 s v) ≤ row 0 := by
  have hh := UpperMomentFirstRows.first_cell_integral_le U (UpperMomentDamping.G U U)
    (UpperMomentDamping.continuous_G U U) (UpperMomentDamping.G_nonpos U U)
    4 s (v1 1) U_pos (by norm_num) d_le_s (v1_nonneg 1)
    (by norm_num [v1, UpperMomentN47ScalarSemantics.v1])
  have hz : v1 0 = 0 := by norm_num [v1, UpperMomentN47ScalarSemantics.v1]
  simpa only [hz, UpperMomentFirstRows.firstIntegrand, UpperMomentFirstRows.kernel,
    UpperMomentAbsoluteProfile.first] using hh.trans head_arithmetic

private lemma sum_getD (xs : List ℤ) :
    (∑ j ∈ Finset.range xs.length, (xs.getD j 0 : ℝ)) = (xs.sum : ℝ) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_zero, List.getD_cons_succ, List.sum_cons, Int.cast_add]
    rw [ih, add_comm]

theorem rows_sum : (∑ j ∈ Finset.range 1024, row j) = (row118.sum : ℝ) / 10 ^ 18 := by
  unfold row
  rw [← Finset.sum_div, ← row118_length, sum_getD]

/-- Deterministic first absolute price at s=940000000/54184321. -/
theorem first_integral_le :
    (∫ v in Ioc (0 : ℝ) (4 / 5), UpperMomentAbsoluteProfile.first U
      (UpperMomentDamping.G U U) 4 s v) ≤ (row118.sum : ℝ) / 10 ^ 18 := by
  have hI := UpperMomentFirstRows.first_intervalIntegrable U (UpperMomentDamping.G U U)
    (UpperMomentDamping.continuous_G U U) (UpperMomentDamping.G_nonpos U U)
    4 s (4 / 5) U_pos (by norm_num) d_le_s (by norm_num) (by norm_num)
  have hcells : ∀ j < 1024, IntervalIntegrable
      (UpperMomentAbsoluteProfile.first U (UpperMomentDamping.G U U) 4 s)
      volume (v1 j) (v1 (j + 1)) := by
    intro j hj
    apply hI.mono_set
    rw [uIcc_of_le (grid_order j), uIcc_of_le (by norm_num : (0 : ℝ) ≤ 4 / 5)]
    intro x hx
    exact ⟨(v1_nonneg j).trans hx.1, hx.2.trans (by
      have hn : ((j + 1 : ℕ) : ℝ) ≤ 1024 := by exact_mod_cast (show j + 1 ≤ 1024 by omega)
      change ((j + 1 : ℕ) : ℝ) / 1280 ≤ 4 / 5
      calc
        _ ≤ (1024 : ℝ) / 1280 := div_le_div_of_nonneg_right hn (by norm_num)
        _ = 4 / 5 := by norm_num)⟩
  have hall := UpperMomentGridPrice.integral_le_rows
    (UpperMomentAbsoluteProfile.first U (UpperMomentDamping.G U U) 4 s) v1 row 1024 hcells
    (fun j hj => by
      by_cases hj0 : j = 0
      · simpa only [hj0] using head_cell_integral
      · exact regular_cell_integral j (Nat.pos_of_ne_zero hj0) hj)
  rw [rows_sum] at hall
  have hz : v1 0 = 0 := by norm_num [v1, UpperMomentN47ScalarSemantics.v1]
  have hA : v1 1024 = 4 / 5 := by norm_num [v1, UpperMomentN47ScalarSemantics.v1]
  rw [hz, hA] at hall
  simpa only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 4 / 5)] using hall

end BerryEsseen.UpperMomentNu235FirstIntegral

#print axioms BerryEsseen.UpperMomentNu235FirstIntegral.actual_forcing_cell_le
#print axioms BerryEsseen.UpperMomentNu235FirstIntegral.actual_R_nodes
#print axioms BerryEsseen.UpperMomentNu235FirstIntegral.regular_cell_integral
#print axioms BerryEsseen.UpperMomentNu235FirstIntegral.head_cell_integral
#print axioms BerryEsseen.UpperMomentNu235FirstIntegral.first_integral_le
