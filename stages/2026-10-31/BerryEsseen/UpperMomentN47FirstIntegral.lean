module

public import BerryEsseen.UpperMomentN47ScalarSemantics
public import BerryEsseen.UpperMomentN47IntegralChecks
public import BerryEsseen.UpperMomentN47KernelTables
public import BerryEsseen.UpperMomentGridPrice
public import BerryEsseen.UpperMomentAbsoluteProfile

@[expose] public section

/-! 2026-10-30: the saved first rows bound the actual global spectral R.
The recurrence and the regular rows read the same Int18 R list. The first
kernel sentinel is excluded and its cell is licensed by the analytic head
formula, with the proved twenty-place rational lower bound for pi. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

noncomputable section

open MeasureTheory Set
open scoped Interval BigOperators

namespace BerryEsseen.UpperMomentN47FirstIntegral

open UpperMomentN47ScalarSemantics
open UpperMomentN47IntegralWitnesses (R18 row118 R18_length row118_length)
open FixedPointEnclosure FixedPointArithmetic
open FixedFourierConstants (scale scale_positive)

def r (j : ℕ) : ℝ := (R18.getD j 0 : ℝ) / 10 ^ 18
def K (j : ℕ) : ℝ := (UpperMomentN47KernelTables.kernel1Upper j : ℝ) / 10 ^ 18
def row (j : ℕ) : ℝ := (row118.getD j 0 : ℝ) / 10 ^ 18

private lemma val_lift (z : ℤ) :
    FixedPointUpperMomentRate.val (UpperMomentN47IntegralChecks.lift18 z) =
      (z : ℝ) / 10 ^ 18 := by
  norm_num [FixedPointUpperMomentRate.val, qval, UpperMomentN47IntegralChecks.lift18,
    UpperMomentN47IntegralWitnesses.factor, FixedFourierConstants.scale]
  ring

private lemma contains_dt : Contains scale UpperMomentN47IntegralChecks.dt1 (1 / 1280 : ℝ) := by
  simpa only [UpperMomentN47IntegralChecks.dt1, Int.cast_one, Int.cast_ofNat] using
    rat_contains scale scale_positive 1 1280 (by decide)

lemma grid_order (j : ℕ) : v1 j ≤ v1 (j + 1) := by
  have hw := v1_width j
  linarith only [hw]

/-- This arithmetic step uses the same R18 entries as all later row gates. -/
theorem recurrence_step (j : ℕ) (hj : j < 1024) :
    D j * r j + UpperMomentGridPrice.cellWidth v1 j * H j ≤ r (j + 1) := by
  have hc := UpperMomentN47IntegralChecks.recurrence_table_checked
  unfold UpperMomentN47IntegralChecks.recurrenceTableCheck at hc
  have hh := FixedPointRecurrence.chainCheck_row _ _ _ _ hc j
    (by simpa only [List.length_map, UpperMomentN47ScalarData.firstData_length] using hj)
  have hR (k : ℕ) : (R18.map UpperMomentN47IntegralChecks.lift18).getD k 0 =
      UpperMomentN47IntegralChecks.lift18 (R18.getD k 0) := by
    simpa only [UpperMomentN47IntegralChecks.lift18, zero_mul] using
      List.getD_map R18 0 UpperMomentN47IntegralChecks.lift18 (n := k)
  have hH : (UpperMomentN47ScalarData.firstData.map
      (fun x => UpperMomentN47IntegralChecks.lift18 x.H)).getD j 0 =
      UpperMomentN47IntegralChecks.lift18 (firstRow j).H := by
    simpa only [firstRow, firstDefault, UpperMomentN47IntegralChecks.lift18, zero_mul] using
      List.getD_map UpperMomentN47ScalarData.firstData firstDefault
        (fun x => UpperMomentN47IntegralChecks.lift18 x.H) (n := j)
  have hD : (UpperMomentN47ScalarData.firstData.map
      (fun x => UpperMomentN47IntegralChecks.lift18 x.D)).getD j 0 =
      UpperMomentN47IntegralChecks.lift18 (firstRow j).D := by
    simpa only [firstRow, firstDefault, UpperMomentN47IntegralChecks.lift18, zero_mul] using
      List.getD_map UpperMomentN47ScalarData.firstData firstDefault
        (fun x => UpperMomentN47IntegralChecks.lift18 x.D) (n := j)
  rw [hR j, hR (j + 1), hH, hD] at hh
  have hs := FixedPointRecurrence.updateCheck_sound contains_dt _ _ _ _ hh
  simpa only [val_lift, D, H, r, UpperMomentGridPrice.cellWidth, v1_width] using hs

private lemma forcing_le (j : ℕ) (hj : j < 1024) {v : ℝ}
    (hv : v ∈ Icc (v1 j) (v1 (j + 1))) :
    UpperMomentSpectralCells.forcing U (UpperMomentDamping.G U U) s v ≤ H j := by
  simpa only [UpperMomentSpectralCells.forcing, ← d_eq] using actual_forcing_cell_le j hj hv

/-- The witness dominates the defining integral R on every saved node. -/
theorem actual_R_nodes :
    ∀ j ≤ 1024, UpperMomentSpectralCells.R U (UpperMomentDamping.G U U) s (v1 j) ≤ r j := by
  apply UpperMomentGridPrice.R_grid_endpoints U (UpperMomentDamping.G U U)
    (UpperMomentDamping.continuous_G U U) s U_pos s_pos v1 H D r 1024
    (v1_nonneg 0) (fun j _ => grid_order j)
  · norm_num [v1, r, R18]
  · exact fun j hj v hv => forcing_le j hj hv
  · exact actual_decay_le
  · exact recurrence_step

theorem r_nonneg (j : ℕ) (hj : j ≤ 1024) : 0 ≤ r j :=
  (UpperMomentSpectralCells.R_nonneg U (UpperMomentDamping.G U U) s (v1 j)
    U_pos s_pos.le (v1_nonneg j)).trans (actual_R_nodes j hj)

private lemma firstPairs_length : UpperMomentN47IntegralChecks.firstPairs.length = 1024 := by
  simp only [UpperMomentN47IntegralChecks.firstPairs, List.length_zip,
    UpperMomentN47ScalarData.firstData_length, R18_length,
    UpperMomentN47KernelWitnesses.kernel118_length, row118_length,
    min_eq_left (by decide : 1024 ≤ 1025), min_self]

theorem regular_row_arithmetic (j : ℕ) (hj0 : 0 < j) (hj : j < 1024) :
    (1 / 1280 : ℝ) * K j * (r j + (1 / 1280 : ℝ) * H j) ≤ row j := by
  have hc := UpperMomentN47IntegralChecks.first_table_checked
  change UpperMomentN47IntegralChecks.firstPairs.zipIdx.all _ = true at hc
  have hjp : j < UpperMomentN47IntegralChecks.firstPairs.length := by
    simpa only [firstPairs_length] using hj
  have hh := (List.forall_mem_zipIdx'.mp (List.all_eq_true.mp hc)) j hjp
  simp only [ite_eq_right (Nat.ne_of_gt hj0)] at hh
  simp only [UpperMomentN47IntegralChecks.firstPairs, List.getElem_zip] at hh
  have hs := FixedPointUpperMomentExp.firstRowCheck_sound contains_dt hh
  have hd : j < UpperMomentN47ScalarData.firstData.length := by
    simpa only [UpperMomentN47ScalarData.firstData_length] using hj
  have hr : j < R18.length := by rw [R18_length]; omega
  have hk : j < UpperMomentN47KernelWitnesses.kernel118.length := by
    simpa only [UpperMomentN47KernelWitnesses.kernel118_length] using hj
  have hw : j < row118.length := by simpa only [row118_length] using hj
  simpa only [val_lift, K, r, H, row, firstRow, UpperMomentN47KernelTables.kernel1Upper,
    List.getD_eq_getElem _ _ hd, List.getD_eq_getElem _ _ hr,
    List.getD_eq_getElem _ _ hk, List.getD_eq_getElem _ _ hw] using hs

theorem actual_kernel_open (j : ℕ) (hj0 : 0 < j) (hj : j < 1024) {v : ℝ}
    (hv : v ∈ Ioo (v1 j) (v1 (j + 1))) :
    UpperMomentFirstRows.kernel 4 v ≤ K j := by
  have hz : v / 4 ∈ Ioo (UpperMomentN47KernelTables.z1 j)
      (UpperMomentN47KernelTables.z1 (j + 1)) := by
    constructor <;>
      simp only [UpperMomentN47KernelTables.z1, UpperMomentN47KernelTables.p1,
        UpperMomentN47KernelTables.q, Int.cast_natCast, Int.cast_mul, Int.cast_ofNat]
    · have := hv.1; dsimp [v1] at this; linarith
    · have := hv.2; dsimp [v1] at this; linarith
  convert UpperMomentN47KernelTables.actual_kernel1_cell_le j hj0 hj hz using 1 <;>
    norm_num [UpperMomentFirstRows.kernel, RaySpectralCurvature.spectralKernelWeight,
      K, UpperMomentN47KernelTables.Sc, UpperMomentN47KernelWitnesses.compactScale]

theorem K_nonneg (j : ℕ) (hj0 : 0 < j) (hj : j < 1024) : 0 ≤ K j := by
  have hh := UpperMomentN47KernelTables.actual_kernel1_left_le j hj0 hj
  have hn := (norm_nonneg _).trans hh
  convert hn using 1
  norm_num [K, UpperMomentN47KernelTables.Sc, UpperMomentN47KernelWitnesses.compactScale]

theorem regular_cell_integral (j : ℕ) (hj0 : 0 < j) (hj : j < 1024) :
    (∫ v in v1 j..v1 (j + 1), UpperMomentAbsoluteProfile.first U
      (UpperMomentDamping.G U U) 4 s v) ≤ row j := by
  apply UpperMomentFirstRows.cell_integral_le_row U (UpperMomentDamping.G U U)
    (UpperMomentDamping.continuous_G U U) 4 s (v1 j) (v1 (j + 1)) (H j) (r j) (K j)
    (row j) U_pos s_pos (v1_nonneg j) (grid_order j)
    (fun v hv => forcing_le j hj hv) (r_nonneg j (by omega)) (actual_R_nodes j (by omega))
    (K_nonneg j hj0 hj)
    (UpperMomentFirstRows.kernel_le_ae_of_Ioo 4 (v1 j) (v1 (j + 1)) (K j)
      (fun v hv => actual_kernel_open j hj0 hj hv))
  simpa only [v1_width] using regular_row_arithmetic j hj0 hj

private lemma d_le_s : UpperMomentSpectrumPrice.d U ≤ s := by
  norm_num [UpperMomentSpectrumPrice.d, U, s]

theorem head_arithmetic :
    s * ((v1 1) ^ 4 / 48 + UpperMomentSpectrumPrice.d U * (v1 1) ^ 5 / 120 +
      4 * (v1 1) ^ 3 / (36 * Real.pi) +
      4 * UpperMomentSpectrumPrice.d U * (v1 1) ^ 4 / (96 * Real.pi)) ≤ row 0 := by
  have hp : (314159265358979323846 : ℝ) / 10 ^ 20 ≤ Real.pi := by
    simpa only [PrawitzRationalGate.piNum, PrawitzRationalGate.piDen,
      Int.cast_ofNat, Int.cast_pow] using PrawitzRationalGate.pi_lower.le
  have hi := one_div_le_one_div_of_le (by norm_num :
      (0 : ℝ) < 314159265358979323846 / 10 ^ 20) hp
  norm_num [s, v1, U, UpperMomentSpectrumPrice.d, row, row118, div_eq_mul_inv] at hi ⊢
  nlinarith only [hi]

theorem head_cell_integral :
    (∫ v in v1 0..v1 1, UpperMomentAbsoluteProfile.first U
      (UpperMomentDamping.G U U) 4 s v) ≤ row 0 := by
  have hh := UpperMomentFirstRows.first_cell_integral_le U (UpperMomentDamping.G U U)
    (UpperMomentDamping.continuous_G U U) (UpperMomentDamping.G_nonpos U U)
    4 s (v1 1) U_pos (by norm_num) d_le_s (v1_nonneg 1) (by norm_num [v1])
  have hz : v1 0 = 0 := by norm_num [v1]
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

/-- The unchanged first absolute integral over the whole 0..4/5 band. -/
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
  have hz : v1 0 = 0 := by norm_num [v1]
  have hA : v1 1024 = 4 / 5 := by norm_num [v1]
  rw [hz, hA] at hall
  simpa only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 4 / 5)] using hall

end BerryEsseen.UpperMomentN47FirstIntegral

#print axioms BerryEsseen.UpperMomentN47FirstIntegral.actual_R_nodes
#print axioms BerryEsseen.UpperMomentN47FirstIntegral.regular_cell_integral
#print axioms BerryEsseen.UpperMomentN47FirstIntegral.head_cell_integral
#print axioms BerryEsseen.UpperMomentN47FirstIntegral.first_integral_le
