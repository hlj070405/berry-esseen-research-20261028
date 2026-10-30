module

public import BerryEsseen.FixedPointCellCheck
public import BerryEsseen.ControlFastKernelTables
public import BerryEsseen.ControlEndpointParameters
public import BerryEsseen.CoefficientQuadrature

@[expose] public section

/-! 2026-10-29: actual second and third integral rows of the unchanged
control endpoint. Integer row gates consume the original Int18 witnesses.
The exponential upper is evaluated once per cell, then multiplied through
the actual physical cell width and the already checked kernel candidate.
Open-cell integration excludes only the source kernel's exceptional endpoints. -/

set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

namespace BerryEsseen.ControlRemainingIntegralRows

open FixedPointEnclosure FixedPointArithmetic
open FixedFourierConstants (scale scale_positive)
open FixedPointUpper (point point_contains)
open MeasureTheory Set
open scoped Interval BigOperators






abbrev Sc : ℤ := ControlEndpointWitnesses.compactScale
abbrev factor : ℤ := ControlEndpointWitnesses.convertFactor

def rowProductBox (dt : Box) (k e : ℤ) : Box :=
  mul scale scale_positive (mul scale scale_positive dt (point (k * factor))) (point e)

def row2Upper (j : ℕ) : ℤ := ControlEndpointWitnesses.row218.getD j 0
def row3Upper (j : ℕ) : ℤ := ControlEndpointWitnesses.row318.getD j 0

def row2CandidateCheck (j : ℕ) (k row : ℤ) : Bool :=
  let X := FixedPointCellCheck.envelopeInputBox ControlEndpointParameters.cBox
    ControlEndpointParameters.betaBox (ControlEndpointParameters.secondGridBox j)
    (ControlEndpointParameters.secondGridBox (j + 1))
  if hden : 0 < (FixedPointCellForcing.expDen X 8).lo then
    if hpos : 0 < (FixedPointCellForcing.expPositive X 8 hden).lo then
      let e := FixedPointCellCheck.envelopeUpper ControlEndpointParameters.cBox
        ControlEndpointParameters.betaBox (ControlEndpointParameters.secondGridBox j)
        (ControlEndpointParameters.secondGridBox (j + 1)) 8 hden hpos
      decide ((rowProductBox ControlEndpointParameters.dt2Box k e).hi ≤ row * factor)
    else false
  else false

def row3CandidateCheck (j : ℕ) (raw row : ℤ) : Bool :=
  let X := FixedPointCellCheck.gaussianInputBox (ControlEndpointParameters.firstGridBox j)
  if hden : 0 < (FixedPointCellForcing.expDen X 8).lo then
    if hpos : 0 < (FixedPointCellForcing.expPositive X 8 hden).lo then
      let e := FixedPointCellCheck.gaussianUpper (ControlEndpointParameters.firstGridBox j) 8 hden hpos
      decide ((rowProductBox ControlEndpointParameters.dtBox (min raw 500000000000000000) e).hi ≤ row * factor)
    else false
  else false

def row2Pairs : List (ℤ × ℤ) := ControlEndpointWitnesses.kernel218.zip ControlEndpointWitnesses.row218
def row3Pairs : List (ℤ × ℤ) := ControlEndpointWitnesses.correctionRaw18.zip ControlEndpointWitnesses.row318

def row2PilotCheck : Bool := (row2Pairs.take 16).zipIdx.all
  (fun p => row2CandidateCheck p.2 p.1.1 p.1.2)
def row3PilotCheck : Bool := (row3Pairs.take 16).zipIdx.all
  (fun p => row3CandidateCheck p.2 p.1.1 p.1.2)

def row2TableCheck : Bool := row2Pairs.zipIdx.all
  (fun p => row2CandidateCheck p.2 p.1.1 p.1.2)
def row3TableCheck : Bool := row3Pairs.zipIdx.all
  (fun p => row3CandidateCheck p.2 p.1.1 p.1.2)

theorem row2_pilot_16 : row2PilotCheck = true := by decide +kernel
theorem row3_pilot_16 : row3PilotCheck = true := by decide +kernel

noncomputable section

def compactValue (u : ℤ) : ℝ := (u : ℝ) / Sc

lemma compact_qval (u : ℤ) : (qval scale (u * factor) : ℝ) = compactValue u := by
  simp only [qval, Rat.cast_div, Rat.cast_intCast, Int.cast_mul, compactValue]
  norm_num [scale, factor, Sc, ControlEndpointWitnesses.convertFactor, ControlEndpointWitnesses.compactScale]
  ring

lemma rowProductBox_contains {dt : Box} {d : ℝ} (hdt : Contains scale dt d) (k e : ℤ) :
    Contains scale (rowProductBox dt k e) (d * compactValue k * (qval scale e : ℝ)) := by
  have hk := point_contains scale (k * factor)
  rw [compact_qval] at hk
  exact mul_contains scale_positive (mul_contains scale_positive hdt hk) (point_contains scale e)

lemma rowProductBox_le {dt : Box} {d : ℝ} (hdt : Contains scale dt d) {k e row : ℤ}
    (hgate : (rowProductBox dt k e).hi ≤ row * factor) :
    d * compactValue k * (qval scale e : ℝ) ≤ compactValue row := by
  have hu := (rowProductBox_contains hdt k e).2
  have hn : (qval scale (rowProductBox dt k e).hi : ℝ) ≤
      (qval scale (row * factor) : ℝ) := by exact_mod_cast qval_mono scale_positive hgate
  exact hu.trans (hn.trans_eq (compact_qval row))

lemma resolution_real_pos : (0 : ℝ) < ControlEndpointParameters.resolution := by
  exact_mod_cast ControlEndpointParameters.resolution_pos

lemma firstGrid_nonneg (j : ℕ) : 0 ≤ ControlEndpointParameters.firstGrid j := by
  unfold ControlEndpointParameters.firstGrid
  exact mul_nonneg ControlEndpointParameters.U0_pos.le
    (div_nonneg (Nat.cast_nonneg j) resolution_real_pos.le)

lemma firstGrid_mono {j k : ℕ} (hjk : j ≤ k) : ControlEndpointParameters.firstGrid j ≤ ControlEndpointParameters.firstGrid k := by
  unfold ControlEndpointParameters.firstGrid
  exact mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right (show (j : ℝ) ≤ k by exact_mod_cast hjk) resolution_real_pos.le) ControlEndpointParameters.U0_pos.le

lemma secondGrid_mono {j k : ℕ} (hjk : j ≤ k) : ControlEndpointParameters.secondGrid j ≤ ControlEndpointParameters.secondGrid k := by
  unfold ControlEndpointParameters.secondGrid
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right (show (j : ℝ) ≤ k by exact_mod_cast hjk) resolution_real_pos.le)
    (sub_nonneg.mpr ControlEndpointParameters.U0_le_U))

lemma firstGrid_zero : ControlEndpointParameters.firstGrid 0 = 0 := by simp [ControlEndpointParameters.firstGrid]
lemma firstGrid_last : ControlEndpointParameters.firstGrid 1024 = ControlEndpointParameters.U0 := by
  norm_num [ControlEndpointParameters.firstGrid, ControlEndpointParameters.resolution, ControlEndpointWitnesses.resolution]
lemma secondGrid_zero : ControlEndpointParameters.secondGrid 0 = ControlEndpointParameters.U0 := by simp [ControlEndpointParameters.secondGrid]
lemma secondGrid_last : ControlEndpointParameters.secondGrid 1024 = ControlEndpointParameters.U := by
  norm_num [ControlEndpointParameters.secondGrid, ControlEndpointParameters.resolution, ControlEndpointWitnesses.resolution]

lemma firstGrid_le_U0 (j : ℕ) (hj : j ≤ 1024) : ControlEndpointParameters.firstGrid j ≤ ControlEndpointParameters.U0 := by
  rw [← firstGrid_last]
  exact firstGrid_mono hj

lemma secondGrid_ge_U0 (j : ℕ) : ControlEndpointParameters.U0 ≤ ControlEndpointParameters.secondGrid j := by
  rw [← secondGrid_zero]
  exact secondGrid_mono (Nat.zero_le j)

lemma secondGrid_le_U (j : ℕ) (hj : j ≤ 1024) : ControlEndpointParameters.secondGrid j ≤ ControlEndpointParameters.U := by
  rw [← secondGrid_last]
  exact secondGrid_mono hj

lemma secondGrid_nonneg (j : ℕ) : 0 ≤ ControlEndpointParameters.secondGrid j := ControlEndpointParameters.U0_pos.le.trans (secondGrid_ge_U0 j)

lemma firstGrid_ratio (j : ℕ) : ControlEndpointParameters.firstGrid j / ControlEndpointParameters.U = ControlFastKernelTables.z1 j := by
  norm_num [ControlEndpointParameters.firstGrid, ControlEndpointParameters.U0, ControlEndpointParameters.U, ControlEndpointParameters.A, ControlEndpointParameters.rootS, ControlEndpointParameters.resolution, ControlEndpointWitnesses.resolution,
    ControlEndpointWitnesses.aNum, ControlEndpointWitnesses.aDen, ControlFastKernelTables.z1, ControlFastKernelTables.p1, ControlFastKernelTables.q]
  ring

lemma secondGrid_ratio (j : ℕ) : ControlEndpointParameters.secondGrid j / ControlEndpointParameters.U = ControlFastKernelTables.z2 j := by
  norm_num [ControlEndpointParameters.secondGrid, ControlEndpointParameters.U0, ControlEndpointParameters.U, ControlEndpointParameters.A, ControlEndpointParameters.rootS, ControlEndpointParameters.resolution, ControlEndpointWitnesses.resolution,
    ControlEndpointWitnesses.aNum, ControlEndpointWitnesses.aDen, ControlFastKernelTables.z2, ControlFastKernelTables.p2, ControlFastKernelTables.q]
  ring

lemma first_open_ratio {j : ℕ} {t : ℝ}
    (ht : t ∈ Ioo (ControlEndpointParameters.firstGrid j) (ControlEndpointParameters.firstGrid (j + 1))) :
    t / ControlEndpointParameters.U ∈ Ioo (ControlFastKernelTables.z1 j) (ControlFastKernelTables.z1 (j + 1)) := by
  rw [← firstGrid_ratio j, ← firstGrid_ratio (j + 1)]
  exact ⟨div_lt_div_of_pos_right ht.1 ControlEndpointParameters.U_pos, div_lt_div_of_pos_right ht.2 ControlEndpointParameters.U_pos⟩

lemma second_open_ratio {j : ℕ} {t : ℝ}
    (ht : t ∈ Ioo (ControlEndpointParameters.secondGrid j) (ControlEndpointParameters.secondGrid (j + 1))) :
    t / ControlEndpointParameters.U ∈ Ioo (ControlFastKernelTables.z2 j) (ControlFastKernelTables.z2 (j + 1)) := by
  rw [← secondGrid_ratio j, ← secondGrid_ratio (j + 1)]
  exact ⟨div_lt_div_of_pos_right ht.1 ControlEndpointParameters.U_pos, div_lt_div_of_pos_right ht.2 ControlEndpointParameters.U_pos⟩

lemma second_integrable : IntervalIntegrable
    (CoefficientPhysicalProfile.secondIntegrand ControlEndpointParameters.c ControlEndpointParameters.beta ControlEndpointParameters.U) volume ControlEndpointParameters.U0 ControlEndpointParameters.U := by
  have h := (CoefficientPhysicalProfile.four_integrands_integrable 42 (by decide)
    ControlEndpointParameters.c ControlEndpointParameters.beta ControlEndpointParameters.A 4 ControlEndpointParameters.beta_pos ControlEndpointParameters.A_pos ControlEndpointParameters.A_lt_four.le).2.1
  simpa only [← ControlEndpointParameters.U0_eq, ← ControlEndpointParameters.U_eq] using h

lemma third_integrable : IntervalIntegrable
    (CoefficientPhysicalProfile.thirdIntegrand ControlEndpointParameters.U) volume 0 ControlEndpointParameters.U0 := by
  have h := (CoefficientPhysicalProfile.four_integrands_integrable 42 (by decide)
    ControlEndpointParameters.c ControlEndpointParameters.beta ControlEndpointParameters.A 4 ControlEndpointParameters.beta_pos ControlEndpointParameters.A_pos ControlEndpointParameters.A_lt_four.le).2.2.1
  simpa only [← ControlEndpointParameters.U0_eq, ← ControlEndpointParameters.U_eq] using h

lemma second_cell_integrable (j : ℕ) (hj : j < 1024) : IntervalIntegrable
    (CoefficientPhysicalProfile.secondIntegrand ControlEndpointParameters.c ControlEndpointParameters.beta ControlEndpointParameters.U) volume
      (ControlEndpointParameters.secondGrid j) (ControlEndpointParameters.secondGrid (j + 1)) := by
  apply second_integrable.mono_set
  rw [uIcc_of_le (secondGrid_mono (Nat.le_succ j)), uIcc_of_le ControlEndpointParameters.U0_le_U]
  exact Icc_subset_Icc (secondGrid_ge_U0 j) (secondGrid_le_U (j + 1) (by omega))

lemma third_cell_integrable (j : ℕ) (hj : j < 1024) : IntervalIntegrable
    (CoefficientPhysicalProfile.thirdIntegrand ControlEndpointParameters.U) volume
      (ControlEndpointParameters.firstGrid j) (ControlEndpointParameters.firstGrid (j + 1)) := by
  apply third_integrable.mono_set
  rw [uIcc_of_le (firstGrid_mono (Nat.le_succ j)), uIcc_of_le ControlEndpointParameters.U0_pos.le]
  exact Icc_subset_Icc (firstGrid_nonneg j) (firstGrid_le_U0 (j + 1) (by omega))

private lemma integral_le_row {f : ℝ → ℝ} {a b d : ℝ} {dt : Box} {k e row : ℤ}
    (hab : a ≤ b) (hint : IntervalIntegrable f volume a b)
    (hdt : Contains scale dt d) (hwidth : b - a = d)
    (hgate : (rowProductBox dt k e).hi ≤ row * factor)
    (hbound : ∀ t ∈ Ioo a b, f t ≤ compactValue k * (qval scale e : ℝ)) :
    (∫ t in a..b, f t) ≤ compactValue row := by
  have hm := intervalIntegral.integral_mono_on_of_le_Ioo hab hint
    (intervalIntegrable_const (c := compactValue k * (qval scale e : ℝ))
      (a := a) (b := b) (μ := volume)) hbound
  rw [intervalIntegral.integral_const, smul_eq_mul] at hm
  calc
    _ ≤ (b - a) * (compactValue k * (qval scale e : ℝ)) := hm
    _ = d * compactValue k * (qval scale e : ℝ) := by rw [hwidth]; ring
    _ ≤ compactValue row := rowProductBox_le hdt hgate

open ControlEndpointParameters ControlFastKernelTables

/-- A successful row gate controls the real envelope throughout the open
physical cell, not only the two exponent samples used by the integer code. -/
theorem row2CandidateCheck_sound (j : ℕ) (hj : j < 1024)
    (hcheck : row2CandidateCheck j (kernel2Upper j) (row2Upper j) = true) :
    (∫ t in secondGrid j..secondGrid (j + 1),
      CoefficientPhysicalProfile.secondIntegrand c beta U t) ≤ compactValue (row2Upper j) := by
  unfold row2CandidateCheck at hcheck
  dsimp only at hcheck
  split_ifs at hcheck with hden hpos
  · have hgate := of_decide_eq_true hcheck
    apply integral_le_row (secondGrid_mono (Nat.le_succ j)) (second_cell_integrable j hj)
      contains_dt2 (second_width j) hgate
    intro t ht
    have hk := actual_kernel2_cell_le j hj (second_open_ratio ht)
    have he := FixedPointCellCheck.envelope_le_upper contains_c contains_beta
      (contains_secondGrid j) (contains_secondGrid (j + 1)) c_pos.le beta_pos.le
      (secondGrid_nonneg j) (secondGrid_mono (Nat.le_succ j)) ⟨ht.1.le, ht.2.le⟩ 8 hden hpos
    have hp := mul_le_mul hk he (CoefficientRayPrice.envelope_nonneg c beta t)
      ((norm_nonneg _).trans hk)
    simpa only [CoefficientPhysicalProfile.secondIntegrand, compactValue] using hp

/-- Gaussian monotonicity and the gated raw correction followed by its
proved half cap control the real third integrand on the entire open cell. -/
theorem row3CandidateCheck_sound (j : ℕ) (hj : j < 1024)
    (hcheck : row3CandidateCheck j (correctionRawUpper j) (row3Upper j) = true) :
    (∫ t in firstGrid j..firstGrid (j + 1),
      CoefficientPhysicalProfile.thirdIntegrand U t) ≤ compactValue (row3Upper j) := by
  unfold row3CandidateCheck at hcheck
  dsimp only at hcheck
  split_ifs at hcheck with hden hpos
  · have hgate := of_decide_eq_true hcheck
    apply integral_le_row (firstGrid_mono (Nat.le_succ j)) (third_cell_integrable j hj)
      contains_dt (first_width j) hgate
    intro t ht
    have hk := actual_correction_cell_le j hj (first_open_ratio ht)
    have he := FixedPointCellCheck.gaussian_le_upper (contains_firstGrid j)
      (firstGrid_nonneg j) ht.1.le 8 hden hpos
    have hp := mul_le_mul hk he (Real.exp_nonneg _) ((norm_nonneg _).trans hk)
    simpa only [CoefficientPhysicalProfile.thirdIntegrand, compactValue,
      correctionCappedUpper] using hp

private lemma indexedZip_sound (xs ys : List ℤ) (check : ℕ → ℤ → ℤ → Bool)
    (h : (xs.zip ys).zipIdx.all (fun p => check p.2 p.1.1 p.1.2) = true)
    (j : ℕ) (hx : j < xs.length) (hy : j < ys.length) :
    check j (xs.getD j 0) (ys.getD j 0) = true := by
  have hj : j < (xs.zip ys).length := by simp only [List.length_zip]; omega
  have hh := (List.forall_mem_zipIdx'.mp (List.all_eq_true.mp h)) j hj
  simpa only [List.getElem_zip, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hx, List.getElem?_eq_getElem hy, Option.getD_some] using hh

theorem row2_all_of_table (h : row2TableCheck = true) (j : ℕ) (hj : j < 1024) :
    row2CandidateCheck j (kernel2Upper j) (row2Upper j) = true := by
  apply indexedZip_sound ControlEndpointWitnesses.kernel218 ControlEndpointWitnesses.row218
    row2CandidateCheck h j
  · simpa only [ControlEndpointWitnesses.kernel218_length] using hj
  · simpa only [ControlEndpointWitnesses.row218_length] using hj

theorem row3_all_of_table (h : row3TableCheck = true) (j : ℕ) (hj : j < 1024) :
    row3CandidateCheck j (correctionRawUpper j) (row3Upper j) = true := by
  apply indexedZip_sound ControlEndpointWitnesses.correctionRaw18 ControlEndpointWitnesses.row318
    row3CandidateCheck h j
  · simpa only [ControlEndpointWitnesses.correctionRaw18_length] using hj
  · simpa only [ControlEndpointWitnesses.row318_length] using hj

private lemma list_sum_as_range (xs : List ℤ) :
    (∑ j ∈ Finset.range xs.length, (xs.getD j 0 : ℝ)) = (xs.sum : ℝ) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simpa [Finset.sum_range_succ', add_comm] using congrArg (fun y : ℝ => (x : ℝ) + y) ih

lemma compact_sum_as_range (xs : List ℤ) :
    (∑ j ∈ Finset.range xs.length, compactValue (xs.getD j 0)) = (xs.sum : ℝ) / Sc := by
  simp only [compactValue, ← Finset.sum_div]
  rw [list_sum_as_range]

/-- The original physical second integral is partitioned without replacing
the value assigned to K(1); its last singleton is ignored only by integration. -/
theorem actual_second_integral_le_rows_of_table (h : row2TableCheck = true) :
    (∫ t in U0..U, CoefficientPhysicalProfile.secondIntegrand c beta U t) ≤
      (ControlEndpointWitnesses.row218.sum : ℝ) / Sc := by
  have hs := intervalIntegral.sum_integral_adjacent_intervals
    (fun j hj => second_cell_integrable j hj)
  rw [secondGrid_zero, secondGrid_last] at hs
  rw [← hs]
  calc
    _ ≤ ∑ j ∈ Finset.range 1024, compactValue (row2Upper j) := by
      apply Finset.sum_le_sum
      intro j hj
      exact row2CandidateCheck_sound j (Finset.mem_range.mp hj)
        (row2_all_of_table h j (Finset.mem_range.mp hj))
    _ = _ := by
      rw [← compact_sum_as_range ControlEndpointWitnesses.row218,
        ControlEndpointWitnesses.row218_length]
      rfl

/-- The full physical third integral is bounded by the actual raw rows;
the correction cap and Gaussian inequality both hold throughout each cell. -/
theorem actual_third_integral_le_rows_of_table (h : row3TableCheck = true) :
    (∫ t in (0 : ℝ)..U0, CoefficientPhysicalProfile.thirdIntegrand U t) ≤
      (ControlEndpointWitnesses.row318.sum : ℝ) / Sc := by
  have hs := intervalIntegral.sum_integral_adjacent_intervals
    (fun j hj => third_cell_integrable j hj)
  rw [firstGrid_zero, firstGrid_last] at hs
  rw [← hs]
  calc
    _ ≤ ∑ j ∈ Finset.range 1024, compactValue (row3Upper j) := by
      apply Finset.sum_le_sum
      intro j hj
      exact row3CandidateCheck_sound j (Finset.mem_range.mp hj)
        (row3_all_of_table h j (Finset.mem_range.mp hj))
    _ = _ := by
      rw [← compact_sum_as_range ControlEndpointWitnesses.row318,
        ControlEndpointWitnesses.row318_length]
      rfl

end

/-- Both full tables are checked only after their sixteen-cell pilots.
Direct kernel reduction performs no native evaluation or fallback branch. -/
theorem row2_table_checked : row2TableCheck = true := by decide +kernel
theorem row3_table_checked : row3TableCheck = true := by decide +kernel

theorem actual_second_integral_le_rows :
    (∫ t in ControlEndpointParameters.U0..ControlEndpointParameters.U,
      CoefficientPhysicalProfile.secondIntegrand ControlEndpointParameters.c
        ControlEndpointParameters.beta ControlEndpointParameters.U t) ≤
      (ControlEndpointWitnesses.row218.sum : ℝ) / Sc :=
  actual_second_integral_le_rows_of_table row2_table_checked

theorem actual_third_integral_le_rows :
    (∫ t in (0 : ℝ)..ControlEndpointParameters.U0,
      CoefficientPhysicalProfile.thirdIntegrand ControlEndpointParameters.U t) ≤
      (ControlEndpointWitnesses.row318.sum : ℝ) / Sc :=
  actual_third_integral_le_rows_of_table row3_table_checked

end BerryEsseen.ControlRemainingIntegralRows

#print axioms BerryEsseen.ControlRemainingIntegralRows.row2_pilot_16
#print axioms BerryEsseen.ControlRemainingIntegralRows.row3_pilot_16
#print axioms BerryEsseen.ControlRemainingIntegralRows.row2_table_checked
#print axioms BerryEsseen.ControlRemainingIntegralRows.row3_table_checked
#print axioms BerryEsseen.ControlRemainingIntegralRows.actual_second_integral_le_rows
#print axioms BerryEsseen.ControlRemainingIntegralRows.actual_third_integral_le_rows
