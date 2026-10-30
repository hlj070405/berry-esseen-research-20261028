module

public import BerryEsseen.ControlPriceGrid
public import BerryEsseen.ControlFastKernelTables
public import Mathlib.Data.List.Enum

@[expose] public section

/-! 2026-10-29: the original raw first-integral row witnesses. The first
row is analytic; regular rows use the same exact physical width and the
already-proved global coarse-price grid. Gates consume the unchanged
compact R/H/K/row columns by a single indexed traversal. -/

set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

open MeasureTheory Set
open scoped Interval BigOperators

namespace BerryEsseen.ControlFirstIntegralRows

open FixedPointEnclosure
open Causalean.Stat.CLT.BerryEsseen (prawitzKernel)

abbrev Sc : ℤ := ControlEndpointWitnesses.compactScale
def widthNum : ℤ := 97 * 45949729863572161
def widthDen : ℤ := 100 * 13500000000000000 * 1024
def widthRat : ℚ := (widthNum : ℚ) / widthDen
def rootRat : ℚ := 45949729863572161 / 13500000000000000
def lambdaRat : ℚ := rootRat / 42
def upperRat : ℚ := 4 * rootRat
def piRat : ℚ := (PrawitzRationalGate.piNum : ℚ) / PrawitzRationalGate.piDen

def firstRat : ℚ := widthRat ^ 4 / 48 + lambdaRat * widthRat ^ 5 / 120 +
  upperRat * widthRat ^ 3 / (36 * piRat) +
  upperRat * lambdaRat * widthRat ^ 4 / (96 * piRat)

def FirstRowGate (row : ℤ) : Prop := firstRat.num * Sc ≤ row * (firstRat.den : ℤ)
instance (row : ℤ) : Decidable (FirstRowGate row) := by unfold FirstRowGate; infer_instance

def RegularRowGate (r h k row : ℤ) : Prop :=
  widthNum * k * (widthDen * r + widthNum * h) ≤ row * widthDen ^ 2 * Sc
instance (r h k row : ℤ) : Decidable (RegularRowGate r h k row) := by
  unfold RegularRowGate
  infer_instance

abbrev Input := ((ℤ × ℤ) × ℤ) × ℤ

def inputs : List Input :=
  ((ControlEndpointWitnesses.r18.zip ControlEndpointWitnesses.forcing18).zip
    ControlEndpointWitnesses.kernel118).zip ControlEndpointWitnesses.row118

def rowCheck (j : ℕ) (x : Input) : Bool :=
  if j = 0 then decide (FirstRowGate x.2)
  else decide (RegularRowGate x.1.1.1 x.1.1.2 x.1.2 x.2)

def prefixCheck (n : ℕ) : Bool := (inputs.take n).zipIdx.all (fun p => rowCheck p.2 p.1)
def tableCheck : Bool := inputs.zipIdx.all (fun p => rowCheck p.2 p.1)

theorem inputs_length : inputs.length = 1024 := by
  simp only [inputs, List.length_zip, ControlEndpointWitnesses.r18_length,
    ControlEndpointWitnesses.forcing18_length, ControlEndpointWitnesses.kernel118_length,
    ControlEndpointWitnesses.row118_length]
  decide

theorem pilot_16 : prefixCheck 16 = true := by decide +kernel

theorem all_rows_checked : tableCheck = true := by decide +kernel

private lemma getD_zip_eq {α β : Type} (xs : List α) (ys : List β) (j : ℕ)
    (hx : j < xs.length) (hy : j < ys.length) (dx : α) (dy : β) :
    (xs.zip ys).getD j (dx, dy) = (xs.getD j dx, ys.getD j dy) := by
  have hxy : j < (xs.zip ys).length := by
    rw [List.length_zip]
    exact lt_min hx hy
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hxy,
    List.getElem?_eq_getElem hx, List.getElem?_eq_getElem hy, Option.getD_some, List.getElem_zip]

private lemma inputs_getD (j : ℕ) (hj : j < 1024) :
    inputs.getD j (((0, 0), 0), 0) =
      (((ControlEndpointWitnesses.r18.getD j 0, ControlEndpointWitnesses.forcing18.getD j 0),
        ControlEndpointWitnesses.kernel118.getD j 0), ControlEndpointWitnesses.row118.getD j 0) := by
  have hr : j < ControlEndpointWitnesses.r18.length := by rw [ControlEndpointWitnesses.r18_length]; omega
  have hh : j < ControlEndpointWitnesses.forcing18.length := by rw [ControlEndpointWitnesses.forcing18_length]; exact hj
  have hk : j < ControlEndpointWitnesses.kernel118.length := by rw [ControlEndpointWitnesses.kernel118_length]; exact hj
  have hw : j < ControlEndpointWitnesses.row118.length := by rw [ControlEndpointWitnesses.row118_length]; exact hj
  have hrh : j < (ControlEndpointWitnesses.r18.zip ControlEndpointWitnesses.forcing18).length := by
    rw [List.length_zip]
    exact lt_min hr hh
  have hrhk : j < ((ControlEndpointWitnesses.r18.zip ControlEndpointWitnesses.forcing18).zip
      ControlEndpointWitnesses.kernel118).length := by
    rw [List.length_zip]
    exact lt_min hrh hk
  unfold inputs
  rw [getD_zip_eq _ _ j hrhk hw ((0, 0), 0) 0,
    getD_zip_eq _ _ j hrh hk (0, 0) 0, getD_zip_eq _ _ j hr hh 0 0]

private lemma indexedAll_sound {α : Type} (xs : List α) (check : ℕ → α → Bool)
    (h : xs.zipIdx.all (fun p => check p.2 p.1) = true) (j : ℕ) (hj : j < xs.length) (d : α) :
    check j (xs.getD j d) = true := by
  have hh := (List.forall_mem_zipIdx'.mp (List.all_eq_true.mp h)) j hj
  simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some] using hh

theorem row_checked (j : ℕ) (hj : j < 1024) :
    rowCheck j (((ControlEndpointWitnesses.r18.getD j 0, ControlEndpointWitnesses.forcing18.getD j 0),
      ControlEndpointWitnesses.kernel118.getD j 0), ControlEndpointWitnesses.row118.getD j 0) = true := by
  have hj' : j < inputs.length := by rw [inputs_length]; exact hj
  have hh := indexedAll_sound inputs rowCheck all_rows_checked j hj' (((0, 0), 0), 0)
  rw [inputs_getD j hj] at hh
  exact hh

theorem first_row_gate : FirstRowGate (ControlEndpointWitnesses.row118.getD 0 0) := by
  have hh := row_checked 0 (by decide)
  simp only [rowCheck] at hh
  exact of_decide_eq_true hh

theorem regular_row_gate (j : ℕ) (hj0 : 0 < j) (hj : j < 1024) :
    RegularRowGate (ControlEndpointWitnesses.r18.getD j 0)
      (ControlEndpointWitnesses.forcing18.getD j 0) (ControlEndpointWitnesses.kernel118.getD j 0)
      (ControlEndpointWitnesses.row118.getD j 0) := by
  have hh := row_checked j hj
  simp only [rowCheck, ite_eq_right (Nat.ne_of_gt hj0)] at hh
  exact of_decide_eq_true hh

/-- A general bridge for the unchanged integer row lists, also usable by
the other integral components without importing a numerical budget. -/
theorem sum_range_getD (xs : List ℤ) :
    (∑ j ∈ Finset.range xs.length, xs.getD j 0) = xs.sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.length_cons, List.sum_cons]
      rw [Finset.sum_range_succ']
      simp only [List.getD_cons_succ, List.getD_cons_zero]
      rw [ih]
      exact add_comm _ _

theorem sum_range_getD_div (xs : List ℤ) (den : ℝ) :
    (∑ j ∈ Finset.range xs.length, (xs.getD j 0 : ℝ) / den) = (xs.sum : ℝ) / den := by
  have hh : (∑ j ∈ Finset.range xs.length, (xs.getD j 0 : ℝ)) = (xs.sum : ℝ) := by
    exact_mod_cast sum_range_getD xs
  rw [← Finset.sum_div, hh]

noncomputable section

open ControlEndpointParameters
open CoefficientRayPrice

lemma Sc_pos : (0 : ℝ) < Sc := by norm_num [Sc, ControlEndpointWitnesses.compactScale]
lemma widthDen_pos : (0 : ℝ) < widthDen := by norm_num [widthDen]

lemma first_width_eq : U0 / resolution = (widthRat : ℝ) := by
  norm_num [U0, A, rootS, resolution, ControlEndpointWitnesses.resolution,
    ControlEndpointWitnesses.aNum, ControlEndpointWitnesses.aDen, widthRat, widthNum, widthDen]

lemma first_point_eq : firstGrid 1 = (widthRat : ℝ) := by
  rw [← first_width_eq]
  simp only [firstGrid, Nat.cast_one]
  ring

lemma widthRat_pos : (0 : ℝ) < (widthRat : ℝ) := by
  norm_num [widthRat, widthNum, widthDen]

lemma lambda_eq : CoarseHighMomentRayPrice.lambda 42 beta = (lambdaRat : ℝ) := by
  rw [← CoarseHighMomentRayPrice.loss_div_eq_lambda 42 beta beta_pos, loss_eq]
  norm_num [beta, lambdaRat, rootRat]

lemma upper_eq : U = (upperRat : ℝ) := by norm_num [U, rootS, upperRat, rootRat]

lemma compact_up_eq (u : ℤ) :
    (qval FixedFourierConstants.scale (ControlRecurrenceChecks.up u) : ℝ) = (u : ℝ) / Sc := by
  simp only [qval, ControlRecurrenceChecks.up, Rat.cast_div, Rat.cast_intCast, Int.cast_mul]
  norm_num [FixedFourierConstants.scale, ControlEndpointWitnesses.convertFactor,
    Sc, ControlEndpointWitnesses.compactScale]
  ring

lemma R_eq (j : ℕ) : ControlRecurrenceChecks.R j =
    (ControlEndpointWitnesses.r18.getD j 0 : ℝ) / Sc :=
  compact_up_eq _

lemma H_eq (j : ℕ) : ControlRecurrenceChecks.H j =
    (ControlEndpointWitnesses.forcing18.getD j 0 : ℝ) / Sc :=
  compact_up_eq _

/-- The integer row gate has the literal exact-rational raw-row meaning. -/
theorem regular_gate_sound (r h k row : ℤ) (hg : RegularRowGate r h k row) :
    (widthRat : ℝ) * ((k : ℝ) / Sc) *
      ((r : ℝ) / Sc + (widthRat : ℝ) * ((h : ℝ) / Sc)) ≤ (row : ℝ) / Sc := by
  have hc : (widthNum : ℝ) * k * (widthDen * r + widthNum * h) ≤
      row * (widthDen : ℝ) ^ 2 * Sc := by exact_mod_cast hg
  have hd : (0 : ℝ) < (widthDen : ℝ) ^ 2 * Sc := mul_pos (sq_pos_of_pos widthDen_pos) Sc_pos
  have hh : ((widthNum : ℝ) * k * (widthDen * r + widthNum * h)) /
      ((widthDen : ℝ) ^ 2 * Sc) ≤ row := by
    apply (div_le_iff₀ hd).mpr
    nlinarith only [hc]
  have hs := div_le_div_of_nonneg_right hh Sc_pos.le
  apply le_trans (b := (((widthNum : ℝ) * k * (widthDen * r + widthNum * h)) /
      ((widthDen : ℝ) ^ 2 * Sc)) / Sc)
  · apply le_of_eq
    simp only [widthRat, Rat.cast_div, Rat.cast_intCast]
    field_simp [widthDen_pos.ne', Sc_pos.ne']
  · exact hs

theorem first_gate_sound (row : ℤ) (hg : FirstRowGate row) :
    (firstRat : ℝ) ≤ (row : ℝ) / Sc := by
  rw [Rat.cast_def]
  apply (div_le_div_iff₀ (Nat.cast_pos.mpr firstRat.den_pos) Sc_pos).mpr
  exact_mod_cast hg

lemma piRat_pos : (0 : ℝ) < (piRat : ℝ) := by
  norm_num [piRat, PrawitzRationalGate.piNum, PrawitzRationalGate.piDen]

lemma piRat_le_pi : (piRat : ℝ) ≤ Real.pi := by
  simpa only [piRat, Rat.cast_div, Rat.cast_intCast] using PrawitzRationalGate.pi_lower.le

/-- Replacing pi by the proved lower bound is paid in the two positive
reciprocal-pi terms of the actual analytic raw first cell. -/
theorem analytic_first_le_firstRat :
    (firstGrid 1) ^ 4 / 48 + CoarseHighMomentRayPrice.lambda 42 beta * (firstGrid 1) ^ 5 / 120 +
      U * (firstGrid 1) ^ 3 / (36 * Real.pi) +
      U * CoarseHighMomentRayPrice.lambda 42 beta * (firstGrid 1) ^ 4 / (96 * Real.pi) ≤
      (firstRat : ℝ) := by
  have hl : 0 ≤ CoarseHighMomentRayPrice.lambda 42 beta :=
    CoefficientPriceCells.lambda_nonneg 42 (by decide) beta beta_pos
  have hb : 0 ≤ firstGrid 1 := first_point_eq.symm ▸ widthRat_pos.le
  have hU := U_pos
  have hPi := piRat_pos
  have h3 := div_le_div_of_nonneg_left (by positivity : 0 ≤ U * (firstGrid 1) ^ 3)
    (show (0 : ℝ) < 36 * (piRat : ℝ) by positivity)
    (mul_le_mul_of_nonneg_left piRat_le_pi (by norm_num : (0 : ℝ) ≤ 36))
  have h4 := div_le_div_of_nonneg_left
    (by positivity : 0 ≤ U * CoarseHighMomentRayPrice.lambda 42 beta * (firstGrid 1) ^ 4)
    (show (0 : ℝ) < 96 * (piRat : ℝ) by positivity)
    (mul_le_mul_of_nonneg_left piRat_le_pi (by norm_num : (0 : ℝ) ≤ 96))
  have hsum := add_le_add h3 h4
  rw [first_point_eq, lambda_eq, upper_eq] at hsum ⊢
  unfold firstRat
  push_cast
  linarith only [hsum]

def integrand (u : ℝ) : ℝ := CoefficientPhysicalProfile.firstIntegrand 42 c beta U u
def rowUpper (j : ℕ) : ℝ := (ControlEndpointWitnesses.row118.getD j 0 : ℝ) / Sc

lemma grid_end : firstGrid 1024 = U0 := by
  norm_num [firstGrid, resolution, ControlEndpointWitnesses.resolution]

lemma grid_le_U0 (j : ℕ) (hj : j ≤ 1024) : firstGrid j ≤ U0 := by
  have hcast : (j : ℝ) ≤ resolution := by
    exact_mod_cast (show j ≤ resolution by simpa only [resolution, ControlEndpointWitnesses.resolution] using hj)
  calc
    _ ≤ U0 * 1 := mul_le_mul_of_nonneg_left
      ((div_le_one (Nat.cast_pos.mpr resolution_pos)).mpr hcast) U0_pos.le
    _ = U0 := mul_one _

lemma grid_kernel_ratio (j : ℕ) : firstGrid j / U = ControlFastKernelTables.z1 j := by
  unfold firstGrid U0 U ControlFastKernelTables.z1 ControlFastKernelTables.p1 ControlFastKernelTables.q
  norm_num [A, resolution, ControlEndpointWitnesses.resolution,
    ControlEndpointWitnesses.aNum, ControlEndpointWitnesses.aDen]
  field_simp [rootS_pos.ne']
  ring

theorem integrand_intervalIntegrable : IntervalIntegrable integrand volume 0 U0 :=
  CoefficientQuadrature.first_integrand_intervalIntegrable 42 (by decide) c beta U0 U
    beta_pos U0_pos U0_le_U

theorem cell_intervalIntegrable (j : ℕ) (hj : j < 1024) :
    IntervalIntegrable integrand volume (firstGrid j) (firstGrid (j + 1)) := by
  apply integrand_intervalIntegrable.mono_set
  rw [uIcc_of_le (ControlForcingTables.firstGrid_adjacent_le j), uIcc_of_le U0_pos.le]
  exact Icc_subset_Icc (ControlForcingTables.firstGrid_nonneg j) (grid_le_U0 (j + 1) (by omega))

/-- Recovering raw scale requires exactly U/2 times the already-proved
normalized analytic first cell. The dummy K_0 is never used here. -/
theorem first_cell_integral_le :
    (∫ u in firstGrid 0..firstGrid 1, integrand u) ≤ rowUpper 0 := by
  have hb : 0 < firstGrid 1 := first_point_eq.symm ▸ widthRat_pos
  have hscaled := CoefficientQuadrature.first_cell_le 42 (by decide) c beta (firstGrid 1) U
    beta_pos hb ((grid_le_U0 1 (by decide)).trans U0_le_U)
  have hm := mul_le_mul_of_nonneg_left hscaled (show 0 ≤ U / 2 by positivity [U_pos])
  have hraw : (∫ u in (0 : ℝ)..firstGrid 1, integrand u) ≤
      (firstGrid 1) ^ 4 / 48 + CoarseHighMomentRayPrice.lambda 42 beta * (firstGrid 1) ^ 5 / 120 +
        U * (firstGrid 1) ^ 3 / (36 * Real.pi) +
        U * CoarseHighMomentRayPrice.lambda 42 beta * (firstGrid 1) ^ 4 / (96 * Real.pi) := by
    calc
      _ = (U / 2) * ((2 / U) * (∫ u in (0 : ℝ)..firstGrid 1, integrand u)) := by
        field_simp [U_pos.ne'] <;> ring
      _ ≤ (U / 2) *
          ((firstGrid 1) ^ 4 / (24 * U) +
            CoarseHighMomentRayPrice.lambda 42 beta * (firstGrid 1) ^ 5 / (60 * U) +
            (firstGrid 1) ^ 3 / (18 * Real.pi) +
            CoarseHighMomentRayPrice.lambda 42 beta * (firstGrid 1) ^ 4 / (48 * Real.pi)) := hm
      _ = _ := by field_simp [U_pos.ne', Real.pi_ne_zero] <;> ring
  rw [ControlPriceGrid.start_grid_zero]
  exact hraw.trans (analytic_first_le_firstRat.trans (first_gate_sound _ first_row_gate))

theorem regular_cell_integral_le (j : ℕ) (hj0 : 0 < j) (hj : j < 1024) :
    (∫ u in firstGrid j..firstGrid (j + 1), integrand u) ≤ rowUpper j := by
  let k : ℝ := (ControlEndpointWitnesses.kernel118.getD j 0 : ℝ) / Sc
  let r : ℝ := (ControlEndpointWitnesses.r18.getD j 0 : ℝ) / Sc
  let h : ℝ := (ControlEndpointWitnesses.forcing18.getD j 0 : ℝ) / Sc
  have hk0 : 0 ≤ k := (norm_nonneg _).trans
    (ControlFastKernelTables.actual_kernel1_left_le j hj0 hj)
  have hm := intervalIntegral.integral_mono_on_of_le_Ioo
    (ControlForcingTables.firstGrid_adjacent_le j) (cell_intervalIntegrable j hj)
    (intervalIntegrable_const (c := k * (r + (widthRat : ℝ) * h))
      (a := firstGrid j) (b := firstGrid (j + 1)) (μ := volume)) (fun u hu => by
      have hz : u / U ∈ Ioo (ControlFastKernelTables.z1 j) (ControlFastKernelTables.z1 (j + 1)) := by
        rw [← grid_kernel_ratio j, ← grid_kernel_ratio (j + 1)]
        exact ⟨div_lt_div_of_pos_right hu.1 U_pos, div_lt_div_of_pos_right hu.2 U_pos⟩
      have hk := ControlFastKernelTables.actual_kernel1_cell_le j hj0 hj hz
      have hp := ControlPriceGrid.all_price_cells j hj u ⟨hu.1.le, hu.2.le⟩
      change coarsePrice 42 c beta u ≤ ControlRecurrenceChecks.R j +
        (firstGrid (j + 1) - firstGrid j) * ControlRecurrenceChecks.H j at hp
      rw [first_width, first_width_eq, R_eq, H_eq] at hp
      have hp0 := CoefficientPriceCells.coarsePrice_nonneg 42 (by decide) c beta u beta_pos
        ((ControlForcingTables.firstGrid_nonneg j).trans hu.1.le)
      exact mul_le_mul hk hp hp0 hk0)
  rw [intervalIntegral.integral_const, smul_eq_mul, first_width, first_width_eq] at hm
  apply hm.trans
  have hg := regular_gate_sound _ _ _ _ (regular_row_gate j hj0 hj)
  convert hg using 1 <;> dsimp [k, r, h, rowUpper] <;> ring

theorem all_cell_integrals_le (j : ℕ) (hj : j < 1024) :
    (∫ u in firstGrid j..firstGrid (j + 1), integrand u) ≤ rowUpper j := by
  by_cases hz : j = 0
  · subst j
    exact first_cell_integral_le
  · exact regular_cell_integral_le j (by omega) hj

/-- The complete original row118 list bounds the true raw first integral.
Neither numerical samples nor default-zero integral values enter the proof. -/
theorem actual_first_integral_le_rows :
    (∫ u in (0 : ℝ)..U0, CoefficientPhysicalProfile.firstIntegrand 42 c beta U u) ≤
      (ControlEndpointWitnesses.row118.sum : ℝ) / ControlEndpointWitnesses.compactScale := by
  have hs : (∑ j ∈ Finset.range 1024,
      ∫ u in firstGrid j..firstGrid (j + 1), integrand u) ≤
      ∑ j ∈ Finset.range 1024, rowUpper j := by
    apply Finset.sum_le_sum
    intro j hj
    exact all_cell_integrals_le j (Finset.mem_range.mp hj)
  rw [intervalIntegral.sum_integral_adjacent_intervals (fun j hj => cell_intervalIntegrable j hj),
    ControlPriceGrid.start_grid_zero, grid_end] at hs
  have hsum := sum_range_getD_div ControlEndpointWitnesses.row118 (Sc : ℝ)
  rw [ControlEndpointWitnesses.row118_length] at hsum
  change (∑ j ∈ Finset.range 1024, rowUpper j) = _ at hsum
  exact hs.trans_eq hsum

end

end BerryEsseen.ControlFirstIntegralRows

#print axioms BerryEsseen.ControlFirstIntegralRows.pilot_16
#print axioms BerryEsseen.ControlFirstIntegralRows.all_rows_checked
#print axioms BerryEsseen.ControlFirstIntegralRows.regular_gate_sound
#print axioms BerryEsseen.ControlFirstIntegralRows.first_gate_sound
#print axioms BerryEsseen.ControlFirstIntegralRows.analytic_first_le_firstRat
#print axioms BerryEsseen.ControlFirstIntegralRows.first_cell_integral_le
#print axioms BerryEsseen.ControlFirstIntegralRows.regular_cell_integral_le
#print axioms BerryEsseen.ControlFirstIntegralRows.actual_first_integral_le_rows
