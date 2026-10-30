module

public import BerryEsseen.PrawitzRationalGate
public import BerryEsseen.ControlEndpointWitnesses
public import Mathlib.Data.List.Enum

@[expose] public section

/-! 2026-10-29: direct polynomial gates for the unchanged compact kernel
witnesses at the original control endpoint. Candidates are Int18, with no
scale-10^40 conversion or fixed-point divisions during table validation.
The first zero index is only a dummy, and correction witnesses are raw. -/

set_option maxRecDepth 30000
set_option maxHeartbeats 2000000

namespace BerryEsseen.ControlFastKernelTables

open PrawitzRationalGate
open Causalean.Stat.CLT.BerryEsseen (prawitzKernel)

abbrev Sc : ℤ := ControlEndpointWitnesses.compactScale
def q : ℤ := 400 * 1024
def p1 (j : ℕ) : ℤ := 97 * (j : ℤ)
def p2 (j : ℕ) : ℤ := 97 * 1024 + 303 * (j : ℤ)

def kernel1Upper (j : ℕ) : ℤ := ControlEndpointWitnesses.kernel118.getD j 0
def kernel2Upper (j : ℕ) : ℤ := ControlEndpointWitnesses.kernel218.getD j 0
def correctionRawUpper (j : ℕ) : ℤ := ControlEndpointWitnesses.correctionRaw18.getD j 0
def correctionCappedUpper (j : ℕ) : ℤ := min (correctionRawUpper j) 500000000000000000

def kernel1CandidateCheck (j : ℕ) (u : ℤ) : Bool :=
  if j = 0 then true else decide (KernelGate (p1 j) q u Sc)
def kernel2CandidateCheck (j : ℕ) (u : ℤ) : Bool := decide (KernelGate (p2 j) q u Sc)
def correctionCandidateCheck (j : ℕ) (u : ℤ) : Bool :=
  decide (CorrectionGate (p1 j) (p1 (j + 1)) q u Sc)

def kernel1PilotCheck : Bool := (ControlEndpointWitnesses.kernel118.take 16).zipIdx.all
  (fun p => kernel1CandidateCheck p.2 p.1)
def kernel2PilotCheck : Bool := (ControlEndpointWitnesses.kernel218.take 16).zipIdx.all
  (fun p => kernel2CandidateCheck p.2 p.1)
def correctionPilotCheck : Bool := (ControlEndpointWitnesses.correctionRaw18.take 16).zipIdx.all
  (fun p => correctionCandidateCheck p.2 p.1)

def kernel1TableCheck : Bool := ControlEndpointWitnesses.kernel118.zipIdx.all
  (fun p => kernel1CandidateCheck p.2 p.1)
def kernel2TableCheck : Bool := ControlEndpointWitnesses.kernel218.zipIdx.all
  (fun p => kernel2CandidateCheck p.2 p.1)
def correctionTableCheck : Bool := ControlEndpointWitnesses.correctionRaw18.zipIdx.all
  (fun p => correctionCandidateCheck p.2 p.1)

theorem kernel1_pilot_16 : kernel1PilotCheck = true := by decide
theorem kernel2_pilot_16 : kernel2PilotCheck = true := by decide
theorem correction_pilot_16 : correctionPilotCheck = true := by decide

/-- Direct kernel reduction avoids repeating these same full table
computations in both the elaborator and the kernel. -/
theorem kernel1_table_checked : kernel1TableCheck = true := by decide +kernel
theorem kernel2_table_checked : kernel2TableCheck = true := by decide +kernel
theorem correction_table_checked : correctionTableCheck = true := by decide +kernel

private lemma indexedAll_sound (xs : List ℤ) (check : ℕ → ℤ → Bool)
    (h : xs.zipIdx.all (fun p => check p.2 p.1) = true) (j : ℕ) (hj : j < xs.length) :
    check j (xs.getD j 0) = true := by
  have hh := (List.forall_mem_zipIdx'.mp (List.all_eq_true.mp h)) j hj
  simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some] using hh

theorem kernel1_gate (j : ℕ) (hj0 : 0 < j) (hj : j < 1024) :
    KernelGate (p1 j) q (kernel1Upper j) Sc := by
  have hj' : j < ControlEndpointWitnesses.kernel118.length := by
    rw [ControlEndpointWitnesses.kernel118_length]
    exact hj
  have hh := indexedAll_sound _ kernel1CandidateCheck kernel1_table_checked j hj'
  simp only [kernel1CandidateCheck, ite_eq_right (Nat.ne_of_gt hj0)] at hh
  exact of_decide_eq_true hh

theorem kernel2_gate (j : ℕ) (hj : j < 1024) : KernelGate (p2 j) q (kernel2Upper j) Sc := by
  have hj' : j < ControlEndpointWitnesses.kernel218.length := by
    rw [ControlEndpointWitnesses.kernel218_length]
    exact hj
  exact of_decide_eq_true (indexedAll_sound _ kernel2CandidateCheck kernel2_table_checked j hj')

theorem correction_gate (j : ℕ) (hj : j < 1024) :
    CorrectionGate (p1 j) (p1 (j + 1)) q (correctionRawUpper j) Sc := by
  have hj' : j < ControlEndpointWitnesses.correctionRaw18.length := by
    rw [ControlEndpointWitnesses.correctionRaw18_length]
    exact hj
  exact of_decide_eq_true (indexedAll_sound _ correctionCandidateCheck correction_table_checked j hj')

theorem first_raw_correction_exceeds_half :
    500000000000000000 < correctionRawUpper 0 := by decide

noncomputable section

def z1 (j : ℕ) : ℝ := (p1 j : ℝ) / q
def z2 (j : ℕ) : ℝ := (p2 j : ℝ) / q

lemma z1_nonneg (j : ℕ) : 0 ≤ z1 j := by
  simp only [z1, p1, q, Int.cast_mul, Int.cast_natCast, Int.cast_ofNat]
  positivity

lemma z1_pos (j : ℕ) (hj : 0 < j) : 0 < z1 j := by
  have h : (0 : ℝ) < j := Nat.cast_pos.mpr hj
  simp only [z1, p1, q, Int.cast_mul, Int.cast_natCast, Int.cast_ofNat]
  positivity

lemma z1_lt_one (j : ℕ) (hj : j ≤ 1024) : z1 j < 1 := by
  have h : (j : ℝ) ≤ 1024 := by exact_mod_cast hj
  simp only [z1, p1, q, Int.cast_mul, Int.cast_natCast, Int.cast_ofNat]
  nlinarith only [h]

lemma z2_pos (j : ℕ) : 0 < z2 j := by
  simp only [z2, p2, q, Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_ofNat]
  positivity

lemma z2_lt_one (j : ℕ) (hj : j < 1024) : z2 j < 1 := by
  have h : (j : ℝ) < 1024 := by exact_mod_cast hj
  simp only [z2, p2, q, Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_ofNat]
  nlinarith only [h]

lemma z2_le_one (j : ℕ) (hj : j ≤ 1024) : z2 j ≤ 1 := by
  have h : (j : ℝ) ≤ 1024 := by exact_mod_cast hj
  simp only [z2, p2, q, Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_ofNat]
  nlinarith only [h]

lemma z1_cell_scope (j : ℕ) (hj : j < 1024) {z : ℝ}
    (hz : z ∈ Set.Ioo (z1 j) (z1 (j + 1))) : z ∈ Set.Ioo (0 : ℝ) 1 :=
  ⟨(z1_nonneg j).trans_lt hz.1, hz.2.trans (z1_lt_one (j + 1) (by omega))⟩

lemma z2_cell_scope (j : ℕ) (hj : j < 1024) {z : ℝ}
    (hz : z ∈ Set.Ioo (z2 j) (z2 (j + 1))) : z ∈ Set.Ioo (0 : ℝ) 1 :=
  ⟨(z2_pos j).trans hz.1, hz.2.trans_le (z2_le_one (j + 1) (by omega))⟩

theorem actual_kernel1_left_le (j : ℕ) (hj0 : 0 < j) (hj : j < 1024) :
    ‖prawitzKernel (z1 j)‖ ≤ (kernel1Upper j : ℝ) / Sc :=
  PrawitzRationalGate.kernel_norm_le (kernel1_gate j hj0 hj)

theorem actual_kernel2_left_le (j : ℕ) (hj : j < 1024) :
    ‖prawitzKernel (z2 j)‖ ≤ (kernel2Upper j : ℝ) / Sc :=
  PrawitzRationalGate.kernel_norm_le (kernel2_gate j hj)

/-- Zero is an explicit first-table dummy, so the first real analytic
cell using this table is j=1. -/
theorem actual_kernel1_cell_le (j : ℕ) (hj0 : 0 < j) (hj : j < 1024) {z : ℝ}
    (hz : z ∈ Set.Ioo (z1 j) (z1 (j + 1))) :
    ‖prawitzKernel z‖ ≤ (kernel1Upper j : ℝ) / Sc := by
  have hl : z1 j ∈ Set.Ioo (0 : ℝ) 1 := ⟨z1_pos j hj0, z1_lt_one j hj.le⟩
  exact (PrawitzKernelMonotone.norm_kernel_antitone hl (z1_cell_scope j hj hz) hz.1.le).trans
    (actual_kernel1_left_le j hj0 hj)

/-- The last second cell remains open at the separately totalized z=1. -/
theorem actual_kernel2_cell_le (j : ℕ) (hj : j < 1024) {z : ℝ}
    (hz : z ∈ Set.Ioo (z2 j) (z2 (j + 1))) :
    ‖prawitzKernel z‖ ≤ (kernel2Upper j : ℝ) / Sc := by
  have hl : z2 j ∈ Set.Ioo (0 : ℝ) 1 := ⟨z2_pos j, z2_lt_one j hj⟩
  exact (PrawitzKernelMonotone.norm_kernel_antitone hl (z2_cell_scope j hj hz) hz.1.le).trans
    (actual_kernel2_left_le j hj)

/-- The unchanged raw candidate is gated first; the half bound applies
to the same actual correction norm only after that successful gate. -/
theorem actual_correction_cell_le_min_half (j : ℕ) (hj : j < 1024) {z : ℝ}
    (hz : z ∈ Set.Ioo (z1 j) (z1 (j + 1))) :
    ‖prawitzKernel z - Complex.I / ((2 * Real.pi * z : ℝ) : ℂ)‖ ≤
      min ((correctionRawUpper j : ℝ) / Sc) (1 / 2) :=
  correction_norm_le_min_half (correction_gate j hj) (z1_cell_scope j hj hz)
    ⟨hz.1.le, hz.2.le⟩

lemma compact_min_half (u : ℤ) : ((min u 500000000000000000 : ℤ) : ℝ) / Sc =
    min ((u : ℝ) / Sc) (1 / 2) := by
  rw [Int.cast_min, ← min_div_div_right (show (0 : ℝ) ≤ Sc by norm_num [Sc, ControlEndpointWitnesses.compactScale])]
  norm_num [Sc, ControlEndpointWitnesses.compactScale]

theorem actual_correction_cell_le (j : ℕ) (hj : j < 1024) {z : ℝ}
    (hz : z ∈ Set.Ioo (z1 j) (z1 (j + 1))) :
    ‖prawitzKernel z - Complex.I / ((2 * Real.pi * z : ℝ) : ℂ)‖ ≤
      (correctionCappedUpper j : ℝ) / Sc := by
  unfold correctionCappedUpper
  rw [compact_min_half]
  exact actual_correction_cell_le_min_half j hj hz

end

end BerryEsseen.ControlFastKernelTables

#print axioms BerryEsseen.ControlFastKernelTables.kernel1_pilot_16
#print axioms BerryEsseen.ControlFastKernelTables.kernel2_pilot_16
#print axioms BerryEsseen.ControlFastKernelTables.correction_pilot_16
#print axioms BerryEsseen.ControlFastKernelTables.kernel1_table_checked
#print axioms BerryEsseen.ControlFastKernelTables.kernel2_table_checked
#print axioms BerryEsseen.ControlFastKernelTables.correction_table_checked
#print axioms BerryEsseen.ControlFastKernelTables.actual_kernel1_cell_le
#print axioms BerryEsseen.ControlFastKernelTables.actual_kernel2_cell_le
#print axioms BerryEsseen.ControlFastKernelTables.actual_correction_cell_le
