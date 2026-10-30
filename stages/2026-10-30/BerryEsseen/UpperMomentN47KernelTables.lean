module

public import BerryEsseen.PrawitzRationalGate
public import BerryEsseen.UpperMomentN47KernelWitnesses
public import Mathlib.Data.List.Enum

@[expose] public section

/-! 2026-10-30: direct Int18 kernel checks for the unchanged fixed n47
pure spectral candidate (U=7361/4000, A=4/5, V=4, 1024 cells).
The first zero entry is unused. The correction producer has already capped
its raw square-root upper by 1/2 before ceil+2. Its first candidate is
therefore licensed by the actual correction's half bound; every remaining
candidate passes the raw polynomial gate. The last T2 cell is open at 1. -/

set_option maxRecDepth 30000
set_option maxHeartbeats 2000000

namespace BerryEsseen.UpperMomentN47KernelTables

open PrawitzRationalGate
open Causalean.Stat.CLT.BerryEsseen (prawitzKernel)

abbrev Sc : ℤ := UpperMomentN47KernelWitnesses.compactScale
def q : ℤ := 5 * 1024
def p1 (j : ℕ) : ℤ := (j : ℤ)
def p2 (j : ℕ) : ℤ := 1024 + 4 * (j : ℤ)

def kernel1Upper (j : ℕ) : ℤ := UpperMomentN47KernelWitnesses.kernel118.getD j 0
def kernel2Upper (j : ℕ) : ℤ := UpperMomentN47KernelWitnesses.kernel218.getD j 0
def correctionUpper (j : ℕ) : ℤ := UpperMomentN47KernelWitnesses.correction18.getD j 0

def kernel1CandidateCheck (j : ℕ) (u : ℤ) : Bool :=
  if j = 0 then true else decide (KernelGate (p1 j) q u Sc)
def kernel2CandidateCheck (j : ℕ) (u : ℤ) : Bool := decide (KernelGate (p2 j) q u Sc)

/-- Two sufficient bounds on the same actual norm. The half branch never
asserts that a capped value passes the uncapped rational square gate. -/
def CorrectionCandidateGate (j : ℕ) (u : ℤ) : Prop :=
  Sc ≤ 2 * u ∨ CorrectionGate (p1 j) (p1 (j + 1)) q u Sc

instance (j : ℕ) (u : ℤ) : Decidable (CorrectionCandidateGate j u) := by
  unfold CorrectionCandidateGate
  infer_instance

def correctionCandidateCheck (j : ℕ) (u : ℤ) : Bool := decide (CorrectionCandidateGate j u)

def kernel1TableCheck : Bool := UpperMomentN47KernelWitnesses.kernel118.zipIdx.all
  (fun p => kernel1CandidateCheck p.2 p.1)
def kernel2TableCheck : Bool := UpperMomentN47KernelWitnesses.kernel218.zipIdx.all
  (fun p => kernel2CandidateCheck p.2 p.1)
def correctionTableCheck : Bool := UpperMomentN47KernelWitnesses.correction18.zipIdx.all
  (fun p => correctionCandidateCheck p.2 p.1)

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
  have hj' : j < UpperMomentN47KernelWitnesses.kernel118.length := by
    rw [UpperMomentN47KernelWitnesses.kernel118_length]
    exact hj
  have hh := indexedAll_sound _ kernel1CandidateCheck kernel1_table_checked j hj'
  simp only [kernel1CandidateCheck, ite_eq_right (Nat.ne_of_gt hj0)] at hh
  exact of_decide_eq_true hh

theorem kernel2_gate (j : ℕ) (hj : j < 1024) : KernelGate (p2 j) q (kernel2Upper j) Sc := by
  have hj' : j < UpperMomentN47KernelWitnesses.kernel218.length := by
    rw [UpperMomentN47KernelWitnesses.kernel218_length]
    exact hj
  exact of_decide_eq_true (indexedAll_sound _ kernel2CandidateCheck kernel2_table_checked j hj')

theorem correction_gate (j : ℕ) (hj : j < 1024) :
    CorrectionCandidateGate j (correctionUpper j) := by
  have hj' : j < UpperMomentN47KernelWitnesses.correction18.length := by
    rw [UpperMomentN47KernelWitnesses.correction18_length]
    exact hj
  exact of_decide_eq_true (indexedAll_sound _ correctionCandidateCheck correction_table_checked j hj')

theorem unused_kernel1_head : kernel1Upper 0 = 0 := by decide
theorem first_correction_uses_half : Sc ≤ 2 * correctionUpper 0 := by decide
theorem first_correction_is_not_raw_gate :
    ¬ CorrectionGate (p1 0) (p1 1) q (correctionUpper 0) Sc := by decide

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

/-- K1[0] is unused: this theorem begins with the first genuine cell j=1. -/
theorem actual_kernel1_cell_le (j : ℕ) (hj0 : 0 < j) (hj : j < 1024) {z : ℝ}
    (hz : z ∈ Set.Ioo (z1 j) (z1 (j + 1))) :
    ‖prawitzKernel z‖ ≤ (kernel1Upper j : ℝ) / Sc := by
  have hl : z1 j ∈ Set.Ioo (0 : ℝ) 1 := ⟨z1_pos j hj0, z1_lt_one j hj.le⟩
  exact (PrawitzKernelMonotone.norm_kernel_antitone hl (z1_cell_scope j hj hz) hz.1.le).trans
    (actual_kernel1_left_le j hj0 hj)

/-- The last cell is open at z2(1024)=1, so no totalized endpoint is used. -/
theorem actual_kernel2_cell_le (j : ℕ) (hj : j < 1024) {z : ℝ}
    (hz : z ∈ Set.Ioo (z2 j) (z2 (j + 1))) :
    ‖prawitzKernel z‖ ≤ (kernel2Upper j : ℝ) / Sc := by
  have hl : z2 j ∈ Set.Ioo (0 : ℝ) 1 := ⟨z2_pos j, z2_lt_one j hj⟩
  exact (PrawitzKernelMonotone.norm_kernel_antitone hl (z2_cell_scope j hj hz) hz.1.le).trans
    (actual_kernel2_left_le j hj)

/-- A capped row is proved by the same actual correction's half bound.
An uncapped row uses the rational gate and its mathematically proved cap. -/
theorem actual_correction_cell_le (j : ℕ) (hj : j < 1024) {z : ℝ}
    (hz : z ∈ Set.Ioo (z1 j) (z1 (j + 1))) :
    ‖prawitzKernel z - Complex.I / ((2 * Real.pi * z : ℝ) : ℂ)‖ ≤
      (correctionUpper j : ℝ) / Sc := by
  have hscope := z1_cell_scope j hj hz
  rcases correction_gate j hj with hhalf | hraw
  · have hh := Causalean.Stat.CLT.BerryEsseen.prawitzKernel_principal_correction_norm_le z
      (by simpa only [abs_of_pos hscope.1] using hscope.1)
      (by simpa only [abs_of_pos hscope.1] using hscope.2.le)
    apply hh.trans
    apply (le_div_iff₀ (show (0 : ℝ) < Sc by norm_num [Sc, UpperMomentN47KernelWitnesses.compactScale])).mpr
    have hR : (Sc : ℝ) ≤ 2 * (correctionUpper j : ℝ) := by exact_mod_cast hhalf
    linarith only [hR]
  · exact (correction_norm_le_min_half hraw hscope ⟨hz.1.le, hz.2.le⟩).trans
      (min_le_left _ _)

end

end BerryEsseen.UpperMomentN47KernelTables

#print axioms BerryEsseen.UpperMomentN47KernelTables.kernel1_table_checked
#print axioms BerryEsseen.UpperMomentN47KernelTables.kernel2_table_checked
#print axioms BerryEsseen.UpperMomentN47KernelTables.correction_table_checked
#print axioms BerryEsseen.UpperMomentN47KernelTables.first_correction_is_not_raw_gate
#print axioms BerryEsseen.UpperMomentN47KernelTables.actual_kernel1_cell_le
#print axioms BerryEsseen.UpperMomentN47KernelTables.actual_kernel2_cell_le
#print axioms BerryEsseen.UpperMomentN47KernelTables.actual_correction_cell_le
