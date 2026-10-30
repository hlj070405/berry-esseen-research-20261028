module

public import BerryEsseen.FixedPointCellCheck
public import BerryEsseen.ControlEndpointParameters
public import Mathlib.Data.List.Enum

@[expose] public section

/-! 2026-10-29: consumption of the original control endpoint's H/D
witnesses on its unchanged 1024-cell first frequency grid. Each Int18
candidate is converted by the original factor, and the full lists are
checked by one zipIdx traversal. No data or frequency grid is enlarged. -/

set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

namespace BerryEsseen.ControlForcingTables

open FixedPointEnclosure FixedPointCellCheck
open FixedFourierConstants (scale scale_positive)
open ControlEndpointParameters (cBox betaBox alphaBox lambdaBox firstGridBox)

def forcingUpper (j : ℕ) : ℤ :=
  ControlEndpointWitnesses.forcing18.getD j 0 * ControlEndpointWitnesses.convertFactor

def decayUpper (j : ℕ) : ℤ :=
  ControlEndpointWitnesses.decay18.getD j 0 * ControlEndpointWitnesses.convertFactor

def forcingCandidateCheck (j : ℕ) (candidate18 : ℤ) : Bool :=
  forcingCheck cBox betaBox (firstGridBox j) (firstGridBox (j + 1)) alphaBox lambdaBox
    (candidate18 * ControlEndpointWitnesses.convertFactor)

def decayCandidateCheck (j : ℕ) (candidate18 : ℤ) : Bool :=
  decayCheck (firstGridBox j) (firstGridBox (j + 1))
    (candidate18 * ControlEndpointWitnesses.convertFactor)

def forcingPrefixCheck (n : ℕ) : Bool := (ControlEndpointWitnesses.forcing18.take n).zipIdx.all
  (fun p => forcingCandidateCheck p.2 p.1)

def decayPrefixCheck (n : ℕ) : Bool := (ControlEndpointWitnesses.decay18.take n).zipIdx.all
  (fun p => decayCandidateCheck p.2 p.1)

def forcingTableCheck : Bool := ControlEndpointWitnesses.forcing18.zipIdx.all
  (fun p => forcingCandidateCheck p.2 p.1)

def decayTableCheck : Bool := ControlEndpointWitnesses.decay18.zipIdx.all
  (fun p => decayCandidateCheck p.2 p.1)

theorem witness_lengths : ControlEndpointWitnesses.forcing18.length = 1024 ∧
    ControlEndpointWitnesses.decay18.length = 1024 :=
  ⟨ControlEndpointWitnesses.forcing18_length, ControlEndpointWitnesses.decay18_length⟩

theorem forcing_pilot_16 : forcingPrefixCheck 16 = true := by decide +kernel
theorem decay_pilot_16 : decayPrefixCheck 16 = true := by decide +kernel

theorem forcing_table_checked : forcingTableCheck = true := by decide +kernel
theorem decay_table_checked : decayTableCheck = true := by decide +kernel

theorem conversion_exact : ControlEndpointWitnesses.compactScale *
    ControlEndpointWitnesses.convertFactor = scale := by decide

private lemma indexedAll_sound (xs : List ℤ) (check : ℕ → ℤ → Bool)
    (h : xs.zipIdx.all (fun p => check p.2 p.1) = true) (j : ℕ) (hj : j < xs.length) :
    check j (xs.getD j 0) = true := by
  have hh := (List.forall_mem_zipIdx'.mp (List.all_eq_true.mp h)) j hj
  simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some] using hh

theorem forcing_check (j : ℕ) (hj : j < 1024) :
    forcingCheck cBox betaBox (firstGridBox j) (firstGridBox (j + 1)) alphaBox lambdaBox
      (forcingUpper j) = true := by
  have hj' : j < ControlEndpointWitnesses.forcing18.length := by
    rw [ControlEndpointWitnesses.forcing18_length]
    exact hj
  exact indexedAll_sound _ forcingCandidateCheck forcing_table_checked j hj'

theorem decay_check (j : ℕ) (hj : j < 1024) :
    decayCheck (firstGridBox j) (firstGridBox (j + 1)) (decayUpper j) = true := by
  have hj' : j < ControlEndpointWitnesses.decay18.length := by
    rw [ControlEndpointWitnesses.decay18_length]
    exact hj
  exact indexedAll_sound _ decayCandidateCheck decay_table_checked j hj'

theorem firstGrid_nonneg (j : ℕ) : 0 ≤ ControlEndpointParameters.firstGrid j := by
  unfold ControlEndpointParameters.firstGrid
  exact mul_nonneg ControlEndpointParameters.U0_pos.le
    (div_nonneg (Nat.cast_nonneg j) (Nat.cast_nonneg _))

theorem firstGrid_adjacent_le (j : ℕ) :
    ControlEndpointParameters.firstGrid j ≤ ControlEndpointParameters.firstGrid (j + 1) := by
  have hstep : 0 < ControlEndpointParameters.firstGrid (j + 1) -
      ControlEndpointParameters.firstGrid j := by
    rw [ControlEndpointParameters.first_width]
    exact div_pos ControlEndpointParameters.U0_pos
      (Nat.cast_pos.mpr ControlEndpointParameters.resolution_pos)
  exact (sub_pos.mp hstep).le

/-- The complete original H table bounds the actual forcing at every
real point of each closed first-grid cell, including j=0. -/
theorem actual_forcing_cell_le (j : ℕ) (hj : j < 1024) {u : ℝ}
    (hu : u ∈ Set.Icc (ControlEndpointParameters.firstGrid j)
      (ControlEndpointParameters.firstGrid (j + 1))) :
    CoefficientRayPrice.lossEnvelope 42 ControlEndpointParameters.c ControlEndpointParameters.beta u *
        (u ^ 2 / 2 + CoarseHighMomentRayPrice.lambda 42 ControlEndpointParameters.beta * u ^ 3 / 3) ≤
      (qval scale (forcingUpper j) : ℝ) :=
  forcingCheck_sound 42 (by decide) ControlEndpointParameters.contains_c
    ControlEndpointParameters.contains_beta (ControlEndpointParameters.contains_firstGrid j)
    (ControlEndpointParameters.contains_firstGrid (j + 1)) ControlEndpointParameters.contains_alpha
    ControlEndpointParameters.contains_lambda ControlEndpointParameters.c_pos.le
    ControlEndpointParameters.beta_pos (firstGrid_nonneg j) (firstGrid_adjacent_le j) hu
    (forcing_check j hj)

/-- The complete original D table bounds the actual Gaussian step
attenuation between the same two actual first-grid endpoints. -/
theorem actual_decay_step_le (j : ℕ) (hj : j < 1024) :
    Real.exp (-((ControlEndpointParameters.firstGrid (j + 1) ^ 2 -
      ControlEndpointParameters.firstGrid j ^ 2) / 2)) ≤
      (qval scale (decayUpper j) : ℝ) :=
  decayCheck_sound (ControlEndpointParameters.contains_firstGrid j)
    (ControlEndpointParameters.contains_firstGrid (j + 1)) (firstGrid_nonneg j)
    (firstGrid_adjacent_le j) (decay_check j hj)

end BerryEsseen.ControlForcingTables

#print axioms BerryEsseen.ControlForcingTables.forcing_pilot_16
#print axioms BerryEsseen.ControlForcingTables.decay_pilot_16
#print axioms BerryEsseen.ControlForcingTables.forcing_table_checked
#print axioms BerryEsseen.ControlForcingTables.decay_table_checked
#print axioms BerryEsseen.ControlForcingTables.actual_forcing_cell_le
#print axioms BerryEsseen.ControlForcingTables.actual_decay_step_le
