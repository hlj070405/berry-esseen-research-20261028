module

public import BerryEsseen.FixedPointRecurrence
public import BerryEsseen.ControlEndpointParameters

@[expose] public section

/-! 2026-10-29: all original control-endpoint R updates, consuming the
same compact H and D witnesses. H/D's analytic licenses are separate
theorems; this file checks every numerical recurrence step in one pass. -/

set_option maxRecDepth 30000
set_option maxHeartbeats 2000000

namespace BerryEsseen.ControlRecurrenceChecks

open FixedPointEnclosure FixedPointRecurrence
open FixedFourierConstants (scale scale_positive)

def up (z : ℤ) : ℤ := z * ControlEndpointWitnesses.convertFactor

def step (r h d next : ℤ) : Bool :=
  updateCheck ControlEndpointParameters.dtBox (up r) (up h) (up d) (up next)

def allSteps : Bool := chainCheck step ControlEndpointWitnesses.r18
  ControlEndpointWitnesses.forcing18 ControlEndpointWitnesses.decay18

theorem all_steps_checked : allSteps = true := by decide +kernel

theorem initial_r_zero : ControlEndpointWitnesses.r18.getD 0 0 = 0 := by decide

theorem step_checked (j : ℕ) (hj : j < 1024) :
    step (ControlEndpointWitnesses.r18.getD j 0)
      (ControlEndpointWitnesses.forcing18.getD j 0)
      (ControlEndpointWitnesses.decay18.getD j 0)
      (ControlEndpointWitnesses.r18.getD (j + 1) 0) = true := by
  exact chainCheck_row step _ _ _ all_steps_checked j
    (by simpa only [ControlEndpointWitnesses.forcing18_length] using hj)

noncomputable section

def R (j : ℕ) : ℝ := (qval scale (up (ControlEndpointWitnesses.r18.getD j 0)) : ℝ)
def H (j : ℕ) : ℝ := (qval scale (up (ControlEndpointWitnesses.forcing18.getD j 0)) : ℝ)
def D (j : ℕ) : ℝ := (qval scale (up (ControlEndpointWitnesses.decay18.getD j 0)) : ℝ)

theorem actual_step_inequality (j : ℕ) (hj : j < 1024) :
    D j * R j +
      (ControlEndpointParameters.firstGrid (j + 1) - ControlEndpointParameters.firstGrid j) * H j ≤
      R (j + 1) := by
  rw [ControlEndpointParameters.first_width]
  exact updateCheck_sound ControlEndpointParameters.contains_dt _ _ _ _ (step_checked j hj)

end

end BerryEsseen.ControlRecurrenceChecks

#print axioms BerryEsseen.ControlRecurrenceChecks.all_steps_checked
#print axioms BerryEsseen.ControlRecurrenceChecks.actual_step_inequality
