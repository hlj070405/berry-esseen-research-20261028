module

public import BerryEsseen.ControlEndpointParameters
public import BerryEsseen.SmallBetaRayEndpoint

@[expose] public section

/-! 2026-10-29: exact sums and a deliberately simple Gaussian tail for
the unchanged control endpoint.  The sums are checked integers; the
integral-row bounds must be supplied by their separate mathematical proofs.
No endpoint conclusion is inferred from the witness data alone. -/

set_option maxRecDepth 30000

noncomputable section

open MeasureTheory Set

namespace BerryEsseen.ControlEndpointBudget

open ControlEndpointParameters

theorem row1_integer_sum : ControlEndpointWitnesses.row118.sum = 586940414713814604 := by
  decide +kernel

theorem row2_integer_sum : ControlEndpointWitnesses.row218.sum = 48586315699385355 := by
  decide +kernel

theorem row3_integer_sum : ControlEndpointWitnesses.row318.sum = 591952176129449467 := by
  decide +kernel

def rowSum (xs : List ℤ) : ℝ := (xs.sum : ℝ) / ControlEndpointWitnesses.compactScale

theorem rowSum1_eq : rowSum ControlEndpointWitnesses.row118 =
    (586940414713814604 : ℝ) / 1000000000000000000 := by
  rw [rowSum, row1_integer_sum]
  norm_num [ControlEndpointWitnesses.compactScale]

theorem rowSum2_eq : rowSum ControlEndpointWitnesses.row218 =
    (48586315699385355 : ℝ) / 1000000000000000000 := by
  rw [rowSum, row2_integer_sum]
  norm_num [ControlEndpointWitnesses.compactScale]

theorem rowSum3_eq : rowSum ControlEndpointWitnesses.row318 =
    (591952176129449467 : ℝ) / 1000000000000000000 := by
  rw [rowSum, row3_integer_sum]
  norm_num [ControlEndpointWitnesses.compactScale]

theorem exp_neg_cutoff_le : Real.exp (-(27 / 5 : ℝ)) ≤ 1 / 200 := by
  have hh := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 27 / 5) 10
  have hl : (200 : ℝ) ≤ Real.exp (27 / 5) := by
    norm_num [Finset.sum_range_succ] at hh
    linarith only [hh]
  rw [Real.exp_neg]
  simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 200) hl

theorem gaussian_cutoff_le : Real.exp (-(U0 ^ 2 / 2)) ≤ 1 / 200 := by
  apply (Real.exp_le_exp.mpr ?_).trans exp_neg_cutoff_le
  norm_num [U0, A, rootS, ControlEndpointWitnesses.aNum, ControlEndpointWitnesses.aDen]

theorem fourth_integral_le :
    (1 / (Real.pi * beta)) *
      (∫ t in Ioi U0, CoefficientPhysicalProfile.fourthIntegrand t) ≤
      1 / (600 * beta * U0 ^ 2) := by
  have ht := SmallBetaRayEndpoint.gaussian_reciprocal_tail_le (1 / 2) U0
    (by norm_num) U0_pos
  have hf : (fun x : ℝ => Real.exp (-(1 / 2) * x ^ 2) / x) =
      CoefficientPhysicalProfile.fourthIntegrand := by
    funext x
    unfold CoefficientPhysicalProfile.fourthIntegrand
    congr 2
    ring
  rw [hf] at ht
  have heq : -(1 / 2 : ℝ) * U0 ^ 2 = -(U0 ^ 2 / 2) := by ring
  rw [heq] at ht
  norm_num only [show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_mul] at ht
  have hi : (∫ t in Ioi U0, CoefficientPhysicalProfile.fourthIntegrand t) ≤
      (1 / 200 : ℝ) / U0 ^ 2 := by
    apply ht.trans
    exact div_le_div_of_nonneg_right gaussian_cutoff_le (sq_nonneg U0)
  have hp : (3 : ℝ) ≤ Real.pi := Real.pi_gt_three.le
  have hb := beta_pos
  have hu := U0_pos
  have hpi := Real.pi_pos
  have hc : 0 ≤ 1 / (Real.pi * beta) := by positivity
  calc
    _ ≤ (1 / (Real.pi * beta)) * ((1 / 200 : ℝ) / U0 ^ 2) :=
      mul_le_mul_of_nonneg_left hi hc
    _ = 1 / (200 * Real.pi * beta * U0 ^ 2) := by ring
    _ ≤ 1 / (600 * beta * U0 ^ 2) := by
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith only [mul_le_mul_of_nonneg_right hp (by positivity :
        0 ≤ 200 * beta * U0 ^ 2)]

/-- A small rational budget leaves room for a simple, analytic tail bound.
The three integral-row theorems are intentionally not assumed here. -/
theorem normalized_row_budget :
    (2 / U) * rowSum ControlEndpointWitnesses.row118 +
      (2 / (U * beta)) * rowSum ControlEndpointWitnesses.row218 +
      (2 / (U * beta)) * rowSum ControlEndpointWitnesses.row318 +
      1 / (600 * beta * U0 ^ 2) < 4071 / 10000 := by
  rw [rowSum1_eq, rowSum2_eq, rowSum3_eq]
  norm_num [U, U0, A, beta, rootS, ControlEndpointWitnesses.aNum, ControlEndpointWitnesses.aDen]

end BerryEsseen.ControlEndpointBudget

#print axioms BerryEsseen.ControlEndpointBudget.row1_integer_sum
#print axioms BerryEsseen.ControlEndpointBudget.fourth_integral_le
#print axioms BerryEsseen.ControlEndpointBudget.normalized_row_budget
