module

public import BerryEsseen.AllocationEnvelope
public import BerryEsseen.BernoulliMomentFloor
public import BerryEsseen.StaircasePrices

@[expose] public section

/-! 2026-10-29: transfer the original P39 signed allocation plane to a
single count-11 variance ceiling. The plane is an acquired input, not a
consequence of replaying these coordinate formulas. No noise/allocation
subdivision is used. -/

noncomputable section
open MeasureTheory Set

namespace BerryEsseen.P39CountVariance

def resource : ℝ := 292937005451 / 500000000000
def charge0 : ℝ := 3371907359183 / 1000000000000
def charge1 : ℝ := 53718504159 / 125000000000

lemma resource_pos : 0 < resource := by norm_num [resource]

lemma endpoint_prices :
    resource * (25 / 26) ≤ (17 / 100) * charge0 ∧
      resource * (550 / 507) ≤ (17 / 100) * (charge0 + charge1) := by
  norm_num [resource, charge0, charge1]

lemma coefficient_upper {p α : ℝ}
    (hp : p ∈ Icc (39 / 100 : ℝ) (2 / 5)) (hα : α ∈ Icc (0 : ℝ) 1) :
    15 * (1 - α) / (26 * (1 - p)) + 11 * α / (26 * p) ≤
      (1 - α) * (25 / 26) + α * (550 / 507) := by
  have hq : 0 < 1 - p := by linarith only [hp.2]
  have hp0 : 0 < p := by linarith only [hp.1]
  have h0 : (15 : ℝ) / (26 * (1 - p)) ≤ 25 / 26 := by
    apply (div_le_iff₀ (by positivity : 0 < 26 * (1 - p))).mpr
    linarith only [hp.2]
  have h1 : (11 : ℝ) / (26 * p) ≤ 550 / 507 := by
    apply (div_le_iff₀ (by positivity : 0 < 26 * p)).mpr
    linarith only [hp.1]
  have hs := add_le_add
    (mul_le_mul_of_nonneg_left h0 (sub_nonneg.mpr hα.2))
    (mul_le_mul_of_nonneg_left h1 hα.1)
  convert hs using 1 <;> ring

theorem allocationVariance_le {p α l : ℝ}
    (hp : p ∈ Icc (39 / 100 : ℝ) (2 / 5)) (hα : α ∈ Icc (0 : ℝ) 1)
    (hl : 0 ≤ l) (hplane : l * (charge0 + charge1 * α) ≤ resource) :
    AllocationEnvelope.allocationVariance p (l / 26) 26 11 α ≤ 17 / 100 := by
  let V := AllocationEnvelope.allocationVariance p (l / 26) 26 11 α
  let C := (1 - α) * (25 / 26) + α * (550 / 507)
  have hV : V ≤ l * C := by
    have hh := mul_le_mul_of_nonneg_left (coefficient_upper hp hα) hl
    have heq : V = l * (15 * (1 - α) / (26 * (1 - p)) + 11 * α / (26 * p)) := by
      dsimp only [V, AllocationEnvelope.allocationVariance]
      norm_num only [Nat.cast_ofNat, Nat.reduceSub]
      have hp0 : p ≠ 0 := ne_of_gt (by linarith only [hp.1] : 0 < p)
      have hq0 : 1 - p ≠ 0 := ne_of_gt (by linarith only [hp.2] : 0 < 1 - p)
      field_simp [hp0, hq0]
    rw [heq]
    exact hh
  have hC : resource * C ≤ (17 / 100) * (charge0 + charge1 * α) := by
    have hh := add_le_add
      (mul_le_mul_of_nonneg_left endpoint_prices.1 (sub_nonneg.mpr hα.2))
      (mul_le_mul_of_nonneg_left endpoint_prices.2 hα.1)
    dsimp only [C]
    nlinarith only [hh]
  have hpaid : resource * V ≤ (17 / 100) * resource := by
    calc
      _ ≤ resource * (l * C) := mul_le_mul_of_nonneg_left hV resource_pos.le
      _ = l * (resource * C) := by ring
      _ ≤ l * ((17 / 100) * (charge0 + charge1 * α)) := mul_le_mul_of_nonneg_left hC hl
      _ = (17 / 100) * (l * (charge0 + charge1 * α)) := by ring
      _ ≤ (17 / 100) * resource := mul_le_mul_of_nonneg_left hplane (by norm_num)
  apply (mul_le_mul_iff_right₀ resource_pos).mp
  change resource * V ≤ resource * (17 / 100)
  nlinarith only [hpaid]

theorem canonical_countVariance_eq (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ) :
    StaircasePrices.actualCountVariance (CanonicalSign.residual0 μ hμ : Measure ℝ)
        (CanonicalSign.residual1 μ hμ : Measure ℝ) 26 11 =
      AllocationEnvelope.allocationVariance (CanonicalSign.p μ)
        (CanonicalSign.noiseVariance μ hμ) 26 11 (ConditionalResidual.actualAllocation μ hμ) := by
  by_cases hs : CanonicalSign.noiseVariance μ hμ = 0
  · obtain ⟨h0, h1, _⟩ := ConditionalResidual.canonical_zero_noise_moments μ hμ hs
    change 15 * MomentBudget.residualSecondMoment (CanonicalSign.residual0 μ hμ) +
        11 * MomentBudget.residualSecondMoment (CanonicalSign.residual1 μ hμ) = _
    rw [h0, h1, hs]
    simp only [AllocationEnvelope.allocationVariance, zero_mul, mul_zero, add_zero]
  · change 15 * MomentBudget.residualSecondMoment (CanonicalSign.residual0 μ hμ) +
        11 * MomentBudget.residualSecondMoment (CanonicalSign.residual1 μ hμ) = _
    exact MomentBudget.allocation_count_variance (CanonicalSign.p μ) _ _
      (CanonicalSign.noiseVariance μ hμ) (ConditionalResidual.actualAllocation μ hμ) 15 11
      (CanonicalSign.p_pos μ hμ) (CanonicalSign.p_lt_one μ hμ)
      (lt_of_le_of_ne (CanonicalSign.noiseVariance_nonneg μ hμ) (Ne.symm hs)) rfl rfl

/-- Both allocation and variance are the actual canonical values of μ.
The predecessor/resource argument must independently supply hplane. -/
theorem canonical_countVariance_le (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (hp : CanonicalSign.p μ ∈ Icc (39 / 100 : ℝ) (2 / 5))
    (hplane : (26 * CanonicalSign.noiseVariance μ hμ) *
      (charge0 + charge1 * ConditionalResidual.actualAllocation μ hμ) ≤ resource) :
    StaircasePrices.actualCountVariance (CanonicalSign.residual0 μ hμ : Measure ℝ)
      (CanonicalSign.residual1 μ hμ : Measure ℝ) 26 11 ≤ 17 / 100 := by
  rw [canonical_countVariance_eq μ hμ]
  have hh := allocationVariance_le hp (BernoulliMomentFloor.canonical_allocation_mem_Icc μ hμ)
    (mul_nonneg (by norm_num) (CanonicalSign.noiseVariance_nonneg μ hμ)) hplane
  simpa only [show (26 * CanonicalSign.noiseVariance μ hμ) / 26 =
    CanonicalSign.noiseVariance μ hμ by ring] using hh

end BerryEsseen.P39CountVariance

#print axioms BerryEsseen.P39CountVariance.allocationVariance_le
#print axioms BerryEsseen.P39CountVariance.canonical_countVariance_eq
#print axioms BerryEsseen.P39CountVariance.canonical_countVariance_le
