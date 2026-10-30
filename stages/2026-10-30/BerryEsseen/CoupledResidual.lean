module

public import BerryEsseen.StaircaseIntegral
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
The actual common residual construction. Indices are zero based: count
`j` uses the first `j` residuals from group 1 and the remaining residuals
from group 0. Independence is not needed for the support comparison or
for the finite-sum expectation identities proved here.
-/

namespace BerryEsseen.CoupledResidual

open MeasureTheory
open scoped BigOperators

noncomputable section

/-- An algebraic form of the common residual, convenient for comparing counts. -/
def value (U0 U1 : ℕ → ℝ) (n j : ℕ) : ℝ :=
  (∑ i ∈ Finset.range n, U0 i) + ∑ i ∈ Finset.range j, (U1 i - U0 i)

/-- For valid counts, the algebraic form is exactly the original split sum. -/
theorem value_eq_split (U0 U1 : ℕ → ℝ) (n j : ℕ) (hj : j ≤ n) :
    value U0 U1 n j = (∑ i ∈ Finset.range j, U1 i) +
      ∑ i ∈ Finset.range (n - j), U0 (j + i) := by
  have hlength : j + (n - j) = n := Nat.add_sub_of_le hj
  have hsplit := Finset.sum_range_add U0 j (n - j)
  rw [hlength] at hsplit
  unfold value
  rw [hsplit, Finset.sum_sub_distrib]
  ring

theorem value_add (U0 U1 : ℕ → ℝ) (n k r : ℕ) :
    value U0 U1 n (k + r) = value U0 U1 n k +
      ∑ i ∈ Finset.range r, (U1 (k + i) - U0 (k + i)) := by
  unfold value
  rw [Finset.sum_range_add]
  ring

/-- The coupling inequality follows from the two original group support
bounds. It is not assumed as a property of the constructed residuals. -/
theorem support_implies_coupling (U0 U1 : ℕ → ℝ) (n k r : ℕ) (a0 a1 Δ : ℝ)
    (hkr : k + r ≤ n)
    (hU0 : ∀ i : ℕ, i < n → U0 i ≤ a0)
    (hU1 : ∀ i : ℕ, i < n → -a1 ≤ U1 i)
    (hcap : a0 + a1 ≤ Δ) :
    value U0 U1 n k - (r : ℝ) * Δ ≤ value U0 U1 n (k + r) := by
  have hsum : -(r : ℝ) * Δ ≤
      ∑ i ∈ Finset.range r, (U1 (k + i) - U0 (k + i)) := by
    calc
      _ = ∑ i ∈ Finset.range r, -Δ := by
        simp [nsmul_eq_mul, neg_mul]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i hi
        have hindex : k + i < n :=
          lt_of_lt_of_le (Nat.add_lt_add_left (Finset.mem_range.mp hi) k) hkr
        have h0 := hU0 (k + i) hindex
        have h1 := hU1 (k + i) hindex
        linarith
  rw [value_add]
  linarith

variable {Ω : Type*} [MeasurableSpace Ω]

def randomValue (U0 U1 : ℕ → Ω → ℝ) (n j : ℕ) (ω : Ω) : ℝ :=
  value (fun i => U0 i ω) (fun i => U1 i ω) n j

/-- The almost-everywhere coupling hypothesis used by the staircase
integral theorems, now derived from the actual group support bounds. -/
theorem ae_support_implies_staircaseCoupling (μ : Measure Ω)
    (U0 U1 : ℕ → Ω → ℝ) (n k N : ℕ) (a0 a1 Δ : ℝ)
    (hkn : k + N ≤ n)
    (hU0 : ∀ᵐ ω ∂μ, ∀ i : ℕ, i < n → U0 i ω ≤ a0)
    (hU1 : ∀ᵐ ω ∂μ, ∀ i : ℕ, i < n → -a1 ≤ U1 i ω)
    (hcap : a0 + a1 ≤ Δ) :
    ∀ᵐ ω ∂μ, ∀ r : ℕ, 1 ≤ r → r ≤ N →
      randomValue U0 U1 n k ω - (r : ℝ) * Δ ≤ randomValue U0 U1 n (k + r) ω := by
  exact (hU0.and hU1).mono (fun ω hs r _ hrN =>
    support_implies_coupling (fun i => U0 i ω) (fun i => U1 i ω) n k r a0 a1 Δ
      ((Nat.add_le_add_left hrN k).trans hkn) hs.1 hs.2 hcap)

theorem measurable_randomValue (U0 U1 : ℕ → Ω → ℝ) (n j : ℕ) (hj : j ≤ n)
    (hU0 : ∀ i : ℕ, i < n → Measurable (U0 i))
    (hU1 : ∀ i : ℕ, i < n → Measurable (U1 i)) :
    Measurable (randomValue U0 U1 n j) := by
  have hbase : Measurable (fun ω => ∑ i ∈ Finset.range n, U0 i ω) :=
    Finset.measurable_sum _ (fun i hi => hU0 i (Finset.mem_range.mp hi))
  have hswitch : Measurable (fun ω => ∑ i ∈ Finset.range j, (U1 i ω - U0 i ω)) :=
    Finset.measurable_sum _ (fun i hi =>
      (hU1 i (lt_of_lt_of_le (Finset.mem_range.mp hi) hj)).sub
        (hU0 i (lt_of_lt_of_le (Finset.mem_range.mp hi) hj)))
  exact hbase.add hswitch

theorem integrable_randomValue (μ : Measure Ω) (U0 U1 : ℕ → Ω → ℝ)
    (n j : ℕ) (hj : j ≤ n)
    (hU0 : ∀ i : ℕ, i < n → Integrable (U0 i) μ)
    (hU1 : ∀ i : ℕ, i < n → Integrable (U1 i) μ) :
    Integrable (randomValue U0 U1 n j) μ := by
  have hbase : Integrable (fun ω => ∑ i ∈ Finset.range n, U0 i ω) μ :=
    integrable_finsetSum _ (fun i hi => hU0 i (Finset.mem_range.mp hi))
  have hswitch : Integrable (fun ω => ∑ i ∈ Finset.range j, (U1 i ω - U0 i ω)) μ :=
    integrable_finsetSum _ (fun i hi =>
      (hU1 i (lt_of_lt_of_le (Finset.mem_range.mp hi) hj)).sub
        (hU0 i (lt_of_lt_of_le (Finset.mem_range.mp hi) hj)))
  exact hbase.add hswitch

theorem integral_randomValue (μ : Measure Ω) (U0 U1 : ℕ → Ω → ℝ)
    (n j : ℕ) (hj : j ≤ n)
    (hU0 : ∀ i : ℕ, i < n → Integrable (U0 i) μ)
    (hU1 : ∀ i : ℕ, i < n → Integrable (U1 i) μ) :
    (∫ ω, randomValue U0 U1 n j ω ∂μ) =
      (∑ i ∈ Finset.range n, ∫ ω, U0 i ω ∂μ) +
      ∑ i ∈ Finset.range j, ((∫ ω, U1 i ω ∂μ) - ∫ ω, U0 i ω ∂μ) := by
  have hbase : Integrable (fun ω => ∑ i ∈ Finset.range n, U0 i ω) μ :=
    integrable_finsetSum _ (fun i hi => hU0 i (Finset.mem_range.mp hi))
  have hswitch : ∀ i ∈ Finset.range j, Integrable (fun ω => U1 i ω - U0 i ω) μ := by
    intro i hi
    exact (hU1 i (lt_of_lt_of_le (Finset.mem_range.mp hi) hj)).sub
      (hU0 i (lt_of_lt_of_le (Finset.mem_range.mp hi) hj))
  unfold randomValue value
  rw [integral_add hbase (integrable_finsetSum _ hswitch),
    integral_finsetSum _ (fun i hi => hU0 i (Finset.mem_range.mp hi)),
    integral_finsetSum _ hswitch]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  exact integral_sub (hU1 i (lt_of_lt_of_le (Finset.mem_range.mp hi) hj))
    (hU0 i (lt_of_lt_of_le (Finset.mem_range.mp hi) hj))

/-- Centering every group residual centers the common residual at every
valid count. No independence assumption is used in this finite-sum fact. -/
theorem integral_randomValue_eq_zero (μ : Measure Ω) (U0 U1 : ℕ → Ω → ℝ)
    (n j : ℕ) (hj : j ≤ n)
    (hU0 : ∀ i : ℕ, i < n → Integrable (U0 i) μ)
    (hU1 : ∀ i : ℕ, i < n → Integrable (U1 i) μ)
    (hcenter0 : ∀ i : ℕ, i < n → ∫ ω, U0 i ω ∂μ = 0)
    (hcenter1 : ∀ i : ℕ, i < n → ∫ ω, U1 i ω ∂μ = 0) :
    ∫ ω, randomValue U0 U1 n j ω ∂μ = 0 := by
  rw [integral_randomValue μ U0 U1 n j hj hU0 hU1]
  have hbase : (∑ i ∈ Finset.range n, ∫ ω, U0 i ω ∂μ) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    exact hcenter0 i (Finset.mem_range.mp hi)
  have hswitch : (∑ i ∈ Finset.range j,
      ((∫ ω, U1 i ω ∂μ) - ∫ ω, U0 i ω ∂μ)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hindex := lt_of_lt_of_le (Finset.mem_range.mp hi) hj
    rw [hcenter1 i hindex, hcenter0 i hindex, sub_self]
  rw [hbase, hswitch, zero_add]

/-- The stop-loss bound for the constructed residual family itself.
Here the required coupling, CDF measurability, integrability and centering
are all supplied by the group hypotheses, rather than assumed for `W`.
Identifying this mixture with a Bernoulli conditional distribution is a
separate statement and is not asserted by this theorem. -/
theorem constructedResidualCDF_le_stopLoss (μ : Measure Ω) [IsProbabilityMeasure μ]
    (π : ℕ → ℝ) (U0 U1 : ℕ → Ω → ℝ) (n k N : ℕ) (a0 a1 Δ η t : ℝ)
    (hkn : k + N ≤ n) (hπ : ∀ j, 0 ≤ π j) (hd : 0 ≤ 1 - Δ) (hη : 0 < η)
    (hU0m : ∀ i : ℕ, i < n → Measurable (U0 i))
    (hU1m : ∀ i : ℕ, i < n → Measurable (U1 i))
    (hU0i : ∀ i : ℕ, i < n → Integrable (U0 i) μ)
    (hU1i : ∀ i : ℕ, i < n → Integrable (U1 i) μ)
    (hcenter0 : ∀ i : ℕ, i < n → ∫ ω, U0 i ω ∂μ = 0)
    (hcenter1 : ∀ i : ℕ, i < n → ∫ ω, U1 i ω ∂μ = 0)
    (hU0s : ∀ᵐ ω ∂μ, ∀ i : ℕ, i < n → U0 i ω ≤ a0)
    (hU1s : ∀ᵐ ω ∂μ, ∀ i : ℕ, i < n → -a1 ≤ U1 i ω)
    (hcap : a0 + a1 ≤ Δ)
    (hprefix : ∀ r : ℕ, 1 ≤ r → r ≤ N →
      Staircase.prefixMass (fun j => π (k + j)) r ≤ η * ((r : ℝ) * (1 - Δ))) :
    Staircase.closedMixtureCDF μ π (randomValue U0 U1 n) (k + N) ((k : ℝ) + t) ≤
      Staircase.lowerMass π k + η * (t +
        ∫ ω, max (randomValue U0 U1 n k ω - t - π k / η) 0 ∂μ) := by
  have hkn' : k ≤ n := (Nat.le_add_right k N).trans hkn
  refine Staircase.coupledMixtureCDF_le_stopLoss μ π (randomValue U0 U1 n)
    k N Δ η t hπ hd hη ?_ ?_ ?_ ?_ hprefix
  · intro j hj
    exact measurableSet_le
      (measurable_const.add (measurable_randomValue U0 U1 n j (hj.trans hkn) hU0m hU1m))
      measurable_const
  · exact integrable_randomValue μ U0 U1 n k hkn' hU0i hU1i
  · exact integral_randomValue_eq_zero μ U0 U1 n k hkn' hU0i hU1i hcenter0 hcenter1
  · exact ae_support_implies_staircaseCoupling μ U0 U1 n k N a0 a1 Δ hkn hU0s hU1s hcap

end

end BerryEsseen.CoupledResidual

#print axioms BerryEsseen.CoupledResidual.support_implies_coupling
#print axioms BerryEsseen.CoupledResidual.ae_support_implies_staircaseCoupling
#print axioms BerryEsseen.CoupledResidual.integral_randomValue_eq_zero
#print axioms BerryEsseen.CoupledResidual.constructedResidualCDF_le_stopLoss
