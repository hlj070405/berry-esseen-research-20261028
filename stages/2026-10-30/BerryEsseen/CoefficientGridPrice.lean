module

public import BerryEsseen.CoefficientQuadrature

@[expose] public section

/-! 2026-10-29: finite meshes of the actual coefficient-ray coarse price.
Numerical arrays are connected to the defining price by true forcing and
decay gates. The first Prawitz integral uses genuine integrability, an
analytic first cell, and open-cell kernel bounds on all remaining cells.
No characteristic-function-error bound is substituted for the price. -/

noncomputable section

open MeasureTheory Set
open scoped Interval BigOperators

namespace BerryEsseen.CoefficientGridPrice

open CoefficientRayPrice CoefficientPriceCells CoefficientQuadrature
open Causalean.Stat.CLT.BerryEsseen (prawitzKernel)

def cellWidth (t : ℕ → ℝ) (j : ℕ) : ℝ := t (j + 1) - t j

def cellPriceUpper (t H R : ℕ → ℝ) (j : ℕ) : ℝ := R j + cellWidth t j * H j

private lemma grid_le (t : ℕ → ℝ) (m : ℕ)
    (horder : ∀ j < m, t j ≤ t (j + 1))
    (i j : ℕ) (hij : i ≤ j) (hjm : j ≤ m) : t i ≤ t j := by
  revert hjm
  induction j, hij using Nat.le_induction with
  | base => intro _; exact le_rfl
  | succ j hij ih =>
      intro hjm
      exact (ih (by omega)).trans (horder j (by omega))

private lemma grid_nonneg (t : ℕ → ℝ) (m : ℕ) (h0 : 0 ≤ t 0)
    (horder : ∀ j < m, t j ≤ t (j + 1)) (j : ℕ) (hj : j ≤ m) : 0 ≤ t j :=
  h0.trans (grid_le t m horder 0 j (Nat.zero_le j) hj)

/-- The entire endpoint recurrence concerns the defining coarse price P.
In particular, R_j is nonnegative because P(t_j) is, so rounding the decay
factor upwards is justified rather than silently assumed monotone. -/
theorem coarsePrice_grid_endpoints (N : ℕ) (hN : 0 < N) (c β : ℝ) (hβ : 0 < β)
    (t H D R : ℕ → ℝ) (m : ℕ) (h0 : 0 ≤ t 0)
    (horder : ∀ j < m, t j ≤ t (j + 1))
    (hstart : coarsePrice N c β (t 0) ≤ R 0)
    (hforcing : ∀ j < m, ∀ u ∈ Icc (t j) (t (j + 1)),
      lossEnvelope N c β u *
        (u ^ 2 / 2 + CoarseHighMomentRayPrice.lambda N β * u ^ 3 / 3) ≤ H j)
    (hdecay : ∀ j < m, Real.exp (-((t (j + 1) ^ 2 - t j ^ 2) / 2)) ≤ D j)
    (hstep : ∀ j < m, D j * R j + cellWidth t j * H j ≤ R (j + 1)) :
    ∀ j ≤ m, coarsePrice N c β (t j) ≤ R j := by
  intro j
  induction j with
  | zero => intro _; exact hstart
  | succ j ih =>
      intro hjm
      have hj : j < m := by omega
      have hp := ih (by omega : j ≤ m)
      have ht0 := grid_nonneg t m h0 horder j (by omega)
      have hR0 : 0 ≤ R j := (coarsePrice_nonneg N hN c β (t j) hβ ht0).trans hp
      have hc := coarsePrice_cell_step_of_le N hN c β (t j) (t (j + 1)) (H j) (R j)
        hβ ht0 (horder j hj) (hforcing j hj) hp
      have hd := mul_le_mul_of_nonneg_right (hdecay j hj) hR0
      have hs := hstep j hj
      dsimp [cellWidth] at hs
      linarith only [hc, hd, hs]

/-- Once the genuine endpoint induction is available, each complete cell
has the stated price bound. No sampled interior information is used. -/
theorem coarsePrice_grid_inner (N : ℕ) (hN : 0 < N) (c β : ℝ) (hβ : 0 < β)
    (t H R : ℕ → ℝ) (m : ℕ) (h0 : 0 ≤ t 0)
    (horder : ∀ j < m, t j ≤ t (j + 1))
    (hnodes : ∀ j ≤ m, coarsePrice N c β (t j) ≤ R j)
    (hforcing : ∀ j < m, ∀ u ∈ Icc (t j) (t (j + 1)),
      lossEnvelope N c β u *
        (u ^ 2 / 2 + CoarseHighMomentRayPrice.lambda N β * u ^ 3 / 3) ≤ H j) :
    ∀ j < m, ∀ u ∈ Icc (t j) (t (j + 1)), coarsePrice N c β u ≤ cellPriceUpper t H R j := by
  intro j hj u hu
  exact coarsePrice_cell_inner_of_le N hN c β (t j) (t (j + 1)) (H j) (R j)
    hβ (grid_nonneg t m h0 horder j (by omega)) (horder j hj)
      (hforcing j hj) (hnodes j (by omega)) u hu

/-- A certified finite mesh controls both every node and every whole cell.
All numerical-array hypotheses remain actual analytic gates. -/
theorem coarsePrice_grid_bounds (N : ℕ) (hN : 0 < N) (c β : ℝ) (hβ : 0 < β)
    (t H D R : ℕ → ℝ) (m : ℕ) (h0 : 0 ≤ t 0)
    (horder : ∀ j < m, t j ≤ t (j + 1))
    (hstart : coarsePrice N c β (t 0) ≤ R 0)
    (hforcing : ∀ j < m, ∀ u ∈ Icc (t j) (t (j + 1)),
      lossEnvelope N c β u *
        (u ^ 2 / 2 + CoarseHighMomentRayPrice.lambda N β * u ^ 3 / 3) ≤ H j)
    (hdecay : ∀ j < m, Real.exp (-((t (j + 1) ^ 2 - t j ^ 2) / 2)) ≤ D j)
    (hstep : ∀ j < m, D j * R j + cellWidth t j * H j ≤ R (j + 1)) :
    (∀ j ≤ m, coarsePrice N c β (t j) ≤ R j) ∧
      (∀ j < m, ∀ u ∈ Icc (t j) (t (j + 1)), coarsePrice N c β u ≤ cellPriceUpper t H R j) := by
  have hn := coarsePrice_grid_endpoints N hN c β hβ t H D R m h0 horder hstart
    hforcing hdecay hstep
  exact ⟨hn, coarsePrice_grid_inner N hN c β hβ t H R m h0 horder hn hforcing⟩

/-- The actual first Prawitz integral is bounded by its analytic first
cell plus the regular finite cell sum. The singular endpoint is made
integrable analytically before partitioning the integral. -/
theorem first_integral_le_grid (N : ℕ) (hN : 0 < N) (c β U : ℝ) (hβ : 0 < β)
    (t H D R K : ℕ → ℝ) (m : ℕ) (hm : 0 < m) (ht0 : t 0 = 0)
    (hfirst : 0 < t 1) (hend : t m ≤ U)
    (horder : ∀ j < m, t j ≤ t (j + 1))
    (hstart : coarsePrice N c β (t 0) ≤ R 0)
    (hforcing : ∀ j < m, ∀ u ∈ Icc (t j) (t (j + 1)),
      lossEnvelope N c β u *
        (u ^ 2 / 2 + CoarseHighMomentRayPrice.lambda N β * u ^ 3 / 3) ≤ H j)
    (hdecay : ∀ j < m, Real.exp (-((t (j + 1) ^ 2 - t j ^ 2) / 2)) ≤ D j)
    (hstep : ∀ j < m, D j * R j + cellWidth t j * H j ≤ R (j + 1))
    (hK0 : ∀ j < m, 1 ≤ j → 0 ≤ K j)
    (hK : ∀ j < m, 1 ≤ j → ∀ u ∈ Ioo (t j) (t (j + 1)),
      ‖prawitzKernel (u / U)‖ ≤ K j) :
    (2 / U) * (∫ u in (0 : ℝ)..t m, ‖prawitzKernel (u / U)‖ * coarsePrice N c β u) ≤
      (t 1) ^ 4 / (24 * U) + CoarseHighMomentRayPrice.lambda N β * (t 1) ^ 5 / (60 * U) +
        (t 1) ^ 3 / (18 * Real.pi) + CoarseHighMomentRayPrice.lambda N β * (t 1) ^ 4 / (48 * Real.pi) +
      (2 / U) * ∑ j ∈ Finset.range (m - 1),
        cellWidth t (j + 1) * (K (j + 1) * cellPriceUpper t H R (j + 1)) := by
  have h0 : 0 ≤ t 0 := by rw [ht0]
  have h1m : t 1 ≤ t m := grid_le t m horder 1 m (by omega) le_rfl
  have hend0 : 0 < t m := hfirst.trans_le h1m
  have hU : 0 < U := hend0.trans_le hend
  let f : ℝ → ℝ := fun u => ‖prawitzKernel (u / U)‖ * coarsePrice N c β u
  have hfull : IntervalIntegrable f volume 0 (t m) :=
    first_integrand_intervalIntegrable N hN c β (t m) U hβ hend0 hend
  have hnodes := coarsePrice_grid_endpoints N hN c β hβ t H D R m h0 horder hstart
    hforcing hdecay hstep
  have hcells := coarsePrice_grid_inner N hN c β hβ t H R m h0 horder hnodes hforcing
  have hcellI : ∀ j < m, IntervalIntegrable f volume (t j) (t (j + 1)) := by
    intro j hj
    apply hfull.mono_set
    rw [uIcc_of_le (horder j hj), uIcc_of_le hend0.le]
    exact Icc_subset_Icc (grid_nonneg t m h0 horder j (by omega))
      (grid_le t m horder (j + 1) m (by omega) le_rfl)
  have hregular := integral_le_cell_sum f (fun j => t (j + 1))
    (fun j => K (j + 1) * cellPriceUpper t H R (j + 1)) (m - 1)
    (fun j hj => horder (j + 1) (by omega))
    (fun j hj => hcellI (j + 1) (by omega)) (fun j hj u hu => by
      have hjm : j + 1 < m := by omega
      have hp := hcells (j + 1) hjm u ⟨hu.1.le, hu.2.le⟩
      have hpu : 0 ≤ coarsePrice N c β u := coarsePrice_nonneg N hN c β u hβ
        ((grid_nonneg t m h0 horder (j + 1) (by omega)).trans hu.1.le)
      exact mul_le_mul (hK (j + 1) hjm (by omega) u hu) hp hpu
        (hK0 (j + 1) hjm (by omega)))
  have hm1 : m - 1 + 1 = m := by omega
  change (∫ u in t (0 + 1)..t (m - 1 + 1), f u) ≤
    ∑ j ∈ Finset.range (m - 1), (t (j + 1 + 1) - t (j + 1)) *
      (K (j + 1) * cellPriceUpper t H R (j + 1)) at hregular
  rw [hm1] at hregular
  change (∫ u in t 1..t m, f u) ≤ ∑ j ∈ Finset.range (m - 1),
    cellWidth t (j + 1) * (K (j + 1) * cellPriceUpper t H R (j + 1)) at hregular
  have hfirstI : IntervalIntegrable f volume 0 (t 1) := by
    apply hfull.mono_set
    rw [uIcc_of_le hfirst.le, uIcc_of_le hend0.le]
    exact Icc_subset_Icc le_rfl h1m
  have hregularI : IntervalIntegrable f volume (t 1) (t m) := by
    apply hfull.mono_set
    rw [uIcc_of_le h1m, uIcc_of_le hend0.le]
    exact Icc_subset_Icc hfirst.le le_rfl
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hfirstI hregularI
  have hfirstPrice := first_cell_le N hN c β (t 1) U hβ hfirst (h1m.trans hend)
  have hscaled := mul_le_mul_of_nonneg_left hregular (by positivity : 0 ≤ 2 / U)
  change (2 / U) * (∫ u in (0 : ℝ)..t m, f u) ≤ _
  rw [← hsplit, mul_add]
  change (2 / U) * (∫ u in (0 : ℝ)..t 1, f u) ≤ _ at hfirstPrice
  linarith only [hfirstPrice, hscaled]

end BerryEsseen.CoefficientGridPrice

#print axioms BerryEsseen.CoefficientGridPrice.coarsePrice_grid_endpoints
#print axioms BerryEsseen.CoefficientGridPrice.coarsePrice_grid_inner
#print axioms BerryEsseen.CoefficientGridPrice.coarsePrice_grid_bounds
#print axioms BerryEsseen.CoefficientGridPrice.first_integral_le_grid
