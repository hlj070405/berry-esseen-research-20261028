module

public import BerryEsseen.UpperMomentFirstRows

@[expose] public section

/-! 2026-10-30: finite-grid induction for the defining global spectral
comparison R. Witness nonnegativity is derived from the real price at
every node before increasing the decay factor. Integral rows are joined
only when their actual cell integrability has been supplied. -/

noncomputable section

open MeasureTheory Set
open scoped Interval BigOperators

namespace BerryEsseen.UpperMomentGridPrice

open UpperMomentSpectralCells (R forcing)

def cellWidth (t : ℕ → ℝ) (j : ℕ) : ℝ := t (j + 1) - t j

def cellPriceUpper (t H r : ℕ → ℝ) (j : ℕ) : ℝ := r j + cellWidth t j * H j

lemma grid_le (t : ℕ → ℝ) (m : ℕ) (horder : ∀ j < m, t j ≤ t (j + 1))
    (i j : ℕ) (hij : i ≤ j) (hjm : j ≤ m) : t i ≤ t j := by
  revert hjm
  induction j, hij using Nat.le_induction with
  | base => intro _; exact le_rfl
  | succ j hij ih =>
      intro hjm
      exact (ih (by omega)).trans (horder j (by omega))

lemma grid_nonneg (t : ℕ → ℝ) (m : ℕ) (h0 : 0 ≤ t 0)
    (horder : ∀ j < m, t j ≤ t (j + 1)) (j : ℕ) (hj : j ≤ m) : 0 ≤ t j :=
  h0.trans (grid_le t m horder 0 j (Nat.zero_le j) hj)

/-- The recurrence bounds the defining R at every node. Its witness is
nonnegative because the real price is, which licenses each decay gate. -/
theorem R_grid_endpoints (U : ℝ) (G : ℝ → ℝ) (hG : Continuous G) (s : ℝ)
    (hU : 0 < U) (hs : 0 < s) (t H D r : ℕ → ℝ) (m : ℕ) (h0 : 0 ≤ t 0)
    (horder : ∀ j < m, t j ≤ t (j + 1)) (hstart : R U G s (t 0) ≤ r 0)
    (hforcing : ∀ j < m, ∀ w ∈ Icc (t j) (t (j + 1)), forcing U G s w ≤ H j)
    (hdecay : ∀ j < m, Real.exp (-s * (t (j + 1) ^ 2 - t j ^ 2) / 2) ≤ D j)
    (hstep : ∀ j < m, D j * r j + cellWidth t j * H j ≤ r (j + 1)) :
    ∀ j ≤ m, R U G s (t j) ≤ r j := by
  intro j
  induction j with
  | zero => intro _; exact hstart
  | succ j ih =>
      intro hjm
      have hj : j < m := by omega
      have hp := ih (by omega : j ≤ m)
      have ht0 := grid_nonneg t m h0 horder j (by omega)
      have hr0 : 0 ≤ r j := (UpperMomentSpectralCells.R_nonneg U G s (t j) hU hs.le ht0).trans hp
      have hc := UpperMomentSpectralCells.R_cell_step_of_le U G hG s (t j) (t (j + 1)) (H j) (r j)
        hU hs ht0 (horder j hj) (hforcing j hj) hr0 hp
      have hd := mul_le_mul_of_nonneg_right (hdecay j hj) hr0
      have hnext := hstep j hj
      dsimp [cellWidth] at hnext
      linarith only [hc, hd, hnext]

theorem R_grid_witness_nonneg (U : ℝ) (G : ℝ → ℝ) (s : ℝ) (hU : 0 < U) (hs : 0 ≤ s)
    (t r : ℕ → ℝ) (m : ℕ) (h0 : 0 ≤ t 0) (horder : ∀ j < m, t j ≤ t (j + 1))
    (hnodes : ∀ j ≤ m, R U G s (t j) ≤ r j) : ∀ j ≤ m, 0 ≤ r j := by
  intro j hj
  exact (UpperMomentSpectralCells.R_nonneg U G s (t j) hU hs
    (grid_nonneg t m h0 horder j hj)).trans (hnodes j hj)

/-- The exact prefix width is retained throughout each closed cell. -/
theorem R_grid_inner_prefix (U : ℝ) (G : ℝ → ℝ) (hG : Continuous G) (s : ℝ)
    (hU : 0 < U) (hs : 0 < s) (t H r : ℕ → ℝ) (m : ℕ) (h0 : 0 ≤ t 0)
    (horder : ∀ j < m, t j ≤ t (j + 1)) (hnodes : ∀ j ≤ m, R U G s (t j) ≤ r j)
    (hforcing : ∀ j < m, ∀ w ∈ Icc (t j) (t (j + 1)), forcing U G s w ≤ H j) :
    ∀ j < m, ∀ v ∈ Icc (t j) (t (j + 1)), R U G s v ≤ r j + (v - t j) * H j := by
  intro j hj v hv
  have ht0 := grid_nonneg t m h0 horder j (by omega)
  have hr0 := R_grid_witness_nonneg U G s hU hs.le t r m h0 horder hnodes j (by omega)
  exact UpperMomentSpectralCells.R_cell_inner_of_le U G hG s (t j) (t (j + 1)) (H j) (r j)
    hU hs ht0 (horder j hj) (hforcing j hj) hr0 (hnodes j (by omega)) v hv

theorem R_grid_inner (U : ℝ) (G : ℝ → ℝ) (hG : Continuous G) (s : ℝ)
    (hU : 0 < U) (hs : 0 < s) (t H r : ℕ → ℝ) (m : ℕ) (h0 : 0 ≤ t 0)
    (horder : ∀ j < m, t j ≤ t (j + 1)) (hnodes : ∀ j ≤ m, R U G s (t j) ≤ r j)
    (hforcing : ∀ j < m, ∀ w ∈ Icc (t j) (t (j + 1)), forcing U G s w ≤ H j) :
    ∀ j < m, ∀ v ∈ Icc (t j) (t (j + 1)), R U G s v ≤ cellPriceUpper t H r j := by
  intro j hj v hv
  have hp := R_grid_inner_prefix U G hG s hU hs t H r m h0 horder hnodes hforcing j hj v hv
  have ht0 := grid_nonneg t m h0 horder j (by omega)
  have hH0 := UpperMomentSpectralCells.forcing_upper_nonneg U G s (t j) (t (j + 1)) (H j)
    hU hs.le ht0 (horder j hj) (hforcing j hj)
  have hw := mul_le_mul_of_nonneg_right (sub_le_sub_right hv.2 (t j)) hH0
  unfold cellPriceUpper cellWidth
  linarith only [hp, hw]

theorem R_grid_bounds (U : ℝ) (G : ℝ → ℝ) (hG : Continuous G) (s : ℝ)
    (hU : 0 < U) (hs : 0 < s) (t H D r : ℕ → ℝ) (m : ℕ) (h0 : 0 ≤ t 0)
    (horder : ∀ j < m, t j ≤ t (j + 1)) (hstart : R U G s (t 0) ≤ r 0)
    (hforcing : ∀ j < m, ∀ w ∈ Icc (t j) (t (j + 1)), forcing U G s w ≤ H j)
    (hdecay : ∀ j < m, Real.exp (-s * (t (j + 1) ^ 2 - t j ^ 2) / 2) ≤ D j)
    (hstep : ∀ j < m, D j * r j + cellWidth t j * H j ≤ r (j + 1)) :
    (∀ j ≤ m, R U G s (t j) ≤ r j) ∧
      (∀ j < m, ∀ v ∈ Icc (t j) (t (j + 1)), R U G s v ≤ cellPriceUpper t H r j) := by
  have hn := R_grid_endpoints U G hG s hU hs t H D r m h0 horder hstart hforcing hdecay hstep
  exact ⟨hn, R_grid_inner U G hG s hU hs t H r m h0 horder hn hforcing⟩

/-- A finite sum of licensed integral rows, for the unchanged volume
integral and exact grid endpoints. Actual integrability is an input. -/
theorem integral_le_rows (f : ℝ → ℝ) (t row : ℕ → ℝ) (m : ℕ)
    (hI : ∀ j < m, IntervalIntegrable f volume (t j) (t (j + 1)))
    (hrow : ∀ j < m, (∫ v in t j..t (j + 1), f v) ≤ row j) :
    (∫ v in t 0..t m, f v) ≤ ∑ j ∈ Finset.range m, row j := by
  rw [← intervalIntegral.sum_integral_adjacent_intervals hI]
  apply Finset.sum_le_sum
  intro j hj
  exact hrow j (Finset.mem_range.mp hj)

/-- The analytic head row and the remaining regular rows may be licensed
separately. The m=0 case is exactly the single head interval. -/
theorem integral_le_head_rows (f : ℝ → ℝ) (t row : ℕ → ℝ) (m : ℕ) (head : ℝ)
    (hI : ∀ j < m + 1, IntervalIntegrable f volume (t j) (t (j + 1)))
    (hhead : (∫ v in t 0..t 1, f v) ≤ head)
    (hrow : ∀ j < m, (∫ v in t (j + 1)..t (j + 1 + 1), f v) ≤ row j) :
    (∫ v in t 0..t (m + 1), f v) ≤ head + ∑ j ∈ Finset.range m, row j := by
  rw [← intervalIntegral.sum_integral_adjacent_intervals hI, Finset.sum_range_succ']
  have ht : (∑ j ∈ Finset.range m, ∫ v in t (j + 1)..t (j + 1 + 1), f v) ≤
      ∑ j ∈ Finset.range m, row j := by
    apply Finset.sum_le_sum
    intro j hj
    exact hrow j (Finset.mem_range.mp hj)
  simpa only [Nat.zero_add, add_comm] using add_le_add ht hhead

end BerryEsseen.UpperMomentGridPrice

#print axioms BerryEsseen.UpperMomentGridPrice.R_grid_endpoints
#print axioms BerryEsseen.UpperMomentGridPrice.R_grid_witness_nonneg
#print axioms BerryEsseen.UpperMomentGridPrice.R_grid_inner_prefix
#print axioms BerryEsseen.UpperMomentGridPrice.R_grid_inner
#print axioms BerryEsseen.UpperMomentGridPrice.R_grid_bounds
#print axioms BerryEsseen.UpperMomentGridPrice.integral_le_rows
#print axioms BerryEsseen.UpperMomentGridPrice.integral_le_head_rows
