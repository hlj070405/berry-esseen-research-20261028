module

public import BerryEsseen.ControlRecurrenceChecks
public import BerryEsseen.ControlForcingTables
public import BerryEsseen.CoefficientGridPrice

@[expose] public section

/-! 2026-10-29: all original R witnesses now bound the defining coarse
price. The forcing, decay and arithmetic recurrence premises are supplied
by actual full-table kernel proofs, rather than retained as numerical inputs. -/

noncomputable section

namespace BerryEsseen.ControlPriceGrid

open ControlEndpointParameters
open ControlRecurrenceChecks (R H D)
open CoefficientRayPrice

lemma start_grid_zero : firstGrid 0 = 0 := by simp [firstGrid]

lemma start_price_zero : coarsePrice 42 c beta (firstGrid 0) = 0 := by
  rw [start_grid_zero]
  simp only [coarsePrice, intervalIntegral.integral_same, mul_zero]

lemma start_R_zero : R 0 = 0 := by
  unfold R
  rw [ControlRecurrenceChecks.initial_r_zero]
  norm_num [ControlRecurrenceChecks.up, FixedPointEnclosure.qval]

theorem all_price_nodes (j : ℕ) (hj : j ≤ 1024) :
    coarsePrice 42 c beta (firstGrid j) ≤ R j := by
  apply CoefficientGridPrice.coarsePrice_grid_endpoints 42 (by decide) c beta beta_pos
    firstGrid H D R 1024 (by rw [start_grid_zero])
    (fun k _ => ControlForcingTables.firstGrid_adjacent_le k)
    (by rw [start_price_zero, start_R_zero])
    (fun k hk u hu => ControlForcingTables.actual_forcing_cell_le k hk hu)
    (fun k hk => ControlForcingTables.actual_decay_step_le k hk)
    (fun k hk => ControlRecurrenceChecks.actual_step_inequality k hk) j hj

theorem all_price_cells (j : ℕ) (hj : j < 1024) (u : ℝ)
    (hu : u ∈ Set.Icc (firstGrid j) (firstGrid (j + 1))) :
    coarsePrice 42 c beta u ≤ CoefficientGridPrice.cellPriceUpper firstGrid H R j := by
  exact CoefficientGridPrice.coarsePrice_grid_inner 42 (by decide) c beta beta_pos
    firstGrid H R 1024 (by rw [start_grid_zero])
    (fun k _ => ControlForcingTables.firstGrid_adjacent_le k)
    all_price_nodes (fun k hk v hv => ControlForcingTables.actual_forcing_cell_le k hk hv)
    j hj u hu

end BerryEsseen.ControlPriceGrid

#print axioms BerryEsseen.ControlPriceGrid.all_price_nodes
#print axioms BerryEsseen.ControlPriceGrid.all_price_cells
