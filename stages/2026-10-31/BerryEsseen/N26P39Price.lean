module

public import BerryEsseen.RationalReferencePrice

@[expose] public section

/-! 2026-10-29: One literal old N26/B0/P39 corner.
Source: result_b0_n26_p39_complete_merged_fresh_20261027.json,
pieces[0].data.boxes[0], count 11, first noise/allocation band, p=2/5,t=0.
conservative_box uses b0=a0 for group 0 and cfg.outer1 for group 1.
The fixed width was selected by probe_n26_p39_rational_corner_20261029.py;
no optimizer, stationarity, or active-face hypothesis enters these theorems. -/

namespace BerryEsseen.N26P39Price

open MeasureTheory RationalReferencePrice

set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

def b0 : ℚ := 28411442497 / 500000000000
def z0 : ℚ := 615144231 / 250000000000
def b1 : ℚ := 119001 / 200000
def z1 : ℚ := 47318787 / 50000000000
def inward : ℚ := 5769 / 100000
def pUpper : ℚ := 2 / 5
def slopeMultiplier : ℚ := 3 / 2
def CA : ℚ := (1 - inward) * (12 / 15) / slopeMultiplier
def threshold : ℚ := CA * (1 - pUpper) / pUpper
def width : ℚ := 13669219 / 100000000
def upper : ℚ := 240777899 / 250000000000

noncomputable def reference : Measure ℝ :=
  DoubleBinomialReference.law (b0 : ℝ) (z0 : ℝ) 15 (b1 : ℝ) (z1 : ℝ) 11

theorem threshold_eq : threshold = 94231 / 125000 := by decide +kernel
theorem threshold_pos : 0 < threshold := by decide +kernel
theorem width_pos : 0 < width := by decide +kernel

/-- Exact closed rational computation of all 16 by 12 atoms at this fixed width. -/
theorem rational_price_upper : rationalPrice b0 z0 15 b1 z1 11 threshold width ≤ upper := by
  decide +kernel

theorem actual_price_eq : StopLossShape.price reference (threshold : ℝ) (width : ℝ) =
    (rationalPrice b0 z0 15 b1 z1 11 threshold width : ℝ) :=
  RationalReferencePrice.price_eq_cast b0 z0 15 b1 z1 11 threshold width
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem actual_price_upper : StopLossShape.price reference (threshold : ℝ) (width : ℝ) ≤
    (upper : ℝ) := by
  rw [actual_price_eq]
  exact Rat.cast_le.mpr rational_price_upper

/-- The actual reference-law infimum is bounded by one legal rational width. -/
theorem actual_Q_upper : StopLossShape.Q reference (threshold : ℝ) ≤ (upper : ℝ) :=
  RationalReferencePrice.Q_le_of_rational_bound b0 z0 15 b1 z1 11 threshold width upper
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    width_pos rational_price_upper

end BerryEsseen.N26P39Price

#print axioms BerryEsseen.N26P39Price.threshold_eq
#print axioms BerryEsseen.N26P39Price.rational_price_upper
#print axioms BerryEsseen.N26P39Price.actual_price_eq
#print axioms BerryEsseen.N26P39Price.actual_price_upper
#print axioms BerryEsseen.N26P39Price.actual_Q_upper
