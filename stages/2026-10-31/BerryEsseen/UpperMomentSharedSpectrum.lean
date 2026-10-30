module

public import BerryEsseen.UpperMomentN47ScalarSemantics
public import BerryEsseen.FixedPointUpperMomentExp

@[expose] public section

/-! 2026-10-30: reuse the already checked fixed-U spectrum at arbitrary
real s. Only the new exponential gates depend on s; the spectral and W
majorants are read from the checked scalar tables. New candidates use
the existing 10^40 fixed-point scale, while lift18 imports old table points. -/

namespace BerryEsseen.UpperMomentSharedSpectrum

open Set
open FixedPointEnclosure FixedPointArithmetic FixedPointUpperMomentRate
open FixedPointUpperMomentCoarseW FixedPointUpperMomentExp
open FixedFourierConstants (scale)
open UpperMomentN47ScalarChecks (ub lift18 firstLeft firstRight)
open UpperMomentN47ScalarSemantics
  (U d v1 v2 firstRow secondRow U_pos v1_nonneg contains_U
    contains_firstLeft contains_firstRight firstRow_mem firstRow_index)

noncomputable section

/-- Exact conversion from the frozen 10^18 table points to the 10^40 scale. -/
theorem val_lift18 (z : ℤ) : val (lift18 z) = (z : ℝ) / 10 ^ 18 :=
  UpperMomentN47ScalarSemantics.val_lift18 z

/-- The actual right-endpoint forcing primitive is nonnegative. -/
theorem actual_Wright_nonneg (j : ℕ) :
    0 ≤ UpperMomentSpectrumPrice.W U (v1 (j + 1)) :=
  UpperMomentSpectrumPrice.W_nonneg U _ U_pos (v1_nonneg _)

/-- The old coarse W gate licenses the actual right endpoint independently of s. -/
theorem actual_Wright_le (j : ℕ) (hj : j < 1024) :
    UpperMomentSpectrumPrice.W U (v1 (j + 1)) ≤ val (lift18 (firstRow j).W) := by
  have hc := UpperMomentN47ScalarChecks.first_W_checked (firstRow_mem j hj)
  rw [firstRow_index j hj] at hc
  exact coarseWCheck_sound contains_U (contains_firstRight j) hc

/-- Nonnegativity is inherited from the actual W, not assumed of a free bound. -/
theorem W_candidate_nonneg (j : ℕ) (hj : j < 1024) :
    0 ≤ val (lift18 (firstRow j).W) :=
  (actual_Wright_nonneg j).trans (actual_Wright_le j hj)

/-- The frozen right-endpoint candidate bounds W on the whole closed cell. -/
theorem actual_W_cell_le (j : ℕ) (hj : j < 1024) {v : ℝ}
    (hv : v ∈ Icc (v1 j) (v1 (j + 1))) :
    UpperMomentSpectrumPrice.W U v ≤ val (lift18 (firstRow j).W) :=
  (W_mono U v (v1 (j + 1)) U_pos ((v1_nonneg j).trans hv.1) hv.2).trans
    (actual_Wright_le j hj)

/-- A new forcing gate at any s reuses the checked G and W bounds directly. -/
theorem actual_forcing_cell_le (j : ℕ) (hj : j < 1024)
    {sBox : Box} {s v : ℝ} {P H : ℤ}
    (hs : Contains scale sBox s)
    (hv : v ∈ Icc (v1 j) (v1 (j + 1)))
    (hc : forcingCheck ub sBox (lift18 (firstRow j).G)
      (lift18 (firstRow j).W) P H = true) :
    s * Real.exp ((s - d) * UpperMomentDamping.G U U v) *
      UpperMomentSpectrumPrice.W U v ≤ val H := by
  have hG : UpperMomentDamping.G U U v ≤ val (lift18 (firstRow j).G) := by
    simpa only [val_lift18, UpperMomentN47ScalarSemantics.G1] using
      UpperMomentN47ScalarSemantics.actual_G1_cell_le j hj hv
  simpa only [UpperMomentN47ScalarSemantics.d_eq] using
    forcingCheck_sound contains_U hs ((v1_nonneg j).trans hv.1) hG
      (actual_W_cell_le j hj hv) hc

/-- The T2 power gate reuses the same checked spectrum on its closed cell. -/
theorem actual_power_cell_le (j : ℕ) (hj : j < 1024)
    {sBox : Box} {s v : ℝ} {Q : ℤ}
    (hs : Contains scale sBox s)
    (hv : v ∈ Icc (v2 j) (v2 (j + 1)))
    (hc : powerCheck sBox (lift18 (secondRow j).G) Q = true) :
    Real.exp (s * UpperMomentDamping.G U U v) ≤ val Q := by
  have hG : UpperMomentDamping.G U U v ≤ val (lift18 (secondRow j).G) := by
    simpa only [val_lift18, UpperMomentN47ScalarSemantics.G2] using
      UpperMomentN47ScalarSemantics.actual_G2_cell_le j hj hv
  exact powerCheck_sound hs hG hc

/-- New Gaussian transport depends only on s and the unchanged cell endpoints. -/
theorem actual_decay_le (j : ℕ) {sBox : Box} {s : ℝ} {D : ℤ}
    (hs : Contains scale sBox s)
    (hc : decayCheck sBox (firstLeft j) (firstRight j) D = true) :
    Real.exp (-s * (v1 (j + 1) ^ 2 - v1 j ^ 2) / 2) ≤ val D :=
  decayCheck_sound hs (contains_firstLeft j) (contains_firstRight j) hc

end

end BerryEsseen.UpperMomentSharedSpectrum

#print axioms BerryEsseen.UpperMomentSharedSpectrum.actual_Wright_nonneg
#print axioms BerryEsseen.UpperMomentSharedSpectrum.actual_Wright_le
#print axioms BerryEsseen.UpperMomentSharedSpectrum.actual_forcing_cell_le
#print axioms BerryEsseen.UpperMomentSharedSpectrum.actual_power_cell_le
#print axioms BerryEsseen.UpperMomentSharedSpectrum.actual_decay_le
