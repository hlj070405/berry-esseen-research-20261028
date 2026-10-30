module

public import BerryEsseen.ContactVariation
public import BerryEsseen.SupportRays

@[expose] public section

/-! 2026-10-28: the Gaussian predecessor bound applied to the actual
contact expression. Attainment and the actual previous-index law are retained.
-/

noncomputable section

open MeasureTheory Set

namespace BerryEsseen.ContactMajorant

open GaussianTools GaussianContactApplication ContactVariation SupportRays AnalyticConstants

/-- The predecessor estimate for this same original marginal, in raw sum coordinates. -/
def PredecessorBound (μ : ProbabilityMeasure ℝ) (n : ℕ) (C : ℝ) : Prop :=
  ∀ t : ℝ, (MixtureSum.iidSumLaw (μ : Measure ℝ) (n - 1)).real (Iic t) ≤
    Phi (t / Real.sqrt (n - 1 : ℕ)) + C * thirdAbsoluteMoment μ / Real.sqrt (n - 1 : ℕ)

theorem sqrt_mul_D_le (μ : ProbabilityMeasure ℝ) (n : ℕ) (hn : 25 ≤ n)
    (H C : ℝ) (hm : PositiveClosedMaximum μ n H C)
    (hprev : PredecessorBound μ n C) (x : ℝ) :
    Real.sqrt n * D μ n H C x ≤
      hermiteProjection (n : ℝ) H x + C * actualCost μ (n : ℝ) x := by
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hn1 : 0 < (n : ℝ) - 1 := by
    have hnR : (25 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
  have hv : 0 < Real.sqrt ((n : ℝ) - 1) := Real.sqrt_pos.mpr hn1
  have hFn : (MixtureSum.iidSumLaw (μ : Measure ℝ) n).real (Iic H) =
      Phi (H / Real.sqrt n) + C * thirdAbsoluteMoment μ / Real.sqrt n := by
    linarith [hm.attainment]
  have hpx := hprev (H - x)
  rw [hcast] at hpx
  have herror : (MixtureSum.iidSumLaw (μ : Measure ℝ) (n - 1)).real (Iic (H - x)) -
      Phi ((H - x) / Real.sqrt ((n : ℝ) - 1)) -
      C * thirdAbsoluteMoment μ / Real.sqrt ((n : ℝ) - 1) ≤ 0 := by linarith
  have hmul := mul_nonpos_of_nonneg_of_nonpos
    (mul_nonneg (Nat.cast_nonneg n) (Real.sqrt_nonneg (n : ℝ))) herror
  have heq : Real.sqrt n * D μ n H C x -
      (hermiteProjection (n : ℝ) H x + C * actualCost μ (n : ℝ) x) =
      (n : ℝ) * Real.sqrt n *
        ((MixtureSum.iidSumLaw (μ : Measure ℝ) (n - 1)).real (Iic (H - x)) -
          Phi ((H - x) / Real.sqrt ((n : ℝ) - 1)) -
          C * thirdAbsoluteMoment μ / Real.sqrt ((n : ℝ) - 1)) := by
    unfold D momentSlope hermiteProjection actualCost scaleExcess
    rw [hFn, Real.sqrt_div hn0.le]
    field_simp [hs.ne', hv.ne']
    rw [Real.sq_sqrt hn0.le]
    ring
  rw [← heq] at hmul
  linarith

end BerryEsseen.ContactMajorant

#print axioms BerryEsseen.ContactMajorant.sqrt_mul_D_le
