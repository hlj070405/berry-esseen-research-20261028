module

public import BerryEsseen.ContactMajorant
public import BerryEsseen.SupportContact

@[expose] public section

/-! 2026-10-28: the initial support theorem for an actual global maximizing law.
The unrestricted predecessor implication supplies the displayed law-level bound;
existence of the maximizer is proved separately rather than assumed universally.
-/

noncomputable section

open MeasureTheory Set

namespace BerryEsseen.InitialSupport

open ContactVariation ContactMajorant SupportRays

/-- The low-moment support radius for the original maximizing distribution. -/
theorem low_moment_support (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (hn : 25 ≤ n) (H C : ℝ) (hm : PositiveClosedMaximum μ n H C)
    (hprev : PredecessorBound μ n C) (hC : esseenConstant ≤ C)
    (hR : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) :
    (μ : Measure ℝ).support ⊆ Ioo (-(12 / 5 : ℝ)) (12 / 5) := by
  intro x hxs
  change -(12 / 5 : ℝ) < x ∧ x < 12 / 5
  apply abs_lt.mp
  by_contra hnot
  have hr : (12 : ℝ) / 5 ≤ |x| := le_of_not_gt hnot
  have hnR : (25 : ℝ) ≤ n := by exact_mod_cast hn
  have hneg := low_moment_ray_neg μ h n H C x hnR hC hR hr
  have hmajor := sqrt_mul_D_le μ n hn H C hm hprev x
  rw [SupportContact.D_eq_zero_on_support μ h n (by omega) H C hm x hxs, mul_zero] at hmajor
  linarith

/-- The intermediate-moment support radius, with the same full predecessor condition. -/
theorem mid_moment_support (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (hn : 25 ≤ n) (H C : ℝ) (hm : PositiveClosedMaximum μ n H C)
    (hprev : PredecessorBound μ n C) (hC : esseenConstant ≤ C)
    (hR : thirdAbsoluteMoment μ ≤ (6 : ℝ) / 5) :
    (μ : Measure ℝ).support ⊆ Ioo (-(13 / 5 : ℝ)) (13 / 5) := by
  intro x hxs
  change -(13 / 5 : ℝ) < x ∧ x < 13 / 5
  apply abs_lt.mp
  by_contra hnot
  have hr : (13 : ℝ) / 5 ≤ |x| := le_of_not_gt hnot
  have hnR : (25 : ℝ) ≤ n := by exact_mod_cast hn
  have hneg := mid_moment_ray_neg μ h n H C x hnR hC hR hr
  have hmajor := sqrt_mul_D_le μ n hn H C hm hprev x
  rw [SupportContact.D_eq_zero_on_support μ h n (by omega) H C hm x hxs, mul_zero] at hmajor
  linarith

end BerryEsseen.InitialSupport

#print axioms BerryEsseen.InitialSupport.low_moment_support
#print axioms BerryEsseen.InitialSupport.mid_moment_support
