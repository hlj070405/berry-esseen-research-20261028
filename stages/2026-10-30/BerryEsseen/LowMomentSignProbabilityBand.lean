module

public import BerryEsseen.PhysicalSkewnessLower

@[expose] public section

/-! 2026-10-30: a support-free sign-probability band for the original
standardized law with third absolute moment at most 11/10. The two
one-sided second-moment inequalities use the actual conditional variance
shares of this same law. No reflection or restriction of the law is used. -/

noncomputable section

open MeasureTheory

namespace BerryEsseen.LowMomentSignProbabilityBand

open CanonicalSign NoiseCoordinates SignedMoment

/-- The positive-sign variance supplies the one-sided Cauchy inequality. -/
theorem first_sq_le_positive_sign (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    firstAbsoluteMoment μ ^ 2 ≤ 2 * p μ * (1 + signedSecondMoment μ) := by
  have heq : 2 * p μ * (1 + signedSecondMoment μ) - firstAbsoluteMoment μ ^ 2 =
      4 * p μ * thetaPlus μ h := by
    rw [PhysicalSkewnessLower.firstAbsoluteMoment_eq_twice_positive μ h,
      mul_pow, positiveFirstMoment_sq μ h, signedSecondMoment_eq_physical μ h]
    unfold q theta
    ring
  have hnon := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (p_pos μ h).le)
    (thetaPlus_nonneg μ h)
  linarith only [heq, hnon]

/-- The nonpositive-sign variance includes any atom at zero. -/
theorem first_sq_le_nonpositive_sign (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    firstAbsoluteMoment μ ^ 2 ≤ 2 * q μ * (1 - signedSecondMoment μ) := by
  have heq : 2 * q μ * (1 - signedSecondMoment μ) - firstAbsoluteMoment μ ^ 2 =
      4 * q μ * thetaMinus μ h := by
    rw [PhysicalSkewnessLower.firstAbsoluteMoment_eq_twice_positive μ h,
      mul_pow, positiveFirstMoment_sq μ h, signedSecondMoment_eq_physical μ h]
    unfold q theta
    ring
  have hnon := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (q_pos μ h).le)
    (thetaMinus_nonneg μ h)
  linarith only [heq, hnon]

private theorem probability_gt_of_moment_bounds (a b s : ℝ)
    (ha : 0 < a) (hs : 0 < s)
    (hfirst : 1 + b ^ 2 ≤ a * (11 / 10 : ℝ))
    (hside : a ^ 2 ≤ 2 * s * (1 + b)) : (37 / 100 : ℝ) < s := by
  have hsidepos : 0 < 2 * s * (1 + b) := (sq_pos_of_pos ha).trans_le hside
  have hsign : 0 < 1 + b :=
    (mul_pos_iff_of_pos_left (by positivity : (0 : ℝ) < 2 * s)).mp hsidepos
  have hleft : 0 ≤ 1 + b ^ 2 := by positivity
  have hright : 0 ≤ a * (11 / 10 : ℝ) := by positivity
  have hsquare := (sq_le_sq₀ hleft hright).mpr hfirst
  have hweighted := mul_le_mul_of_nonneg_left hside (by norm_num : (0 : ℝ) ≤ 121 / 100)
  have hpoly : (1 + b ^ 2) ^ 2 ≤ (121 / 50 : ℝ) * s * (1 + b) := by
    nlinarith only [hsquare, hweighted]
  by_contra hnot
  have hsmax : s ≤ (37 / 100 : ℝ) := le_of_not_gt hnot
  have hupper := mul_le_mul_of_nonneg_right hsmax
    (by positivity : (0 : ℝ) ≤ (121 / 50 : ℝ) * (1 + b))
  have hbad : (1 + b ^ 2) ^ 2 ≤ (4477 / 5000 : ℝ) * (1 + b) := by
    nlinarith only [hpoly, hupper]
  -- The remaining constant after completing the square is 876471/200000000.
  nlinarith only [hbad, sq_nonneg (b ^ 2), sq_nonneg (b - 4477 / 20000)]

/-- The lower positive-sign probability follows on the full original-law domain. -/
theorem p_gt_37_100_of_rho_cap (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) : (37 / 100 : ℝ) < p μ := by
  have ha := firstAbsoluteMoment_pos μ h
  have hfirst : 1 + signedSecondMoment μ ^ 2 ≤ firstAbsoluteMoment μ * (11 / 10 : ℝ) :=
    (first_mul_third_ge_one_add_signed_sq μ h).trans
      (mul_le_mul_of_nonneg_left hρ ha.le)
  exact probability_gt_of_moment_bounds _ _ _ ha (p_pos μ h) hfirst
    (first_sq_le_positive_sign μ h)

/-- The same original law supplies the nonpositive-sign lower probability. -/
theorem q_gt_37_100_of_rho_cap (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) : (37 / 100 : ℝ) < q μ := by
  have ha := firstAbsoluteMoment_pos μ h
  have hfirst : 1 + (-signedSecondMoment μ) ^ 2 ≤
      firstAbsoluteMoment μ * (11 / 10 : ℝ) := by
    simpa only [neg_sq] using (first_mul_third_ge_one_add_signed_sq μ h).trans
      (mul_le_mul_of_nonneg_left hρ ha.le)
  apply probability_gt_of_moment_bounds _ (-signedSecondMoment μ) _ ha (q_pos μ h) hfirst
  simpa only [sub_eq_add_neg] using first_sq_le_nonpositive_sign μ h

theorem p_mem_Icc_37_100_63_100 (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) :
    p μ ∈ Set.Icc (37 / 100 : ℝ) (63 / 100) := by
  have hp := p_gt_37_100_of_rho_cap μ h hρ
  have hq := q_gt_37_100_of_rho_cap μ h hρ
  unfold q at hq
  exact ⟨hp.le, by linarith only [hq]⟩

theorem q_mem_Icc_37_100_63_100 (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) :
    q μ ∈ Set.Icc (37 / 100 : ℝ) (63 / 100) := by
  have hp := p_gt_37_100_of_rho_cap μ h hρ
  have hq := q_gt_37_100_of_rho_cap μ h hρ
  refine ⟨hq.le, ?_⟩
  unfold q
  linarith only [hp]

end BerryEsseen.LowMomentSignProbabilityBand

#print axioms BerryEsseen.LowMomentSignProbabilityBand.p_mem_Icc_37_100_63_100
#print axioms BerryEsseen.LowMomentSignProbabilityBand.q_mem_Icc_37_100_63_100
