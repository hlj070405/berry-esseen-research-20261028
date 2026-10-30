module

public import BerryEsseen.ThirdMomentRegion

@[expose] public section

/-! 2026-10-29: sound strict moment-region discard for closed rectangles.
The squared-skewness lower endpoint and the absolute-third upper endpoint
give an upper bound on the actual feasibility polynomial when 1 ≤ ρ ≤ 2.
Only a strictly negative bound discards a rectangle. Rational endpoints
are connected by exact casts; this module runs no rows or grids. -/

noncomputable section

open MeasureTheory Set

namespace BerryEsseen.N2MomentRectangle

def squareLower (gl gh : ℝ) : ℝ :=
  if gl ≤ 0 ∧ 0 ≤ gh then 0 else min (gl ^ 2) (gh ^ 2)

def feasibility (γ ρ : ℝ) : ℝ :=
  ρ ^ 2 * (γ ^ 2 + 4) - (γ ^ 2 + 2) ^ 2

def rectangleBound (gl gh rh : ℝ) : ℝ :=
  rh ^ 2 * (squareLower gl gh + 4) - (squareLower gl gh + 2) ^ 2

theorem squareLower_nonneg (gl gh : ℝ) : 0 ≤ squareLower gl gh := by
  unfold squareLower
  split_ifs
  · exact le_rfl
  · exact le_min (sq_nonneg gl) (sq_nonneg gh)

theorem squareLower_le_square (gl gh γ : ℝ) (hgl : gl ≤ γ) (hgh : γ ≤ gh) :
    squareLower gl gh ≤ γ ^ 2 := by
  by_cases hc : gl ≤ 0 ∧ 0 ≤ gh
  · rw [squareLower, if_pos hc]
    exact sq_nonneg γ
  · rw [squareLower, if_neg hc]
    by_cases hgl0 : 0 ≤ gl
    · have hγ0 : 0 ≤ γ := hgl0.trans hgl
      exact (min_le_left _ _).trans ((sq_le_sq₀ hgl0 hγ0).mpr hgl)
    · have hgl0' : gl ≤ 0 := (lt_of_not_ge hgl0).le
      have hgh0 : gh < 0 := lt_of_not_ge (fun hh => hc ⟨hgl0', hh⟩)
      have hγ0 : γ ≤ 0 := hgh.trans hgh0.le
      have hs : gh ^ 2 ≤ γ ^ 2 := by
        have hn := (sq_le_sq₀ (neg_nonneg.mpr hgh0.le) (neg_nonneg.mpr hγ0)).mpr
          (neg_le_neg hgh)
        simpa only [neg_sq] using hn
      exact (min_le_right _ _).trans hs

/-- Decrease the squared-skewness coordinate first, then increase ρ.
No sign or width restriction is imposed on the skewness rectangle. -/
theorem feasibility_le_rectangleBound (gl gh rh γ ρ : ℝ)
    (hgl : gl ≤ γ) (hgh : γ ≤ gh) (hρ1 : 1 ≤ ρ) (hρ2 : ρ ≤ 2) (hρh : ρ ≤ rh) :
    feasibility γ ρ ≤ rectangleBound gl gh rh := by
  let m := squareLower gl gh
  have hm : 0 ≤ m := squareLower_nonneg gl gh
  have hms : m ≤ γ ^ 2 := squareLower_le_square gl gh γ hgl hgh
  have hρ0 : 0 ≤ ρ := by linarith
  have hρsq : ρ ^ 2 ≤ 4 := by
    have hh := (sq_le_sq₀ hρ0 (by norm_num : (0 : ℝ) ≤ 2)).mpr hρ2
    norm_num at hh
    exact hh
  have hc : ρ ^ 2 - γ ^ 2 - m - 4 ≤ 0 := by nlinarith [sq_nonneg γ]
  have hp : (γ ^ 2 - m) * (ρ ^ 2 - γ ^ 2 - m - 4) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hms) hc
  have hfirst : feasibility γ ρ ≤ ρ ^ 2 * (m + 4) - (m + 2) ^ 2 := by
    unfold feasibility
    nlinarith only [hp]
  have hrh0 : 0 ≤ rh := hρ0.trans hρh
  have hsq := (sq_le_sq₀ hρ0 hrh0).mpr hρh
  have hw := mul_le_mul_of_nonneg_right hsq (show 0 ≤ m + 4 by linarith)
  have hsecond : ρ ^ 2 * (m + 4) - (m + 2) ^ 2 ≤ rectangleBound gl gh rh := by
    change ρ ^ 2 * (m + 4) - (m + 2) ^ 2 ≤ rh ^ 2 * (m + 4) - (m + 2) ^ 2
    linarith only [hw]
  exact hfirst.trans hsecond

/-- The pure real gate is strict: a zero bound is not a discard certificate. -/
theorem strict_discard (gl gh rh γ ρ : ℝ)
    (hgl : gl ≤ γ) (hgh : γ ≤ gh) (hρ1 : 1 ≤ ρ) (hρ2 : ρ ≤ 2) (hρh : ρ ≤ rh)
    (hnegative : rectangleBound gl gh rh < 0) : ¬ 0 ≤ feasibility γ ρ := by
  have hupper := feasibility_le_rectangleBound gl gh rh γ ρ hgl hgh hρ1 hρ2 hρh
  exact not_le_of_gt (hupper.trans_lt hnegative)

/-- Actual standardized moments force every containing rectangle's bound
to be nonnegative. The feasibility premise is derived, never assumed. -/
theorem actual_rectangleBound_nonneg (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (gl gh rh : ℝ) (hgl : gl ≤ ZeroBias.gamma μ) (hgh : ZeroBias.gamma μ ≤ gh)
    (hρ2 : thirdAbsoluteMoment μ ≤ 2) (hρh : thirdAbsoluteMoment μ ≤ rh) :
    0 ≤ rectangleBound gl gh rh := by
  have hfeas : 0 ≤ feasibility (ZeroBias.gamma μ) (thirdAbsoluteMoment μ) :=
    ThirdMomentRegion.feasibility_polynomial_nonneg μ hμ
  exact hfeas.trans (feasibility_le_rectangleBound gl gh rh _ _ hgl hgh
    (ThirdMomentRegion.one_le_third μ hμ) hρ2 hρh)

theorem actual_strict_discard (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (gl gh rh : ℝ) (hgl : gl ≤ ZeroBias.gamma μ) (hgh : ZeroBias.gamma μ ≤ gh)
    (hρ2 : thirdAbsoluteMoment μ ≤ 2) (hρh : thirdAbsoluteMoment μ ≤ rh)
    (hnegative : rectangleBound gl gh rh < 0) : False :=
  (not_lt_of_ge (actual_rectangleBound_nonneg μ hμ gl gh rh hgl hgh hρ2 hρh)) hnegative

theorem actual_not_mem_rectangle (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (hρ2 : thirdAbsoluteMoment μ ≤ 2) (gl gh rh : ℝ)
    (hnegative : rectangleBound gl gh rh < 0) :
    ¬ (ZeroBias.gamma μ ∈ Icc gl gh ∧ thirdAbsoluteMoment μ ≤ rh) := by
  rintro ⟨⟨hgl, hgh⟩, hρh⟩
  exact actual_strict_discard μ hμ gl gh rh hgl hgh hρ2 hρh hnegative

/-- The checker's endpoint arithmetic can remain entirely rational. -/
def squareLowerRat (gl gh : ℚ) : ℚ :=
  if gl ≤ 0 ∧ 0 ≤ gh then 0 else min (gl ^ 2) (gh ^ 2)

def rectangleBoundRat (gl gh rh : ℚ) : ℚ :=
  rh ^ 2 * (squareLowerRat gl gh + 4) - (squareLowerRat gl gh + 2) ^ 2

theorem cast_squareLowerRat (gl gh : ℚ) :
    (squareLowerRat gl gh : ℝ) = squareLower (gl : ℝ) (gh : ℝ) := by
  by_cases hc : gl ≤ 0 ∧ 0 ≤ gh
  · have hcR : (gl : ℝ) ≤ 0 ∧ 0 ≤ (gh : ℝ) := by exact_mod_cast hc
    simp only [squareLowerRat, if_pos hc, squareLower, if_pos hcR, Rat.cast_zero]
  · have hcR : ¬ ((gl : ℝ) ≤ 0 ∧ 0 ≤ (gh : ℝ)) := by
      intro hh
      apply hc
      exact_mod_cast hh
    rw [squareLowerRat, if_neg hc, squareLower, if_neg hcR, Rat.cast_min]
    push_cast
    rfl

theorem cast_rectangleBoundRat (gl gh rh : ℚ) :
    (rectangleBoundRat gl gh rh : ℝ) = rectangleBound (gl : ℝ) (gh : ℝ) (rh : ℝ) := by
  unfold rectangleBoundRat rectangleBound
  push_cast
  rw [cast_squareLowerRat]

theorem strict_discard_rat (gl gh rh : ℚ) (γ ρ : ℝ)
    (hgl : (gl : ℝ) ≤ γ) (hgh : γ ≤ (gh : ℝ))
    (hρ1 : 1 ≤ ρ) (hρ2 : ρ ≤ 2) (hρh : ρ ≤ (rh : ℝ))
    (hnegative : rectangleBoundRat gl gh rh < 0) : ¬ 0 ≤ feasibility γ ρ := by
  have hnegativeR : rectangleBound (gl : ℝ) (gh : ℝ) (rh : ℝ) < 0 := by
    rw [← cast_rectangleBoundRat]
    exact_mod_cast hnegative
  exact strict_discard (gl : ℝ) (gh : ℝ) (rh : ℝ) γ ρ hgl hgh hρ1 hρ2 hρh hnegativeR

theorem actual_rectangleBoundRat_nonneg (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (gl gh rh : ℚ) (hgl : (gl : ℝ) ≤ ZeroBias.gamma μ) (hgh : ZeroBias.gamma μ ≤ (gh : ℝ))
    (hρ2 : thirdAbsoluteMoment μ ≤ 2) (hρh : thirdAbsoluteMoment μ ≤ (rh : ℝ)) :
    0 ≤ rectangleBoundRat gl gh rh := by
  have hh := actual_rectangleBound_nonneg μ hμ (gl : ℝ) (gh : ℝ) (rh : ℝ) hgl hgh hρ2 hρh
  rw [← cast_rectangleBoundRat] at hh
  exact_mod_cast hh

theorem actual_strict_discard_rat (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (gl gh rh : ℚ) (hgl : (gl : ℝ) ≤ ZeroBias.gamma μ) (hgh : ZeroBias.gamma μ ≤ (gh : ℝ))
    (hρ2 : thirdAbsoluteMoment μ ≤ 2) (hρh : thirdAbsoluteMoment μ ≤ (rh : ℝ))
    (hnegative : rectangleBoundRat gl gh rh < 0) : False :=
  (not_lt_of_ge (actual_rectangleBoundRat_nonneg μ hμ gl gh rh hgl hgh hρ2 hρh)) hnegative

end BerryEsseen.N2MomentRectangle

#print axioms BerryEsseen.N2MomentRectangle.squareLower_nonneg
#print axioms BerryEsseen.N2MomentRectangle.squareLower_le_square
#print axioms BerryEsseen.N2MomentRectangle.feasibility_le_rectangleBound
#print axioms BerryEsseen.N2MomentRectangle.strict_discard
#print axioms BerryEsseen.N2MomentRectangle.actual_rectangleBound_nonneg
#print axioms BerryEsseen.N2MomentRectangle.actual_strict_discard
#print axioms BerryEsseen.N2MomentRectangle.cast_rectangleBoundRat
#print axioms BerryEsseen.N2MomentRectangle.actual_strict_discard_rat
