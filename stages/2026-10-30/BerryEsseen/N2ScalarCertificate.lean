module

public import BerryEsseen.N2BernsteinFast
public import BerryEsseen.N2MomentRectangle

@[expose] public section

/-! 2026-10-29: fixed bicubic physical scalar-certificate replay.
Accepted leaves recompute all rational Bernstein coefficients from the
same incoming power polynomial. Discarded leaves require a strictly
negative upper bound on the true moment-region polynomial. Literal
midpoints and both closed children are checked; unresolved leaves fail.
Gaussian prices, source expectations and actual-law specialization are
composed outside this checker. -/

namespace BerryEsseen.N2ScalarCertificate

open N2RectangleBernstein N2BernsteinFast

inductive Certificate where
  | accept
  | discard
  | splitGamma (mid : ℚ) (left right : Certificate)
  | splitRho (mid : ℚ) (left right : Certificate)
  | unresolved

/-- All leaf decisions use the constructive rational/Fin4 instances.
The literal polynomial is unchanged throughout the recursion. -/
def check (a : Power) (gl gh rl rh : ℚ) : Certificate → Bool
  | .accept => decide (gl < gh ∧ rl < rh ∧
      ∀ i j, 0 ≤ fastBoxCoeff a gl gh rl rh i j)
  | .discard => decide (N2MomentRectangle.rectangleBoundRat gl gh rh < 0)
  | .splitGamma mid left right => decide (mid = midpoint gl gh) &&
      (check a gl mid rl rh left && check a mid gh rl rh right)
  | .splitRho mid left right => decide (mid = midpoint rl rh) &&
      (check a gl gh rl mid left && check a gl gh mid rh right)
  | .unresolved => false

private theorem and_true {p q : Bool} (h : (p && q) = true) : p = true ∧ q = true := by
  cases p <;> cases q <;> simp_all

private theorem sound_by_recursion (a : Power) (certificate : Certificate) :
    ∀ (gl gh rl rh : ℚ), check a gl gh rl rh certificate = true →
      ∀ γ ρ : ℝ, InBox gl gh rl rh γ ρ → 1 ≤ ρ → ρ ≤ 2 →
        0 ≤ N2MomentRectangle.feasibility γ ρ → 0 ≤ evalPower a γ ρ := by
  induction certificate with
  | accept =>
      intro gl gh rl rh hcheck γ ρ hbox _ _ _
      have hc : gl < gh ∧ rl < rh ∧
          ∀ i j, 0 ≤ fastBoxCoeff a gl gh rl rh i j := of_decide_eq_true hcheck
      have hbc : ∀ i j, 0 ≤ boxCoeff a gl gh rl rh i j := by
        intro i j
        rw [← fastBoxCoeff_eq_boxCoeff]
        exact hc.2.2 i j
      simpa only [Rat.cast_zero] using
        box_lower_bound a gl gh rl rh 0 hc.1 hc.2.1 hbc γ ρ hbox
  | discard =>
      intro gl gh rl rh hcheck γ ρ hbox hρ1 hρ2 hfeasible
      have hn : N2MomentRectangle.rectangleBoundRat gl gh rh < 0 :=
        of_decide_eq_true hcheck
      exact False.elim ((N2MomentRectangle.strict_discard_rat gl gh rh γ ρ
        hbox.1.1 hbox.1.2 hρ1 hρ2 hbox.2.2 hn) hfeasible)
  | splitGamma mid left right ihLeft ihRight =>
      intro gl gh rl rh hcheck
      have hc : decide (mid = midpoint gl gh) = true ∧
          (check a gl mid rl rh left && check a mid gh rl rh right) = true := and_true hcheck
      have hmid : mid = midpoint gl gh := of_decide_eq_true hc.1
      have hchildren := and_true hc.2
      have hl := ihLeft gl mid rl rh hchildren.1
      have hr := ihRight mid gh rl rh hchildren.2
      rw [hmid] at hl hr
      intro γ ρ hbox hρ1 hρ2 hfeasible
      rcases box_x_bisect_cover gl gh rl rh γ ρ hbox with hleft | hright
      · exact hl γ ρ hleft hρ1 hρ2 hfeasible
      · exact hr γ ρ hright hρ1 hρ2 hfeasible
  | splitRho mid left right ihLeft ihRight =>
      intro gl gh rl rh hcheck
      have hc : decide (mid = midpoint rl rh) = true ∧
          (check a gl gh rl mid left && check a gl gh mid rh right) = true := and_true hcheck
      have hmid : mid = midpoint rl rh := of_decide_eq_true hc.1
      have hchildren := and_true hc.2
      have hl := ihLeft gl gh rl mid hchildren.1
      have hr := ihRight gl gh mid rh hchildren.2
      rw [hmid] at hl hr
      intro γ ρ hbox hρ1 hρ2 hfeasible
      rcases box_y_bisect_cover gl gh rl rh γ ρ hbox with hleft | hright
      · exact hl γ ρ hleft hρ1 hρ2 hfeasible
      · exact hr γ ρ hright hρ1 hρ2 hfeasible
  | unresolved =>
      intro gl gh rl rh hcheck
      cases hcheck

/-- Successful replay gives the original power polynomial's nonnegativity
on every physically feasible point of the complete closed root box.
The global rho bounds are unchanged inputs at every recursive step. -/
theorem check_sound (a : Power) (gl gh rl rh : ℚ) (certificate : Certificate)
    (hcheck : check a gl gh rl rh certificate = true) :
    ∀ γ ρ : ℝ, InBox gl gh rl rh γ ρ → 1 ≤ ρ → ρ ≤ 2 →
      0 ≤ N2MomentRectangle.feasibility γ ρ → 0 ≤ evalPower a γ ρ :=
  sound_by_recursion a certificate gl gh rl rh hcheck

theorem check_unresolved (a : Power) (gl gh rl rh : ℚ) :
    check a gl gh rl rh .unresolved = false := rfl

def microOnePower : Power := fun i j => if i.val = 0 ∧ j.val = 0 then 1 else 0

/-- A constant polynomial is checked over the full original moment rectangle. -/
theorem micro_constant_accept : check microOnePower (-2) 2 1 2 .accept = true := by decide +kernel

/-- The original outer corner has exactly h-upper=-4 and is strictly discarded. -/
theorem micro_negative_four_discard (a : Power) :
    N2MomentRectangle.rectangleBoundRat (-2) (-3 / 2) (3 / 2) = -4 ∧
      check a (-2) (-3 / 2) 1 (3 / 2) .discard = true := by
  change N2MomentRectangle.rectangleBoundRat (-2) (-3 / 2) (3 / 2) = -4 ∧
    decide (N2MomentRectangle.rectangleBoundRat (-2) (-3 / 2) (3 / 2) < 0) = true
  decide +kernel

/-- Equality at zero, including the physical (gamma,rho)=(0,1) boundary,
does not constitute a discard certificate. -/
theorem micro_zero_not_discard (a : Power) :
    N2MomentRectangle.rectangleBoundRat (-1) 1 1 = 0 ∧
      check a (-1) 1 1 1 .discard = false := by
  change N2MomentRectangle.rectangleBoundRat (-1) 1 1 = 0 ∧
    decide (N2MomentRectangle.rectangleBoundRat (-1) 1 1 < 0) = false
  decide +kernel

end BerryEsseen.N2ScalarCertificate

#print axioms BerryEsseen.N2ScalarCertificate.check
#print axioms BerryEsseen.N2ScalarCertificate.check_sound
#print axioms BerryEsseen.N2ScalarCertificate.check_unresolved
#print axioms BerryEsseen.N2ScalarCertificate.micro_constant_accept
#print axioms BerryEsseen.N2ScalarCertificate.micro_negative_four_discard
#print axioms BerryEsseen.N2ScalarCertificate.micro_zero_not_discard
