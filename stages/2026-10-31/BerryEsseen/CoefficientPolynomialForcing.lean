module

public import BerryEsseen.HighMomentRayPrice
public import BerryEsseen.FiniteRhoSinePrice
public import BerryEsseen.CharacteristicExpansion
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

@[expose] public section

/-! 2026-10-29: a positive degree-six deterministic frequency forcing.
The cosine estimate is taken from the pure imaginary exponential Taylor
theorem at a fixed real argument; no random-variable sixth moment is an
assumption.  The comparison with B retains the explicit unsaturated domain
beta>0, t>=0, beta*t<=pi.  No new profile or numerical price is asserted. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped Interval

namespace BerryEsseen.CoefficientPolynomialForcing

def W6 (v : ℝ) : ℝ := v ^ 2 / 2 - v ^ 4 / 96 + v ^ 6 / 11520

def P6 (β t : ℝ) : ℝ := t ^ 2 / 2 - β ^ 2 * t ^ 4 / 96 + β ^ 4 * t ^ 6 / 11520

theorem W6_factor (v : ℝ) :
    W6 v = v ^ 2 * (3 / 16 + (v ^ 2 - 60) ^ 2 / 11520) := by unfold W6; ring

theorem W6_nonneg (v : ℝ) : 0 ≤ W6 v := by rw [W6_factor]; positivity

theorem P6_factor (β t : ℝ) :
    P6 β t = t ^ 2 * (3 / 16 + ((β * t) ^ 2 - 60) ^ 2 / 11520) := by unfold P6; ring

theorem P6_nonneg (β t : ℝ) : 0 ≤ P6 β t := by rw [P6_factor]; positivity

lemma continuous_P6 (β : ℝ) : Continuous (P6 β) := by unfold P6; fun_prop

theorem hasDerivAt_P6 (β t : ℝ) :
    HasDerivAt (P6 β) (t * (1 / 6 + ((β * t) ^ 2 - 40) ^ 2 / 1920)) t := by
  unfold P6
  convert (((((hasDerivAt_id' t).fun_pow 2).div_const 2).fun_sub
    ((((hasDerivAt_id' t).fun_pow 4).const_mul (β ^ 2)).div_const 96)).fun_add
      ((((hasDerivAt_id' t).fun_pow 6).const_mul (β ^ 4)).div_const 11520)) using 1
  ring

theorem deriv_P6_nonneg (β t : ℝ) (ht : 0 ≤ t) : 0 ≤ deriv (P6 β) t := by
  rw [(hasDerivAt_P6 β t).deriv]
  positivity

theorem monotoneOn_P6 (β : ℝ) : MonotoneOn (P6 β) (Ici 0) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici (0 : ℝ))
    (continuous_P6 β).continuousOn
    (fun t _ => (hasDerivAt_P6 β t).hasDerivWithinAt)
  intro t ht
  have ht0 : 0 ≤ t := interior_subset ht
  positivity

theorem P6_le_P6 (β a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) : P6 β a ≤ P6 β b :=
  monotoneOn_P6 β ha (ha.trans hab) hab

lemma expPolynomial_five_real (x : ℝ) :
    (CharacteristicExpansion.expPolynomial 5 x).re = 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
  norm_num [CharacteristicExpansion.expPolynomial, Finset.sum_range_succ, pow_succ,
    Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im, Complex.normSq_apply]
  ring

/-- Global scalar cosine minorant, with no probabilistic moment input. -/
theorem cos_ge_sextic (x : ℝ) :
    1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 ≤ Real.cos x := by
  have hh := (Complex.abs_re_le_norm
    (CharacteristicExpansion.pureExp x - CharacteristicExpansion.expPolynomial 5 x)).trans
      (CharacteristicExpansion.pureExp_taylor_bound 5 x)
  rw [Complex.sub_re, CharacteristicExpansion.pureExp_real, expPolynomial_five_real] at hh
  have hx6 : |x| ^ 6 = x ^ 6 := by
    rw [← abs_pow, abs_of_nonneg (by positivity : (0 : ℝ) ≤ x ^ 6)]
  rw [show (5 + 1 : ℕ) = 6 by rfl, hx6,
    show (6 : ℕ).factorial = 720 by norm_num] at hh
  norm_num only [Nat.cast_ofNat] at hh
  have hl := (abs_le.mp hh).1
  linarith only [hl]

/-- Only the stated prefix permits removal of B's sine cap. -/
theorem B_eq_uncapped (β t : ℝ) (hβ : 0 < β) (ht : 0 ≤ t) (hcap : β * t ≤ Real.pi) :
    HighMomentRayPrice.B β t = 8 * Real.sin (β * t / 4) ^ 2 / β := by
  unfold HighMomentRayPrice.B
  rw [← FiniteRhoSinePrice.integral_first_uncapped β t hβ]
  apply intervalIntegral.integral_congr
  intro v hv
  rw [uIcc_of_le ht] at hv
  have hh := (mul_le_mul_of_nonneg_left hv.2 hβ.le).trans hcap
  have harg : β * v / 2 ≤ Real.pi / 2 := by linarith only [hh]
  rw [HighMomentRayPrice.sineKernel, min_eq_left harg]

theorem B_div_beta_eq_cos (β t : ℝ) (hβ : 0 < β) (ht : 0 ≤ t) (hcap : β * t ≤ Real.pi) :
    HighMomentRayPrice.B β t / β = 4 * (1 - Real.cos (β * t / 2)) / β ^ 2 := by
  rw [B_eq_uncapped β t hβ ht hcap]
  have hc : Real.cos (β * t / 2) = 1 - 2 * Real.sin (β * t / 4) ^ 2 := by
    rw [show β * t / 2 = 2 * (β * t / 4) by ring, Real.cos_two_mul_eq_one_sub]
  rw [hc]
  field_simp [hβ.ne']
  ring

theorem B_div_beta_le_P6 (β t : ℝ) (hβ : 0 < β) (ht : 0 ≤ t) (hcap : β * t ≤ Real.pi) :
    HighMomentRayPrice.B β t / β ≤ P6 β t := by
  rw [B_div_beta_eq_cos β t hβ ht hcap]
  apply (div_le_iff₀ (sq_pos_of_pos hβ)).mpr
  calc
    4 * (1 - Real.cos (β * t / 2)) ≤
        4 * (1 - (1 - (β * t / 2) ^ 2 / 2 + (β * t / 2) ^ 4 / 24 - (β * t / 2) ^ 6 / 720)) :=
      mul_le_mul_of_nonneg_left (sub_le_sub_left (cos_ge_sextic (β * t / 2)) 1) (by norm_num)
    _ = P6 β t * β ^ 2 := by unfold P6; ring

theorem P6_le_quadratic (β t : ℝ) (hβ : 0 < β) (ht : 0 ≤ t) (hcap : β * t ≤ Real.pi) :
    P6 β t ≤ t ^ 2 / 2 := by
  have hbt0 : 0 ≤ β * t := mul_nonneg hβ.le ht
  have hbt4 : β * t ≤ 4 := hcap.trans Real.pi_lt_four.le
  have hs : (β * t) ^ 2 ≤ 120 := (pow_le_pow_left₀ hbt0 hbt4 2).trans (by norm_num)
  have hp := mul_nonpos_of_nonneg_of_nonpos
    (show 0 ≤ β ^ 2 * t ^ 4 by positivity) (sub_nonpos.mpr hs)
  unfold P6
  nlinarith only [hp]

theorem P6_spectral_eq (β w : ℝ) (hβ : 0 < β) :
    P6 β (w / β) = (1 / β ^ 2) * W6 w := by
  unfold P6 W6
  field_simp [hβ.ne']

end BerryEsseen.CoefficientPolynomialForcing

#print axioms BerryEsseen.CoefficientPolynomialForcing.W6_nonneg
#print axioms BerryEsseen.CoefficientPolynomialForcing.hasDerivAt_P6
#print axioms BerryEsseen.CoefficientPolynomialForcing.monotoneOn_P6
#print axioms BerryEsseen.CoefficientPolynomialForcing.cos_ge_sextic
#print axioms BerryEsseen.CoefficientPolynomialForcing.B_div_beta_le_P6
#print axioms BerryEsseen.CoefficientPolynomialForcing.P6_le_quadratic
#print axioms BerryEsseen.CoefficientPolynomialForcing.P6_spectral_eq
