module

public import BerryEsseen.ZeroBiasTransport
public import BerryEsseen.ReferencePriceDerivatives
public import Mathlib.Analysis.Calculus.Deriv.Shift

@[expose] public section

/-!
Actual positive and negative stop-loss prices of the zero-bias density.
The original law may have atoms and unbounded support. Gap expansions
below use explicit almost-everywhere gap hypotheses on that same law.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology Interval

namespace BerryEsseen.ZeroBiasStopLoss

open ZeroBias ZeroBiasTransport

def positivePart (x : ℝ) : ℝ := max x 0
def negativePart (x : ℝ) : ℝ := max (-x) 0

def positiveHinge (A t : ℝ) : ℝ := max (t - A) 0
def negativeHinge (A t : ℝ) : ℝ := max (-t - A) 0

def positiveSquare (A x : ℝ) : ℝ := (max (x - A) 0) ^ 2 / 2
def negativeSquare (A x : ℝ) : ℝ := -positiveSquare A (-x)

def positiveCost (A x : ℝ) : ℝ :=
  positivePart x * (max (positivePart x - A) 0) ^ 2

def negativeCost (A x : ℝ) : ℝ :=
  negativePart x * (max (negativePart x - A) 0) ^ 2

lemma positivePart_nonneg (x : ℝ) : 0 ≤ positivePart x := le_max_right _ _
lemma negativePart_nonneg (x : ℝ) : 0 ≤ negativePart x := le_max_right _ _

lemma positivePart_le_abs (x : ℝ) : positivePart x ≤ |x| :=
  max_le (le_abs_self x) (abs_nonneg x)

lemma negativePart_le_abs (x : ℝ) : negativePart x ≤ |x| :=
  max_le (neg_le_abs x) (abs_nonneg x)

lemma positivePart_cube_le (x : ℝ) : positivePart x ^ 3 ≤ |x| ^ 3 := by
  have hs := (sq_le_sq₀ (positivePart_nonneg x) (abs_nonneg x)).mpr (positivePart_le_abs x)
  have hm := mul_le_mul hs (positivePart_le_abs x) (positivePart_nonneg x) (sq_nonneg |x|)
  simpa only [pow_succ] using hm

lemma negativePart_cube_le (x : ℝ) : negativePart x ^ 3 ≤ |x| ^ 3 := by
  simpa only [positivePart, negativePart, abs_neg] using positivePart_cube_le (-x)

lemma positiveCost_nonneg (A x : ℝ) : 0 ≤ positiveCost A x :=
  mul_nonneg (positivePart_nonneg x) (sq_nonneg _)

lemma negativeCost_nonneg (A x : ℝ) : 0 ≤ negativeCost A x :=
  mul_nonneg (negativePart_nonneg x) (sq_nonneg _)

lemma positiveCost_le_cube (A x : ℝ) (hA : 0 ≤ A) : positiveCost A x ≤ |x| ^ 3 := by
  have hq : max (positivePart x - A) 0 ≤ positivePart x :=
    max_le (by linarith) (positivePart_nonneg x)
  have hs := (sq_le_sq₀ (le_max_right (positivePart x - A) 0) (positivePart_nonneg x)).mpr hq
  have hm := mul_le_mul_of_nonneg_left hs (positivePart_nonneg x)
  have hc : positiveCost A x ≤ positivePart x ^ 3 := by
    unfold positiveCost
    nlinarith
  exact le_trans hc (positivePart_cube_le x)

lemma negativeCost_le_cube (A x : ℝ) (hA : 0 ≤ A) : negativeCost A x ≤ |x| ^ 3 := by
  simpa only [positiveCost, negativeCost, positivePart, negativePart, abs_neg] using
    positiveCost_le_cube A (-x) hA

theorem integrable_positiveCost (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (A : ℝ) (hA : 0 ≤ A) : Integrable (positiveCost A) (μ : Measure ℝ) := by
  have hc : Continuous (positiveCost A) := by unfold positiveCost positivePart; fun_prop
  apply h.integrable_cube.mono' hc.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (positiveCost_nonneg A x)]
    exact positiveCost_le_cube A x hA

theorem integrable_negativeCost (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (A : ℝ) (hA : 0 ≤ A) : Integrable (negativeCost A) (μ : Measure ℝ) := by
  have hc : Continuous (negativeCost A) := by unfold negativeCost negativePart; fun_prop
  apply h.integrable_cube.mono' hc.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (negativeCost_nonneg A x)]
    exact negativeCost_le_cube A x hA

lemma positiveHinge_abs_le (A t : ℝ) (hA : 0 ≤ A) : |positiveHinge A t| ≤ |t| := by
  unfold positiveHinge
  rw [abs_of_nonneg (le_max_right (t - A) 0)]
  exact max_le (by linarith [le_abs_self t]) (abs_nonneg t)

lemma negativeHinge_abs_le (A t : ℝ) (hA : 0 ≤ A) : |negativeHinge A t| ≤ |t| := by
  unfold negativeHinge
  rw [abs_of_nonneg (le_max_right (-t - A) 0)]
  exact max_le (by linarith [neg_le_abs t]) (abs_nonneg t)

theorem primitive_positiveHinge (A : ℝ) (hA : 0 ≤ A) (x : ℝ) :
    primitive (positiveHinge A) x = positiveSquare A x := by
  have hc : Continuous (positiveHinge A) := by unfold positiveHinge; fun_prop
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := positiveSquare A) (f' := positiveHinge A) (a := 0) (b := x)
    (fun t _ => by
      have hd := HasDerivAt.comp_sub_const t A (TwoMoment.hasDerivAt_hinge_zero (t - A))
      unfold positiveSquare positiveHinge
      simpa only [GaussianPeano.hinge, GaussianPeano.hingeSlope,
        sub_zero] using hd) (hc.intervalIntegrable 0 x)
  have hzero : positiveSquare A 0 = 0 := by
    simp [positiveSquare, max_eq_right (neg_nonpos.mpr hA)]
  unfold primitive
  rw [hFTC, hzero, sub_zero]

theorem primitive_negativeHinge (A : ℝ) (hA : 0 ≤ A) (x : ℝ) :
    primitive (negativeHinge A) x = negativeSquare A x := by
  have hc : Continuous (negativeHinge A) := by unfold negativeHinge; fun_prop
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := negativeSquare A) (f' := negativeHinge A) (a := 0) (b := x)
    (fun t _ => by
      have hd := (HasDerivAt.comp_const_sub (-A) t (TwoMoment.hasDerivAt_hinge_zero (-A - t))).fun_neg
      have harg : ∀ u : ℝ, -A - u = -u - A := fun u => by ring
      unfold negativeSquare positiveSquare negativeHinge
      simpa only [GaussianPeano.hinge, GaussianPeano.hingeSlope,
        sub_zero, neg_neg, harg] using hd) (hc.intervalIntegrable 0 x)
  have hzero : negativeSquare A 0 = 0 := by
    simp [negativeSquare, positiveSquare, max_eq_right (neg_nonpos.mpr hA)]
  unfold primitive
  rw [hFTC, hzero, sub_zero]

lemma positive_square_cost (A x : ℝ) (hA : 0 ≤ A) :
    x * positiveSquare A x = positiveCost A x / 2 := by
  rcases le_total 0 x with hx | hx
  · simp only [positiveSquare, positiveCost, positivePart, max_eq_left hx]
    ring
  · have hxA : x - A ≤ 0 := by linarith
    simp [positiveSquare, positiveCost, positivePart, max_eq_right hx,
      max_eq_right hxA, max_eq_right (neg_nonpos.mpr hA)]

lemma negative_square_cost (A x : ℝ) (hA : 0 ≤ A) :
    x * negativeSquare A x = negativeCost A x / 2 := by
  have hp := positive_square_cost A (-x) hA
  have hc : positiveCost A (-x) = negativeCost A x := rfl
  rw [hc] at hp
  unfold negativeSquare
  nlinarith

lemma positive_weight_integrable (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (A : ℝ) (hA : 0 ≤ A) : Integrable (fun t : ℝ => |positiveHinge A t| * tau μ t) := by
  apply integrable_abs_mul_tau_of_linear_growth μ h (positiveHinge A)
    (by unfold positiveHinge; fun_prop) 0 1 (by norm_num) (by norm_num)
  intro t
  simpa only [zero_add, one_mul] using positiveHinge_abs_le A t hA

lemma negative_weight_integrable (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (A : ℝ) (hA : 0 ≤ A) : Integrable (fun t : ℝ => |negativeHinge A t| * tau μ t) := by
  apply integrable_abs_mul_tau_of_linear_growth μ h (negativeHinge A)
    (by unfold negativeHinge; fun_prop) 0 1 (by norm_num) (by norm_num)
  intro t
  simpa only [zero_add, one_mul] using negativeHinge_abs_le A t hA

theorem integrable_tau_positiveHinge (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (A : ℝ) (hA : 0 ≤ A) : Integrable (fun t : ℝ => tau μ t * positiveHinge A t) :=
  integrable_tau_mul μ h (positiveHinge A) (by unfold positiveHinge; fun_prop)
    (positive_weight_integrable μ h A hA)

theorem integrable_tau_negativeHinge (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (A : ℝ) (hA : 0 ≤ A) : Integrable (fun t : ℝ => tau μ t * negativeHinge A t) :=
  integrable_tau_mul μ h (negativeHinge A) (by unfold negativeHinge; fun_prop)
    (negative_weight_integrable μ h A hA)

theorem positive_stopLoss_identity (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (A : ℝ) (hA : 0 ≤ A) :
    2 * (∫ t : ℝ, tau μ t * max (t - A) 0) = ∫ x : ℝ, positiveCost A x ∂(μ : Measure ℝ) := by
  have ht := transport_identity μ h (positiveHinge A) (by unfold positiveHinge; fun_prop)
    (positive_weight_integrable μ h A hA)
  have heq : (fun x : ℝ => x * primitive (positiveHinge A) x) =
      (fun x : ℝ => positiveCost A x / 2) := by
    funext x
    rw [primitive_positiveHinge A hA x]
    exact positive_square_cost A x hA
  rw [heq, integral_div] at ht
  change 2 * (∫ t : ℝ, tau μ t * positiveHinge A t) = _
  linarith

theorem negative_stopLoss_identity (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (A : ℝ) (hA : 0 ≤ A) :
    2 * (∫ t : ℝ, tau μ t * max (-t - A) 0) = ∫ x : ℝ, negativeCost A x ∂(μ : Measure ℝ) := by
  have ht := transport_identity μ h (negativeHinge A) (by unfold negativeHinge; fun_prop)
    (negative_weight_integrable μ h A hA)
  have heq : (fun x : ℝ => x * primitive (negativeHinge A) x) =
      (fun x : ℝ => negativeCost A x / 2) := by
    funext x
    rw [primitive_negativeHinge A hA x]
    exact negative_square_cost A x hA
  rw [heq, integral_div] at ht
  change 2 * (∫ t : ℝ, tau μ t * negativeHinge A t) = _
  linarith

lemma integrable_positivePart (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    Integrable positivePart (μ : Measure ℝ) := h.integrable_mean.pos_part

lemma integrable_negativePart (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    Integrable negativePart (μ : Measure ℝ) := h.integrable_mean.neg_part

lemma integrable_positivePart_sq (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    Integrable (fun x : ℝ => positivePart x ^ 2) (μ : Measure ℝ) := by
  have hc : Continuous (fun x : ℝ => positivePart x ^ 2) := by unfold positivePart; fun_prop
  apply h.integrable_square.mono' hc.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact TwoMoment.positivePart_sq_le_sq x

lemma integrable_negativePart_sq (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    Integrable (fun x : ℝ => negativePart x ^ 2) (μ : Measure ℝ) := by
  have hc : Continuous (fun x : ℝ => negativePart x ^ 2) := by unfold negativePart; fun_prop
  apply h.integrable_square.mono' hc.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    simpa only [negativePart, neg_sq] using TwoMoment.positivePart_sq_le_sq (-x)

lemma integrable_positivePart_cube (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    Integrable (fun x : ℝ => positivePart x ^ 3) (μ : Measure ℝ) := by
  have hc : Continuous (fun x : ℝ => positivePart x ^ 3) := by unfold positivePart; fun_prop
  apply h.integrable_cube.mono' hc.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (positivePart_nonneg x) 3)]
    exact positivePart_cube_le x

lemma integrable_negativePart_cube (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    Integrable (fun x : ℝ => negativePart x ^ 3) (μ : Measure ℝ) := by
  have hc : Continuous (fun x : ℝ => negativePart x ^ 3) := by unfold negativePart; fun_prop
  apply h.integrable_cube.mono' hc.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (negativePart_nonneg x) 3)]
    exact negativePart_cube_le x

lemma positiveCost_expand_point (A x : ℝ) (hgap : 0 < x → A ≤ x) :
    positiveCost A x = positivePart x ^ 3 - (2 * A) * positivePart x ^ 2 + A ^ 2 * positivePart x := by
  by_cases hx : 0 < x
  · have hAx := hgap hx
    unfold positiveCost positivePart
    rw [max_eq_left hx.le, max_eq_left (sub_nonneg.mpr hAx)]
    ring
  · have hx0 : x ≤ 0 := le_of_not_gt hx
    simp [positiveCost, positivePart, max_eq_right hx0]

/-- The expansion uses the original law's actual a.e. absence of positive
mass below A. No universal support gap is asserted. -/
theorem positive_cost_expansion (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (A : ℝ)
    (hgap : ∀ᵐ x ∂(μ : Measure ℝ), 0 < x → A ≤ x) :
    (∫ x : ℝ, positiveCost A x ∂(μ : Measure ℝ)) =
      (∫ x : ℝ, positivePart x ^ 3 ∂(μ : Measure ℝ)) -
        (2 * A) * (∫ x : ℝ, positivePart x ^ 2 ∂(μ : Measure ℝ)) +
        A ^ 2 * (∫ x : ℝ, positivePart x ∂(μ : Measure ℝ)) := by
  have heq := hgap.mono fun x hx => positiveCost_expand_point A x hx
  have hB : Integrable (fun x : ℝ => (2 * A) * positivePart x ^ 2) (μ : Measure ℝ) :=
    (integrable_positivePart_sq μ h).const_mul (2 * A)
  have hC : Integrable (fun x : ℝ => A ^ 2 * positivePart x) (μ : Measure ℝ) :=
    (integrable_positivePart μ h).const_mul (A ^ 2)
  have hAB : Integrable (fun x : ℝ => positivePart x ^ 3 - (2 * A) * positivePart x ^ 2)
      (μ : Measure ℝ) := (integrable_positivePart_cube μ h).sub hB
  rw [integral_congr_ae heq, integral_add hAB hC,
    integral_sub (integrable_positivePart_cube μ h) hB, integral_const_mul, integral_const_mul]

theorem negative_cost_expansion (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (A : ℝ)
    (hgap : ∀ᵐ x ∂(μ : Measure ℝ), x < 0 → A ≤ -x) :
    (∫ x : ℝ, negativeCost A x ∂(μ : Measure ℝ)) =
      (∫ x : ℝ, negativePart x ^ 3 ∂(μ : Measure ℝ)) -
        (2 * A) * (∫ x : ℝ, negativePart x ^ 2 ∂(μ : Measure ℝ)) +
        A ^ 2 * (∫ x : ℝ, negativePart x ∂(μ : Measure ℝ)) := by
  have heq : (fun x : ℝ => negativeCost A x) =ᵐ[(μ : Measure ℝ)]
      (fun x : ℝ => negativePart x ^ 3 - (2 * A) * negativePart x ^ 2 + A ^ 2 * negativePart x) := by
    filter_upwards [hgap] with x hx
    have hp := positiveCost_expand_point A (-x) (fun hn => hx (by linarith))
    exact hp
  have hB : Integrable (fun x : ℝ => (2 * A) * negativePart x ^ 2) (μ : Measure ℝ) :=
    (integrable_negativePart_sq μ h).const_mul (2 * A)
  have hC : Integrable (fun x : ℝ => A ^ 2 * negativePart x) (μ : Measure ℝ) :=
    (integrable_negativePart μ h).const_mul (A ^ 2)
  have hAB : Integrable (fun x : ℝ => negativePart x ^ 3 - (2 * A) * negativePart x ^ 2)
      (μ : Measure ℝ) := (integrable_negativePart_cube μ h).sub hB
  rw [integral_congr_ae heq, integral_add hAB hC,
    integral_sub (integrable_negativePart_cube μ h) hB, integral_const_mul, integral_const_mul]

theorem positive_stopLoss_gap_expansion (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (A : ℝ) (hA : 0 ≤ A) (hgap : ∀ᵐ x ∂(μ : Measure ℝ), 0 < x → A ≤ x) :
    2 * (∫ t : ℝ, tau μ t * max (t - A) 0) =
      (∫ x : ℝ, positivePart x ^ 3 ∂(μ : Measure ℝ)) -
        (2 * A) * (∫ x : ℝ, positivePart x ^ 2 ∂(μ : Measure ℝ)) +
        A ^ 2 * (∫ x : ℝ, positivePart x ∂(μ : Measure ℝ)) := by
  rw [positive_stopLoss_identity μ h A hA, positive_cost_expansion μ h A hgap]

theorem negative_stopLoss_gap_expansion (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (A : ℝ) (hA : 0 ≤ A) (hgap : ∀ᵐ x ∂(μ : Measure ℝ), x < 0 → A ≤ -x) :
    2 * (∫ t : ℝ, tau μ t * max (-t - A) 0) =
      (∫ x : ℝ, negativePart x ^ 3 ∂(μ : Measure ℝ)) -
        (2 * A) * (∫ x : ℝ, negativePart x ^ 2 ∂(μ : Measure ℝ)) +
        A ^ 2 * (∫ x : ℝ, negativePart x ∂(μ : Measure ℝ)) := by
  rw [negative_stopLoss_identity μ h A hA, negative_cost_expansion μ h A hgap]

lemma positive_sub_negative (x : ℝ) : positivePart x - negativePart x = x := by
  rcases le_total 0 x with hx | hx
  · simp [positivePart, negativePart, max_eq_left hx, max_eq_right (neg_nonpos.mpr hx)]
  · simp [positivePart, negativePart, max_eq_right hx, max_eq_left (neg_nonneg.mpr hx)]

theorem negative_firstMoment_eq_positive (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    (∫ x : ℝ, negativePart x ∂(μ : Measure ℝ)) = ∫ x : ℝ, positivePart x ∂(μ : Measure ℝ) := by
  have heq : (∫ x : ℝ, positivePart x ∂(μ : Measure ℝ)) -
      (∫ x : ℝ, negativePart x ∂(μ : Measure ℝ)) = 0 := by
    calc
      _ = ∫ x : ℝ, positivePart x - negativePart x ∂(μ : Measure ℝ) :=
        (integral_sub (integrable_positivePart μ h) (integrable_negativePart μ h)).symm
      _ = ∫ x : ℝ, x ∂(μ : Measure ℝ) :=
        integral_congr_ae (Filter.Eventually.of_forall positive_sub_negative)
      _ = 0 := h.mean_zero
  linarith

end BerryEsseen.ZeroBiasStopLoss

#print axioms BerryEsseen.ZeroBiasStopLoss.integrable_positiveCost
#print axioms BerryEsseen.ZeroBiasStopLoss.integrable_negativeCost
#print axioms BerryEsseen.ZeroBiasStopLoss.positive_stopLoss_identity
#print axioms BerryEsseen.ZeroBiasStopLoss.negative_stopLoss_identity
#print axioms BerryEsseen.ZeroBiasStopLoss.positive_cost_expansion
#print axioms BerryEsseen.ZeroBiasStopLoss.negative_cost_expansion
#print axioms BerryEsseen.ZeroBiasStopLoss.negative_firstMoment_eq_positive
#print axioms BerryEsseen.ZeroBiasStopLoss.positive_stopLoss_gap_expansion
#print axioms BerryEsseen.ZeroBiasStopLoss.negative_stopLoss_gap_expansion
