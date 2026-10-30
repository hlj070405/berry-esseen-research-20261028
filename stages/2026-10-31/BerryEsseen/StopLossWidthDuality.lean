module

public import BerryEsseen.StopLossSubgradient

@[expose] public section

/-! 2026-10-29: global width duality for the actual inf-width price.
Stationarity is an equation between actual hinge integrals under one L2
probability law. It certifies both the infimum value and a global supporting
slope without a derivative or an assumed optimizer. -/

noncomputable section

namespace BerryEsseen.StopLossWidthDuality

open MeasureTheory Set
open StopLossShape StopLossSubgradient

def hinge (A h z : ℝ) : ℝ := max (z - A + h) 0
def weight (A h z : ℝ) : ℝ := hinge A h z / (2 * h)

def StationaryWidth (ν : Measure ℝ) (A h : ℝ) : Prop :=
  2 * h * (∫ z, hinge A h z ∂ν) = ∫ z, hinge A h z ^ 2 ∂ν

/-- Completing a square on the active half-line; the inactive half-line
uses `u ≥ 0`. This is the scalar Fenchel inequality, including activation. -/
theorem positivePart_fenchel (x k u : ℝ) (hk : 0 < k) (hu : 0 ≤ u) :
    u * x + k * (u - u ^ 2) ≤ (max (x + k) 0) ^ 2 / (4 * k) := by
  by_cases hx : 0 ≤ x + k
  · rw [max_eq_left hx]
    apply (le_div_iff₀ (by positivity : 0 < 4 * k)).mpr
    nlinarith only [sq_nonneg (x + k - 2 * k * u)]
  · have hxp : x + k ≤ 0 := le_of_not_ge hx
    rw [max_eq_right hxp]
    simp only [zero_pow (by decide : (2 : ℕ) ≠ 0), zero_div]
    have hm := mul_nonpos_of_nonneg_of_nonpos hu hxp
    have hs := mul_nonneg hk.le (sq_nonneg u)
    nlinarith only [hm, hs]

lemma positivePart_fenchel_eq (x h : ℝ) (hh : 0 < h) :
    (max (x + h) 0) ^ 2 / (4 * h) =
      (max (x + h) 0 / (2 * h)) * x +
        h * (max (x + h) 0 / (2 * h) - (max (x + h) 0 / (2 * h)) ^ 2) := by
  by_cases hx : 0 ≤ x + h
  · rw [max_eq_left hx]
    field_simp [hh.ne']
    ring
  · rw [max_eq_right (le_of_not_ge hx)]
    simp

theorem pointwise_support_inequality (z A B h k : ℝ) (hh : 0 < h) (hk : 0 < k) :
    weight A h z * (z - B) + k * (weight A h z - weight A h z ^ 2) ≤ kernel z B k := by
  exact positivePart_fenchel (z - B) k (weight A h z) hk
    (div_nonneg (le_max_right _ _) (by positivity))

lemma pointwise_self_equality (z A h : ℝ) (hh : 0 < h) :
    kernel z A h = weight A h z * (z - A) + h * (weight A h z - weight A h z ^ 2) :=
  positivePart_fenchel_eq (z - A) h hh

lemma integrable_hinge (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hSq : Integrable (fun z : ℝ => z ^ 2) ν) (A h : ℝ) :
    Integrable (hinge A h) ν := by
  have hI := TwoMoment.integrable_of_integrable_sq ν id measurable_id hSq
  exact ((hI.sub (integrable_const A)).add (integrable_const h)).pos_part

lemma integrable_hinge_sq (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hSq : Integrable (fun z : ℝ => z ^ 2) ν) (A h : ℝ) :
    Integrable (fun z => hinge A h z ^ 2) ν := integrable_numerator ν hSq A h

lemma integrable_weight (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hSq : Integrable (fun z : ℝ => z ^ 2) ν) (A h : ℝ) :
    Integrable (weight A h) ν := (integrable_hinge ν hSq A h).div_const (2 * h)

lemma integrable_weight_sq (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hSq : Integrable (fun z : ℝ => z ^ 2) ν) (A h : ℝ) :
    Integrable (fun z => weight A h z ^ 2) ν := by
  simpa only [weight, div_pow] using (integrable_hinge_sq ν hSq A h).div_const ((2 * h) ^ 2)

private lemma hinge_self_product (x : ℝ) : max x 0 * x = (max x 0) ^ 2 := by
  by_cases hx : 0 ≤ x
  · rw [max_eq_left hx]
    ring
  · rw [max_eq_right (le_of_not_ge hx)]
    simp

/-- The apparent bilinear term is an L1 quadratic-minus-linear expression. -/
lemma integrable_weight_shift_product (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hSq : Integrable (fun z : ℝ => z ^ 2) ν) (A h B : ℝ) (hh : 0 < h) :
    Integrable (fun z => weight A h z * (z - B)) ν := by
  have heq : (fun z => weight A h z * (z - B)) =
      (fun z => hinge A h z ^ 2 / (2 * h) - (B - A + h) * weight A h z) := by
    ext z
    unfold weight hinge
    have hr := hinge_self_product (z - A + h)
    field_simp [hh.ne']
    nlinarith only [hr]
  rw [heq]
  exact ((integrable_hinge_sq ν hSq A h).div_const (2 * h)).sub
    ((integrable_weight ν hSq A h).const_mul (B - A + h))

lemma integral_weight (ν : Measure ℝ) (A h : ℝ) :
    (∫ z, weight A h z ∂ν) = (∫ z, hinge A h z ∂ν) / (2 * h) := by
  simp only [weight, integral_div]

lemma integral_weight_sq (ν : Measure ℝ) (A h : ℝ) :
    (∫ z, weight A h z ^ 2 ∂ν) = (∫ z, hinge A h z ^ 2 ∂ν) / (2 * h) ^ 2 := by
  simp only [weight, div_pow, integral_div]

theorem stationarity_cancels_defect (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hSq : Integrable (fun z : ℝ => z ^ 2) ν) (A h : ℝ) (hh : 0 < h)
    (hs : StationaryWidth ν A h) :
    (∫ z, weight A h z - weight A h z ^ 2 ∂ν) = 0 := by
  unfold StationaryWidth at hs
  rw [integral_sub (integrable_weight ν hSq A h) (integrable_weight_sq ν hSq A h),
    integral_weight, integral_weight_sq, ← hs]
  field_simp [hh.ne']
  ring

private lemma stationary_price_eq_linear_integral (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hSq : Integrable (fun z : ℝ => z ^ 2) ν) (A h : ℝ) (hh : 0 < h)
    (hs : StationaryWidth ν A h) :
    price ν A h = ∫ z, weight A h z * (z - A) ∂ν := by
  have hProd := integrable_weight_shift_product ν hSq A h A hh
  have hDef : Integrable (fun z => weight A h z - weight A h z ^ 2) ν :=
    (integrable_weight ν hSq A h).sub (integrable_weight_sq ν hSq A h)
  calc
    _ = ∫ z, kernel z A h ∂ν := price_eq_integral ν A h
    _ = ∫ z, weight A h z * (z - A) + h * (weight A h z - weight A h z ^ 2) ∂ν :=
      integral_congr_ae (Filter.Eventually.of_forall (fun z => pointwise_self_equality z A h hh))
    _ = (∫ z, weight A h z * (z - A) ∂ν) +
        h * (∫ z, weight A h z - weight A h z ^ 2 ∂ν) := by
      rw [integral_add hProd (hDef.const_mul h), integral_const_mul]
    _ = _ := by rw [stationarity_cancels_defect ν hSq A h hh hs]; ring

theorem stationary_affine_price_bound (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hSq : Integrable (fun z : ℝ => z ^ 2) ν) (A h : ℝ) (hh : 0 < h)
    (hs : StationaryWidth ν A h) (B k : ℝ) (hk : 0 < k) :
    price ν A h - (∫ z, weight A h z ∂ν) * (B - A) ≤ price ν B k := by
  have hProd := integrable_weight_shift_product ν hSq A h B hh
  have hDef : Integrable (fun z => weight A h z - weight A h z ^ 2) ν :=
    (integrable_weight ν hSq A h).sub (integrable_weight_sq ν hSq A h)
  have hi := integral_mono (hProd.add (hDef.const_mul k)) (integrable_kernel ν hSq B k)
    (fun z => pointwise_support_inequality z A B h k hh hk)
  change (∫ z, weight A h z * (z - B) + k * (weight A h z - weight A h z ^ 2) ∂ν) ≤
    ∫ z, kernel z B k ∂ν at hi
  rw [integral_add hProd (hDef.const_mul k), integral_const_mul,
    stationarity_cancels_defect ν hSq A h hh hs, mul_zero, add_zero,
    ← price_eq_integral ν B k] at hi
  have heq : (fun z => weight A h z * (z - B)) =
      (fun z => weight A h z * (z - A) - (B - A) * weight A h z) := by ext z; ring
  rw [heq, integral_sub (integrable_weight_shift_product ν hSq A h A hh)
    ((integrable_weight ν hSq A h).const_mul _), integral_const_mul,
    ← stationary_price_eq_linear_integral ν hSq A h hh hs] at hi
  nlinarith only [hi]

/-- A verified stationary positive width is a global minimizer of the
actual width family. The theorem does not assert that such a width exists. -/
theorem stationary_Q_eq_price (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hSq : Integrable (fun z : ℝ => z ^ 2) ν) (A h : ℝ) (hh : 0 < h)
    (hs : StationaryWidth ν A h) : Q ν A = price ν A h := by
  apply le_antisymm (Q_le_price ν A h hh)
  apply (le_Q_iff ν A _).mpr
  intro k hk
  simpa only [sub_self, mul_zero, sub_zero] using
    stationary_affine_price_bound ν hSq A h hh hs A k hk

theorem stationary_supports_Q (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hSq : Integrable (fun z : ℝ => z ^ 2) ν) (A h : ℝ) (hh : 0 < h)
    (hs : StationaryWidth ν A h) :
    Supports (Q ν) A (-((∫ z, hinge A h z ∂ν) / (2 * h))) := by
  intro B
  have hl : price ν A h - (∫ z, weight A h z ∂ν) * (B - A) ≤ Q ν B := by
    apply (le_Q_iff ν B _).mpr
    intro k hk
    exact stationary_affine_price_bound ν hSq A h hh hs B k hk
  rw [stationary_Q_eq_price ν hSq A h hh hs, ← integral_weight ν A h]
  nlinarith only [hl]

theorem stationary_width_duality (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hSq : Integrable (fun z : ℝ => z ^ 2) ν) (A h : ℝ) (hh : 0 < h)
    (hs : StationaryWidth ν A h) :
    Q ν A = price ν A h ∧ Supports (Q ν) A (-((∫ z, hinge A h z ∂ν) / (2 * h))) :=
  ⟨stationary_Q_eq_price ν hSq A h hh hs, stationary_supports_Q ν hSq A h hh hs⟩

theorem stationary_slope_range (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hSq : Integrable (fun z : ℝ => z ^ 2) ν) (A h : ℝ) (hh : 0 < h)
    (hs : StationaryWidth ν A h) :
    -((∫ z, hinge A h z ∂ν) / (2 * h)) ∈ Icc (-1) 0 :=
  Q_support_mem_Icc ν hSq (stationary_supports_Q ν hSq A h hh hs)

theorem price_le_width_quarter_of_ae_le (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hSq : Integrable (fun z : ℝ => z ^ 2) ν) (A h : ℝ) (hh : 0 < h)
    (hupper : ∀ᵐ z ∂ν, z ≤ A) : price ν A h ≤ h / 4 := by
  have hi : (∫ z, (max (z - A + h) 0) ^ 2 ∂ν) ≤ h ^ 2 := by
    have hI := integral_mono_ae (integrable_numerator ν hSq A h) (integrable_const (h ^ 2))
      (hupper.mono (fun z hz => by
        have hm : max (z - A + h) 0 ≤ h := max_le (by linarith) hh.le
        exact (sq_le_sq₀ (le_max_right _ _) hh.le).mpr hm))
    simpa using hI
  unfold price
  apply (div_le_iff₀ (by positivity : 0 < 4 * h)).mpr
  nlinarith only [hi]

/-- A top-support threshold has zero infimum, whether or not any positive
width attains it. The estimate uses all arbitrarily small positive widths. -/
theorem Q_eq_zero_of_ae_le (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hSq : Integrable (fun z : ℝ => z ^ 2) ν) (A : ℝ)
    (hupper : ∀ᵐ z ∂ν, z ≤ A) : Q ν A = 0 := by
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro ε hε
    have hp := price_le_width_quarter_of_ae_le ν hSq A ε hε hupper
    have hq := Q_le_price ν A ε hε
    linarith
  · exact Q_nonneg ν A

theorem zero_supports_Q_of_ae_le (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hSq : Integrable (fun z : ℝ => z ^ 2) ν) (A : ℝ)
    (hupper : ∀ᵐ z ∂ν, z ≤ A) : Supports (Q ν) A 0 := by
  intro B
  rw [Q_eq_zero_of_ae_le ν hSq A hupper]
  simpa only [zero_mul, zero_add] using Q_nonneg ν B

end BerryEsseen.StopLossWidthDuality

#print axioms BerryEsseen.StopLossWidthDuality.positivePart_fenchel
#print axioms BerryEsseen.StopLossWidthDuality.pointwise_support_inequality
#print axioms BerryEsseen.StopLossWidthDuality.integrable_weight_shift_product
#print axioms BerryEsseen.StopLossWidthDuality.stationarity_cancels_defect
#print axioms BerryEsseen.StopLossWidthDuality.stationary_affine_price_bound
#print axioms BerryEsseen.StopLossWidthDuality.stationary_width_duality
#print axioms BerryEsseen.StopLossWidthDuality.stationary_slope_range
#print axioms BerryEsseen.StopLossWidthDuality.Q_eq_zero_of_ae_le
#print axioms BerryEsseen.StopLossWidthDuality.zero_supports_Q_of_ae_le
