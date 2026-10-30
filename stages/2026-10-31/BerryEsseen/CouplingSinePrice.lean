module

public import BerryEsseen.SquareBiasDistance
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

@[expose] public section

/-! 2026-10-29: a sine characteristic-function price from an actual
coupling cost. A single affine support of capped sine suffices for Jensen;
no general optimal-transport framework or optimizer is assumed. -/

noncomputable section
open MeasureTheory Set

namespace BerryEsseen.CouplingSinePrice

open SquareBiasDistance

lemma sine_tangent {a x : ℝ} (ha : a ∈ Icc (0 : ℝ) Real.pi)
    (hx : x ∈ Icc (0 : ℝ) Real.pi) :
    Real.sin x ≤ Real.sin a + Real.cos a * (x - a) := by
  have hconc : ConcaveOn ℝ (Icc 0 Real.pi) Real.sin :=
    StrictConcaveOn.concaveOn strictConcaveOn_sin_Icc
  rcases lt_trichotomy x a with hxa | rfl | hax
  · have h := hconc.le_slope_of_hasDerivAt
      hx ha hxa (Real.hasDerivAt_sin a)
    rw [slope_def_field] at h
    have hm := (le_div_iff₀ (sub_pos.mpr hxa)).mp h
    nlinarith only [hm]
  · simp
  · have h := hconc.slope_le_of_hasDerivAt
      ha hx hax (Real.hasDerivAt_sin a)
    rw [slope_def_field] at h
    have hm := (div_le_iff₀ (sub_pos.mpr hax)).mp h
    nlinarith only [hm]

lemma capped_sine_tangent {a x : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ Real.pi / 2)
    (hx : 0 ≤ x) :
    Real.sin (min x (Real.pi / 2)) ≤ Real.sin a + Real.cos a * (x - a) := by
  have haπ : a ≤ Real.pi := ha.trans (by linarith only [Real.pi_pos])
  by_cases hxcap : x ≤ Real.pi / 2
  · rw [min_eq_left hxcap]
    exact sine_tangent ⟨ha0, haπ⟩ ⟨hx, hxcap.trans (by linarith only [Real.pi_pos])⟩
  · rw [min_eq_right (le_of_not_ge hxcap)]
    have ht := sine_tangent ⟨ha0, haπ⟩
      (show Real.pi / 2 ∈ Icc (0 : ℝ) Real.pi by constructor <;> linarith only [Real.pi_pos])
    have hc := Real.cos_nonneg_of_mem_Icc (show a ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) by
      exact ⟨by linarith only [ha0, Real.pi_pos], ha⟩)
    have hm := mul_nonneg hc (show 0 ≤ x - Real.pi / 2 by linarith only [hxcap])
    linarith only [ht, hm]

lemma norm_phase_sub (t x y : ℝ) :
    ‖phase t x - phase t y‖ = 2 * |Real.sin (t * (x - y) / 2)| := by
  have heq : phase t x - phase t y =
      phase t y * (Complex.exp (Complex.I * ((t * (x - y) : ℝ) : ℂ)) - 1) := by
    unfold phase
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [heq, norm_mul, norm_phase, one_mul, Complex.norm_exp_I_mul_ofReal_sub_one,
    Real.norm_eq_abs, abs_mul]
  norm_num

theorem norm_phase_sub_le_capped (t x y : ℝ) :
    ‖phase t x - phase t y‖ ≤
      2 * Real.sin (min (|t| * |x - y| / 2) (Real.pi / 2)) := by
  rw [norm_phase_sub]
  have ha : |t * (x - y) / 2| = |t| * |x - y| / 2 := by
    rw [abs_div, abs_mul]
    norm_num
  by_cases hx : |t| * |x - y| / 2 ≤ Real.pi / 2
  · rw [min_eq_left hx, Real.abs_sin_eq_sin_abs_of_abs_le_pi
      (show |t * (x - y) / 2| ≤ Real.pi by rw [ha]; linarith only [hx, Real.pi_pos]), ha]
  · rw [min_eq_right (le_of_not_ge hx), Real.sin_pi_div_two]
    nlinarith only [Real.abs_sin_le_one (t * (x - y) / 2)]

lemma integrable_composed_phase {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (X : Ω → ℝ) (hX : Measurable X) (t : ℝ) :
    Integrable (fun w => phase t (X w)) ν := by
  apply (integrable_const (1 : ℝ)).mono' ((continuous_phase t).measurable.comp hX).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun w => (norm_phase t (X w)).le

/-- A true probability coupling with finite expected distance gives the
capped-sine price. Only the displayed transport cost is used. -/
theorem norm_integral_difference_le {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (X Y : Ω → ℝ)
    (hX : Measurable X) (hY : Measurable Y)
    (hD : Integrable (fun w => |X w - Y w|) ν) (R t : ℝ)
    (hcost : (∫ w, |X w - Y w| ∂ν) ≤ R) :
    ‖(∫ w, phase t (X w) ∂ν) - (∫ w, phase t (Y w) ∂ν)‖ ≤
      2 * Real.sin (min (R * |t| / 2) (Real.pi / 2)) := by
  have hR : 0 ≤ R := (integral_nonneg fun w => abs_nonneg (X w - Y w)).trans hcost
  have hIX := integrable_composed_phase ν X hX t
  have hIY := integrable_composed_phase ν Y hY t
  rw [← integral_sub hIX hIY]
  by_cases hcap : R * |t| / 2 ≤ Real.pi / 2
  · rw [min_eq_left hcap]
    let a := R * |t| / 2
    have ha0 : 0 ≤ a := by dsimp only [a]; positivity
    have hc : 0 ≤ Real.cos a := Real.cos_nonneg_of_mem_Icc
      ⟨by linarith only [ha0, Real.pi_pos], hcap⟩
    let B := 2 * Real.sin a - 2 * Real.cos a * a
    have hIG : Integrable (fun w => B + (Real.cos a * |t|) * |X w - Y w|) ν :=
      (integrable_const B).add (hD.const_mul _)
    calc
      _ ≤ ∫ w, B + (Real.cos a * |t|) * |X w - Y w| ∂ν := by
        apply norm_integral_le_of_norm_le hIG
        exact Filter.Eventually.of_forall fun w => by
          have hp := norm_phase_sub_le_capped t (X w) (Y w)
          have ht := capped_sine_tangent ha0 hcap
            (show 0 ≤ |t| * |X w - Y w| / 2 by positivity)
          dsimp only [B]
          nlinarith only [hp, ht]
      _ = B + (Real.cos a * |t|) * (∫ w, |X w - Y w| ∂ν) := by
        rw [integral_add (integrable_const B) (hD.const_mul _), integral_const, integral_const_mul]
        simp only [probReal_univ, one_smul]
      _ ≤ B + (Real.cos a * |t|) * R :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hcost (mul_nonneg hc (abs_nonneg t)))
      _ = 2 * Real.sin (R * |t| / 2) := by dsimp only [B, a]; ring
  · rw [min_eq_right (le_of_not_ge hcap), Real.sin_pi_div_two]
    calc
      _ ≤ ∫ _ : Ω, (2 : ℝ) ∂ν := by
        apply norm_integral_le_of_norm_le (integrable_const (2 : ℝ))
        exact Filter.Eventually.of_forall fun w => by
          rw [norm_phase_sub]
          nlinarith only [Real.abs_sin_le_one (t * (X w - Y w) / 2)]
      _ = _ := by simp

end BerryEsseen.CouplingSinePrice

#print axioms BerryEsseen.CouplingSinePrice.capped_sine_tangent
#print axioms BerryEsseen.CouplingSinePrice.norm_phase_sub_le_capped
#print axioms BerryEsseen.CouplingSinePrice.norm_integral_difference_le
