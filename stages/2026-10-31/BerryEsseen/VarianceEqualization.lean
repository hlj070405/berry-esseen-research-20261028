module

public import BerryEsseen.TwoMomentProduct
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-!
The two-coordinate squared-positive-part variance equalization. The
algebra retains every activation boundary. The reference measures are
the genuine two-point measures from `TwoMomentProduct`.
-/

namespace BerryEsseen.TwoMoment

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- Four-atom price in lower-amplitude coordinates: the variances are
`b * x` and `b * y` and the upper endpoint of both summands is `b`. -/
def pairPrice (b x y c : ℝ) : ℝ :=
  (b ^ 2 * (max (-x - y - c) 0) ^ 2 +
    b * x * (max (b - y - c) 0) ^ 2 +
    b * y * (max (b - x - c) 0) ^ 2 +
    x * y * (max (2 * b - c) 0) ^ 2) / ((b + x) * (b + y))

/-- The same price with fixed average amplitude `m` and spread `d`. -/
def spreadPairPrice (b m d c : ℝ) : ℝ :=
  (b ^ 2 * (max (-2 * m - c) 0) ^ 2 +
    b * (m - d) * (max (b - m - d - c) 0) ^ 2 +
    b * (m + d) * (max (b - m + d - c) 0) ^ 2 +
    (m ^ 2 - d ^ 2) * (max (2 * b - c) 0) ^ 2) / ((b + m) ^ 2 - d ^ 2)

lemma pairPrice_eq_spreadPairPrice (b m d c : ℝ) :
    pairPrice b (m - d) (m + d) c = spreadPairPrice b m d c := by
  have hlow : -(m - d) - (m + d) - c = -2 * m - c := by ring
  have h₁ : b - (m + d) - c = b - m - d - c := by ring
  have h₂ : b - (m - d) - c = b - m + d - c := by ring
  unfold pairPrice spreadPairPrice
  rw [hlow, h₁, h₂]
  congr 1 <;> ring

lemma pairPrice_comm (b x y c : ℝ) : pairPrice b x y c = pairPrice b y x c := by
  have hlow : -x - y - c = -y - x - c := by ring
  unfold pairPrice
  rw [hlow, mul_comm (b + x) (b + y)]
  congr 1
  ring

/-- Two-item full equalization, proved on all six activation intervals.
In particular, either input variance is allowed to be zero. -/
theorem spreadPairPrice_le_equalized (b m d c : ℝ)
    (hb : 0 < b) (hd : 0 ≤ d) (hdm : d ≤ m) :
    spreadPairPrice b m d c ≤ spreadPairPrice b m 0 c := by
  have hm : 0 ≤ m := hd.trans hdm
  have hbm : 0 ≤ b + m := by linarith
  have hbm₂ : 0 ≤ b + 2 * m := by linarith
  have hα : 0 ≤ m - d := sub_nonneg.mpr hdm
  have hB : 0 < b + m - d := by linarith
  have hA : 0 < (b + m) ^ 2 := sq_pos_of_pos (by linarith)
  have hD : 0 < (b + m) ^ 2 - d ^ 2 := by
    have hp : 0 < (b + m - d) * (b + m + d) := mul_pos hB (by linarith)
    nlinarith only [hp]
  unfold spreadPairPrice
  simp only [sub_zero, add_zero, zero_pow (by decide : 2 ≠ 0)]
  by_cases hlow : c ≤ -2 * m
  · simp only [max_eq_left (by linarith : 0 ≤ -2 * m - c),
      max_eq_left (by linarith : 0 ≤ b - m - d - c),
      max_eq_left (by linarith : 0 ≤ b - m + d - c),
      max_eq_left (by linarith : 0 ≤ b - m - c),
      max_eq_left (by linarith : 0 ≤ 2 * b - c)]
    apply (div_le_div_iff₀ hD hA).mpr
    apply le_of_eq
    ring
  by_cases hhigh : 2 * b ≤ c
  · simp only [max_eq_right (by linarith : -2 * m - c ≤ 0),
      max_eq_right (by linarith : b - m - d - c ≤ 0),
      max_eq_right (by linarith : b - m + d - c ≤ 0),
      max_eq_right (by linarith : b - m - c ≤ 0),
      max_eq_right (by linarith : 2 * b - c ≤ 0), zero_pow (by decide : 2 ≠ 0),
      mul_zero, add_zero, zero_div, le_refl]
  have hzero : -2 * m - c ≤ 0 := by linarith
  have htop : 0 ≤ 2 * b - c := by linarith
  by_cases h₁ : c ≤ b - m - d
  · simp only [max_eq_right hzero, max_eq_left htop,
      max_eq_left (by linarith : 0 ≤ b - m - d - c),
      max_eq_left (by linarith : 0 ≤ b - m + d - c),
      max_eq_left (by linarith : 0 ≤ b - m - c), zero_pow (by decide : 2 ≠ 0),
      mul_zero, zero_add]
    apply (div_le_div_iff₀ hD hA).mpr
    nlinarith only [sq_nonneg (b * d * (2 * m + c))]
  have hfirst : b - m - d - c ≤ 0 := by linarith
  by_cases h₂ : c ≤ b - m
  · simp only [max_eq_right hzero, max_eq_right hfirst, max_eq_left htop,
      max_eq_left (by linarith : 0 ≤ b - m + d - c),
      max_eq_left (by linarith : 0 ≤ b - m - c), zero_pow (by decide : 2 ≠ 0),
      mul_zero, zero_add]
    apply (div_le_div_iff₀ hD hA).mpr
    have hsos : 0 ≤ b * (b + m - d) *
        (((b + m) * d - m * (b - m - c)) ^ 2 + b * (m - d) * (b - m - c) ^ 2) :=
      mul_nonneg (mul_nonneg hb.le hB.le)
        (add_nonneg (sq_nonneg _) (mul_nonneg (mul_nonneg hb.le hα) (sq_nonneg _)))
    nlinarith only [hsos]
  have hmiddle : b - m - c ≤ 0 := by linarith
  by_cases h₃ : c ≤ b - m + d
  · simp only [max_eq_right hzero, max_eq_right hfirst, max_eq_right hmiddle,
      max_eq_left htop, max_eq_left (by linarith : 0 ≤ b - m + d - c),
      zero_pow (by decide : 2 ≠ 0), mul_zero, zero_add, add_zero]
    apply (div_le_div_iff₀ hD hA).mpr
    have hx : 0 ≤ -(b - m - c) := by linarith
    have hxd : 0 ≤ b - m - c + d := by linarith
    have hAx : 0 ≤ (b + m) + (b - m - c) := by linarith
    have hsum : 0 ≤ d * ((b + m) + (b - m - c)) +
        (b + m) * ((b - m - c) + d) :=
      add_nonneg (mul_nonneg hd hAx) (mul_nonneg hbm hxd)
    have hsos : 0 ≤ b * (b + m - d) *
        ((b + 2 * m) * (-(b - m - c)) *
          (d * ((b + m) + (b - m - c)) + (b + m) * ((b - m - c) + d)) +
          (b + m) ^ 2 * ((b - m - c) + d) ^ 2) :=
      mul_nonneg (mul_nonneg hb.le hB.le)
        (add_nonneg (mul_nonneg (mul_nonneg hbm₂ hx) hsum)
          (mul_nonneg (sq_nonneg _) (sq_nonneg _)))
    nlinarith only [hsos]
  · simp only [max_eq_right hzero, max_eq_right hfirst, max_eq_right hmiddle,
      max_eq_left htop, max_eq_right (by linarith : b - m + d - c ≤ 0),
      zero_pow (by decide : 2 ≠ 0), mul_zero, zero_add, add_zero]
    apply (div_le_div_iff₀ hD hA).mpr
    have hsos : 0 ≤ b * (b + 2 * m) * d ^ 2 * (2 * b - c) ^ 2 :=
      mul_nonneg (mul_nonneg (mul_nonneg hb.le hbm₂) (sq_nonneg _)) (sq_nonneg _)
    nlinarith only [hsos]

theorem pairPrice_le_equalized_of_le (b x y c : ℝ)
    (hb : 0 < b) (hx : 0 ≤ x) (hxy : x ≤ y) :
    pairPrice b x y c ≤ pairPrice b ((x + y) / 2) ((x + y) / 2) c := by
  let m := (x + y) / 2
  let d := (y - x) / 2
  have hd : 0 ≤ d := by dsimp [d]; linarith
  have hdm : d ≤ m := by dsimp [d, m]; linarith
  have hxm : m - d = x := by dsimp [m, d]; ring
  have hym : m + d = y := by dsimp [m, d]; ring
  have hsplit := pairPrice_eq_spreadPairPrice b m d c
  rw [hxm, hym] at hsplit
  have hbalance : pairPrice b m m c = spreadPairPrice b m 0 c := by
    simpa using pairPrice_eq_spreadPairPrice b m 0 c
  rw [hsplit, hbalance]
  exact spreadPairPrice_le_equalized b m d c hb hd hdm

theorem pairPrice_le_equalized (b x y c : ℝ)
    (hb : 0 < b) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    pairPrice b x y c ≤ pairPrice b ((x + y) / 2) ((x + y) / 2) c := by
  rcases le_total x y with hxy | hyx
  · exact pairPrice_le_equalized_of_le b x y c hb hx hxy
  · rw [pairPrice_comm b x y c]
    simpa only [add_comm y x] using pairPrice_le_equalized_of_le b y x c hb hy hyx

lemma integrable_reference_pair_squarePositivePart (b z₁ z₂ c : ℝ)
    (hb : 0 < b) (hz₁ : 0 ≤ z₁) (hz₂ : 0 ≤ z₂) :
    Integrable (fun p : ℝ × ℝ => (max (p.1 + p.2 - c) 0) ^ 2)
      ((referenceLaw b z₁).prod (referenceLaw b z₂)) := by
  have := referenceLaw_isProbabilityMeasure b z₁ hb hz₁
  have := referenceLaw_isProbabilityMeasure b z₂ hb hz₂
  have hfst := (integrable_referenceLaw b z₁ (fun x => x ^ 2)).comp_fst (referenceLaw b z₂)
  have hsnd := (integrable_referenceLaw b z₂ (fun x => x ^ 2)).comp_snd (referenceLaw b z₁)
  have hdom : Integrable (fun p : ℝ × ℝ => 3 * p.1 ^ 2 + 3 * p.2 ^ 2 + 3 * c ^ 2)
      ((referenceLaw b z₁).prod (referenceLaw b z₂)) := by
    convert ((hfst.const_mul 3).add (hsnd.const_mul 3)).add
      (integrable_const (3 * c ^ 2)) using 1
  have hm : Measurable (fun p : ℝ × ℝ => (max (p.1 + p.2 - c) 0) ^ 2) := by fun_prop
  apply hdom.mono' hm.aestronglyMeasurable
  filter_upwards [] with p
  change ‖(max (p.1 + p.2 - c) 0) ^ 2‖ ≤ 3 * p.1 ^ 2 + 3 * p.2 ^ 2 + 3 * c ^ 2
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hp := positivePart_sq_le_sq (p.1 + p.2 - c)
  nlinarith [sq_nonneg (p.1 - p.2), sq_nonneg (p.1 + c), sq_nonneg (p.2 + c)]

/-- The four-atom algebraic price is the ordinary expectation under the
genuine product reference measure. Its integrability is proved above. -/
theorem integral_reference_pair_eq_pairPrice (b x y c : ℝ)
    (hb : 0 < b) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (∫ p : ℝ × ℝ, (max (p.1 + p.2 - c) 0) ^ 2
      ∂(referenceLaw b (b * x)).prod (referenceLaw b (b * y))) = pairPrice b x y c := by
  have hzx : 0 ≤ b * x := mul_nonneg hb.le hx
  have hzy : 0 ≤ b * y := mul_nonneg hb.le hy
  have := referenceLaw_isProbabilityMeasure b (b * x) hb hzx
  have := referenceLaw_isProbabilityMeasure b (b * y) hb hzy
  rw [integral_prod _ (integrable_reference_pair_squarePositivePart b (b * x) (b * y) c hb hzx hzy),
    integral_referenceLaw b (b * x) hb hzx,
    integral_referenceLaw b (b * y) hb hzy, integral_referenceLaw b (b * y) hb hzy]
  dsimp only
  have hlowx : -(b * x) / b = -x := by field_simp [hb.ne']
  have hlowy : -(b * y) / b = -y := by field_simp [hb.ne']
  rw [hlowx, hlowy]
  rw [show b + b - c = 2 * b - c by ring,
    show b + -y - c = b - y - c by ring,
    show -x + b - c = b - x - c by ring,
    show -x + -y - c = -x - y - c by ring]
  have hbx : 0 < b + x := by linarith
  have hby : 0 < b + y := by linarith
  have hDx : 0 < b ^ 2 + b * x := add_pos_of_pos_of_nonneg (sq_pos_of_pos hb) hzx
  have hDy : 0 < b ^ 2 + b * y := add_pos_of_pos_of_nonneg (sq_pos_of_pos hb) hzy
  unfold pairPrice
  field_simp [hb.ne', hbx.ne', hby.ne', hDx.ne', hDy.ne'] ; ring

theorem lintegral_reference_pair_eq_ofReal_pairPrice (b x y c : ℝ)
    (hb : 0 < b) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (∫⁻ p : ℝ × ℝ, ENNReal.ofReal ((max (p.1 + p.2 - c) 0) ^ 2)
      ∂(referenceLaw b (b * x)).prod (referenceLaw b (b * y))) =
        ENNReal.ofReal (pairPrice b x y c) := by
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable_reference_pair_squarePositivePart b (b * x) (b * y) c hb
      (mul_nonneg hb.le hx) (mul_nonneg hb.le hy))
    (Filter.Eventually.of_forall (fun p => sq_nonneg _)),
    integral_reference_pair_eq_pairPrice b x y c hb hx hy]

/-- Full two-item variance equalization under a genuine product measure,
with fixed common upper endpoint. Both input variances may vanish. -/
theorem lintegral_reference_pair_le_equalized (b z₁ z₂ c : ℝ)
    (hb : 0 < b) (hz₁ : 0 ≤ z₁) (hz₂ : 0 ≤ z₂) :
    (∫⁻ p : ℝ × ℝ, ENNReal.ofReal ((max (p.1 + p.2 - c) 0) ^ 2)
      ∂(referenceLaw b z₁).prod (referenceLaw b z₂)) ≤
    ∫⁻ p : ℝ × ℝ, ENNReal.ofReal ((max (p.1 + p.2 - c) 0) ^ 2)
      ∂(referenceLaw b ((z₁ + z₂) / 2)).prod (referenceLaw b ((z₁ + z₂) / 2)) := by
  have hx : 0 ≤ z₁ / b := div_nonneg hz₁ hb.le
  have hy : 0 ≤ z₂ / b := div_nonneg hz₂ hb.le
  have hm : 0 ≤ (z₁ / b + z₂ / b) / 2 := by positivity
  have hzx : b * (z₁ / b) = z₁ := by field_simp [hb.ne']
  have hzy : b * (z₂ / b) = z₂ := by field_simp [hb.ne']
  have hzm : b * ((z₁ / b + z₂ / b) / 2) = (z₁ + z₂) / 2 := by
    field_simp [hb.ne']
  have horig := lintegral_reference_pair_eq_ofReal_pairPrice b (z₁ / b) (z₂ / b) c hb hx hy
  have hbal := lintegral_reference_pair_eq_ofReal_pairPrice b
    ((z₁ / b + z₂ / b) / 2) ((z₁ / b + z₂ / b) / 2) c hb hm hm
  rw [hzx, hzy] at horig
  rw [hzm] at hbal
  rw [horig, hbal]
  exact ENNReal.ofReal_le_ofReal (pairPrice_le_equalized b (z₁ / b) (z₂ / b) c hb hx hy)

/-- Measure-order form, ready for independent addition of the unchanged
remaining coordinates. This theorem concerns two-coordinate equalization. -/
theorem squarePositiveOrder_reference_pair_equalized (b z₁ z₂ : ℝ)
    (hb : 0 < b) (hz₁ : 0 ≤ z₁) (hz₂ : 0 ≤ z₂) :
    SquarePositiveOrder
      (((referenceLaw b z₁).prod (referenceLaw b z₂)).map (fun p => p.1 + p.2))
      (((referenceLaw b ((z₁ + z₂) / 2)).prod
        (referenceLaw b ((z₁ + z₂) / 2))).map (fun p => p.1 + p.2)) := by
  intro c
  have hm : Measurable (fun x : ℝ => ENNReal.ofReal ((max (x - c) 0) ^ 2)) := by fun_prop
  have hadd : Measurable (fun p : ℝ × ℝ => p.1 + p.2) := by fun_prop
  rw [lintegral_map hm hadd, lintegral_map hm hadd]
  exact lintegral_reference_pair_le_equalized b z₁ z₂ c hb hz₁ hz₂

end

end BerryEsseen.TwoMoment

#print axioms BerryEsseen.TwoMoment.spreadPairPrice_le_equalized
#print axioms BerryEsseen.TwoMoment.pairPrice_le_equalized
#print axioms BerryEsseen.TwoMoment.integral_reference_pair_eq_pairPrice
#print axioms BerryEsseen.TwoMoment.lintegral_reference_pair_le_equalized
#print axioms BerryEsseen.TwoMoment.squarePositiveOrder_reference_pair_equalized
