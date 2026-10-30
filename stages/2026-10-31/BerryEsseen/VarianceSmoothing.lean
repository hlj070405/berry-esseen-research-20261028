module

public import BerryEsseen.VarianceEqualization

@[expose] public section

/-!
Partial two-coordinate variance smoothing. At fixed average amplitude,
the true four-atom price decreases with its nonnegative spread. The
proof compares the three active formulas directly, with their common
activation boundary retained.
-/

namespace BerryEsseen.TwoMoment

open MeasureTheory
open scoped ENNReal

noncomputable section

private lemma spread_denominator_pos (b m d : ℝ)
    (hb : 0 < b) (hd : 0 ≤ d) (hdm : d ≤ m) :
    0 < (b + m) ^ 2 - d ^ 2 := by
  have hp : 0 < (b + m - d) * (b + m + d) := mul_pos (by linarith) (by linarith)
  nlinarith only [hp]

private lemma spreadPrice_of_le_lower (b m d c : ℝ)
    (hb : 0 < b) (hd : 0 ≤ d) (hdm : d ≤ m) (hc : c ≤ -2 * m) :
    spreadPairPrice b m d c = 2 * b * m + c ^ 2 := by
  have hD := spread_denominator_pos b m d hb hd hdm
  unfold spreadPairPrice
  rw [max_eq_left (by linarith : 0 ≤ -2 * m - c),
    max_eq_left (by linarith : 0 ≤ b - m - d - c),
    max_eq_left (by linarith : 0 ≤ b - m + d - c),
    max_eq_left (by linarith : 0 ≤ 2 * b - c)]
  apply (div_eq_iff hD.ne').mpr
  ring

private lemma spreadPrice_of_upper_le (b m d c : ℝ)
    (hb : 0 < b) (hd : 0 ≤ d) (hdm : d ≤ m) (hc : 2 * b ≤ c) :
    spreadPairPrice b m d c = 0 := by
  have hm := hd.trans hdm
  unfold spreadPairPrice
  rw [max_eq_right (by linarith : -2 * m - c ≤ 0),
    max_eq_right (by linarith : b - m - d - c ≤ 0),
    max_eq_right (by linarith : b - m + d - c ≤ 0),
    max_eq_right (by linarith : 2 * b - c ≤ 0)]
  simp

private lemma spreadPrice_of_both_cross (b m d c : ℝ)
    (hb : 0 < b) (hd : 0 ≤ d) (hdm : d ≤ m)
    (hlow : -2 * m ≤ c) (hcross : c ≤ b - m - d) :
    spreadPairPrice b m d c = 2 * b * m + c ^ 2 -
      b ^ 2 * (2 * m + c) ^ 2 / ((b + m) ^ 2 - d ^ 2) := by
  have hD := spread_denominator_pos b m d hb hd hdm
  unfold spreadPairPrice
  rw [max_eq_right (by linarith : -2 * m - c ≤ 0),
    max_eq_left (by linarith : 0 ≤ b - m - d - c),
    max_eq_left (by linarith : 0 ≤ b - m + d - c),
    max_eq_left (by linarith : 0 ≤ 2 * b - c)]
  field_simp [hD.ne'] ; ring

/-- The active middle formula, after cancelling the lower-amplitude
factor from the true four-atom expectation. -/
def smoothingMiddlePrice (b m d c : ℝ) : ℝ :=
  (m + d) * ((b - c) ^ 2 + b * (m - d)) / (b + m + d)

private lemma spreadPrice_of_one_cross (b m d c : ℝ)
    (hb : 0 < b) (hd : 0 ≤ d) (hdm : d ≤ m)
    (hlow : b - m - d ≤ c) (hhigh : c ≤ b - m + d) :
    spreadPairPrice b m d c = smoothingMiddlePrice b m d c := by
  have hD := spread_denominator_pos b m d hb hd hdm
  have hplus : 0 < b + m + d := by linarith
  unfold spreadPairPrice smoothingMiddlePrice
  rw [max_eq_right (by linarith : -2 * m - c ≤ 0),
    max_eq_right (by linarith : b - m - d - c ≤ 0),
    max_eq_left (by linarith : 0 ≤ b - m + d - c),
    max_eq_left (by linarith : 0 ≤ 2 * b - c)]
  field_simp [hD.ne', hplus.ne'] ; ring

private lemma spreadPrice_of_top (b m d c : ℝ)
    (hb : 0 < b) (hd : 0 ≤ d) (hdm : d ≤ m)
    (hlow : b - m + d ≤ c) (hhigh : c ≤ 2 * b) :
    spreadPairPrice b m d c =
      (m ^ 2 - d ^ 2) * (2 * b - c) ^ 2 / ((b + m) ^ 2 - d ^ 2) := by
  have hm := hd.trans hdm
  unfold spreadPairPrice
  rw [max_eq_right (by linarith : -2 * m - c ≤ 0),
    max_eq_right (by linarith : b - m - d - c ≤ 0),
    max_eq_right (by linarith : b - m + d - c ≤ 0),
    max_eq_left (by linarith : 0 ≤ 2 * b - c)]
  simp

private lemma both_cross_formula_mono (b m d₁ d₂ c : ℝ)
    (hb : 0 < b) (hd₂ : 0 ≤ d₂) (h₂₁ : d₂ ≤ d₁) (h₁m : d₁ ≤ m) :
    2 * b * m + c ^ 2 - b ^ 2 * (2 * m + c) ^ 2 / ((b + m) ^ 2 - d₁ ^ 2) ≤
      2 * b * m + c ^ 2 - b ^ 2 * (2 * m + c) ^ 2 / ((b + m) ^ 2 - d₂ ^ 2) := by
  have hd₁ := hd₂.trans h₂₁
  have hD₁ := spread_denominator_pos b m d₁ hb hd₁ h₁m
  have hden : (b + m) ^ 2 - d₁ ^ 2 ≤ (b + m) ^ 2 - d₂ ^ 2 := by
    have hsq := (sq_le_sq₀ hd₂ hd₁).mpr h₂₁
    linarith
  have hnum : 0 ≤ b ^ 2 * (2 * m + c) ^ 2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hf := div_le_div_of_nonneg_left hnum hD₁ hden
  linarith

private lemma top_formula_mono (b m d₁ d₂ c : ℝ)
    (hb : 0 < b) (hd₂ : 0 ≤ d₂) (h₂₁ : d₂ ≤ d₁) (h₁m : d₁ ≤ m) :
    (m ^ 2 - d₁ ^ 2) * (2 * b - c) ^ 2 / ((b + m) ^ 2 - d₁ ^ 2) ≤
      (m ^ 2 - d₂ ^ 2) * (2 * b - c) ^ 2 / ((b + m) ^ 2 - d₂ ^ 2) := by
  have hd₁ := hd₂.trans h₂₁
  have hm := hd₁.trans h₁m
  have hD₁ := spread_denominator_pos b m d₁ hb hd₁ h₁m
  have hD₂ := spread_denominator_pos b m d₂ hb hd₂ (h₂₁.trans h₁m)
  have hsq : 0 ≤ d₁ ^ 2 - d₂ ^ 2 := sub_nonneg.mpr ((sq_le_sq₀ hd₂ hd₁).mpr h₂₁)
  have hcoef : 0 ≤ b * (b + 2 * m) := mul_nonneg hb.le (by linarith)
  have hs : 0 ≤ b * (b + 2 * m) * (d₁ ^ 2 - d₂ ^ 2) * (2 * b - c) ^ 2 :=
    mul_nonneg (mul_nonneg hcoef hsq) (sq_nonneg _)
  apply (div_le_div_iff₀ hD₁ hD₂).mpr
  nlinarith only [hs]

private lemma middle_formula_mono (b m d₁ d₂ c : ℝ)
    (hb : 0 < b) (hd₂ : 0 ≤ d₂) (h₂₁ : d₂ ≤ d₁) (h₁m : d₁ ≤ m)
    (hlow : b - m - d₂ ≤ c) (hhigh : c ≤ b - m + d₂) :
    smoothingMiddlePrice b m d₁ c ≤ smoothingMiddlePrice b m d₂ c := by
  have hd₁ := hd₂.trans h₂₁
  have hm := hd₁.trans h₁m
  have hplus₁ : 0 < b + m + d₁ := by linarith
  have hplus₂ : 0 < b + m + d₂ := by linarith
  have hx : 0 ≤ d₂ - (b - m - c) := by linarith
  have hy : 0 ≤ d₂ + (b - m - c) + 2 * m := by linarith
  have hbd : 0 ≤ 2 * b * d₂ := mul_nonneg (mul_nonneg (by norm_num) hb.le) hd₂
  have hgap₀ := add_nonneg (mul_nonneg hx hy) hbd
  have hgap₁ := mul_nonneg (sub_nonneg.mpr h₂₁) hplus₂.le
  have hgap : 0 ≤ (b + m + d₁) * (b + m + d₂) -
      ((b - c) ^ 2 + 2 * b * m + b ^ 2) := by
    nlinarith only [hgap₀, hgap₁]
  have hs := mul_nonneg (mul_nonneg hb.le (sub_nonneg.mpr h₂₁)) hgap
  unfold smoothingMiddlePrice
  apply (div_le_div_iff₀ hplus₁ hplus₂).mpr
  nlinarith only [hs]

private lemma spreadPrice_mono_both_cross (b m d₁ d₂ c : ℝ)
    (hb : 0 < b) (hd₂ : 0 ≤ d₂) (h₂₁ : d₂ ≤ d₁) (h₁m : d₁ ≤ m)
    (hlow : -2 * m ≤ c) (hcross : c ≤ b - m - d₁) :
    spreadPairPrice b m d₁ c ≤ spreadPairPrice b m d₂ c := by
  rw [spreadPrice_of_both_cross b m d₁ c hb (hd₂.trans h₂₁) h₁m hlow hcross,
    spreadPrice_of_both_cross b m d₂ c hb hd₂ (h₂₁.trans h₁m) hlow (by linarith)]
  exact both_cross_formula_mono b m d₁ d₂ c hb hd₂ h₂₁ h₁m

private lemma spreadPrice_mono_top (b m d₁ d₂ c : ℝ)
    (hb : 0 < b) (hd₂ : 0 ≤ d₂) (h₂₁ : d₂ ≤ d₁) (h₁m : d₁ ≤ m)
    (hlow : b - m + d₁ ≤ c) (hhigh : c ≤ 2 * b) :
    spreadPairPrice b m d₁ c ≤ spreadPairPrice b m d₂ c := by
  rw [spreadPrice_of_top b m d₁ c hb (hd₂.trans h₂₁) h₁m hlow hhigh,
    spreadPrice_of_top b m d₂ c hb hd₂ (h₂₁.trans h₁m) (by linarith) hhigh]
  exact top_formula_mono b m d₁ d₂ c hb hd₂ h₂₁ h₁m

private lemma spreadPrice_mono_one_cross (b m d₁ d₂ c : ℝ)
    (hb : 0 < b) (hd₂ : 0 ≤ d₂) (h₂₁ : d₂ ≤ d₁) (h₁m : d₁ ≤ m)
    (hlow : b - m - d₂ ≤ c) (hhigh : c ≤ b - m + d₂) :
    spreadPairPrice b m d₁ c ≤ spreadPairPrice b m d₂ c := by
  rw [spreadPrice_of_one_cross b m d₁ c hb (hd₂.trans h₂₁) h₁m (by linarith) (by linarith),
    spreadPrice_of_one_cross b m d₂ c hb hd₂ (h₂₁.trans h₁m) hlow hhigh]
  exact middle_formula_mono b m d₁ d₂ c hb hd₂ h₂₁ h₁m hlow hhigh

/-- At fixed average amplitude the squared-positive-part expectation is
nonincreasing in spread. This is arbitrary partial smoothing, including
zero variances and every activation boundary. -/
theorem spreadPairPrice_antitone_spread (b m d₁ d₂ c : ℝ)
    (hb : 0 < b) (hd₂ : 0 ≤ d₂) (h₂₁ : d₂ ≤ d₁) (h₁m : d₁ ≤ m) :
    spreadPairPrice b m d₁ c ≤ spreadPairPrice b m d₂ c := by
  have hd₁ := hd₂.trans h₂₁
  have h₂m := h₂₁.trans h₁m
  by_cases hlow : c ≤ -2 * m
  · rw [spreadPrice_of_le_lower b m d₁ c hb hd₁ h₁m hlow,
      spreadPrice_of_le_lower b m d₂ c hb hd₂ h₂m hlow]
  by_cases hhigh : 2 * b ≤ c
  · rw [spreadPrice_of_upper_le b m d₁ c hb hd₁ h₁m hhigh,
      spreadPrice_of_upper_le b m d₂ c hb hd₂ h₂m hhigh]
  have hlow' : -2 * m ≤ c := by linarith
  have hhigh' : c ≤ 2 * b := by linarith
  set x := b - m - c with hx
  by_cases hx0 : 0 ≤ x
  · by_cases h₁x : d₁ ≤ x
    · exact spreadPrice_mono_both_cross b m d₁ d₂ c hb hd₂ h₂₁ h₁m hlow' (by linarith)
    by_cases hx₂ : x ≤ d₂
    · exact spreadPrice_mono_one_cross b m d₁ d₂ c hb hd₂ h₂₁ h₁m (by linarith) (by linarith)
    have hxm : x ≤ m := by linarith
    have h₂x : d₂ ≤ x := by linarith
    have hx₁ : x ≤ d₁ := by linarith
    exact (spreadPrice_mono_one_cross b m d₁ x c hb hx0 hx₁ h₁m
      (by linarith) (by linarith)).trans
        (spreadPrice_mono_both_cross b m x d₂ c hb hd₂ h₂x hxm hlow' (by linarith))
  · have hnx : 0 ≤ -x := by linarith
    by_cases h₁x : d₁ ≤ -x
    · exact spreadPrice_mono_top b m d₁ d₂ c hb hd₂ h₂₁ h₁m (by linarith) hhigh'
    by_cases hx₂ : -x ≤ d₂
    · exact spreadPrice_mono_one_cross b m d₁ d₂ c hb hd₂ h₂₁ h₁m (by linarith) (by linarith)
    have hxm : -x ≤ m := by linarith
    have h₂x : d₂ ≤ -x := by linarith
    have hx₁ : -x ≤ d₁ := by linarith
    exact (spreadPrice_mono_one_cross b m d₁ (-x) c hb hnx hx₁ h₁m
      (by linarith) (by linarith)).trans
        (spreadPrice_mono_top b m (-x) d₂ c hb hd₂ h₂x hxm (by linarith) hhigh')

private lemma pairPrice_le_smoothed_of_sorted (b x y u v c : ℝ)
    (hb : 0 < b) (hx : 0 ≤ x) (hxy : x ≤ y) (_hu : 0 ≤ u) (huv : u ≤ v)
    (hsum : x + y = u + v) (hprod : x * y ≤ u * v) :
    pairPrice b x y c ≤ pairPrice b u v c := by
  let m := (x + y) / 2
  let d₁ := (y - x) / 2
  let d₂ := (v - u) / 2
  have hd₁ : 0 ≤ d₁ := by dsimp [d₁]; linarith
  have hd₂ : 0 ≤ d₂ := by dsimp [d₂]; linarith
  have h₁m : d₁ ≤ m := by dsimp [d₁, m]; linarith
  have hsum_sq : (x + y) ^ 2 = (u + v) ^ 2 := congrArg (fun t : ℝ => t ^ 2) hsum
  have hsq : d₂ ^ 2 ≤ d₁ ^ 2 := by
    dsimp [d₁, d₂]
    nlinarith only [hprod, hsum_sq]
  have h₂₁ : d₂ ≤ d₁ := (sq_le_sq₀ hd₂ hd₁).mp hsq
  have hx' : m - d₁ = x := by dsimp [m, d₁]; ring
  have hy' : m + d₁ = y := by dsimp [m, d₁]; ring
  have hu' : m - d₂ = u := by dsimp [m, d₂]; linarith
  have hv' : m + d₂ = v := by dsimp [m, d₂]; linarith
  have hold := pairPrice_eq_spreadPairPrice b m d₁ c
  have hnew := pairPrice_eq_spreadPairPrice b m d₂ c
  rw [hx', hy'] at hold
  rw [hu', hv'] at hnew
  rw [hold, hnew]
  exact spreadPairPrice_antitone_spread b m d₁ d₂ c hb hd₂ h₂₁ h₁m

/-- For two nonnegative amplitudes at fixed sum, increasing their product
means moving them closer together, and increases the true reference price. -/
theorem pairPrice_le_smoothed (b x y u v c : ℝ)
    (hb : 0 < b) (hx : 0 ≤ x) (hy : 0 ≤ y) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hsum : x + y = u + v) (hprod : x * y ≤ u * v) :
    pairPrice b x y c ≤ pairPrice b u v c := by
  rcases le_total x y with hxy | hyx
  · rcases le_total u v with huv | hvu
    · exact pairPrice_le_smoothed_of_sorted b x y u v c hb hx hxy hu huv hsum hprod
    · calc
        pairPrice b x y c ≤ pairPrice b v u c :=
          pairPrice_le_smoothed_of_sorted b x y v u c hb hx hxy hv hvu
            (by linarith) (by simpa only [mul_comm v u] using hprod)
        _ = pairPrice b u v c := pairPrice_comm b v u c
  · rcases le_total u v with huv | hvu
    · calc
        pairPrice b x y c = pairPrice b y x c := pairPrice_comm b x y c
        _ ≤ pairPrice b u v c :=
          pairPrice_le_smoothed_of_sorted b y x u v c hb hy hyx hu huv
            (by linarith) (by simpa only [mul_comm y x] using hprod)
    · calc
        pairPrice b x y c = pairPrice b y x c := pairPrice_comm b x y c
        _ ≤ pairPrice b v u c :=
          pairPrice_le_smoothed_of_sorted b y x v u c hb hy hyx hv hvu
            (by linarith) (by simpa only [mul_comm y x, mul_comm v u] using hprod)
        _ = pairPrice b u v c := pairPrice_comm b v u c

/-- Arbitrary two-coordinate variance smoothing for genuine independent
two-point laws. The total variance stays fixed; its product increases. -/
theorem lintegral_reference_pair_le_smoothed (b z₁ z₂ w₁ w₂ c : ℝ)
    (hb : 0 < b) (hz₁ : 0 ≤ z₁) (hz₂ : 0 ≤ z₂) (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂)
    (hsum : z₁ + z₂ = w₁ + w₂) (hprod : z₁ * z₂ ≤ w₁ * w₂) :
    (∫⁻ p : ℝ × ℝ, ENNReal.ofReal ((max (p.1 + p.2 - c) 0) ^ 2)
      ∂(referenceLaw b z₁).prod (referenceLaw b z₂)) ≤
      ∫⁻ p : ℝ × ℝ, ENNReal.ofReal ((max (p.1 + p.2 - c) 0) ^ 2)
        ∂(referenceLaw b w₁).prod (referenceLaw b w₂) := by
  have hx := div_nonneg hz₁ hb.le
  have hy := div_nonneg hz₂ hb.le
  have hu := div_nonneg hw₁ hb.le
  have hv := div_nonneg hw₂ hb.le
  have hsum' : z₁ / b + z₂ / b = w₁ / b + w₂ / b := by
    rw [← add_div, ← add_div, hsum]
  have hprod' : (z₁ / b) * (z₂ / b) ≤ (w₁ / b) * (w₂ / b) := by
    simpa only [div_mul_div_comm, pow_two] using
      div_le_div_of_nonneg_right hprod (sq_nonneg b)
  have hzx : b * (z₁ / b) = z₁ := by field_simp [hb.ne']
  have hzy : b * (z₂ / b) = z₂ := by field_simp [hb.ne']
  have hwu : b * (w₁ / b) = w₁ := by field_simp [hb.ne']
  have hwv : b * (w₂ / b) = w₂ := by field_simp [hb.ne']
  have hold := lintegral_reference_pair_eq_ofReal_pairPrice b (z₁ / b) (z₂ / b) c hb hx hy
  have hnew := lintegral_reference_pair_eq_ofReal_pairPrice b (w₁ / b) (w₂ / b) c hb hu hv
  rw [hzx, hzy] at hold
  rw [hwu, hwv] at hnew
  rw [hold, hnew]
  exact ENNReal.ofReal_le_ofReal
    (pairPrice_le_smoothed b (z₁ / b) (z₂ / b) (w₁ / b) (w₂ / b) c hb
      hx hy hu hv hsum' hprod')

theorem squarePositiveOrder_reference_pair_smoothed (b z₁ z₂ w₁ w₂ : ℝ)
    (hb : 0 < b) (hz₁ : 0 ≤ z₁) (hz₂ : 0 ≤ z₂) (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂)
    (hsum : z₁ + z₂ = w₁ + w₂) (hprod : z₁ * z₂ ≤ w₁ * w₂) :
    SquarePositiveOrder
      (((referenceLaw b z₁).prod (referenceLaw b z₂)).map (fun p => p.1 + p.2))
      (((referenceLaw b w₁).prod (referenceLaw b w₂)).map (fun p => p.1 + p.2)) := by
  intro c
  have hm : Measurable (fun x : ℝ => ENNReal.ofReal ((max (x - c) 0) ^ 2)) := by fun_prop
  have hadd : Measurable (fun p : ℝ × ℝ => p.1 + p.2) := by fun_prop
  rw [lintegral_map hm hadd, lintegral_map hm hadd]
  exact lintegral_reference_pair_le_smoothed b z₁ z₂ w₁ w₂ c hb hz₁ hz₂ hw₁ hw₂ hsum hprod

/-- A finite-algorithm step: moving either of two bracketing variances
exactly to `t` preserves the total and leaves the other variance nonnegative. -/
theorem squarePositiveOrder_reference_pair_move_to_target (b z₁ z₂ t : ℝ)
    (hb : 0 < b) (hz₁ : 0 ≤ z₁) (h₁t : z₁ ≤ t) (ht₂ : t ≤ z₂) :
    0 ≤ z₁ + z₂ - t ∧
      SquarePositiveOrder
        (((referenceLaw b z₁).prod (referenceLaw b z₂)).map (fun p => p.1 + p.2))
        (((referenceLaw b t).prod (referenceLaw b (z₁ + z₂ - t))).map (fun p => p.1 + p.2)) := by
  have hrest : 0 ≤ z₁ + z₂ - t := by linarith
  constructor
  · exact hrest
  · apply squarePositiveOrder_reference_pair_smoothed b z₁ z₂ t (z₁ + z₂ - t) hb hz₁
      (by linarith) (by linarith) hrest (by ring)
    nlinarith [mul_nonneg (sub_nonneg.mpr h₁t) (sub_nonneg.mpr ht₂)]

end

end BerryEsseen.TwoMoment

#print axioms BerryEsseen.TwoMoment.spreadPairPrice_antitone_spread
#print axioms BerryEsseen.TwoMoment.pairPrice_le_smoothed
#print axioms BerryEsseen.TwoMoment.lintegral_reference_pair_le_smoothed
#print axioms BerryEsseen.TwoMoment.squarePositiveOrder_reference_pair_move_to_target
