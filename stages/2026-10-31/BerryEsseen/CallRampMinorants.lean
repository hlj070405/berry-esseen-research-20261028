module

public import BerryEsseen.TwoMomentProduct

@[expose] public section

/-! 2026-10-30: pointwise call and ramp minorants and their real integral forms.
The measure is arbitrary. Integrability and genuine moment/price bounds are
explicit hypotheses; no two-point or standardized-law assumption is used. -/

noncomputable section

namespace BerryEsseen.CallRampMinorants

open MeasureTheory Set

/-- A quartic minorant of the positive part, tangent at `-a` and `b`. -/
def callPolynomial (a b x : ℝ) : ℝ :=
  x * (x + a) ^ 2 * (a + 3 * b - 2 * x) / (a + b) ^ 3

/-- The positive ramp includes its right endpoint and excludes zero. -/
def positiveRamp (g x : ℝ) : ℝ :=
  if 0 < x ∧ x ≤ g then g - x else 0

/-- The negative ramp includes zero and excludes its right endpoint. -/
def negativeRamp (g x : ℝ) : ℝ :=
  if 0 ≤ x ∧ x < g then x else 0

def upperTail (g x : ℝ) : ℝ := if g ≤ x then x else 0

lemma callPolynomial_expansion (a b x : ℝ) :
    callPolynomial a b x =
      (a ^ 2 * (a + 3 * b) * x + 6 * a * b * x ^ 2 +
        3 * (b - a) * x ^ 3 - 2 * x ^ 4) / (a + b) ^ 3 := by
  unfold callPolynomial
  congr 1
  ring

lemma callPolynomial_gap (a b x : ℝ) (hab : a + b ≠ 0) :
    x - callPolynomial a b x =
      x * (x - b) ^ 2 * (3 * a + b + 2 * x) / (a + b) ^ 3 := by
  unfold callPolynomial
  field_simp [hab]
  ring

theorem callPolynomial_le_positivePart (a b x : ℝ) (ha : 0 < a) (hb : 0 < b) :
    callPolynomial a b x ≤ max x 0 := by
  have hd : 0 < (a + b) ^ 3 := by positivity
  by_cases hx : 0 ≤ x
  · rw [max_eq_left hx]
    have hgap := callPolynomial_gap a b x (by positivity)
    have hn : 0 ≤ x * (x - b) ^ 2 * (3 * a + b + 2 * x) := by positivity
    have := div_nonneg hn hd.le
    linarith
  · have hx' : x ≤ 0 := (lt_of_not_ge hx).le
    rw [max_eq_right hx']
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hx' (sq_nonneg _))
        (by linarith)) hd.le

lemma integrable_callPolynomial (ν : Measure ℝ) (a b : ℝ)
    (h1 : Integrable (fun x : ℝ => x) ν)
    (h2 : Integrable (fun x : ℝ => x ^ 2) ν)
    (h3 : Integrable (fun x : ℝ => x ^ 3) ν)
    (h4 : Integrable (fun x : ℝ => x ^ 4) ν) :
    Integrable (callPolynomial a b) ν := by
  have hi := (((h1.const_mul (a ^ 2 * (a + 3 * b))).add
    (h2.const_mul (6 * a * b))).add (h3.const_mul (3 * (b - a)))).sub
      (h4.const_mul 2)
  convert hi.div_const ((a + b) ^ 3) using 1
  funext x
  exact callPolynomial_expansion a b x

theorem integral_callPolynomial (ν : Measure ℝ) (a b : ℝ)
    (h1 : Integrable (fun x : ℝ => x) ν)
    (h2 : Integrable (fun x : ℝ => x ^ 2) ν)
    (h3 : Integrable (fun x : ℝ => x ^ 3) ν)
    (h4 : Integrable (fun x : ℝ => x ^ 4) ν) :
    (∫ x, callPolynomial a b x ∂ν) =
      (a ^ 2 * (a + 3 * b) * (∫ x : ℝ, x ∂ν) +
        6 * a * b * (∫ x : ℝ, x ^ 2 ∂ν) +
        3 * (b - a) * (∫ x : ℝ, x ^ 3 ∂ν) -
        2 * (∫ x : ℝ, x ^ 4 ∂ν)) / (a + b) ^ 3 := by
  simp_rw [callPolynomial_expansion]
  have hA : Integrable (fun x : ℝ => a ^ 2 * (a + 3 * b) * x) ν := h1.const_mul _
  have hB : Integrable (fun x : ℝ => 6 * a * b * x ^ 2) ν := h2.const_mul _
  have hC : Integrable (fun x : ℝ => 3 * (b - a) * x ^ 3) ν := h3.const_mul _
  have hD : Integrable (fun x : ℝ => 2 * x ^ 4) ν := h4.const_mul _
  have hAB : Integrable (fun x : ℝ =>
      a ^ 2 * (a + 3 * b) * x + 6 * a * b * x ^ 2) ν := hA.add hB
  have hABC : Integrable (fun x : ℝ =>
      a ^ 2 * (a + 3 * b) * x + 6 * a * b * x ^ 2 + 3 * (b - a) * x ^ 3) ν := hAB.add hC
  rw [integral_div, integral_sub hABC hD, integral_add hAB hC, integral_add hA hB]
  simp only [integral_const_mul]
  rw [integral_const_mul (a ^ 2 * (a + 3 * b)) (fun x : ℝ => x)]

theorem integral_callPolynomial_le_positivePart (ν : Measure ℝ) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hP : Integrable (callPolynomial a b) ν)
    (hplus : Integrable (fun x : ℝ => max x 0) ν) :
    (∫ x, callPolynomial a b x ∂ν) ≤ ∫ x : ℝ, max x 0 ∂ν :=
  integral_mono hP hplus (fun x => callPolynomial_le_positivePart a b x ha hb)

lemma measurable_positiveRamp (g : ℝ) : Measurable (positiveRamp g) := by
  exact (measurable_const.sub measurable_id).ite
    (measurableSet_Ioc (a := (0 : ℝ)) (b := g)) measurable_const

lemma measurable_negativeRamp (g : ℝ) : Measurable (negativeRamp g) := by
  exact measurable_id.ite
    (measurableSet_Ico (a := (0 : ℝ)) (b := g)) measurable_const

lemma positiveRamp_nonneg (g x : ℝ) : 0 ≤ positiveRamp g x := by
  unfold positiveRamp
  split_ifs with h
  · exact sub_nonneg.mpr h.2
  · exact le_rfl

lemma negativeRamp_nonneg (g x : ℝ) : 0 ≤ negativeRamp g x := by
  unfold negativeRamp
  split_ifs with h
  · exact h.1
  · exact le_rfl

lemma positiveRamp_le (g x : ℝ) (hg : 0 ≤ g) : positiveRamp g x ≤ g := by
  unfold positiveRamp
  split_ifs with h
  · linarith [h.1]
  · exact hg

lemma negativeRamp_le (g x : ℝ) (hg : 0 ≤ g) : negativeRamp g x ≤ g := by
  unfold negativeRamp
  split_ifs with h
  · exact h.2.le
  · exact hg

lemma integrable_positiveRamp (ν : Measure ℝ) [IsFiniteMeasure ν]
    (g : ℝ) (hg : 0 ≤ g) : Integrable (positiveRamp g) ν := by
  apply (integrable_const g).mono' (measurable_positiveRamp g).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (positiveRamp_nonneg g x)]
    exact positiveRamp_le g x hg)

lemma integrable_negativeRamp (ν : Measure ℝ) [IsFiniteMeasure ν]
    (g : ℝ) (hg : 0 ≤ g) : Integrable (negativeRamp g) ν := by
  apply (integrable_const g).mono' (measurable_negativeRamp g).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (negativeRamp_nonneg g x)]
    exact negativeRamp_le g x hg)

lemma positiveRamp_quadratic_gap (g c s x : ℝ) (hs : s ≠ 0) :
    g - x - ((2 * g * c / s - 1) * x - (g * c ^ 2 / s ^ 2) * x ^ 2) =
      g * (1 - c * x / s) ^ 2 := by
  field_simp [hs]
  ring

theorem positiveRamp_quadratic_lower (g c s x : ℝ) (hg : 0 < g) (hs : 0 < s) :
    (2 * g * c / s - 1) * max x 0 - (g * c ^ 2 / s ^ 2) * (max x 0) ^ 2 ≤
      positiveRamp g x := by
  by_cases hx : 0 < x
  · rw [max_eq_left hx.le]
    have hgap := positiveRamp_quadratic_gap g c s x hs.ne'
    have hnonneg : 0 ≤ g * (1 - c * x / s) ^ 2 := mul_nonneg hg.le (sq_nonneg _)
    by_cases hxg : x ≤ g
    · rw [positiveRamp, ite_eq_left ⟨hx, hxg⟩]
      linarith
    · rw [positiveRamp, ite_eq_right (by simpa only [hx, true_and] using hxg)]
      linarith [lt_of_not_ge hxg]
  · rw [max_eq_right (le_of_not_gt hx)]
    simp [positiveRamp, hx]

/-- A real integral bound from the actual first and second positive-part
moments. Both moment integrability assumptions are retained. -/
theorem integral_positiveRamp_lower (ν : Measure ℝ) [IsFiniteMeasure ν]
    (g c s : ℝ) (hg : 0 < g) (hs : 0 < s)
    (hplus : Integrable (fun x : ℝ => max x 0) ν)
    (hplus2 : Integrable (fun x : ℝ => (max x 0) ^ 2) ν)
    (hc : c ≤ ∫ x : ℝ, max x 0 ∂ν)
    (hs2 : (∫ x : ℝ, (max x 0) ^ 2 ∂ν) ≤ s)
    (hbalance : s ≤ 2 * g * c) :
    g * c ^ 2 / s - c ≤ ∫ x, positiveRamp g x ∂ν := by
  have hA : 0 ≤ 2 * g * c / s - 1 := by
    have hdiv : (1 : ℝ) ≤ 2 * g * c / s :=
      (le_div_iff₀ hs).mpr (by simpa using hbalance)
    linarith
  have hB : 0 ≤ g * c ^ 2 / s ^ 2 := by positivity
  have hi := integral_mono
    ((hplus.const_mul (2 * g * c / s - 1)).sub
      (hplus2.const_mul (g * c ^ 2 / s ^ 2)))
    (integrable_positiveRamp ν g hg.le)
    (fun x => positiveRamp_quadratic_lower g c s x hg hs)
  change (∫ x : ℝ, (2 * g * c / s - 1) * max x 0 -
    (g * c ^ 2 / s ^ 2) * (max x 0) ^ 2 ∂ν) ≤ _ at hi
  rw [integral_sub (hplus.const_mul _) (hplus2.const_mul _),
    integral_const_mul, integral_const_mul] at hi
  have hfirst := mul_le_mul_of_nonneg_left hc hA
  have hsecond := mul_le_mul_of_nonneg_left hs2 hB
  have heq : (2 * g * c / s - 1) * c - (g * c ^ 2 / s ^ 2) * s =
      g * c ^ 2 / s - c := by field_simp [hs.ne']; ring
  linarith

lemma negativeRamp_eq_positivePart_sub_tail (g x : ℝ) (hg : 0 < g) :
    negativeRamp g x = max x 0 - upperTail g x := by
  by_cases hx : 0 ≤ x
  · rw [max_eq_left hx]
    by_cases hxg : x < g
    · simp [negativeRamp, upperTail, hx, hxg, not_le.mpr hxg]
    · simp [negativeRamp, upperTail, hx, hxg, le_of_not_gt hxg]
  · have hx' : x < 0 := lt_of_not_ge hx
    have hgx : ¬g ≤ x := by linarith
    simp [negativeRamp, upperTail, hx, hgx, max_eq_right hx'.le]

lemma upperTail_square_gap (g z x : ℝ) :
    g * (x - z) ^ 2 - x * (g - z) ^ 2 = (x - g) * (g * x - z ^ 2) := by ring

theorem upperTail_le_squarePositivePart (g z x : ℝ) (hz : 0 ≤ z) (hzg : z < g) :
    upperTail g x ≤ g / (g - z) ^ 2 * (max (x - z) 0) ^ 2 := by
  have hg : 0 < g := hz.trans_lt hzg
  have hd : 0 < (g - z) ^ 2 := sq_pos_of_pos (sub_pos.mpr hzg)
  by_cases hxg : g ≤ x
  · rw [upperTail, ite_eq_left hxg, max_eq_left (by linarith : 0 ≤ x - z),
      div_mul_eq_mul_div]
    apply (le_div_iff₀ hd).mpr
    have hx : 0 ≤ x - g := sub_nonneg.mpr hxg
    have hgx := mul_le_mul_of_nonneg_left hxg hg.le
    have hzz := (sq_lt_sq₀ hz hg.le).mpr hzg
    have hfactor : 0 ≤ (x - g) * (g * x - z ^ 2) :=
      mul_nonneg hx (by nlinarith)
    rw [← upperTail_square_gap] at hfactor
    linarith
  · rw [upperTail, ite_eq_right hxg]
    positivity

theorem negativeRamp_polynomial_lower (a b g z x : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hz : 0 ≤ z) (hzg : z < g) :
    callPolynomial a b x - g / (g - z) ^ 2 * (max (x - z) 0) ^ 2 ≤
      negativeRamp g x := by
  rw [negativeRamp_eq_positivePart_sub_tail g x (hz.trans_lt hzg)]
  have hp := callPolynomial_le_positivePart a b x ha hb
  have ht := upperTail_le_squarePositivePart g z x hz hzg
  linarith

/-- Consume a genuine squared-positive-part price bound `T` for the law `ν`. -/
theorem integral_negativeRamp_lower (ν : Measure ℝ) [IsFiniteMeasure ν]
    (a b g z T : ℝ) (ha : 0 < a) (hb : 0 < b) (hz : 0 ≤ z) (hzg : z < g)
    (hP : Integrable (callPolynomial a b) ν)
    (hSq : Integrable (fun x : ℝ => (max (x - z) 0) ^ 2) ν)
    (hT : (∫ x : ℝ, (max (x - z) 0) ^ 2 ∂ν) ≤ T) :
    (∫ x, callPolynomial a b x ∂ν) - g * T / (g - z) ^ 2 ≤
      ∫ x, negativeRamp g x ∂ν := by
  have hg : 0 < g := hz.trans_lt hzg
  have hc : 0 ≤ g / (g - z) ^ 2 := by positivity
  have hi := integral_mono (hP.sub (hSq.const_mul (g / (g - z) ^ 2)))
    (integrable_negativeRamp ν g hg.le)
    (fun x => negativeRamp_polynomial_lower a b g z x ha hb hz hzg)
  change (∫ x : ℝ, callPolynomial a b x -
    g / (g - z) ^ 2 * (max (x - z) 0) ^ 2 ∂ν) ≤ _ at hi
  rw [integral_sub hP (hSq.const_mul _), integral_const_mul] at hi
  have ht := mul_le_mul_of_nonneg_left hT hc
  have hres := (sub_le_sub_left ht (∫ x, callPolynomial a b x ∂ν)).trans hi
  simpa only [div_mul_eq_mul_div] using hres

theorem integral_negativeRamp_moment_lower (ν : Measure ℝ) [IsFiniteMeasure ν]
    (a b g z T : ℝ) (ha : 0 < a) (hb : 0 < b) (hz : 0 ≤ z) (hzg : z < g)
    (h1 : Integrable (fun x : ℝ => x) ν)
    (h2 : Integrable (fun x : ℝ => x ^ 2) ν)
    (h3 : Integrable (fun x : ℝ => x ^ 3) ν)
    (h4 : Integrable (fun x : ℝ => x ^ 4) ν)
    (hT : (∫ x : ℝ, (max (x - z) 0) ^ 2 ∂ν) ≤ T) :
    (a ^ 2 * (a + 3 * b) * (∫ x : ℝ, x ∂ν) +
      6 * a * b * (∫ x : ℝ, x ^ 2 ∂ν) +
      3 * (b - a) * (∫ x : ℝ, x ^ 3 ∂ν) -
      2 * (∫ x : ℝ, x ^ 4 ∂ν)) / (a + b) ^ 3 - g * T / (g - z) ^ 2 ≤
        ∫ x, negativeRamp g x ∂ν := by
  rw [← integral_callPolynomial ν a b h1 h2 h3 h4]
  exact integral_negativeRamp_lower ν a b g z T ha hb hz hzg
    (integrable_callPolynomial ν a b h1 h2 h3 h4)
    (TwoMoment.integrable_squarePositivePart ν id z measurable_id h2) hT

/-- Fix the pointwise dual ratio at `5 / (4 * g)`. -/
theorem positiveRamp_fixed_quadratic_lower (g : ℝ) (hg : 0 < g) (x : ℝ) :
    (3 / 2 : ℝ) * max x 0 - (25 / (16 * g)) * (max x 0) ^ 2 ≤
      positiveRamp g x := by
  have hi := positiveRamp_quadratic_lower g (5 / 4) g x hg hg
  have hA : 2 * g * (5 / 4 : ℝ) / g - 1 = 3 / 2 := by
    field_simp [hg.ne']
    ring
  have hB : g * (5 / 4 : ℝ) ^ 2 / g ^ 2 = 25 / (16 * g) := by
    field_simp [hg.ne']
    ring
  simpa only [hA, hB] using hi

/-- The fixed dual bound needs no positivity or balancing condition on the
actual moment bounds `c` and `s`. -/
theorem integral_positiveRamp_fixed_lower (ν : Measure ℝ) [IsFiniteMeasure ν]
    (g c s : ℝ) (hg : 0 < g)
    (hplus : Integrable (fun x : ℝ => max x 0) ν)
    (hplus2 : Integrable (fun x : ℝ => (max x 0) ^ 2) ν)
    (hc : c ≤ ∫ x : ℝ, max x 0 ∂ν)
    (hs2 : (∫ x : ℝ, (max x 0) ^ 2 ∂ν) ≤ s) :
    (3 / 2 : ℝ) * c - 25 * s / (16 * g) ≤ ∫ x, positiveRamp g x ∂ν := by
  have hi := integral_mono
    ((hplus.const_mul (3 / 2 : ℝ)).sub (hplus2.const_mul (25 / (16 * g))))
    (integrable_positiveRamp ν g hg.le)
    (positiveRamp_fixed_quadratic_lower g hg)
  change (∫ x : ℝ, (3 / 2 : ℝ) * max x 0 -
    (25 / (16 * g)) * (max x 0) ^ 2 ∂ν) ≤ _ at hi
  rw [integral_sub (hplus.const_mul _) (hplus2.const_mul _),
    integral_const_mul, integral_const_mul] at hi
  have hfirst := mul_le_mul_of_nonneg_left hc (by norm_num : 0 ≤ (3 / 2 : ℝ))
  have hsecond := mul_le_mul_of_nonneg_left hs2 (by positivity : 0 ≤ 25 / (16 * g))
  have hres := (sub_le_sub hfirst hsecond).trans hi
  simpa only [div_mul_eq_mul_div] using hres

end BerryEsseen.CallRampMinorants

#print axioms BerryEsseen.CallRampMinorants.callPolynomial_le_positivePart
#print axioms BerryEsseen.CallRampMinorants.integral_callPolynomial
#print axioms BerryEsseen.CallRampMinorants.integral_positiveRamp_lower
#print axioms BerryEsseen.CallRampMinorants.integral_negativeRamp_moment_lower
#print axioms BerryEsseen.CallRampMinorants.positiveRamp_fixed_quadratic_lower
#print axioms BerryEsseen.CallRampMinorants.integral_positiveRamp_fixed_lower

