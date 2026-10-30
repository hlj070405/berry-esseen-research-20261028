module

public import BerryEsseen.StaircaseSquare
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
The squared-positive-part two-moment comparison, on arbitrary probability
spaces. The quadratic majorant uses the supplied upper bound on the
second moment directly. The reference price is the exact weighted price
at the two atoms, including zero variance and both activation boundaries.
-/

namespace BerryEsseen.TwoMoment

open MeasureTheory

noncomputable section

/-- The exact squared-positive-part price of the centered two-point law
with upper atom `a`, variance `z`, and lower atom `-z / a`. -/
def referencePrice (a z c : ℝ) : ℝ :=
  z / (a ^ 2 + z) * (max (a - c) 0) ^ 2 +
    a ^ 2 / (a ^ 2 + z) * (max (-z / a - c) 0) ^ 2

lemma lowerAtom_nonpos (a z : ℝ) (ha : 0 < a) (hz : 0 ≤ z) :
    -z / a ≤ 0 := div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hz) ha.le

lemma referencePrice_of_le_lower (a z c : ℝ) (ha : 0 < a) (hz : 0 ≤ z)
    (hc : c ≤ -z / a) : referencePrice a z c = z + c ^ 2 := by
  have hl := lowerAtom_nonpos a z ha hz
  have hd : 0 < a ^ 2 + z := add_pos_of_pos_of_nonneg (sq_pos_of_pos ha) hz
  unfold referencePrice
  rw [max_eq_left (by linarith : 0 ≤ a - c), max_eq_left (by linarith)]
  field_simp [ha.ne', hd.ne'] ; ring

lemma referencePrice_of_upper_le (a z c : ℝ) (ha : 0 < a) (hz : 0 ≤ z)
    (hc : a ≤ c) : referencePrice a z c = 0 := by
  have hl := lowerAtom_nonpos a z ha hz
  simp [referencePrice, max_eq_right (by linarith : a - c ≤ 0),
    max_eq_right (by linarith : -z / a - c ≤ 0)]

lemma referencePrice_of_between (a z c : ℝ) (hc : -z / a ≤ c) (hca : c ≤ a) :
    referencePrice a z c = z / (a ^ 2 + z) * (a - c) ^ 2 := by
  simp [referencePrice, max_eq_left (by linarith : 0 ≤ a - c),
    max_eq_right (by linarith : -z / a - c ≤ 0)]

lemma referencePrice_zero (a c : ℝ) (ha : 0 < a) :
    referencePrice a 0 c = (max (-c) 0) ^ 2 := by
  simp [referencePrice, ha.ne']

lemma reference_full_square (a z d : ℝ) (ha : 0 < a) (hz : 0 ≤ z) :
    z / (a ^ 2 + z) * (a - d) ^ 2 +
      a ^ 2 / (a ^ 2 + z) * (-z / a - d) ^ 2 = z + d ^ 2 := by
  have hd : 0 < a ^ 2 + z := add_pos_of_pos_of_nonneg (sq_pos_of_pos ha) hz
  field_simp [ha.ne', hd.ne'] ; ring

lemma positivePart_sq_le_sq (x : ℝ) : (max x 0) ^ 2 ≤ x ^ 2 := by
  by_cases h : 0 ≤ x
  · rw [max_eq_left h]
  · rw [max_eq_right (le_of_not_ge h)]
    simpa only [zero_pow (by decide : 2 ≠ 0)] using sq_nonneg x

lemma referencePrice_le_full_square (a z c : ℝ) (ha : 0 < a) (hz : 0 ≤ z) :
    referencePrice a z c ≤ z + c ^ 2 := by
  rw [← reference_full_square a z c ha hz]
  exact add_le_add
    (mul_le_mul_of_nonneg_left (positivePart_sq_le_sq _) (div_nonneg hz (by positivity)))
    (mul_le_mul_of_nonneg_left (positivePart_sq_le_sq _) (div_nonneg (sq_nonneg _) (by positivity)))

lemma quadratic_reference_identity (a z c : ℝ) (ha : 0 < a) (hz : 0 ≤ z) :
    ((a - c) / (a - -z / a)) ^ 2 * (z + (-z / a) ^ 2) =
      z / (a ^ 2 + z) * (a - c) ^ 2 := by
  have hd : 0 < a ^ 2 + z := add_pos_of_pos_of_nonneg (sq_pos_of_pos ha) hz
  have had : 0 < a - -z / a := by
    have := lowerAtom_nonpos a z ha hz
    linarith
  field_simp [ha.ne', hd.ne', had.ne'] ; ring

/-- The majorant agrees with the squared positive part at both atoms. -/
theorem squarePositivePart_le_quadratic (a l c u : ℝ)
    (hlc : l < c) (hca : c < a) (hua : u ≤ a) :
    (max (u - c) 0) ^ 2 ≤ ((a - c) / (a - l)) ^ 2 * (u - l) ^ 2 := by
  have had : 0 < a - l := by linarith
  by_cases huc : u ≤ c
  · rw [max_eq_right (by linarith : u - c ≤ 0)]
    simpa only [zero_pow (by decide : 2 ≠ 0)] using
      mul_nonneg (sq_nonneg ((a - c) / (a - l))) (sq_nonneg (u - l))
  · have hcu : c < u := lt_of_not_ge huc
    have hr : 0 ≤ (a - c) / (a - l) := div_nonneg (by linarith) had.le
    have hlin : u - c ≤ (a - c) / (a - l) * (u - l) := by
      calc
        u - c ≤ ((a - c) * (u - l)) / (a - l) :=
          (le_div_iff₀ had).mpr (by nlinarith)
        _ = (a - c) / (a - l) * (u - l) := by ring
    rw [max_eq_left (by linarith : 0 ≤ u - c), ← mul_pow]
    have hleft : 0 ≤ u - c := by linarith
    have hright : 0 ≤ (a - c) / (a - l) * (u - l) := mul_nonneg hr (by linarith)
    exact (sq_le_sq₀ hleft hright).mpr hlin

variable {Ω : Type*} [MeasurableSpace Ω]

lemma integrable_of_integrable_sq (μ : Measure Ω) [IsFiniteMeasure μ]
    (U : Ω → ℝ) (hU : Measurable U) (hSq : Integrable (fun ω => U ω ^ 2) μ) :
    Integrable U μ := by
  have hdom : Integrable (fun ω => U ω ^ 2 + 1) μ := by
    convert hSq.add (integrable_const (1 : ℝ)) using 1
  apply hdom.mono' hU.aestronglyMeasurable
  filter_upwards [] with ω
  change ‖U ω‖ ≤ U ω ^ 2 + 1
  rw [Real.norm_eq_abs]
  nlinarith [sq_nonneg (|U ω| - 1), sq_abs (U ω)]

lemma integrable_shift_sq (μ : Measure Ω) [IsFiniteMeasure μ]
    (U : Ω → ℝ) (d : ℝ) (hI : Integrable U μ)
    (hSq : Integrable (fun ω => U ω ^ 2) μ) :
    Integrable (fun ω => (U ω - d) ^ 2) μ := by
  have hp := (hSq.sub (hI.const_mul (2 * d))).add (integrable_const (d ^ 2))
  convert hp using 1
  funext ω
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

lemma integral_shift_sq (μ : Measure Ω) [IsProbabilityMeasure μ]
    (U : Ω → ℝ) (d : ℝ) (hI : Integrable U μ)
    (hSq : Integrable (fun ω => U ω ^ 2) μ) (hcenter : ∫ ω, U ω ∂μ = 0) :
    (∫ ω, (U ω - d) ^ 2 ∂μ) = (∫ ω, U ω ^ 2 ∂μ) + d ^ 2 := by
  have hp : (fun ω => (U ω - d) ^ 2) =
      (fun ω => (U ω ^ 2 - (2 * d) * U ω) + d ^ 2) := by
    funext ω
    ring
  have hpoly : Integrable (fun ω => U ω ^ 2 - (2 * d) * U ω) μ := by
    convert hSq.sub (hI.const_mul (2 * d)) using 1
  rw [hp, integral_add hpoly (integrable_const _),
    integral_sub hSq (hI.const_mul (2 * d)), integral_const_mul, hcenter]
  simp

/-- One-sided two-moment comparison for a general real random variable.
The second moment may be strictly less than the reference variance. -/
theorem integral_squarePositivePart_le_referencePrice
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → ℝ) (a z c : ℝ)
    (ha : 0 < a) (hz : 0 ≤ z) (hU : Measurable U)
    (hSq : Integrable (fun ω => U ω ^ 2) μ)
    (hcenter : ∫ ω, U ω ∂μ = 0)
    (hvariance : (∫ ω, U ω ^ 2 ∂μ) ≤ z)
    (hupper : ∀ᵐ ω ∂μ, U ω ≤ a) :
    (∫ ω, (max (U ω - c) 0) ^ 2 ∂μ) ≤ referencePrice a z c := by
  have hI := integrable_of_integrable_sq μ U hU hSq
  have hpos : Integrable (fun ω => (max (U ω - c) 0) ^ 2) μ := by
    have hn := Staircase.integrable_clippedSquare_of_integrable_sq μ
      (fun ω => -U ω) (-c) hU.neg (by simpa using hSq)
    convert hn using 1
    funext ω
    congr 2
    ring
  by_cases hlow : c ≤ -z / a
  · rw [referencePrice_of_le_lower a z c ha hz hlow]
    have hpoint : (fun ω => (max (U ω - c) 0) ^ 2) ≤ᵐ[μ]
        (fun ω => (U ω - c) ^ 2) := by
      filter_upwards [] with ω
      exact positivePart_sq_le_sq (U ω - c)
    calc
      (∫ ω, (max (U ω - c) 0) ^ 2 ∂μ) ≤ ∫ ω, (U ω - c) ^ 2 ∂μ :=
        integral_mono_ae hpos (integrable_shift_sq μ U c hI hSq) hpoint
      _ = (∫ ω, U ω ^ 2 ∂μ) + c ^ 2 := integral_shift_sq μ U c hI hSq hcenter
      _ ≤ z + c ^ 2 := add_le_add hvariance le_rfl
  by_cases hhigh : a ≤ c
  · rw [referencePrice_of_upper_le a z c ha hz hhigh]
    have heq : (fun ω => (max (U ω - c) 0) ^ 2) =ᵐ[μ] (fun _ => 0) := by
      filter_upwards [hupper] with ω hu
      simp [max_eq_right (by linarith : U ω - c ≤ 0)]
    rw [integral_congr_ae heq, integral_zero]
  have hcl : -z / a < c := lt_of_not_ge hlow
  have hca : c < a := lt_of_not_ge hhigh
  rw [referencePrice_of_between a z c hcl.le hca.le]
  let l := -z / a
  let k := (a - c) / (a - l)
  have hquad := integrable_shift_sq μ U l hI hSq
  have hpoint : (fun ω => (max (U ω - c) 0) ^ 2) ≤ᵐ[μ]
      (fun ω => k ^ 2 * (U ω - l) ^ 2) := by
    filter_upwards [hupper] with ω hu
    exact squarePositivePart_le_quadratic a l c (U ω) hcl hca hu
  calc
    (∫ ω, (max (U ω - c) 0) ^ 2 ∂μ) ≤ ∫ ω, k ^ 2 * (U ω - l) ^ 2 ∂μ :=
      integral_mono_ae hpos (hquad.const_mul (k ^ 2)) hpoint
    _ = k ^ 2 * ((∫ ω, U ω ^ 2 ∂μ) + l ^ 2) := by
      rw [integral_const_mul, integral_shift_sq μ U l hI hSq hcenter]
    _ ≤ k ^ 2 * (z + l ^ 2) := mul_le_mul_of_nonneg_left
      (add_le_add hvariance le_rfl) (sq_nonneg k)
    _ = z / (a ^ 2 + z) * (a - c) ^ 2 := by
      exact quadratic_reference_identity a z c ha hz

/-- Enlarging the upper endpoint and the variance bound increases the
two-point price. This is a consequence of the same quadratic majorant. -/
theorem referencePrice_mono (a₁ a₂ z₁ z₂ c : ℝ)
    (ha₁ : 0 < a₁) (ha : a₁ ≤ a₂) (hz₁ : 0 ≤ z₁) (hz : z₁ ≤ z₂) :
    referencePrice a₁ z₁ c ≤ referencePrice a₂ z₂ c := by
  have ha₂ : 0 < a₂ := ha₁.trans_le ha
  have hz₂ : 0 ≤ z₂ := hz₁.trans hz
  by_cases hlow : c ≤ -z₂ / a₂
  · rw [referencePrice_of_le_lower a₂ z₂ c ha₂ hz₂ hlow]
    exact (referencePrice_le_full_square a₁ z₁ c ha₁ hz₁).trans
      (add_le_add hz le_rfl)
  by_cases hhigh : a₂ ≤ c
  · rw [referencePrice_of_upper_le a₂ z₂ c ha₂ hz₂ hhigh,
      referencePrice_of_upper_le a₁ z₁ c ha₁ hz₁ (ha.trans hhigh)]
  have hcl : -z₂ / a₂ < c := lt_of_not_ge hlow
  have hca : c < a₂ := lt_of_not_ge hhigh
  let l := -z₂ / a₂
  let k := (a₂ - c) / (a₂ - l)
  have hleft := squarePositivePart_le_quadratic a₂ l c a₁ hcl hca ha
  have hlower : -z₁ / a₁ ≤ a₂ := (lowerAtom_nonpos a₁ z₁ ha₁ hz₁).trans ha₂.le
  have hright := squarePositivePart_le_quadratic a₂ l c (-z₁ / a₁) hcl hca hlower
  have hw₁ : 0 ≤ z₁ / (a₁ ^ 2 + z₁) := div_nonneg hz₁ (by positivity)
  have hw₂ : 0 ≤ a₁ ^ 2 / (a₁ ^ 2 + z₁) := div_nonneg (sq_nonneg _) (by positivity)
  calc
    referencePrice a₁ z₁ c ≤
        z₁ / (a₁ ^ 2 + z₁) * (k ^ 2 * (a₁ - l) ^ 2) +
        a₁ ^ 2 / (a₁ ^ 2 + z₁) * (k ^ 2 * (-z₁ / a₁ - l) ^ 2) :=
      add_le_add (mul_le_mul_of_nonneg_left hleft hw₁)
        (mul_le_mul_of_nonneg_left hright hw₂)
    _ = k ^ 2 * (z₁ + l ^ 2) := by
      calc
        _ = k ^ 2 * (z₁ / (a₁ ^ 2 + z₁) * (a₁ - l) ^ 2 +
            a₁ ^ 2 / (a₁ ^ 2 + z₁) * (-z₁ / a₁ - l) ^ 2) := by ring
        _ = _ := by rw [reference_full_square a₁ z₁ l ha₁ hz₁]
    _ ≤ k ^ 2 * (z₂ + l ^ 2) := mul_le_mul_of_nonneg_left
      (add_le_add hz le_rfl) (sq_nonneg k)
    _ = z₂ / (a₂ ^ 2 + z₂) * (a₂ - c) ^ 2 :=
      quadratic_reference_identity a₂ z₂ c ha₂ hz₂
    _ = referencePrice a₂ z₂ c :=
      (referencePrice_of_between a₂ z₂ c hcl.le hca.le).symm

lemma positivePart_sq_add_negativePart_sq (x : ℝ) :
    (max x 0) ^ 2 + (max (-x) 0) ^ 2 = x ^ 2 := by
  by_cases h : 0 ≤ x
  · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]
    ring
  · rw [max_eq_right (le_of_not_ge h), max_eq_left (by linarith : 0 ≤ -x)]
    ring

/-- Reflecting the two-point law swaps its atoms and their weights. -/
theorem referencePrice_add_reflected (a z c : ℝ) (ha : 0 < a) (hz : 0 < z) :
    referencePrice a z c + referencePrice (z / a) z (-c) = z + c ^ 2 := by
  have hd : 0 < a ^ 2 + z := add_pos (sq_pos_of_pos ha) hz
  have hza : 0 < z / a := div_pos hz ha
  have hd' : 0 < (z / a) ^ 2 + z := add_pos (sq_pos_of_pos hza) hz
  have hl : -z / (z / a) = -a := by
    field_simp [ha.ne', hz.ne']
  have hw₁ : z / ((z / a) ^ 2 + z) = a ^ 2 / (a ^ 2 + z) := by
    field_simp [ha.ne', hz.ne', hd.ne', hd'.ne'] ; ring
  have hw₂ : (z / a) ^ 2 / ((z / a) ^ 2 + z) = z / (a ^ 2 + z) := by
    field_simp [ha.ne', hz.ne', hd.ne', hd'.ne'] ; ring
  unfold referencePrice
  rw [hw₁, hw₂, hl]
  have hp : z / a - -c = -(-z / a - c) := by ring
  have hp' : -a - -c = -(a - c) := by ring
  rw [hp, hp']
  calc
    _ = z / (a ^ 2 + z) * ((max (a - c) 0) ^ 2 + (max (-(a - c)) 0) ^ 2) +
        a ^ 2 / (a ^ 2 + z) * ((max (-z / a - c) 0) ^ 2 +
          (max (-(-z / a - c)) 0) ^ 2) := by ring
    _ = z + c ^ 2 := by
      rw [positivePart_sq_add_negativePart_sq, positivePart_sq_add_negativePart_sq]
      exact reference_full_square a z c ha hz.le

lemma referencePrice_le_variance_add_zeroPrice (a z c : ℝ)
    (ha : 0 < a) (hz : 0 ≤ z) :
    referencePrice a z c ≤ z + (max (-c) 0) ^ 2 := by
  by_cases hc : c ≤ 0
  · rw [max_eq_left (by linarith : 0 ≤ -c), neg_sq]
    exact referencePrice_le_full_square a z c ha hz
  have hc' : 0 ≤ c := (lt_of_not_ge hc).le
  have hl := lowerAtom_nonpos a z ha hz
  rw [max_eq_right (neg_nonpos.mpr hc')]
  have hbound : (max (a - c) 0) ^ 2 ≤ a ^ 2 :=
    (sq_le_sq₀ (le_max_right _ _) ha.le).mpr (max_le (by linarith) ha.le)
  have hd : 0 < a ^ 2 + z := add_pos_of_pos_of_nonneg (sq_pos_of_pos ha) hz
  have hweight : 0 ≤ z / (a ^ 2 + z) := div_nonneg hz hd.le
  have hratio : z / (a ^ 2 + z) * a ^ 2 ≤ z := by
    calc
      _ = (z * a ^ 2) / (a ^ 2 + z) := by ring
      _ ≤ z := (div_le_iff₀ hd).mpr (by nlinarith [sq_nonneg z])
  unfold referencePrice
  rw [max_eq_right (by linarith : -z / a - c ≤ 0)]
  simpa using (mul_le_mul_of_nonneg_left hbound hweight).trans hratio

/-- The two-point price is increasing and 1-Lipschitz in variance,
including variance zero. Reflection supplies the upper increment bound. -/
theorem referencePrice_variance_increment (a z₁ z₂ c : ℝ)
    (ha : 0 < a) (hz₁ : 0 ≤ z₁) (hz : z₁ ≤ z₂) :
    0 ≤ referencePrice a z₂ c - referencePrice a z₁ c ∧
      referencePrice a z₂ c - referencePrice a z₁ c ≤ z₂ - z₁ := by
  have hz₂ : 0 ≤ z₂ := hz₁.trans hz
  constructor
  · exact sub_nonneg.mpr (referencePrice_mono a a z₁ z₂ c ha le_rfl hz₁ hz)
  by_cases hzero : z₁ = 0
  · subst z₁
    rw [referencePrice_zero a c ha]
    have hbound := referencePrice_le_variance_add_zeroPrice a z₂ c ha hz₂
    linarith
  have hz₁' : 0 < z₁ := lt_of_le_of_ne hz₁ (Ne.symm hzero)
  have hz₂' : 0 < z₂ := hz₁'.trans_le hz
  have hmono := referencePrice_mono (z₁ / a) (z₂ / a) z₁ z₂ (-c)
    (div_pos hz₁' ha) (div_le_div_of_nonneg_right hz ha.le) hz₁ hz
  have hsum₁ := referencePrice_add_reflected a z₁ c ha hz₁'
  have hsum₂ := referencePrice_add_reflected a z₂ c ha hz₂'
  linarith

end

end BerryEsseen.TwoMoment

#print axioms BerryEsseen.TwoMoment.squarePositivePart_le_quadratic
#print axioms BerryEsseen.TwoMoment.integral_squarePositivePart_le_referencePrice
#print axioms BerryEsseen.TwoMoment.referencePrice_mono
#print axioms BerryEsseen.TwoMoment.referencePrice_variance_increment
