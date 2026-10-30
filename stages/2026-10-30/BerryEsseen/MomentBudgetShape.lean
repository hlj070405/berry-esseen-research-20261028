module

public import BerryEsseen.MomentBudget
public import Mathlib.Analysis.Convex.Deriv

@[expose] public section

/-! 2026-10-28: allocation shape of the same actual-law moment budget.
An arbitrary affine positive cap is allowed, with no restriction on its slope.
The convexity proof uses the exact square-over-affine Jensen gap. -/

noncomputable section

open Set

namespace BerryEsseen.MomentBudgetShape

open MomentBudget

def allocationLinear (p α : ℝ) : ℝ :=
  (1 - α) / Real.sqrt (1 - p) + α / Real.sqrt p

def allocationSlope (p : ℝ) : ℝ :=
  1 / Real.sqrt p - 1 / Real.sqrt (1 - p)

lemma normalizer_pos (p s : ℝ) (hp : 0 < p) (hp1 : p < 1) (hs : 0 ≤ s) :
    0 < Real.sqrt (p * (1 - p) + s) ^ 3 := by
  exact pow_pos (Real.sqrt_pos.mpr (add_pos_of_pos_of_nonneg
    (mul_pos hp (sub_pos.mpr hp1)) hs)) 3

lemma affine_mix_pos (d0 d1 t : ℝ) (hd0 : 0 < d0) (hd1 : 0 < d1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : 0 < (1 - t) * d0 + t * d1 := by
  rcases lt_or_eq_of_le ht1 with ht | rfl
  · have h : 0 < 1 - t := sub_pos.mpr ht
    positivity
  · simpa using hd1

/-- The exact perspective gap; neither numerator is restricted in sign. -/
theorem square_div_jensen_gap (u0 u1 d0 d1 t : ℝ)
    (hd0 : 0 < d0) (hd1 : 0 < d1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - t) * (u0 ^ 2 / d0) + t * (u1 ^ 2 / d1) -
        ((1 - t) * u0 + t * u1) ^ 2 / ((1 - t) * d0 + t * d1) =
      t * (1 - t) * (u0 * d1 - u1 * d0) ^ 2 /
        (d0 * d1 * ((1 - t) * d0 + t * d1)) := by
  have hd := affine_mix_pos d0 d1 t hd0 hd1 ht0 ht1
  field_simp [ne_of_gt hd0, ne_of_gt hd1, ne_of_gt hd]
  ring

lemma square_div_jensen_nonneg (u0 u1 d0 d1 t : ℝ)
    (hd0 : 0 < d0) (hd1 : 0 < d1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ (1 - t) * (u0 ^ 2 / d0) + t * (u1 ^ 2 / d1) -
      ((1 - t) * u0 + t * u1) ^ 2 / ((1 - t) * d0 + t * d1) := by
  rw [square_div_jensen_gap u0 u1 d0 d1 t hd0 hd1 ht0 ht1]
  exact div_nonneg
    (mul_nonneg (mul_nonneg ht0 (sub_nonneg.mpr ht1)) (sq_nonneg _))
    (mul_nonneg (mul_nonneg hd0.le hd1.le)
      (affine_mix_pos d0 d1 t hd0 hd1 ht0 ht1).le)

lemma allocationLinear_mix (p x y t : ℝ) :
    allocationLinear p ((1 - t) * x + t * y) =
      (1 - t) * allocationLinear p x + t * allocationLinear p y := by
  unfold allocationLinear
  ring

/-- Jensen's inequality for the actual budget, with the original shared allocation. -/
theorem gDelta_affine_jensen (p s A B x y t : ℝ)
    (hp : 0 < p) (hp1 : p < 1) (hs : 0 ≤ s)
    (hd0 : 0 < A + B * x) (hd1 : 0 < A + B * y)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    gDelta p s (A + B * ((1 - t) * x + t * y)) ((1 - t) * x + t * y) ≤
      (1 - t) * gDelta p s (A + B * x) x + t * gDelta p s (A + B * y) y := by
  have hcap : A + B * ((1 - t) * x + t * y) =
      (1 - t) * (A + B * x) + t * (A + B * y) := by ring
  have heq (δ α : ℝ) : gDelta p s δ α =
      (p * (1 - p) * (1 - 2 * (p * (1 - p))) +
        (3 * (p + α * ((1 - p) - p)) - δ) * s +
        allocationLinear p α ^ 2 * s ^ 2 / δ) /
          Real.sqrt (p * (1 - p) + s) ^ 3 := rfl
  have hid :
      (1 - t) * gDelta p s (A + B * x) x + t * gDelta p s (A + B * y) y -
        gDelta p s (A + B * ((1 - t) * x + t * y)) ((1 - t) * x + t * y) =
      (s ^ 2 / Real.sqrt (p * (1 - p) + s) ^ 3) *
        ((1 - t) * (allocationLinear p x ^ 2 / (A + B * x)) +
          t * (allocationLinear p y ^ 2 / (A + B * y)) -
          ((1 - t) * allocationLinear p x + t * allocationLinear p y) ^ 2 /
            ((1 - t) * (A + B * x) + t * (A + B * y))) := by
    rw [heq, heq, heq, allocationLinear_mix, hcap]
    ring
  have hnon := mul_nonneg
    (div_nonneg (sq_nonneg s) (normalizer_pos p s hp hp1 hs).le)
    (square_div_jensen_nonneg (allocationLinear p x) (allocationLinear p y)
      (A + B * x) (A + B * y) t hd0 hd1 ht0 ht1)
  rw [← hid] at hnon
  linarith

/-- Positive affine caps give convex allocation floors on every closed interval.
There is no assumption on the sign of `B` or of an allocation derivative. -/
theorem convexOn_gDelta_affine (p s A B l u : ℝ)
    (hp : 0 < p) (hp1 : p < 1) (hs : 0 ≤ s)
    (hδ : ∀ α ∈ Icc l u, 0 < A + B * α) :
    ConvexOn ℝ (Icc l u) (fun α => gDelta p s (A + B * α) α) := by
  refine ⟨convex_Icc l u, ?_⟩
  intro x hx y hy a b ha hb hab
  have hb1 : b ≤ 1 := by linarith
  have haeq : a = 1 - b := by linarith
  simpa only [smul_eq_mul, haeq] using
    gDelta_affine_jensen p s A B x y b hp hp1 hs (hδ x hx) (hδ y hy) hb hb1

lemma hasDerivAt_allocationLinear (p α : ℝ) :
    HasDerivAt (allocationLinear p) (allocationSlope p) α := by
  unfold allocationLinear allocationSlope
  convert (((hasDerivAt_const α (1 : ℝ)).fun_sub (hasDerivAt_id' α)).div_const
    (Real.sqrt (1 - p))).fun_add ((hasDerivAt_id' α).div_const (Real.sqrt p)) using 1
  ring

/-- The cap derivative is `B`; both negative `B` terms are retained. -/
def allocationDeriv (p s A B α : ℝ) : ℝ :=
  s / Real.sqrt (p * (1 - p) + s) ^ 3 *
    (3 * ((1 - p) - p) - B + s *
      (2 * allocationLinear p α * allocationSlope p / (A + B * α) -
        B * allocationLinear p α ^ 2 / (A + B * α) ^ 2))

theorem hasDerivAt_gDelta_affine (p s A B α : ℝ)
    (hp : 0 < p) (hp1 : p < 1) (hs : 0 ≤ s) (hδ : 0 < A + B * α) :
    HasDerivAt (fun x => gDelta p s (A + B * x) x) (allocationDeriv p s A B α) α := by
  have hd : HasDerivAt (fun x : ℝ => A + B * x) B α := by
    convert ((hasDerivAt_id' α).const_mul B).const_add A using 1
    ring
  have ha : HasDerivAt
      (fun x : ℝ => (3 * (p + x * ((1 - p) - p)) - (A + B * x)) * s)
      ((3 * ((1 - p) - p) - B) * s) α := by
    convert (((((hasDerivAt_id' α).mul_const ((1 - p) - p)).const_add p).const_mul 3).fun_sub
      hd).mul_const s using 1
    ring
  have hq := (((hasDerivAt_allocationLinear p α).fun_pow 2).mul_const (s ^ 2)).div hd
    (ne_of_gt hδ)
  have h := (((hasDerivAt_const α (p * (1 - p) * (1 - 2 * (p * (1 - p))))).fun_add
    ha).fun_add hq).div_const (Real.sqrt (p * (1 - p) + s) ^ 3)
  convert h using 1
  · rfl
  · unfold allocationDeriv
    field_simp [ne_of_gt hδ, ne_of_gt (normalizer_pos p s hp hp1 hs)]
    ring

/-- Convexity gives a lower tangent at the left endpoint, including that endpoint. -/
theorem gDelta_affine_left_tangent (p s A B l u α : ℝ)
    (hp : 0 < p) (hp1 : p < 1) (hs : 0 ≤ s)
    (hδ : ∀ x ∈ Icc l u, 0 < A + B * x) (hα : α ∈ Icc l u) :
    gDelta p s (A + B * l) l + allocationDeriv p s A B l * (α - l) ≤
      gDelta p s (A + B * α) α := by
  have hl : l ∈ Icc l u := ⟨le_rfl, hα.1.trans hα.2⟩
  rcases eq_or_lt_of_le hα.1 with heq | hlt
  · rw [← heq]
    simp
  · have hc := convexOn_gDelta_affine p s A B l u hp hp1 hs hδ
    have hd := hasDerivAt_gDelta_affine p s A B l hp hp1 hs (hδ l hl)
    have hsl := hc.le_slope_of_hasDerivAt hl hα hlt hd
    rw [slope_def_field] at hsl
    have hmul := (le_div_iff₀ (sub_pos.mpr hlt)).mp hsl
    linarith

/-- An endpoint derivative price controls the moment floor on the whole interval. -/
theorem gDelta_affine_ge_left (p s A B l u α : ℝ)
    (hp : 0 < p) (hp1 : p < 1) (hs : 0 ≤ s)
    (hδ : ∀ x ∈ Icc l u, 0 < A + B * x) (hα : α ∈ Icc l u)
    (hgate : 0 ≤ allocationDeriv p s A B l) :
    gDelta p s (A + B * l) l ≤ gDelta p s (A + B * α) α := by
  have ht := gDelta_affine_left_tangent p s A B l u α hp hp1 hs hδ hα
  have hn := mul_nonneg hgate (sub_nonneg.mpr hα.1)
  linarith

/-- The actual signed allocation derivative is nondecreasing for a positive affine cap. -/
theorem monotoneOn_allocationDeriv (p s A B l u : ℝ)
    (hp : 0 < p) (hp1 : p < 1) (hs : 0 ≤ s)
    (hδ : ∀ x ∈ Icc l u, 0 < A + B * x) :
    MonotoneOn (allocationDeriv p s A B) (Icc l u) := by
  have hc := convexOn_gDelta_affine p s A B l u hp hp1 hs hδ
  have hm := hc.monotoneOn_deriv
    (fun x hx => (hasDerivAt_gDelta_affine p s A B x hp hp1 hs (hδ x hx)).differentiableAt)
  intro x hx y hy hxy
  have h := hm hx hy hxy
  rw [(hasDerivAt_gDelta_affine p s A B x hp hp1 hs (hδ x hx)).deriv,
    (hasDerivAt_gDelta_affine p s A B y hp hp1 hs (hδ y hy)).deriv] at h
  exact h

lemma allocationSlope_nonneg (p : ℝ) (hp : 0 < p) (hpHalf : p ≤ 1 / 2) :
    0 ≤ allocationSlope p := by
  have hpq : p ≤ 1 - p := by linarith
  unfold allocationSlope
  exact sub_nonneg.mpr (one_div_le_one_div_of_le (Real.sqrt_pos.mpr hp)
    (Real.sqrt_le_sqrt hpq))

lemma allocationLinear_nonneg (p α : ℝ) (hα : α ∈ Icc (0 : ℝ) 1) :
    0 ≤ allocationLinear p α := by
  unfold allocationLinear
  exact add_nonneg (div_nonneg (sub_nonneg.mpr hα.2) (Real.sqrt_nonneg _))
    (div_nonneg hα.1 (Real.sqrt_nonneg _))

lemma allocationDeriv_constant_nonneg (p s δ α : ℝ)
    (hp : 0 < p) (hpHalf : p ≤ 1 / 2) (hs : 0 ≤ s) (hδ : 0 < δ)
    (hα : α ∈ Icc (0 : ℝ) 1) : 0 ≤ allocationDeriv p s δ 0 α := by
  have hp1 : p < 1 := by linarith
  have hc := normalizer_pos p s hp hp1 hs
  have hd := allocationSlope_nonneg p hp hpHalf
  have hu := allocationLinear_nonneg p α hα
  have hqp : 0 ≤ (1 - p) - p := by linarith
  unfold allocationDeriv
  simp only [zero_mul, add_zero, zero_div, sub_zero]
  positivity

/-- The older constant-cap monotonicity is a separate consequence on `[0,1]`. -/
theorem monotoneOn_gDelta_constant (p s δ : ℝ)
    (hp : 0 < p) (hpHalf : p ≤ 1 / 2) (hs : 0 ≤ s) (hδ : 0 < δ) :
    MonotoneOn (fun α => gDelta p s δ α) (Icc (0 : ℝ) 1) := by
  have hp1 : p < 1 := by linarith
  have hd : ∀ α : ℝ, HasDerivAt (fun x => gDelta p s δ x)
      (allocationDeriv p s δ 0 α) α := by
    intro α
    simpa only [zero_mul, add_zero] using hasDerivAt_gDelta_affine p s δ 0 α hp hp1 hs
      (by simpa using hδ)
  apply monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) 1)
  · exact fun x hx => (hd x).continuousAt.continuousWithinAt
  · exact fun x hx => (hd x).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [(hd x).deriv]
    exact allocationDeriv_constant_nonneg p s δ x hp hpHalf hs hδ (interior_subset hx)

end BerryEsseen.MomentBudgetShape

#print axioms BerryEsseen.MomentBudgetShape.square_div_jensen_gap
#print axioms BerryEsseen.MomentBudgetShape.gDelta_affine_jensen
#print axioms BerryEsseen.MomentBudgetShape.convexOn_gDelta_affine
#print axioms BerryEsseen.MomentBudgetShape.hasDerivAt_gDelta_affine
#print axioms BerryEsseen.MomentBudgetShape.gDelta_affine_left_tangent
#print axioms BerryEsseen.MomentBudgetShape.gDelta_affine_ge_left
#print axioms BerryEsseen.MomentBudgetShape.monotoneOn_allocationDeriv
#print axioms BerryEsseen.MomentBudgetShape.monotoneOn_gDelta_constant
