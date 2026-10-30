module

public import BerryEsseen.MomentBudgetShape
public import BerryEsseen.ReferenceSumPrice

@[expose] public section

/-! 2026-10-28: finite allocation increments for the genuine reference-sum
price and the same actual-law moment floor. Probability, residual noise,
allocation and the affine cap remain shared between both terms. -/

noncomputable section

open MeasureTheory Set

namespace BerryEsseen.AllocationEnvelope

open MomentBudget MomentBudgetShape TwoMoment

/-- The count variance in the actual shared allocation coordinates. -/
def allocationVariance (p s : ℝ) (n k : ℕ) (α : ℝ) : ℝ :=
  s * (((n - k : ℕ) : ℝ) * (1 - α) / (1 - p) + (k : ℝ) * α / p)

def varianceSlope (p s : ℝ) (n k : ℕ) : ℝ :=
  s * ((k : ℝ) - (n : ℝ) * p) / (p * (1 - p))

/-- Writing the original noise as `lambda = n*s` gives exactly this variance. -/
theorem allocationVariance_eq_noise (p s : ℝ) (n k : ℕ) (α : ℝ) (hn : 0 < n) :
    allocationVariance p s n k α =
      ((n : ℝ) * s) / (n : ℝ) *
        (((n - k : ℕ) : ℝ) * (1 - α) / (1 - p) + (k : ℝ) * α / p) := by
  rw [mul_div_cancel_left₀ s (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn))]
  rfl

/-- Identification with the true second moment of the same finite product sum. -/
theorem allocationVariance_eq_actual_W (ν0 ν1 : ProbabilityMeasure ℝ)
    (h0 : CenteredResidualLaw ν0) (h1 : CenteredResidualLaw ν1)
    (p s α : ℝ) (hp : 0 < p) (hp1 : p < 1) (hs : 0 < s)
    (hsecond : s = (1 - p) * residualSecondMoment ν0 + p * residualSecondMoment ν1)
    (hα : α = p * residualSecondMoment ν1 / s) (n k : ℕ) (hk : k ≤ n) :
    (∫ ω, CommonProduct.W n k ω ^ 2
      ∂CommonProduct.pairProduct (ν0 : Measure ℝ) (ν1 : Measure ℝ) n) =
      allocationVariance p s n k α := by
  exact CommonProductMoments.actual_allocation_count_variance ν0 ν1 h0 h1 p s α
    hp hp1 hs hsecond hα n k hk

lemma allocationVariance_nonneg (p s : ℝ) (n k : ℕ) (α : ℝ)
    (hp : 0 < p) (hp1 : p < 1) (hs : 0 ≤ s) (hα : α ∈ Icc (0 : ℝ) 1) :
    0 ≤ allocationVariance p s n k α := by
  unfold allocationVariance
  apply mul_nonneg hs
  exact add_nonneg
    (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hα.2)) (sub_pos.mpr hp1).le)
    (div_nonneg (mul_nonneg (Nat.cast_nonneg _) hα.1) hp.le)

theorem allocationVariance_sub (p s : ℝ) (n k : ℕ) (a α : ℝ)
    (hp : 0 < p) (hp1 : p < 1) (hk : k ≤ n) :
    allocationVariance p s n k α - allocationVariance p s n k a =
      varianceSlope p s n k * (α - a) := by
  unfold allocationVariance varianceSlope
  rw [Nat.cast_sub hk]
  field_simp [ne_of_gt hp, ne_of_gt (sub_pos.mpr hp1)]
  ring

/-- The negative-slope branch uses monotonicity; the positive branch uses the
proved finite 1-Lipschitz increment, without any activation or derivative assumption. -/
theorem referencePrice_allocation_increment (p s : ℝ) (n k m : ℕ) (bref c a α : ℝ)
    (hp : 0 < p) (hp1 : p < 1) (hs : 0 ≤ s) (hk : k ≤ n)
    (hm : 0 < m) (hbref : 0 < bref)
    (ha : a ∈ Icc (0 : ℝ) 1) (hα : α ∈ Icc (0 : ℝ) 1) (haα : a ≤ α) :
    referenceSumPrice bref m (allocationVariance p s n k α) c -
        referenceSumPrice bref m (allocationVariance p s n k a) c ≤
      max (varianceSlope p s n k) 0 * (α - a) := by
  have hVa := allocationVariance_nonneg p s n k a hp hp1 hs ha
  have hVα := allocationVariance_nonneg p s n k α hp hp1 hs hα
  have hsub := allocationVariance_sub p s n k a α hp hp1 hk
  by_cases hd : 0 ≤ varianceSlope p s n k
  · have hV : allocationVariance p s n k a ≤ allocationVariance p s n k α := by
      have hn := mul_nonneg hd (sub_nonneg.mpr haα)
      linarith
    have h := (referenceSumPrice_variance_increment bref m _ _ c hbref hm hVa hV).2
    rw [max_eq_left hd, ← hsub]
    exact h
  · have hd' : varianceSlope p s n k ≤ 0 := le_of_lt (lt_of_not_ge hd)
    have hV : allocationVariance p s n k α ≤ allocationVariance p s n k a := by
      have hn := mul_nonpos_of_nonpos_of_nonneg hd' (sub_nonneg.mpr haα)
      linarith
    have h := referenceSumPrice_mono bref bref m _ _ c hbref le_rfl hm hVα hV
    rw [max_eq_right hd', zero_mul]
    linarith

/-- Both terms use the same `p,s,alpha`; no separate moment or variance corner is chosen. -/
def allocationEnvelope (p s A B : ℝ) (n k m : ℕ) (bref c w cn α : ℝ) : ℝ :=
  w * referenceSumPrice bref m (allocationVariance p s n k α) c -
    cn * gDelta p s (A + B * α) α

theorem allocationEnvelope_increment (p s A B : ℝ) (n k m : ℕ) (bref c w cn a b α : ℝ)
    (hp : 0 < p) (hp1 : p < 1) (hs : 0 ≤ s) (hk : k ≤ n)
    (hm : 0 < m) (hbref : 0 < bref) (hw : 0 ≤ w) (hcn : 0 ≤ cn)
    (ha : 0 ≤ a) (hb : b ≤ 1) (hα : α ∈ Icc a b)
    (hδ : ∀ x ∈ Icc a b, 0 < A + B * x) :
    allocationEnvelope p s A B n k m bref c w cn α -
        allocationEnvelope p s A B n k m bref c w cn a ≤
      (w * max (varianceSlope p s n k) 0 - cn * allocationDeriv p s A B a) * (α - a) := by
  have hA : a ∈ Icc (0 : ℝ) 1 := ⟨ha, (hα.1.trans hα.2).trans hb⟩
  have hX : α ∈ Icc (0 : ℝ) 1 := ⟨ha.trans hα.1, hα.2.trans hb⟩
  have hK := mul_le_mul_of_nonneg_left
    (referencePrice_allocation_increment p s n k m bref c a α hp hp1 hs hk hm hbref hA hX hα.1) hw
  have hG := gDelta_affine_left_tangent p s A B a b α hp hp1 hs hδ hα
  have hG' : allocationDeriv p s A B a * (α - a) ≤
      gDelta p s (A + B * α) α - gDelta p s (A + B * a) a := by linarith
  have hcost := mul_le_mul_of_nonneg_left hG' hcn
  unfold allocationEnvelope
  nlinarith only [hK, hcost]

/-- A nonpositive signed finite gate eliminates allocation on the entire interval. -/
theorem allocationEnvelope_le_left (p s A B : ℝ) (n k m : ℕ) (bref c w cn a b α : ℝ)
    (hp : 0 < p) (hp1 : p < 1) (hs : 0 ≤ s) (hk : k ≤ n)
    (hm : 0 < m) (hbref : 0 < bref) (hw : 0 ≤ w) (hcn : 0 ≤ cn)
    (ha : 0 ≤ a) (hb : b ≤ 1) (hα : α ∈ Icc a b)
    (hδ : ∀ x ∈ Icc a b, 0 < A + B * x)
    (hgate : w * max (varianceSlope p s n k) 0 - cn * allocationDeriv p s A B a ≤ 0) :
    allocationEnvelope p s A B n k m bref c w cn α ≤
      allocationEnvelope p s A B n k m bref c w cn a := by
  have hi := allocationEnvelope_increment p s A B n k m bref c w cn a b α
    hp hp1 hs hk hm hbref hw hcn ha hb hα hδ
  have hn := mul_nonpos_of_nonpos_of_nonneg hgate (sub_nonneg.mpr hα.1)
  linarith

/-- The affine variance always lies below the larger endpoint, without a slope sign assumption. -/
lemma allocationVariance_le_endpoint_max (p s : ℝ) (n k : ℕ) (a b α : ℝ)
    (hp : 0 < p) (hp1 : p < 1) (hk : k ≤ n) (hα : α ∈ Icc a b) :
    allocationVariance p s n k α ≤
      max (allocationVariance p s n k a) (allocationVariance p s n k b) := by
  by_cases hd : 0 ≤ varianceSlope p s n k
  · have h := allocationVariance_sub p s n k α b hp hp1 hk
    have hn := mul_nonneg hd (sub_nonneg.mpr hα.2)
    exact le_trans (by linarith) (le_max_right _ _)
  · have h := allocationVariance_sub p s n k a α hp hp1 hk
    have hn := mul_nonpos_of_nonpos_of_nonneg (le_of_lt (lt_of_not_ge hd)) (sub_nonneg.mpr hα.1)
    exact le_trans (by linarith) (le_max_left _ _)

/-- The two variance corners share a single moment floor, rather than using two
actual envelope endpoint values. -/
theorem allocationEnvelope_le_variance_corners (p s A B : ℝ) (n k m : ℕ)
    (bref c w cn a b α L : ℝ)
    (hp : 0 < p) (hp1 : p < 1) (hs : 0 ≤ s) (hk : k ≤ n)
    (hm : 0 < m) (hbref : 0 < bref) (hw : 0 ≤ w) (hcn : 0 ≤ cn)
    (ha : 0 ≤ a) (hb : b ≤ 1) (hα : α ∈ Icc a b)
    (hfloor : L ≤ gDelta p s (A + B * α) α) :
    allocationEnvelope p s A B n k m bref c w cn α ≤
      max (w * referenceSumPrice bref m (allocationVariance p s n k a) c - cn * L)
        (w * referenceSumPrice bref m (allocationVariance p s n k b) c - cn * L) := by
  have hX : α ∈ Icc (0 : ℝ) 1 := ⟨ha.trans hα.1, hα.2.trans hb⟩
  have hVα := allocationVariance_nonneg p s n k α hp hp1 hs hX
  have hv := allocationVariance_le_endpoint_max p s n k a b α hp hp1 hk hα
  have hG := mul_le_mul_of_nonneg_left hfloor hcn
  unfold allocationEnvelope
  by_cases hVab : allocationVariance p s n k a ≤ allocationVariance p s n k b
  · rw [max_eq_right hVab] at hv
    have hK := mul_le_mul_of_nonneg_left
      (referenceSumPrice_mono bref bref m _ _ c hbref le_rfl hm hVα hv) hw
    exact (sub_le_sub hK hG).trans (le_max_right _ _)
  · rw [max_eq_left (le_of_lt (lt_of_not_ge hVab))] at hv
    have hK := mul_le_mul_of_nonneg_left
      (referenceSumPrice_mono bref bref m _ _ c hbref le_rfl hm hVα hv) hw
    exact (sub_le_sub hK hG).trans (le_max_left _ _)

theorem allocationEnvelope_endpoint_max (p s A B : ℝ) (n k m : ℕ)
    (bref c w cn a b α : ℝ)
    (hp : 0 < p) (hp1 : p < 1) (hs : 0 ≤ s) (hk : k ≤ n)
    (hm : 0 < m) (hbref : 0 < bref) (hw : 0 ≤ w) (hcn : 0 ≤ cn)
    (ha : 0 ≤ a) (hb : b ≤ 1) (hα : α ∈ Icc a b)
    (hδ : ∀ x ∈ Icc a b, 0 < A + B * x) (hgate : 0 ≤ allocationDeriv p s A B a) :
    allocationEnvelope p s A B n k m bref c w cn α ≤
      max (w * referenceSumPrice bref m (allocationVariance p s n k a) c -
          cn * gDelta p s (A + B * a) a)
        (w * referenceSumPrice bref m (allocationVariance p s n k b) c -
          cn * gDelta p s (A + B * a) a) := by
  exact allocationEnvelope_le_variance_corners p s A B n k m bref c w cn a b α _
    hp hp1 hs hk hm hbref hw hcn ha hb hα
    (gDelta_affine_ge_left p s A B a b α hp hp1 hs hδ hα hgate)

/-- A signed derivative also supplies a common interval floor when it is negative. -/
theorem gDelta_affine_interval_floor (p s A B a b α : ℝ)
    (hp : 0 < p) (hp1 : p < 1) (hs : 0 ≤ s)
    (hδ : ∀ x ∈ Icc a b, 0 < A + B * x) (hα : α ∈ Icc a b) :
    gDelta p s (A + B * a) a + min (allocationDeriv p s A B a) 0 * (b - a) ≤
      gDelta p s (A + B * α) α := by
  have ht := gDelta_affine_left_tangent p s A B a b α hp hp1 hs hδ hα
  have h1 := mul_le_mul_of_nonneg_right (min_le_left (allocationDeriv p s A B a) 0)
    (sub_nonneg.mpr hα.1)
  have h2 := mul_le_mul_of_nonpos_left (sub_le_sub_right hα.2 a)
    (min_le_right (allocationDeriv p s A B a) 0)
  linarith

/-- No derivative sign is required if both variance corners pay this common signed floor. -/
theorem allocationEnvelope_endpoint_max_signed (p s A B : ℝ) (n k m : ℕ)
    (bref c w cn a b α : ℝ)
    (hp : 0 < p) (hp1 : p < 1) (hs : 0 ≤ s) (hk : k ≤ n)
    (hm : 0 < m) (hbref : 0 < bref) (hw : 0 ≤ w) (hcn : 0 ≤ cn)
    (ha : 0 ≤ a) (hb : b ≤ 1) (hα : α ∈ Icc a b)
    (hδ : ∀ x ∈ Icc a b, 0 < A + B * x) :
    let L := gDelta p s (A + B * a) a + min (allocationDeriv p s A B a) 0 * (b - a)
    allocationEnvelope p s A B n k m bref c w cn α ≤
      max (w * referenceSumPrice bref m (allocationVariance p s n k a) c - cn * L)
        (w * referenceSumPrice bref m (allocationVariance p s n k b) c - cn * L) := by
  exact allocationEnvelope_le_variance_corners p s A B n k m bref c w cn a b α _
    hp hp1 hs hk hm hbref hw hcn ha hb hα
    (gDelta_affine_interval_floor p s A B a b α hp hp1 hs hδ hα)

end BerryEsseen.AllocationEnvelope

#print axioms BerryEsseen.AllocationEnvelope.allocationVariance_eq_actual_W
#print axioms BerryEsseen.AllocationEnvelope.referencePrice_allocation_increment
#print axioms BerryEsseen.AllocationEnvelope.allocationEnvelope_increment
#print axioms BerryEsseen.AllocationEnvelope.allocationEnvelope_le_left
#print axioms BerryEsseen.AllocationEnvelope.allocationEnvelope_endpoint_max
#print axioms BerryEsseen.AllocationEnvelope.allocationEnvelope_endpoint_max_signed
