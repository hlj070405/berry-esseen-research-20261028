module

public import BerryEsseen.CentralGapConditionalIntegral
public import BerryEsseen.CanonicalResidualMomentBounds
public import BerryEsseen.FrozenReferencePrice

@[expose] public section

/-! 2026-10-30: actual canonical conditional sums are bounded by genuine
independent two-group square-positive references. The negative side
rebuilds the comparison from reflected marginal laws and their true
lower support bounds; an existing upper order is never reflected.
Only caps are enlarged. The source variances and actual counts remain.
-/

noncomputable section

namespace BerryEsseen.CentralGapReferenceSquareBounds

open MeasureTheory Set
open CanonicalSign CentralGap CentralGapConditionalIntegral

def variance0 (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) : ℝ :=
  ∫ u : ℝ, u ^ 2 ∂(residual0 μ h : Measure ℝ)

def variance1 (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) : ℝ :=
  ∫ u : ℝ, u ^ 2 ∂(residual1 μ h : Measure ℝ)

lemma variance0_nonneg (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) : 0 ≤ variance0 μ h :=
  integral_nonneg (fun u => sq_nonneg u)

lemma variance1_nonneg (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) : 0 ≤ variance1 μ h :=
  integral_nonneg (fun u => sq_nonneg u)

lemma coupledReferenceLaw_eq_double (ν0 ν1 : Measure ℝ) (B0 B1 : ℝ)
    (hB0 : 0 < B0) (hB1 : 0 < B1) (N k : ℕ) :
    TwoMoment.coupledReferenceLaw ν0 ν1 B0 B1 N k =
      DoubleBinomialReference.law B0 (TwoMoment.lawSecondMoment ν0) (N - k)
        B1 (TwoMoment.lawSecondMoment ν1) k := by
  have := TwoMoment.referenceLaw_isProbabilityMeasure B0 (TwoMoment.lawSecondMoment ν0)
    hB0 (TwoMoment.lawSecondMoment_nonneg ν0)
  have := TwoMoment.referenceLaw_isProbabilityMeasure B1 (TwoMoment.lawSecondMoment ν1)
    hB1 (TwoMoment.lawSecondMoment_nonneg ν1)
  unfold TwoMoment.coupledReferenceLaw DoubleBinomialReference.law
  rw [TwoMoment.endpointReferenceLaw_of_pos ν0 B0 hB0,
    TwoMoment.endpointReferenceLaw_of_pos ν1 B1 hB1, Measure.conv_comm]

lemma integrable_residualCount_square (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (N k : ℕ) : Integrable (fun r : ℝ => r ^ 2) (residualCountLaw μ h N k) := by
  have h0 := residual0_centered μ h
  have h1 := residual1_centered μ h
  have hc0 := CommonProductMoments.convPower_moments (residual0 μ h : Measure ℝ)
    h0.integrable_first h0.integrable_second h0.mean_zero (N - k)
  have hc1 := CommonProductMoments.convPower_moments (residual1 μ h : Measure ℝ)
    h1.integrable_first h1.integrable_second h1.mean_zero k
  unfold residualCountLaw
  exact CommonProductMoments.conv_integrable_square _ _ hc1.1 hc1.2.1 hc0.1 hc0.2.1

/-- The source upper caps are acquired from the same original μ. -/
theorem residualCount_order_le_reference (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (R : ℝ) (_hR : 0 ≤ R) (hbound : (μ : Measure ℝ).support ⊆ Icc (-R) R)
    (N k : ℕ) (hk : k ≤ N) (B0 B1 : ℝ) (hB0 : 0 < B0) (hB1 : 0 < B1)
    (hcap0 : a0 μ h ≤ B0) (hcap1 : O1 μ h R ≤ B1) :
    TwoMoment.SquarePositiveOrder (residualCountLaw μ h N k)
      (DoubleBinomialReference.law B0 (variance0 μ h) (N - k) B1 (variance1 μ h) k) := by
  have h0 := residual0_centered μ h
  have h1 := residual1_centered μ h
  have hu0 : ∀ᵐ u ∂(residual0 μ h : Measure ℝ), u ≤ B0 :=
    (CentralGap.residual0_upper μ h).mono (fun _ hu => hu.trans hcap0)
  have hu1 : ∀ᵐ u ∂(residual1 μ h : Measure ℝ), u ≤ B1 :=
    (CanonicalResidualMomentBounds.residual1_upper_of_support μ h R hbound).mono
      (fun _ hu => hu.trans hcap1)
  have ho := TwoMoment.squarePositiveOrder_map_W
    (residual0 μ h : Measure ℝ) (residual1 μ h : Measure ℝ) B0 B1 hB0.le hB1.le
    h0.integrable_second h1.integrable_second h0.mean_zero h1.mean_zero hu0 hu1 N k hk
  rw [coupledReferenceLaw_eq_double _ _ B0 B1 hB0 hB1 N k] at ho
  rw [residualCountLaw_eq_map_W μ h N k hk]
  exact ho

/-- Rebuild the negative-side order from -ν0 and -ν1. Their variances
are unchanged; their upper caps come from the original lower bounds. -/
theorem reflected_residualCount_order_le_reference (μ : ProbabilityMeasure ℝ)
    (h : StandardizedLaw μ) (R : ℝ) (_hR : 0 ≤ R)
    (hbound : (μ : Measure ℝ).support ⊆ Icc (-R) R)
    (N k : ℕ) (hk : k ≤ N) (B0 B1 : ℝ) (hB0 : 0 < B0) (hB1 : 0 < B1)
    (hcap0 : O0 μ h R ≤ B0) (hcap1 : a1 μ h ≤ B1) :
    TwoMoment.SquarePositiveOrder ((residualCountLaw μ h N k).map (fun r : ℝ => -r))
      (DoubleBinomialReference.law B0 (variance0 μ h) (N - k) B1 (variance1 μ h) k) := by
  have h0 := residual0_centered μ h
  have h1 := residual1_centered μ h
  have hl0 : ∀ᵐ u ∂(residual0 μ h : Measure ℝ), -B0 ≤ u := by
    filter_upwards [CanonicalResidualMomentBounds.residual0_lower_of_support μ h R hbound]
      with u hu
    linarith only [hu, hcap0]
  have hl1 : ∀ᵐ u ∂(residual1 μ h : Measure ℝ), -B1 ≤ u := by
    filter_upwards [CentralGap.residual1_lower μ h] with u hu
    linarith only [hu, hcap1]
  have hr0 := TwoMoment.reflected_residual_moments (residual0 μ h : Measure ℝ)
    h0.integrable_second h0.mean_zero
  have hr1 := TwoMoment.reflected_residual_moments (residual1 μ h : Measure ℝ)
    h1.integrable_second h1.mean_zero
  have ho := TwoMoment.squarePositiveOrder_twoGroup
    ((residual0 μ h : Measure ℝ).map (fun u : ℝ => -u))
    ((residual1 μ h : Measure ℝ).map (fun u : ℝ => -u)) B0 B1 hB0.le hB1.le
    hr0.2.1 hr1.2.1 hr0.2.2.1 hr1.2.2.1
    (TwoMoment.reflected_upper_of_lower _ B0 hl0)
    (TwoMoment.reflected_upper_of_lower _ B1 hl1) N k
  rw [← TwoMoment.map_neg_W _ _ N k hk, TwoMoment.coupledReferenceLaw_map_neg_inputs,
    coupledReferenceLaw_eq_double _ _ B0 B1 hB0 hB1 N k] at ho
  rw [residualCountLaw_eq_map_W μ h N k hk,
    Measure.map_map measurable_neg (CommonProduct.measurable_W N k hk)]
  exact ho

/-- Ordinary square expectations are obtained from the genuine L2 laws. -/
theorem residualCount_square_le_reference (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (R : ℝ) (hR : 0 ≤ R) (hbound : (μ : Measure ℝ).support ⊆ Icc (-R) R)
    (N k : ℕ) (hk : k ≤ N) (B0 B1 : ℝ) (hB0 : 0 < B0) (hB1 : 0 < B1)
    (hcap0 : a0 μ h ≤ B0) (hcap1 : O1 μ h R ≤ B1) (A : ℝ) :
    (∫ r, (max (r - A) 0) ^ 2 ∂residualCountLaw μ h N k) ≤
      ∫ r, (max (r - A) 0) ^ 2
        ∂DoubleBinomialReference.law B0 (variance0 μ h) (N - k) B1 (variance1 μ h) k := by
  have := DoubleBinomialReference.law_isProbabilityMeasure B0 (variance0 μ h) (N - k)
    B1 (variance1 μ h) k hB0 (variance0_nonneg μ h) hB1 (variance1_nonneg μ h)
  exact FrozenReferencePrice.integral_squarePositivePart_mono _ _
    (integrable_residualCount_square μ h N k)
    (DoubleBinomialReference.integrable_law _ _ _ _ _ _
      hB0 (variance0_nonneg μ h) hB1 (variance1_nonneg μ h) _)
    (residualCount_order_le_reference μ h R hR hbound N k hk B0 B1 hB0 hB1 hcap0 hcap1) A

theorem reflected_residualCount_square_le_reference (μ : ProbabilityMeasure ℝ)
    (h : StandardizedLaw μ) (R : ℝ) (hR : 0 ≤ R)
    (hbound : (μ : Measure ℝ).support ⊆ Icc (-R) R)
    (N k : ℕ) (hk : k ≤ N) (B0 B1 : ℝ) (hB0 : 0 < B0) (hB1 : 0 < B1)
    (hcap0 : O0 μ h R ≤ B0) (hcap1 : a1 μ h ≤ B1) (A : ℝ) :
    (∫ r, (max (-r - A) 0) ^ 2 ∂residualCountLaw μ h N k) ≤
      ∫ r, (max (r - A) 0) ^ 2
        ∂DoubleBinomialReference.law B0 (variance0 μ h) (N - k) B1 (variance1 μ h) k := by
  have := DoubleBinomialReference.law_isProbabilityMeasure B0 (variance0 μ h) (N - k)
    B1 (variance1 μ h) k hB0 (variance0_nonneg μ h) hB1 (variance1_nonneg μ h)
  have hSq : Integrable (fun r : ℝ => r ^ 2)
      ((residualCountLaw μ h N k).map (fun r : ℝ => -r)) := by
    apply (integrable_map_measure (by fun_prop) measurable_neg.aemeasurable).mpr
    change Integrable (fun r : ℝ => (-r) ^ 2) (residualCountLaw μ h N k)
    simpa only [neg_sq] using integrable_residualCount_square μ h N k
  have hi := FrozenReferencePrice.integral_squarePositivePart_mono _ _ hSq
    (DoubleBinomialReference.integrable_law _ _ _ _ _ _
      hB0 (variance0_nonneg μ h) hB1 (variance1_nonneg μ h) _)
    (reflected_residualCount_order_le_reference μ h R hR hbound N k hk B0 B1 hB0 hB1 hcap0 hcap1) A
  rw [integral_map measurable_neg.aemeasurable (by fun_prop)] at hi
  exact hi

def positiveSquarePrice (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n j : ℕ) (t B0 B1 : ℝ) : ℝ :=
  ∫ r, (max (r - (t + a1 μ h)) 0) ^ 2
    ∂DoubleBinomialReference.law B0 (variance0 μ h) (n - j) B1 (variance1 μ h) (j - 1)

def negativeTailSquarePrice (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n j : ℕ) (t B0 B1 : ℝ) : ℝ :=
  ∫ r, (max (r - (a0 μ h - t + 3 * (1 - a0 μ h - a1 μ h) / 4)) 0) ^ 2
    ∂DoubleBinomialReference.law B0 (variance0 μ h) (n - 1 - j) B1 (variance1 μ h) j

/-- For N=n-1 and k=j-1, the group-0 count is n-j. -/
theorem positiveAdjacent_square_le_reference (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (R : ℝ) (hR : 0 ≤ R) (hbound : (μ : Measure ℝ).support ⊆ Icc (-R) R)
    (n j : ℕ) (_hn : 2 ≤ n) (hj : 1 ≤ j) (hjn : j ≤ n - 1)
    (t B0 B1 : ℝ) (hB0 : 0 < B0) (hB1 : 0 < B1)
    (hcap0 : a0 μ h ≤ B0) (hcap1 : O1 μ h R ≤ B1) :
    (∫ x, (max x 0) ^ 2 ∂positiveAdjacentLaw μ h n j t) ≤
      positiveSquarePrice μ h n j t B0 B1 := by
  have hcount : (n - 1) - (j - 1) = n - j := by omega
  have hi := residualCount_square_le_reference μ h R hR hbound (n - 1) (j - 1)
    (by omega) B0 B1 hB0 hB1 hcap0 hcap1 (t + a1 μ h)
  rw [hcount] at hi
  unfold positiveAdjacentLaw
  rw [integral_map (by fun_prop) (by fun_prop)]
  calc
    _ = ∫ r, (max (r - (t + a1 μ h)) 0) ^ 2
        ∂residualCountLaw μ h (n - 1) (j - 1) := by
      apply integral_congr_ae
      filter_upwards [] with r
      congr 2
      ring
    _ ≤ _ := hi

/-- The reflected square-tail threshold includes the affine shift.
No positivity of source variances or nonempty source groups is needed. -/
theorem negativeAdjacent_tail_square_le_reference (μ : ProbabilityMeasure ℝ)
    (h : StandardizedLaw μ) (R : ℝ) (hR : 0 ≤ R)
    (hbound : (μ : Measure ℝ).support ⊆ Icc (-R) R)
    (n j : ℕ) (_hn : 2 ≤ n) (_hj : 1 ≤ j) (hjn : j ≤ n - 1)
    (t B0 B1 : ℝ) (hB0 : 0 < B0) (hB1 : 0 < B1)
    (hcap0 : O0 μ h R ≤ B0) (hcap1 : a1 μ h ≤ B1) :
    (∫ x, (max (x - 3 * (1 - a0 μ h - a1 μ h) / 4) 0) ^ 2
      ∂negativeAdjacentLaw μ h n j t) ≤ negativeTailSquarePrice μ h n j t B0 B1 := by
  have hi := reflected_residualCount_square_le_reference μ h R hR hbound (n - 1) j hjn
    B0 B1 hB0 hB1 hcap0 hcap1 (a0 μ h - t + 3 * (1 - a0 μ h - a1 μ h) / 4)
  unfold negativeAdjacentLaw
  rw [integral_map (by fun_prop) (by fun_prop)]
  calc
    _ = ∫ r, (max (-r - (a0 μ h - t + 3 * (1 - a0 μ h - a1 μ h) / 4)) 0) ^ 2
        ∂residualCountLaw μ h (n - 1) j := by
      apply integral_congr_ae
      filter_upwards [] with r
      congr 2
      ring
    _ ≤ _ := hi

end BerryEsseen.CentralGapReferenceSquareBounds

#print axioms BerryEsseen.CentralGapReferenceSquareBounds.residualCount_order_le_reference
#print axioms BerryEsseen.CentralGapReferenceSquareBounds.reflected_residualCount_order_le_reference
#print axioms BerryEsseen.CentralGapReferenceSquareBounds.residualCount_square_le_reference
#print axioms BerryEsseen.CentralGapReferenceSquareBounds.reflected_residualCount_square_le_reference
#print axioms BerryEsseen.CentralGapReferenceSquareBounds.positiveAdjacent_square_le_reference
#print axioms BerryEsseen.CentralGapReferenceSquareBounds.negativeAdjacent_tail_square_le_reference
