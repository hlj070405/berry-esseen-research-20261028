module

public import BerryEsseen.FrozenReferencePrice

@[expose] public section

/-! 2026-10-29: separate the actual inward/support caps from the enlarged
fixed reference caps. Only the actual caps enter Delta and delta budgets.
Zero source caps retain their genuine Dirac reference; fixed reference caps
remain positive even at zero actual source variance. -/

noncomputable section

namespace BerryEsseen.EnlargedFrozenReference

open MeasureTheory
open StopLossShape

/-- At a zero source cap the source reference is literally Dirac zero.
The variance enlargement starts from referenceLaw(B,0), not a fictitious
positive actual source variance. -/
theorem endpointReferenceLaw_le_fixed (ν : Measure ℝ) (a B Z : ℝ)
    (ha : 0 ≤ a) (hB : 0 < B) (haB : a ≤ B)
    (hZ : TwoMoment.lawSecondMoment ν ≤ Z) :
    TwoMoment.SquarePositiveOrder (TwoMoment.endpointReferenceLaw ν a) (TwoMoment.referenceLaw B Z) := by
  by_cases hzero : a = 0
  · rw [hzero, TwoMoment.endpointReferenceLaw_zero]
    have ho := TwoMoment.squarePositiveOrder_referenceLaw_variance_mono B 0 Z hB (by norm_num)
      ((TwoMoment.lawSecondMoment_nonneg ν).trans hZ)
    rw [TwoMoment.referenceLaw_zero B hB] at ho
    exact ho
  · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm hzero)
    rw [TwoMoment.endpointReferenceLaw_of_pos ν a hapos]
    exact TwoMoment.squarePositiveOrder_referenceLaw_parameters_mono a B
      (TwoMoment.lawSecondMoment ν) Z hapos haB (TwoMoment.lawSecondMoment_nonneg ν) hZ

private lemma endpointReference_integrable (ν : Measure ℝ) (a : ℝ) (ha : 0 ≤ a) (f : ℝ → ℝ) :
    Integrable f (TwoMoment.endpointReferenceLaw ν a) := by
  by_cases hzero : a = 0
  · rw [hzero, TwoMoment.endpointReferenceLaw_zero]
    exact integrable_dirac (by simp)
  · rw [TwoMoment.endpointReferenceLaw_of_pos ν a (lt_of_le_of_ne ha (Ne.symm hzero))]
    exact TwoMoment.integrable_referenceLaw _ _ f

private lemma endpointReference_mean_zero (ν : Measure ℝ) (a : ℝ) (ha : 0 ≤ a) :
    (∫ x : ℝ, x ∂TwoMoment.endpointReferenceLaw ν a) = 0 := by
  by_cases hzero : a = 0
  · rw [hzero, TwoMoment.endpointReferenceLaw_zero]
    simp
  · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm hzero)
    rw [TwoMoment.endpointReferenceLaw_of_pos ν a hapos]
    exact TwoMoment.integral_referenceLaw_id a _ hapos (TwoMoment.lawSecondMoment_nonneg ν)

/-- L2 is established for the actual reference convolution, including
zero caps and empty groups, before invoking the ordinary-integral Q order. -/
theorem coupledReference_integrable_square (ν0 ν1 : Measure ℝ) (a0 O1 : ℝ)
    (ha0 : 0 ≤ a0) (hO1 : 0 ≤ O1) (n k : ℕ) :
    Integrable (fun x : ℝ => x ^ 2) (TwoMoment.coupledReferenceLaw ν0 ν1 a0 O1 n k) := by
  haveI := TwoMoment.endpointReferenceLaw_isProbabilityMeasure ν0 a0 ha0
  haveI := TwoMoment.endpointReferenceLaw_isProbabilityMeasure ν1 O1 hO1
  have h0 := CommonProductMoments.convPower_moments (TwoMoment.endpointReferenceLaw ν0 a0)
    (endpointReference_integrable ν0 a0 ha0 (fun x => x))
    (endpointReference_integrable ν0 a0 ha0 (fun x => x ^ 2))
    (endpointReference_mean_zero ν0 a0 ha0) (n - k)
  have h1 := CommonProductMoments.convPower_moments (TwoMoment.endpointReferenceLaw ν1 O1)
    (endpointReference_integrable ν1 O1 hO1 (fun x => x))
    (endpointReference_integrable ν1 O1 hO1 (fun x => x ^ 2))
    (endpointReference_mean_zero ν1 O1 hO1) k
  unfold TwoMoment.coupledReferenceLaw
  exact CommonProductMoments.conv_integrable_square _ _ h1.1 h1.2.1 h0.1 h0.2.1

theorem coupledReference_order_le_enlarged (ν0 ν1 : Measure ℝ)
    (a0 O1 B0 B1 Z0 Z1 : ℝ) (n k : ℕ)
    (ha0 : 0 ≤ a0) (hO1 : 0 ≤ O1) (hB0 : 0 < B0) (hB1 : 0 < B1)
    (haB0 : a0 ≤ B0) (hOB1 : O1 ≤ B1)
    (hZ0 : TwoMoment.lawSecondMoment ν0 ≤ Z0)
    (hZ1 : TwoMoment.lawSecondMoment ν1 ≤ Z1) :
    TwoMoment.SquarePositiveOrder (TwoMoment.coupledReferenceLaw ν0 ν1 a0 O1 n k)
      (DoubleBinomialReference.law B0 Z0 (n - k) B1 Z1 k) := by
  haveI := TwoMoment.endpointReferenceLaw_isProbabilityMeasure ν0 a0 ha0
  haveI := TwoMoment.endpointReferenceLaw_isProbabilityMeasure ν1 O1 hO1
  haveI := TwoMoment.referenceLaw_isProbabilityMeasure B0 Z0 hB0
    ((TwoMoment.lawSecondMoment_nonneg ν0).trans hZ0)
  haveI := TwoMoment.referenceLaw_isProbabilityMeasure B1 Z1 hB1
    ((TwoMoment.lawSecondMoment_nonneg ν1).trans hZ1)
  have h0 := TwoMoment.squarePositiveOrder_convPower (TwoMoment.endpointReferenceLaw ν0 a0)
    (TwoMoment.referenceLaw B0 Z0) (endpointReferenceLaw_le_fixed ν0 a0 B0 Z0 ha0 hB0 haB0 hZ0) (n - k)
  have h1 := TwoMoment.squarePositiveOrder_convPower (TwoMoment.endpointReferenceLaw ν1 O1)
    (TwoMoment.referenceLaw B1 Z1) (endpointReferenceLaw_le_fixed ν1 O1 B1 Z1 hO1 hB1 hOB1 hZ1) k
  unfold TwoMoment.coupledReferenceLaw DoubleBinomialReference.law
  rw [Measure.conv_comm (MixtureSum.convPower (TwoMoment.endpointReferenceLaw ν1 O1) k)
    (MixtureSum.convPower (TwoMoment.endpointReferenceLaw ν0 a0) (n - k))]
  exact TwoMoment.squarePositiveOrder_conv _ _ _ _ h0 h1

theorem coupledReference_Q_le_enlarged (ν0 ν1 : Measure ℝ)
    (a0 O1 B0 B1 Z0 Z1 : ℝ) (n k : ℕ)
    (ha0 : 0 ≤ a0) (hO1 : 0 ≤ O1) (hB0 : 0 < B0) (hB1 : 0 < B1)
    (haB0 : a0 ≤ B0) (hOB1 : O1 ≤ B1)
    (hZ0 : TwoMoment.lawSecondMoment ν0 ≤ Z0)
    (hZ1 : TwoMoment.lawSecondMoment ν1 ≤ Z1) (A : ℝ) :
    Q (TwoMoment.coupledReferenceLaw ν0 ν1 a0 O1 n k) A ≤
      Q (DoubleBinomialReference.law B0 Z0 (n - k) B1 Z1 k) A := by
  haveI := TwoMoment.coupledReferenceLaw_isProbabilityMeasure ν0 ν1 a0 O1 ha0 hO1 n k
  haveI := DoubleBinomialReference.law_isProbabilityMeasure B0 Z0 (n - k) B1 Z1 k
    hB0 ((TwoMoment.lawSecondMoment_nonneg ν0).trans hZ0)
    hB1 ((TwoMoment.lawSecondMoment_nonneg ν1).trans hZ1)
  exact FrozenReferencePrice.Q_mono_of_squarePositiveOrder _ _
    (coupledReference_integrable_square ν0 ν1 a0 O1 ha0 hO1 n k)
    (DoubleBinomialReference.integrable_law B0 Z0 (n - k) B1 Z1 k
      hB0 ((TwoMoment.lawSecondMoment_nonneg ν0).trans hZ0)
      hB1 ((TwoMoment.lawSecondMoment_nonneg ν1).trans hZ1) (fun x => x ^ 2))
    (coupledReference_order_le_enlarged ν0 ν1 a0 O1 B0 B1 Z0 Z1 n k
      ha0 hO1 hB0 hB1 haB0 hOB1 hZ0 hZ1) A

/-- Actual a0/a1/O1 control the original coupling and moment budget.
B0/B1 enlarge only the reference price: no enlarged-cap budget is imposed. -/
theorem canonical_targetResidual_le_enlarged_frozen_Q
    (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ) (n k : ℕ) (hn : 0 < n) (hk : k ≤ n)
    (a0 a1 O1 B0 B1 Z0 Z1 Δ δ η t ci : ℝ)
    (ha0 : 0 ≤ a0) (ha1 : 0 ≤ a1) (hO1 : 0 ≤ O1)
    (hB0 : 0 < B0) (hB1 : 0 < B1) (haB0 : a0 ≤ B0) (hOB1 : O1 ≤ B1)
    (hcapΔ : a0 + a1 ≤ Δ) (hΔ : Δ < 1) (hδ : 0 < δ) (hcapδ : a0 + a1 ≤ δ) (hη : 0 < η)
    (hinner0 : ∀ᵐ u ∂(CanonicalSign.residual0 μ hμ : Measure ℝ), u ≤ a0)
    (hinner1 : ∀ᵐ u ∂(CanonicalSign.residual1 μ hμ : Measure ℝ), -a1 ≤ u)
    (houter1 : ∀ᵐ u ∂(CanonicalSign.residual1 μ hμ : Measure ℝ), u ≤ O1)
    (hPrefix : ∀ r : ℕ, 1 ≤ r → r ≤ n - k →
      Staircase.prefixMass (fun j => CoupledPrice.canonicalBinomialWeight μ n (k + j)) r ≤
        η * ((r : ℝ) * (1 - Δ)))
    (hci0 : 0 ≤ ci) (hci : ci ≤ esseenConstant / Real.sqrt (n : ℝ))
    (hZ0 : TwoMoment.lawSecondMoment (CanonicalSign.residual0 μ hμ : Measure ℝ) ≤ Z0)
    (hZ1 : TwoMoment.lawSecondMoment (CanonicalSign.residual1 μ hμ : Measure ℝ) ≤ Z1) :
    ConditionalResidual.positiveTargetResidual μ n (ConditionalResidual.canonicalThreshold μ hμ n k t) ≤
      Staircase.lowerMass (CoupledPrice.canonicalBinomialWeight μ n) k + η *
        (t + Q (DoubleBinomialReference.law B0 Z0 (n - k) B1 Z1 k)
          (t + CoupledPrice.canonicalBinomialWeight μ n k / η)) -
        GaussianTools.Phi (ConditionalResidual.canonicalThreshold μ hμ n k t) -
        ci * MomentBudget.gDelta (CanonicalSign.p μ) (CanonicalSign.noiseVariance μ hμ) δ
          (ConditionalResidual.actualAllocation μ hμ) := by
  have hActual := OptimizedStaircasePrice.canonical_targetResidual_le_Q
    μ hμ n k hn hk a0 a1 O1 Δ δ η t ci ha0 ha1 hO1
    hcapΔ hΔ hδ hcapδ hη hinner0 hinner1 houter1 hPrefix hci0 hci
  have hQ := coupledReference_Q_le_enlarged
    (CanonicalSign.residual0 μ hμ : Measure ℝ) (CanonicalSign.residual1 μ hμ : Measure ℝ)
    a0 O1 B0 B1 Z0 Z1 n k ha0 hO1 hB0 hB1 haB0 hOB1 hZ0 hZ1
    (t + CoupledPrice.canonicalBinomialWeight μ n k / η)
  have hm := mul_le_mul_of_nonneg_left hQ hη.le
  linarith only [hActual, hm]

end BerryEsseen.EnlargedFrozenReference

#print axioms BerryEsseen.EnlargedFrozenReference.endpointReferenceLaw_le_fixed
#print axioms BerryEsseen.EnlargedFrozenReference.coupledReference_integrable_square
#print axioms BerryEsseen.EnlargedFrozenReference.coupledReference_order_le_enlarged
#print axioms BerryEsseen.EnlargedFrozenReference.coupledReference_Q_le_enlarged
#print axioms BerryEsseen.EnlargedFrozenReference.canonical_targetResidual_le_enlarged_frozen_Q
