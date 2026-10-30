module

public import BerryEsseen.EnlargedFrozenReference

@[expose] public section

/-! 2026-10-29: one common-cap reference from the actual total variance
label of the coupled two-group reference. Independent variance equalization
is applied to the genuine finite list of coordinates. The total ceiling is
an explicit acquired input; the common cap never enters the inward budget. -/

noncomputable section

namespace BerryEsseen.UniformCoupledReference

open MeasureTheory
open StopLossShape

lemma referenceList_replicate_eq_convPower (B z : ℝ) (m : ℕ) :
    TwoMoment.referenceListSumLaw B (List.replicate m z) =
      MixtureSum.convPower (TwoMoment.referenceLaw B z) m := by
  rw [TwoMoment.referenceListSumLaw_replicate_eq_finiteIndependentSumLaw,
    TwoMoment.finiteIndependentSumLaw_const_eq_convPower]

theorem doubleBinomial_eq_referenceList (B z0 z1 : ℝ) (n0 n1 : ℕ) :
    DoubleBinomialReference.law B z0 n0 B z1 n1 =
      TwoMoment.referenceListSumLaw B (List.replicate n0 z0 ++ List.replicate n1 z1) := by
  rw [TwoMoment.referenceListSumLaw_append, referenceList_replicate_eq_convPower,
    referenceList_replicate_eq_convPower]
  rfl

/-- The two labels remain attached to their actual coordinate counts
until the proved finite-list equalization is invoked. -/
theorem doubleBinomial_order_le_uniform (B z0 z1 V : ℝ) (n0 n1 : ℕ)
    (hB : 0 < B) (hn : 0 < n0 + n1) (hz0 : 0 ≤ z0) (hz1 : 0 ≤ z1)
    (hV : (n0 : ℝ) * z0 + (n1 : ℝ) * z1 ≤ V) :
    TwoMoment.SquarePositiveOrder (DoubleBinomialReference.law B z0 n0 B z1 n1)
      (TwoMoment.uniformReferenceSumLaw B (n0 + n1) V) := by
  let zs := List.replicate n0 z0 ++ List.replicate n1 z1
  let T := (n0 : ℝ) * z0 + (n1 : ℝ) * z1
  have hlen : zs.length = n0 + n1 := by simp [zs]
  have hzs : ∀ v ∈ zs, 0 ≤ v := by
    intro v hv
    change v ∈ List.replicate n0 z0 ++ List.replicate n1 z1 at hv
    rcases List.mem_append.mp hv with h0 | h1
    · rw [List.eq_of_mem_replicate h0]
      exact hz0
    · rw [List.eq_of_mem_replicate h1]
      exact hz1
  have hsum : zs.sum = T := by simp [zs, T, nsmul_eq_mul]
  have hT : 0 ≤ T := add_nonneg (mul_nonneg (Nat.cast_nonneg _) hz0)
    (mul_nonneg (Nat.cast_nonneg _) hz1)
  have hequal := TwoMoment.referenceListSumLaw_le_uniform_total B T (n0 + n1) zs
    hB hn hlen hzs hsum
  change TwoMoment.SquarePositiveOrder
    (TwoMoment.referenceListSumLaw B (List.replicate n0 z0 ++ List.replicate n1 z1))
    (TwoMoment.referenceListSumLaw B (List.replicate (n0 + n1) (T / (n0 + n1 : ℕ)) )) at hequal
  rw [← doubleBinomial_eq_referenceList,
    TwoMoment.referenceListSumLaw_replicate_eq_finiteIndependentSumLaw] at hequal
  change TwoMoment.SquarePositiveOrder (DoubleBinomialReference.law B z0 n0 B z1 n1)
    (TwoMoment.uniformReferenceSumLaw B (n0 + n1) T) at hequal
  exact TwoMoment.squarePositiveOrder_trans hequal
    (TwoMoment.squarePositiveOrder_uniformReferenceSumLaw_mono B B (n0 + n1) T V hB le_rfl hT hV)

theorem coupledReference_order_le_uniform (ν0 ν1 : Measure ℝ) (a0 O1 B V : ℝ)
    (n k : ℕ) (hn : 0 < n) (hk : k ≤ n)
    (ha0 : 0 ≤ a0) (hO1 : 0 ≤ O1) (hB : 0 < B) (haB : a0 ≤ B) (hOB : O1 ≤ B)
    (hV : StaircasePrices.actualCountVariance ν0 ν1 n k ≤ V) :
    TwoMoment.SquarePositiveOrder (TwoMoment.coupledReferenceLaw ν0 ν1 a0 O1 n k)
      (TwoMoment.uniformReferenceSumLaw B n V) := by
  have hEnlarge := EnlargedFrozenReference.coupledReference_order_le_enlarged ν0 ν1
    a0 O1 B B (TwoMoment.lawSecondMoment ν0) (TwoMoment.lawSecondMoment ν1) n k
    ha0 hO1 hB hB haB hOB le_rfl le_rfl
  have hcount : (n - k) + k = n := Nat.sub_add_cancel hk
  have hEqualize := doubleBinomial_order_le_uniform B (TwoMoment.lawSecondMoment ν0)
    (TwoMoment.lawSecondMoment ν1) V (n - k) k hB (by simpa only [hcount] using hn)
    (TwoMoment.lawSecondMoment_nonneg ν0) (TwoMoment.lawSecondMoment_nonneg ν1)
    (by simpa only [StaircasePrices.actualCountVariance] using hV)
  rw [hcount] at hEqualize
  exact TwoMoment.squarePositiveOrder_trans hEnlarge hEqualize

/-- Only the actual total label is capped. No separate source variance
ceiling, optimizing width, or numerical value of V is presumed. -/
theorem coupledReference_Q_le_uniform (ν0 ν1 : Measure ℝ) (a0 O1 B V : ℝ)
    (n k : ℕ) (hn : 0 < n) (hk : k ≤ n)
    (ha0 : 0 ≤ a0) (hO1 : 0 ≤ O1) (hB : 0 < B) (haB : a0 ≤ B) (hOB : O1 ≤ B)
    (hV : StaircasePrices.actualCountVariance ν0 ν1 n k ≤ V) (A : ℝ) :
    Q (TwoMoment.coupledReferenceLaw ν0 ν1 a0 O1 n k) A ≤
      Q (TwoMoment.uniformReferenceSumLaw B n V) A := by
  have hV0 : 0 ≤ V := (StaircasePrices.actualCountVariance_nonneg ν0 ν1 n k).trans hV
  haveI := TwoMoment.coupledReferenceLaw_isProbabilityMeasure ν0 ν1 a0 O1 ha0 hO1 n k
  haveI := TwoMoment.uniformReferenceSumLaw_isProbabilityMeasure B n V hB hV0
  exact FrozenReferencePrice.Q_mono_of_squarePositiveOrder _ _
    (EnlargedFrozenReference.coupledReference_integrable_square ν0 ν1 a0 O1 ha0 hO1 n k)
    (TwoMoment.uniformReferenceSumLaw_moments B n V hB hn hV0).2.1
    (coupledReference_order_le_uniform ν0 ν1 a0 O1 B V n k hn hk ha0 hO1 hB haB hOB hV) A

/-- The original actual caps still license the coupling and moment
floor. The common reference cap B is used only after that bound. -/
theorem canonical_targetResidual_le_uniform_Q
    (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ) (n k : ℕ) (hn : 0 < n) (hk : k ≤ n)
    (a0 a1 O1 B V Δ δ η t ci : ℝ)
    (ha0 : 0 ≤ a0) (ha1 : 0 ≤ a1) (hO1 : 0 ≤ O1)
    (hB : 0 < B) (haB : a0 ≤ B) (hOB : O1 ≤ B)
    (hcapΔ : a0 + a1 ≤ Δ) (hΔ : Δ < 1) (hδ : 0 < δ) (hcapδ : a0 + a1 ≤ δ) (hη : 0 < η)
    (hinner0 : ∀ᵐ u ∂(CanonicalSign.residual0 μ hμ : Measure ℝ), u ≤ a0)
    (hinner1 : ∀ᵐ u ∂(CanonicalSign.residual1 μ hμ : Measure ℝ), -a1 ≤ u)
    (houter1 : ∀ᵐ u ∂(CanonicalSign.residual1 μ hμ : Measure ℝ), u ≤ O1)
    (hPrefix : ∀ r : ℕ, 1 ≤ r → r ≤ n - k →
      Staircase.prefixMass (fun j => CoupledPrice.canonicalBinomialWeight μ n (k + j)) r ≤
        η * ((r : ℝ) * (1 - Δ)))
    (hci0 : 0 ≤ ci) (hci : ci ≤ esseenConstant / Real.sqrt (n : ℝ))
    (hV : StaircasePrices.actualCountVariance (CanonicalSign.residual0 μ hμ : Measure ℝ)
      (CanonicalSign.residual1 μ hμ : Measure ℝ) n k ≤ V) :
    ConditionalResidual.positiveTargetResidual μ n (ConditionalResidual.canonicalThreshold μ hμ n k t) ≤
      Staircase.lowerMass (CoupledPrice.canonicalBinomialWeight μ n) k + η *
        (t + Q (TwoMoment.uniformReferenceSumLaw B n V)
          (t + CoupledPrice.canonicalBinomialWeight μ n k / η)) -
        GaussianTools.Phi (ConditionalResidual.canonicalThreshold μ hμ n k t) -
        ci * MomentBudget.gDelta (CanonicalSign.p μ) (CanonicalSign.noiseVariance μ hμ) δ
          (ConditionalResidual.actualAllocation μ hμ) := by
  have hActual := OptimizedStaircasePrice.canonical_targetResidual_le_Q
    μ hμ n k hn hk a0 a1 O1 Δ δ η t ci ha0 ha1 hO1
    hcapΔ hΔ hδ hcapδ hη hinner0 hinner1 houter1 hPrefix hci0 hci
  have hQ := coupledReference_Q_le_uniform
    (CanonicalSign.residual0 μ hμ : Measure ℝ) (CanonicalSign.residual1 μ hμ : Measure ℝ)
    a0 O1 B V n k hn hk ha0 hO1 hB haB hOB hV
    (t + CoupledPrice.canonicalBinomialWeight μ n k / η)
  have hm := mul_le_mul_of_nonneg_left hQ hη.le
  linarith only [hActual, hm]

end BerryEsseen.UniformCoupledReference

#print axioms BerryEsseen.UniformCoupledReference.doubleBinomial_eq_referenceList
#print axioms BerryEsseen.UniformCoupledReference.doubleBinomial_order_le_uniform
#print axioms BerryEsseen.UniformCoupledReference.coupledReference_order_le_uniform
#print axioms BerryEsseen.UniformCoupledReference.coupledReference_Q_le_uniform
#print axioms BerryEsseen.UniformCoupledReference.canonical_targetResidual_le_uniform_Q
