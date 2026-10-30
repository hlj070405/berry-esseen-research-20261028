module

public import BerryEsseen.DoubleBinomialReference
public import BerryEsseen.OptimizedStaircasePrice

@[expose] public section

/-! 2026-10-29: actual squared-positive-part order passes to the genuine
inf-width price. The two-group variance/cap enlargement then freezes the
reference law while retaining the original canonical residual, allocation,
prefix gate and Gaussian threshold. Variance ceilings are incoming bounds
on this same law, not an acquisition asserted by the formula. -/

noncomputable section

namespace BerryEsseen.FrozenReferencePrice

open MeasureTheory
open StopLossShape

theorem integral_squarePositivePart_mono (ν ν' : Measure ℝ)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ν']
    (hSq : Integrable (fun z : ℝ => z ^ 2) ν)
    (hSq' : Integrable (fun z : ℝ => z ^ 2) ν')
    (horder : TwoMoment.SquarePositiveOrder ν ν') (c : ℝ) :
    (∫ z, (max (z - c) 0) ^ 2 ∂ν) ≤ ∫ z, (max (z - c) 0) ^ 2 ∂ν' := by
  have hi : Integrable (fun z : ℝ => (max (z - c) 0) ^ 2) ν := by
    simpa only [id_eq] using TwoMoment.integrable_squarePositivePart ν id c measurable_id hSq
  have hi' : Integrable (fun z : ℝ => (max (z - c) 0) ^ 2) ν' := by
    simpa only [id_eq] using TwoMoment.integrable_squarePositivePart ν' id c measurable_id hSq'
  have ho := horder c
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall (fun _ => sq_nonneg _)),
    ← ofReal_integral_eq_lintegral_ofReal hi' (Filter.Eventually.of_forall (fun _ => sq_nonneg _))] at ho
  exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg (fun _ => sq_nonneg _))).mp ho

theorem price_mono_of_squarePositiveOrder (ν ν' : Measure ℝ)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ν']
    (hSq : Integrable (fun z : ℝ => z ^ 2) ν)
    (hSq' : Integrable (fun z : ℝ => z ^ 2) ν')
    (horder : TwoMoment.SquarePositiveOrder ν ν') (A h : ℝ) (hh : 0 < h) :
    price ν A h ≤ price ν' A h := by
  have ho := integral_squarePositivePart_mono ν ν' hSq hSq' horder (A - h)
  have heq (z : ℝ) : z - (A - h) = z - A + h := by ring
  simp only [heq] at ho
  exact div_le_div_of_nonneg_right ho (by positivity : 0 ≤ 4 * h)

/-- The infimum direction is proved using every positive width in the
right family. Neither law is assumed to admit an optimizing width. -/
theorem Q_mono_of_squarePositiveOrder (ν ν' : Measure ℝ)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ν']
    (hSq : Integrable (fun z : ℝ => z ^ 2) ν)
    (hSq' : Integrable (fun z : ℝ => z ^ 2) ν')
    (horder : TwoMoment.SquarePositiveOrder ν ν') (A : ℝ) : Q ν A ≤ Q ν' A := by
  apply (le_Q_iff ν' A (Q ν A)).mpr
  intro h hh
  exact (Q_le_price ν A h hh).trans
    (price_mono_of_squarePositiveOrder ν ν' hSq hSq' horder A h hh)

/-- Each coordinate's cap and variance are enlarged independently. The
convolution order also includes either empty group and zero variances. -/
theorem doubleBinomial_squarePositiveOrder_mono
    (b0 B0 z0 Z0 : ℝ) (n0 : ℕ) (b1 B1 z1 Z1 : ℝ) (n1 : ℕ)
    (hb0 : 0 < b0) (hB0 : b0 ≤ B0) (hz0 : 0 ≤ z0) (hZ0 : z0 ≤ Z0)
    (hb1 : 0 < b1) (hB1 : b1 ≤ B1) (hz1 : 0 ≤ z1) (hZ1 : z1 ≤ Z1) :
    TwoMoment.SquarePositiveOrder (DoubleBinomialReference.law b0 z0 n0 b1 z1 n1)
      (DoubleBinomialReference.law B0 Z0 n0 B1 Z1 n1) := by
  haveI := TwoMoment.referenceLaw_isProbabilityMeasure b0 z0 hb0 hz0
  haveI := TwoMoment.referenceLaw_isProbabilityMeasure B0 Z0 (hb0.trans_le hB0) (hz0.trans hZ0)
  haveI := TwoMoment.referenceLaw_isProbabilityMeasure b1 z1 hb1 hz1
  haveI := TwoMoment.referenceLaw_isProbabilityMeasure B1 Z1 (hb1.trans_le hB1) (hz1.trans hZ1)
  have h0 := TwoMoment.squarePositiveOrder_convPower (TwoMoment.referenceLaw b0 z0)
    (TwoMoment.referenceLaw B0 Z0)
    (TwoMoment.squarePositiveOrder_referenceLaw_parameters_mono b0 B0 z0 Z0 hb0 hB0 hz0 hZ0) n0
  have h1 := TwoMoment.squarePositiveOrder_convPower (TwoMoment.referenceLaw b1 z1)
    (TwoMoment.referenceLaw B1 Z1)
    (TwoMoment.squarePositiveOrder_referenceLaw_parameters_mono b1 B1 z1 Z1 hb1 hB1 hz1 hZ1) n1
  exact TwoMoment.squarePositiveOrder_conv _ _ _ _ h0 h1

theorem doubleBinomial_Q_parameters_mono
    (b0 B0 z0 Z0 : ℝ) (n0 : ℕ) (b1 B1 z1 Z1 : ℝ) (n1 : ℕ)
    (hb0 : 0 < b0) (hB0 : b0 ≤ B0) (hz0 : 0 ≤ z0) (hZ0 : z0 ≤ Z0)
    (hb1 : 0 < b1) (hB1 : b1 ≤ B1) (hz1 : 0 ≤ z1) (hZ1 : z1 ≤ Z1) (A : ℝ) :
    Q (DoubleBinomialReference.law b0 z0 n0 b1 z1 n1) A ≤
      Q (DoubleBinomialReference.law B0 Z0 n0 B1 Z1 n1) A := by
  haveI := DoubleBinomialReference.law_isProbabilityMeasure b0 z0 n0 b1 z1 n1 hb0 hz0 hb1 hz1
  haveI := DoubleBinomialReference.law_isProbabilityMeasure B0 Z0 n0 B1 Z1 n1
    (hb0.trans_le hB0) (hz0.trans hZ0) (hb1.trans_le hB1) (hz1.trans hZ1)
  exact Q_mono_of_squarePositiveOrder _ _
    (DoubleBinomialReference.integrable_law b0 z0 n0 b1 z1 n1 hb0 hz0 hb1 hz1 (fun z => z ^ 2))
    (DoubleBinomialReference.integrable_law B0 Z0 n0 B1 Z1 n1
      (hb0.trans_le hB0) (hz0.trans hZ0) (hb1.trans_le hB1) (hz1.trans hZ1) (fun z => z ^ 2))
    (doubleBinomial_squarePositiveOrder_mono b0 B0 z0 Z0 n0 b1 B1 z1 Z1 n1
      hb0 hB0 hz0 hZ0 hb1 hB1 hz1 hZ1) A

theorem doubleBinomial_Q_variances_mono
    (b0 z0 Z0 : ℝ) (n0 : ℕ) (b1 z1 Z1 : ℝ) (n1 : ℕ)
    (hb0 : 0 < b0) (hz0 : 0 ≤ z0) (hZ0 : z0 ≤ Z0)
    (hb1 : 0 < b1) (hz1 : 0 ≤ z1) (hZ1 : z1 ≤ Z1) (A : ℝ) :
    Q (DoubleBinomialReference.law b0 z0 n0 b1 z1 n1) A ≤
      Q (DoubleBinomialReference.law b0 Z0 n0 b1 Z1 n1) A :=
  doubleBinomial_Q_parameters_mono b0 b0 z0 Z0 n0 b1 b1 z1 Z1 n1
    hb0 le_rfl hz0 hZ0 hb1 le_rfl hz1 hZ1 A

/-- This compares the two genuine reference measures. The supplied
ceilings concern the two source measures' own `lawSecondMoment` values. -/
theorem coupledReference_Q_le_frozen (ν0 ν1 : Measure ℝ) (b0 b1 Z0 Z1 : ℝ)
    (n k : ℕ) (hb0 : 0 < b0) (hb1 : 0 < b1)
    (hZ0 : TwoMoment.lawSecondMoment ν0 ≤ Z0)
    (hZ1 : TwoMoment.lawSecondMoment ν1 ≤ Z1) (A : ℝ) :
    Q (TwoMoment.coupledReferenceLaw ν0 ν1 b0 b1 n k) A ≤
      Q (DoubleBinomialReference.law b0 Z0 (n - k) b1 Z1 k) A := by
  rw [DoubleBinomialReference.coupledReferenceLaw_eq_law ν0 ν1 b0 b1 n k hb0 hb1]
  exact doubleBinomial_Q_variances_mono b0 _ Z0 (n - k) b1 _ Z1 k
    hb0 (TwoMoment.lawSecondMoment_nonneg ν0) hZ0 hb1 (TwoMoment.lawSecondMoment_nonneg ν1) hZ1 A

/-- The reference law on the right uses fixed positive caps and supplied
variance ceilings. The original law, actual count, noise, allocation,
prefix gate and Gaussian are exactly those in the optimized bound. -/
theorem canonical_targetResidual_le_frozen_Q
    (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ) (n k : ℕ) (hn : 0 < n) (hk : k ≤ n)
    (a0 a1 O1 Z0 Z1 Δ δ η t ci : ℝ) (ha0 : 0 < a0) (ha1 : 0 ≤ a1) (hO1 : 0 < O1)
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
        (t + Q (DoubleBinomialReference.law a0 Z0 (n - k) O1 Z1 k)
          (t + CoupledPrice.canonicalBinomialWeight μ n k / η)) -
        GaussianTools.Phi (ConditionalResidual.canonicalThreshold μ hμ n k t) -
        ci * MomentBudget.gDelta (CanonicalSign.p μ) (CanonicalSign.noiseVariance μ hμ) δ
          (ConditionalResidual.actualAllocation μ hμ) := by
  have hActual := OptimizedStaircasePrice.canonical_targetResidual_le_Q
    μ hμ n k hn hk a0 a1 O1 Δ δ η t ci ha0.le ha1 hO1.le
    hcapΔ hΔ hδ hcapδ hη hinner0 hinner1 houter1 hPrefix hci0 hci
  have hQ := coupledReference_Q_le_frozen
    (CanonicalSign.residual0 μ hμ : Measure ℝ) (CanonicalSign.residual1 μ hμ : Measure ℝ)
    a0 O1 Z0 Z1 n k ha0 hO1 hZ0 hZ1 (t + CoupledPrice.canonicalBinomialWeight μ n k / η)
  have hm := mul_le_mul_of_nonneg_left hQ hη.le
  linarith only [hActual, hm]

end BerryEsseen.FrozenReferencePrice

#print axioms BerryEsseen.FrozenReferencePrice.integral_squarePositivePart_mono
#print axioms BerryEsseen.FrozenReferencePrice.price_mono_of_squarePositiveOrder
#print axioms BerryEsseen.FrozenReferencePrice.Q_mono_of_squarePositiveOrder
#print axioms BerryEsseen.FrozenReferencePrice.doubleBinomial_squarePositiveOrder_mono
#print axioms BerryEsseen.FrozenReferencePrice.doubleBinomial_Q_parameters_mono
#print axioms BerryEsseen.FrozenReferencePrice.doubleBinomial_Q_variances_mono
#print axioms BerryEsseen.FrozenReferencePrice.coupledReference_Q_le_frozen
#print axioms BerryEsseen.FrozenReferencePrice.canonical_targetResidual_le_frozen_Q
