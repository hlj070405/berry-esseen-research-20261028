module

public import BerryEsseen.ConditionalResidual

@[expose] public section

/-!
The actual full-square and fixed-width stop-loss staircase prices.
Both prices retain the original common product, actual count moments,
prefix gates and normalized closed-CDF threshold. The full-square price
needs no outer endpoint; the stop-loss reference uses only (a0,O1).
-/

namespace BerryEsseen.StaircasePrices

open MeasureTheory
open scoped BigOperators

noncomputable section

def actualCountVariance (ν0 ν1 : Measure ℝ) (n k : ℕ) : ℝ :=
  ((n - k : ℕ) : ℝ) * TwoMoment.lawSecondMoment ν0 + (k : ℝ) * TwoMoment.lawSecondMoment ν1

lemma actualCountVariance_nonneg (ν0 ν1 : Measure ℝ) (n k : ℕ) :
    0 ≤ actualCountVariance ν0 ν1 n k := by
  unfold actualCountVariance
  exact add_nonneg (mul_nonneg (Nat.cast_nonneg _) (TwoMoment.lawSecondMoment_nonneg ν0))
    (mul_nonneg (Nat.cast_nonneg _) (TwoMoment.lawSecondMoment_nonneg ν1))

private theorem common_moments (ν0 ν1 : Measure ℝ)
    [IsProbabilityMeasure ν0] [IsProbabilityMeasure ν1]
    (hSq0 : Integrable (fun u : ℝ => u ^ 2) ν0) (hSq1 : Integrable (fun u : ℝ => u ^ 2) ν1)
    (hm0 : (∫ u : ℝ, u ∂ν0) = 0) (hm1 : (∫ u : ℝ, u ∂ν1) = 0)
    (n k : ℕ) (hk : k ≤ n) :
    Integrable (CommonProduct.W n k) (CommonProduct.pairProduct ν0 ν1 n) ∧
    Integrable (fun ω => CommonProduct.W n k ω ^ 2) (CommonProduct.pairProduct ν0 ν1 n) ∧
    (∫ ω, CommonProduct.W n k ω ∂CommonProduct.pairProduct ν0 ν1 n) = 0 ∧
    (∫ ω, CommonProduct.W n k ω ^ 2 ∂CommonProduct.pairProduct ν0 ν1 n) =
      actualCountVariance ν0 ν1 n k :=
  CommonProductMoments.moments_W ν0 ν1
    (TwoMoment.integrable_of_integrable_sq ν0 id measurable_id hSq0) hSq0
    (TwoMoment.integrable_of_integrable_sq ν1 id measurable_id hSq1) hSq1 hm0 hm1 n k hk

/-- The full-square price uses only the inner support bounds and the
same actual count variance. It requires no outer reference endpoint. -/
theorem closedMixtureCDF_le_fullSquare (ν0 ν1 : Measure ℝ)
    [IsProbabilityMeasure ν0] [IsProbabilityMeasure ν1]
    (π : ℕ → ℝ) (n k : ℕ) (hk : k ≤ n)
    (a0 a1 Δ h t : ℝ) (ha0 : 0 ≤ a0) (ha1 : 0 ≤ a1)
    (hcap : a0 + a1 ≤ Δ) (hΔ : Δ < 1) (hh : 0 < h)
    (hSq0 : Integrable (fun u : ℝ => u ^ 2) ν0) (hSq1 : Integrable (fun u : ℝ => u ^ 2) ν1)
    (hm0 : (∫ u : ℝ, u ∂ν0) = 0) (hm1 : (∫ u : ℝ, u ∂ν1) = 0)
    (hinner0 : ∀ᵐ u ∂ν0, u ≤ a0) (hinner1 : ∀ᵐ u ∂ν1, -a1 ≤ u)
    (hπ : ∀ j, 0 ≤ π j) (hπk : 0 < π k)
    (hGate : ∀ r : ℕ, 1 ≤ r → r ≤ n - k →
      Staircase.prefixMass (fun j => π (k + j)) r / π k ≤
        2 * (r : ℝ) * (1 - Δ) / h + (r : ℝ) ^ 2 * (1 - Δ) ^ 2 / h ^ 2) :
    Staircase.closedMixtureCDF (CommonProduct.pairProduct ν0 ν1 n) π (CommonProduct.W n)
      n ((k : ℝ) + t) ≤
      Staircase.lowerMass π k + (π k / h ^ 2) *
        (actualCountVariance ν0 ν1 n k + t ^ 2 + 2 * h * t) := by
  have hkn : k + (n - k) = n := Nat.add_sub_of_le hk
  have hmom := common_moments ν0 ν1 hSq0 hSq1 hm0 hm1 n k hk
  have hbase := Staircase.coupledMixtureCDF_le_clippedSquare
    (CommonProduct.pairProduct ν0 ν1 n) π (CommonProduct.W n) k (n - k) Δ h t
    hπ hπk (by linarith) hh
    (by
      intro j hj
      exact measurableSet_le (measurable_const.add
        (CommonProduct.measurable_W n j (by simpa only [hkn] using hj))) measurable_const)
    (CommonProduct.measurable_W n k hk) hmom.2.1
    (CoupledPrice.ae_common_staircaseCoupling ν0 ν1 n k hk a0 a1 Δ ha0 ha1 hinner0 hinner1 hcap) hGate
  rw [hkn] at hbase
  have hclip := Staircase.integrable_clippedSquare_of_integrable_sq
    (CommonProduct.pairProduct ν0 ν1 n) (CommonProduct.W n k) (t + h)
    (CommonProduct.measurable_W n k hk) hmom.2.1
  have hfull := TwoMoment.integrable_shift_sq (CommonProduct.pairProduct ν0 ν1 n)
    (CommonProduct.W n k) (t + h) hmom.1 hmom.2.1
  have hprice : (∫ ω, (max (t + h - CommonProduct.W n k ω) 0) ^ 2
      ∂CommonProduct.pairProduct ν0 ν1 n) ≤ actualCountVariance ν0 ν1 n k + (t + h) ^ 2 := by
    calc
      _ ≤ ∫ ω, (CommonProduct.W n k ω - (t + h)) ^ 2
          ∂CommonProduct.pairProduct ν0 ν1 n := by
        apply integral_mono_ae hclip hfull
        filter_upwards [] with ω
        have hp := TwoMoment.positivePart_sq_le_sq (t + h - CommonProduct.W n k ω)
        nlinarith only [hp]
      _ = _ := by
        rw [TwoMoment.integral_shift_sq _ _ _ hmom.1 hmom.2.1 hmom.2.2.1, hmom.2.2.2]
  have hcoef : 0 ≤ π k / h ^ 2 := div_nonneg hπk.le (sq_nonneg _)
  calc
    _ ≤ Staircase.lowerMass π k - π k + (π k / h ^ 2) *
        (actualCountVariance ν0 ν1 n k + (t + h) ^ 2) :=
      hbase.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hprice hcoef))
    _ = _ := by field_simp [hh.ne'] ; ring

/-- Width domination is pointwise and valid for every positive width;
it makes no optimizer or infimum assertion. -/
theorem positivePart_le_square_width (x w : ℝ) (hw : 0 < w) :
    max x 0 ≤ (max (x + w) 0) ^ 2 / (4 * w) := by
  have h4w : 0 < 4 * w := mul_pos (by norm_num) hw
  by_cases hx : x ≤ 0
  · rw [max_eq_right hx]
    exact div_nonneg (sq_nonneg _) h4w.le
  · have hxpos : 0 < x := lt_of_not_ge hx
    rw [max_eq_left hxpos.le, max_eq_left (by linarith : 0 ≤ x + w)]
    apply (le_div_iff₀ h4w).mpr
    nlinarith only [sq_nonneg (x - w)]

private theorem integral_positivePart_le_square_width
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (U : Ω → ℝ) (A w : ℝ) (hw : 0 < w) (hU : Measurable U)
    (hSq : Integrable (fun ω => U ω ^ 2) μ) :
    (∫ ω, max (U ω - A) 0 ∂μ) ≤ (∫ ω, (max (U ω - A + w) 0) ^ 2 ∂μ) / (4 * w) := by
  have hI := TwoMoment.integrable_of_integrable_sq μ U hU hSq
  have hlin : Integrable (fun ω => max (U ω - A) 0) μ :=
    (hI.sub (integrable_const A)).pos_part
  have hquad : Integrable (fun ω => (max (U ω - A + w) 0) ^ 2) μ := by
    convert TwoMoment.integrable_squarePositivePart μ U (A - w) hU hSq using 1
    funext ω
    rw [show U ω - (A - w) = U ω - A + w by ring]
  have hbound := integral_mono_ae hlin (hquad.div_const (4 * w))
    (Filter.Eventually.of_forall (fun ω => positivePart_le_square_width (U ω - A) w hw))
  rw [integral_div] at hbound
  exact hbound

def widthReferencePrice (ν0 ν1 : Measure ℝ) (b0 b1 : ℝ) (n k : ℕ) (A w : ℝ) : ℝ :=
  (∫ z : ℝ, (max (z - A + w) 0) ^ 2 ∂TwoMoment.coupledReferenceLaw ν0 ν1 b0 b1 n k) / (4 * w)

/-- The eta gate is the original stop-loss prefix gate, distinct from
the clipped-square ratio gate. Only the positive-side outer cap O1 is used. -/
theorem closedMixtureCDF_le_stopLoss_width (ν0 ν1 : Measure ℝ)
    [IsProbabilityMeasure ν0] [IsProbabilityMeasure ν1]
    (π : ℕ → ℝ) (n k : ℕ) (hk : k ≤ n)
    (a0 a1 O1 Δ η t w : ℝ) (ha0 : 0 ≤ a0) (ha1 : 0 ≤ a1) (hO1 : 0 ≤ O1)
    (hcap : a0 + a1 ≤ Δ) (hΔ : Δ < 1) (hη : 0 < η) (hw : 0 < w)
    (hSq0 : Integrable (fun u : ℝ => u ^ 2) ν0) (hSq1 : Integrable (fun u : ℝ => u ^ 2) ν1)
    (hm0 : (∫ u : ℝ, u ∂ν0) = 0) (hm1 : (∫ u : ℝ, u ∂ν1) = 0)
    (hinner0 : ∀ᵐ u ∂ν0, u ≤ a0) (hinner1 : ∀ᵐ u ∂ν1, -a1 ≤ u)
    (houter1 : ∀ᵐ u ∂ν1, u ≤ O1) (hπ : ∀ j, 0 ≤ π j)
    (hPrefix : ∀ r : ℕ, 1 ≤ r → r ≤ n - k →
      Staircase.prefixMass (fun j => π (k + j)) r ≤ η * ((r : ℝ) * (1 - Δ))) :
    Staircase.closedMixtureCDF (CommonProduct.pairProduct ν0 ν1 n) π (CommonProduct.W n)
      n ((k : ℝ) + t) ≤
      Staircase.lowerMass π k + η *
        (t + widthReferencePrice ν0 ν1 a0 O1 n k (t + π k / η) w) := by
  have hkn : k + (n - k) = n := Nat.add_sub_of_le hk
  have hmom := common_moments ν0 ν1 hSq0 hSq1 hm0 hm1 n k hk
  have hbase := Staircase.coupledMixtureCDF_le_stopLoss
    (CommonProduct.pairProduct ν0 ν1 n) π (CommonProduct.W n) k (n - k) Δ η t
    hπ (by linarith) hη
    (by
      intro j hj
      exact measurableSet_le (measurable_const.add
        (CommonProduct.measurable_W n j (by simpa only [hkn] using hj))) measurable_const)
    hmom.1 hmom.2.2.1
    (CoupledPrice.ae_common_staircaseCoupling ν0 ν1 n k hk a0 a1 Δ ha0 ha1 hinner0 hinner1 hcap) hPrefix
  rw [hkn] at hbase
  have hphase (x : ℝ) : x - t - π k / η = x - (t + π k / η) := by ring
  simp only [hphase] at hbase
  have hwidth := integral_positivePart_le_square_width
    (CommonProduct.pairProduct ν0 ν1 n) (CommonProduct.W n k) (t + π k / η) w hw
    (CommonProduct.measurable_W n k hk) hmom.2.1
  have hquad := TwoMoment.integral_W_squarePositivePart_le_reference
    ν0 ν1 a0 O1 (t + π k / η - w) ha0 hO1 hSq0 hSq1 hm0 hm1 hinner0 houter1 n k hk
  unfold TwoMoment.coupledReferencePrice at hquad
  have hshift (x : ℝ) : x - (t + π k / η - w) = x - (t + π k / η) + w := by ring
  simp only [hshift] at hquad
  have hprice : (∫ ω, max (CommonProduct.W n k ω - (t + π k / η)) 0
      ∂CommonProduct.pairProduct ν0 ν1 n) ≤
      widthReferencePrice ν0 ν1 a0 O1 n k (t + π k / η) w :=
    hwidth.trans (div_le_div_of_nonneg_right hquad (by linarith : 0 ≤ 4 * w))
  exact hbase.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left (add_le_add le_rfl hprice) hη.le))

/-- A reusable proved identity to the original normalized law, at the
same canonical count threshold used by all three staircase prices. -/
theorem canonical_closedCDF_at_count (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (n k : ℕ) (hn : 0 < n) (t : ℝ) :
    (normalizedIidSumLaw μ n).real (Set.Iic (ConditionalResidual.canonicalThreshold μ hμ n k t)) =
      Staircase.closedMixtureCDF
        (CommonProduct.pairProduct (CanonicalSign.residual0 μ hμ : Measure ℝ)
          (CanonicalSign.residual1 μ hμ : Measure ℝ) n)
        (CoupledPrice.canonicalBinomialWeight μ n) (CommonProduct.W n) n ((k : ℝ) + t) := by
  have hCDF := AffineSum.canonical_normalized_closedCDF μ hμ n hn
    (ConditionalResidual.canonicalThreshold μ hμ n k t)
  unfold ConditionalResidual.canonicalThreshold at hCDF ⊢
  have hd : 0 < CanonicalSign.scale μ hμ * Real.sqrt (n : ℝ) :=
    mul_pos (CanonicalSign.scale_pos μ hμ) (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn))
  have hcancel : (CanonicalSign.scale μ hμ * Real.sqrt (n : ℝ)) *
      (((k : ℝ) + t - (n : ℝ) * CanonicalSign.p μ) /
        (CanonicalSign.scale μ hμ * Real.sqrt (n : ℝ))) =
      (k : ℝ) + t - (n : ℝ) * CanonicalSign.p μ := by
    field_simp [hd.ne', (CanonicalSign.scale_pos μ hμ).ne']
  have hphase : (n : ℝ) * CanonicalSign.p μ + CanonicalSign.scale μ hμ * Real.sqrt (n : ℝ) *
      (((k : ℝ) + t - (n : ℝ) * CanonicalSign.p μ) /
        (CanonicalSign.scale μ hμ * Real.sqrt (n : ℝ))) = (k : ℝ) + t := by
    rw [hcancel]
    ring
  rw [hphase] at hCDF
  exact hCDF

theorem canonical_normalized_closedCDF_le_fullSquare
    (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ) (n k : ℕ) (hn : 0 < n) (hk : k ≤ n)
    (a0 a1 Δ h t : ℝ) (ha0 : 0 ≤ a0) (ha1 : 0 ≤ a1)
    (hcap : a0 + a1 ≤ Δ) (hΔ : Δ < 1) (hh : 0 < h)
    (hinner0 : ∀ᵐ u ∂(CanonicalSign.residual0 μ hμ : Measure ℝ), u ≤ a0)
    (hinner1 : ∀ᵐ u ∂(CanonicalSign.residual1 μ hμ : Measure ℝ), -a1 ≤ u)
    (hGate : ∀ r : ℕ, 1 ≤ r → r ≤ n - k →
      Staircase.prefixMass (fun j => CoupledPrice.canonicalBinomialWeight μ n (k + j)) r /
          CoupledPrice.canonicalBinomialWeight μ n k ≤
        2 * (r : ℝ) * (1 - Δ) / h + (r : ℝ) ^ 2 * (1 - Δ) ^ 2 / h ^ 2) :
    (normalizedIidSumLaw μ n).real (Set.Iic (ConditionalResidual.canonicalThreshold μ hμ n k t)) ≤
      Staircase.lowerMass (CoupledPrice.canonicalBinomialWeight μ n) k +
        (CoupledPrice.canonicalBinomialWeight μ n k / h ^ 2) *
          (actualCountVariance (CanonicalSign.residual0 μ hμ : Measure ℝ)
            (CanonicalSign.residual1 μ hμ : Measure ℝ) n k + t ^ 2 + 2 * h * t) := by
  rw [canonical_closedCDF_at_count μ hμ n k hn t]
  have h0 := CanonicalSign.residual0_centered μ hμ
  have h1 := CanonicalSign.residual1_centered μ hμ
  exact closedMixtureCDF_le_fullSquare _ _ _ n k hk a0 a1 Δ h t ha0 ha1 hcap hΔ hh
    h0.integrable_second h1.integrable_second h0.mean_zero h1.mean_zero hinner0 hinner1
    (CoupledPrice.canonicalBinomialWeight_nonneg μ hμ n)
    (CoupledPrice.canonicalBinomialWeight_pos μ hμ n k hk) hGate

theorem canonical_normalized_closedCDF_le_stopLoss_width
    (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ) (n k : ℕ) (hn : 0 < n) (hk : k ≤ n)
    (a0 a1 O1 Δ η t w : ℝ) (ha0 : 0 ≤ a0) (ha1 : 0 ≤ a1) (hO1 : 0 ≤ O1)
    (hcap : a0 + a1 ≤ Δ) (hΔ : Δ < 1) (hη : 0 < η) (hw : 0 < w)
    (hinner0 : ∀ᵐ u ∂(CanonicalSign.residual0 μ hμ : Measure ℝ), u ≤ a0)
    (hinner1 : ∀ᵐ u ∂(CanonicalSign.residual1 μ hμ : Measure ℝ), -a1 ≤ u)
    (houter1 : ∀ᵐ u ∂(CanonicalSign.residual1 μ hμ : Measure ℝ), u ≤ O1)
    (hPrefix : ∀ r : ℕ, 1 ≤ r → r ≤ n - k →
      Staircase.prefixMass (fun j => CoupledPrice.canonicalBinomialWeight μ n (k + j)) r ≤
        η * ((r : ℝ) * (1 - Δ))) :
    (normalizedIidSumLaw μ n).real (Set.Iic (ConditionalResidual.canonicalThreshold μ hμ n k t)) ≤
      Staircase.lowerMass (CoupledPrice.canonicalBinomialWeight μ n) k + η *
        (t + widthReferencePrice (CanonicalSign.residual0 μ hμ : Measure ℝ)
          (CanonicalSign.residual1 μ hμ : Measure ℝ) a0 O1 n k
          (t + CoupledPrice.canonicalBinomialWeight μ n k / η) w) := by
  rw [canonical_closedCDF_at_count μ hμ n k hn t]
  have h0 := CanonicalSign.residual0_centered μ hμ
  have h1 := CanonicalSign.residual1_centered μ hμ
  exact closedMixtureCDF_le_stopLoss_width _ _ _ n k hk a0 a1 O1 Δ η t w ha0 ha1 hO1 hcap hΔ hη hw
    h0.integrable_second h1.integrable_second h0.mean_zero h1.mean_zero hinner0 hinner1 houter1
    (CoupledPrice.canonicalBinomialWeight_nonneg μ hμ n) hPrefix

/-- A supplied ceiling enlarges only the proved actual count variance. -/
theorem canonical_normalized_closedCDF_le_fullSquare_varianceBound
    (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ) (n k : ℕ) (hn : 0 < n) (hk : k ≤ n)
    (a0 a1 Δ h t Vbar : ℝ) (ha0 : 0 ≤ a0) (ha1 : 0 ≤ a1)
    (hcap : a0 + a1 ≤ Δ) (hΔ : Δ < 1) (hh : 0 < h)
    (hinner0 : ∀ᵐ u ∂(CanonicalSign.residual0 μ hμ : Measure ℝ), u ≤ a0)
    (hinner1 : ∀ᵐ u ∂(CanonicalSign.residual1 μ hμ : Measure ℝ), -a1 ≤ u)
    (hGate : ∀ r : ℕ, 1 ≤ r → r ≤ n - k →
      Staircase.prefixMass (fun j => CoupledPrice.canonicalBinomialWeight μ n (k + j)) r /
          CoupledPrice.canonicalBinomialWeight μ n k ≤
        2 * (r : ℝ) * (1 - Δ) / h + (r : ℝ) ^ 2 * (1 - Δ) ^ 2 / h ^ 2)
    (hVbar : actualCountVariance (CanonicalSign.residual0 μ hμ : Measure ℝ)
      (CanonicalSign.residual1 μ hμ : Measure ℝ) n k ≤ Vbar) :
    (normalizedIidSumLaw μ n).real (Set.Iic (ConditionalResidual.canonicalThreshold μ hμ n k t)) ≤
      Staircase.lowerMass (CoupledPrice.canonicalBinomialWeight μ n) k +
        (CoupledPrice.canonicalBinomialWeight μ n k / h ^ 2) * (Vbar + t ^ 2 + 2 * h * t) := by
  have hbase := canonical_normalized_closedCDF_le_fullSquare μ hμ n k hn hk a0 a1 Δ h t
    ha0 ha1 hcap hΔ hh hinner0 hinner1 hGate
  have hcoef : 0 ≤ CoupledPrice.canonicalBinomialWeight μ n k / h ^ 2 :=
    div_nonneg (CoupledPrice.canonicalBinomialWeight_pos μ hμ n k hk).le (sq_nonneg _)
  exact hbase.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left (by linarith :
    actualCountVariance (CanonicalSign.residual0 μ hμ : Measure ℝ)
        (CanonicalSign.residual1 μ hμ : Measure ℝ) n k + t ^ 2 + 2 * h * t ≤
      Vbar + t ^ 2 + 2 * h * t) hcoef))

def cantelliWidth (Vbar t : ℝ) : ℝ := -t + Vbar / (-t)

lemma cantelliWidth_pos (Vbar t : ℝ) (hVbar : 0 ≤ Vbar) (ht : t < 0) :
    0 < cantelliWidth Vbar t :=
  add_pos_of_pos_of_nonneg (neg_pos.mpr ht) (div_nonneg hVbar (neg_pos.mpr ht).le)

lemma fullSquare_cantelli_identity (F atom Vbar t : ℝ) (hVbar : 0 ≤ Vbar) (ht : t < 0) :
    F + (atom / (cantelliWidth Vbar t) ^ 2) *
        (Vbar + t ^ 2 + 2 * cantelliWidth Vbar t * t) =
      F - atom * t ^ 2 / (Vbar + t ^ 2) := by
  have ht0 : t ≠ 0 := ne_of_lt ht
  have htsq : 0 < t ^ 2 := by simpa only [neg_sq] using sq_pos_of_pos (neg_pos.mpr ht)
  have hden : 0 < Vbar + t ^ 2 := add_pos_of_nonneg_of_pos hVbar htsq
  have hform : cantelliWidth Vbar t = -(Vbar + t ^ 2) / t := by
    unfold cantelliWidth
    field_simp [ht0] ; ring
  rw [hform]
  field_simp [ht0, hden.ne'] ; ring

/-- Cantelli's negative-phase form under a legitimate variance ceiling.
The selected width is positive even when Vbar=0, but its original
clipped-square prefix gate is still required explicitly. -/
theorem canonical_normalized_closedCDF_le_cantelli
    (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ) (n k : ℕ) (hn : 0 < n) (hk : k ≤ n)
    (a0 a1 Δ t Vbar : ℝ) (ha0 : 0 ≤ a0) (ha1 : 0 ≤ a1)
    (hcap : a0 + a1 ≤ Δ) (hΔ : Δ < 1) (ht : t < 0)
    (hinner0 : ∀ᵐ u ∂(CanonicalSign.residual0 μ hμ : Measure ℝ), u ≤ a0)
    (hinner1 : ∀ᵐ u ∂(CanonicalSign.residual1 μ hμ : Measure ℝ), -a1 ≤ u)
    (hVbar : actualCountVariance (CanonicalSign.residual0 μ hμ : Measure ℝ)
      (CanonicalSign.residual1 μ hμ : Measure ℝ) n k ≤ Vbar)
    (hGate : ∀ r : ℕ, 1 ≤ r → r ≤ n - k →
      Staircase.prefixMass (fun j => CoupledPrice.canonicalBinomialWeight μ n (k + j)) r /
          CoupledPrice.canonicalBinomialWeight μ n k ≤
        2 * (r : ℝ) * (1 - Δ) / cantelliWidth Vbar t +
          (r : ℝ) ^ 2 * (1 - Δ) ^ 2 / (cantelliWidth Vbar t) ^ 2) :
    (normalizedIidSumLaw μ n).real (Set.Iic (ConditionalResidual.canonicalThreshold μ hμ n k t)) ≤
      Staircase.lowerMass (CoupledPrice.canonicalBinomialWeight μ n) k -
        CoupledPrice.canonicalBinomialWeight μ n k * t ^ 2 / (Vbar + t ^ 2) := by
  have hV0 : 0 ≤ Vbar :=
    (actualCountVariance_nonneg (CanonicalSign.residual0 μ hμ : Measure ℝ)
      (CanonicalSign.residual1 μ hμ : Measure ℝ) n k).trans hVbar
  have hbase := canonical_normalized_closedCDF_le_fullSquare_varianceBound μ hμ n k hn hk
    a0 a1 Δ (cantelliWidth Vbar t) t Vbar ha0 ha1 hcap hΔ (cantelliWidth_pos Vbar t hV0 ht)
    hinner0 hinner1 hGate hVbar
  rw [fullSquare_cantelli_identity _ _ Vbar t hV0 ht] at hbase
  exact hbase

end

end BerryEsseen.StaircasePrices

#print axioms BerryEsseen.StaircasePrices.closedMixtureCDF_le_fullSquare
#print axioms BerryEsseen.StaircasePrices.closedMixtureCDF_le_stopLoss_width
#print axioms BerryEsseen.StaircasePrices.canonical_normalized_closedCDF_le_fullSquare
#print axioms BerryEsseen.StaircasePrices.canonical_normalized_closedCDF_le_stopLoss_width
#print axioms BerryEsseen.StaircasePrices.canonical_normalized_closedCDF_le_cantelli
