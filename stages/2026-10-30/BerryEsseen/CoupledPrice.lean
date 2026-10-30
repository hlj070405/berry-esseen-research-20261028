module

public import BerryEsseen.CoupledReferenceOrder
public import BerryEsseen.AffineSum

@[expose] public section

/-!
The clipped-square common-staircase bound with the actual two-group
reference price, followed by the exact canonical affine change back
to the original standardized law's normalized closed CDF.
The finite prefix-ratio gate remains an explicit mathematical premise.
-/

namespace BerryEsseen.CoupledPrice

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

theorem ae_common_U0_upper (ν0 ν1 : Measure ℝ)
    [IsProbabilityMeasure ν0] [IsProbabilityMeasure ν1]
    (n : ℕ) (a : ℝ) (ha : 0 ≤ a) (hu : ∀ᵐ u ∂ν0, u ≤ a) :
    ∀ᵐ ω ∂CommonProduct.pairProduct ν0 ν1 n, ∀ i : ℕ, CommonProduct.U0 n i ω ≤ a := by
  have hp : ∀ᵐ z : ℝ × ℝ ∂ν0.prod ν1, z.1 ≤ a :=
    (measurePreserving_fst (μ := ν0) (ν := ν1)).quasiMeasurePreserving.ae hu
  have hc : ∀ i : Fin n, ∀ᵐ ω ∂CommonProduct.pairProduct ν0 ν1 n, (ω i).1 ≤ a := by
    intro i
    exact (measurePreserving_eval (μ := fun _ : Fin n => ν0.prod ν1) i).quasiMeasurePreserving.ae hp
  have hall : ∀ᵐ ω ∂CommonProduct.pairProduct ν0 ν1 n, ∀ i : Fin n, (ω i).1 ≤ a :=
    ae_all_iff.mpr hc
  exact hall.mono (fun ω h i => by
    by_cases hi : i < n
    · simpa [CommonProduct.U0, hi] using h ⟨i, hi⟩
    · simpa [CommonProduct.U0, hi] using ha)

theorem ae_common_U1_lower (ν0 ν1 : Measure ℝ)
    [IsProbabilityMeasure ν0] [IsProbabilityMeasure ν1]
    (n : ℕ) (a : ℝ) (ha : 0 ≤ a) (hu : ∀ᵐ u ∂ν1, -a ≤ u) :
    ∀ᵐ ω ∂CommonProduct.pairProduct ν0 ν1 n, ∀ i : ℕ, -a ≤ CommonProduct.U1 n i ω := by
  have hp : ∀ᵐ z : ℝ × ℝ ∂ν0.prod ν1, -a ≤ z.2 :=
    (measurePreserving_snd (μ := ν0) (ν := ν1)).quasiMeasurePreserving.ae hu
  have hc : ∀ i : Fin n, ∀ᵐ ω ∂CommonProduct.pairProduct ν0 ν1 n, -a ≤ (ω i).2 := by
    intro i
    exact (measurePreserving_eval (μ := fun _ : Fin n => ν0.prod ν1) i).quasiMeasurePreserving.ae hp
  have hall : ∀ᵐ ω ∂CommonProduct.pairProduct ν0 ν1 n, ∀ i : Fin n, -a ≤ (ω i).2 :=
    ae_all_iff.mpr hc
  exact hall.mono (fun ω h i => by
    by_cases hi : i < n
    · simpa [CommonProduct.U1, hi] using h ⟨i, hi⟩
    · simpa [CommonProduct.U1, hi] using neg_nonpos.mpr ha)

/-- The staircase coupling is derived from the original marginal
support bounds on the same pair product used for every W_j. -/
theorem ae_common_staircaseCoupling (ν0 ν1 : Measure ℝ)
    [IsProbabilityMeasure ν0] [IsProbabilityMeasure ν1]
    (n k : ℕ) (hk : k ≤ n) (a0 a1 Δ : ℝ) (ha0 : 0 ≤ a0) (ha1 : 0 ≤ a1)
    (hu0 : ∀ᵐ u ∂ν0, u ≤ a0) (hu1 : ∀ᵐ u ∂ν1, -a1 ≤ u)
    (hcap : a0 + a1 ≤ Δ) :
    ∀ᵐ ω ∂CommonProduct.pairProduct ν0 ν1 n, ∀ r : ℕ, 1 ≤ r → r ≤ n - k →
      CommonProduct.W n k ω - (r : ℝ) * Δ ≤ CommonProduct.W n (k + r) ω := by
  have h0 := ae_common_U0_upper ν0 ν1 n a0 ha0 hu0
  have h1 := ae_common_U1_lower ν0 ν1 n a1 ha1 hu1
  exact CoupledResidual.ae_support_implies_staircaseCoupling
    (CommonProduct.pairProduct ν0 ν1 n) (CommonProduct.U0 n) (CommonProduct.U1 n)
    n k (n - k) a0 a1 Δ (Nat.add_sub_of_le hk).le
    (h0.mono (fun ω h i _ => h i)) (h1.mono (fun ω h i _ => h i)) hcap

/-- Actual negative-side reference expectation E(A+Z)_+² with both
group caps and their actual variances retained. -/
def clippedReferencePrice (ν0 ν1 : Measure ℝ) (b0 b1 : ℝ) (n k : ℕ) (A : ℝ) : ℝ :=
  ∫ z : ℝ, (max (A + z) 0) ^ 2 ∂TwoMoment.coupledReferenceLaw ν0 ν1 b0 b1 n k

theorem closedMixtureCDF_le_clippedReferencePrice (ν0 ν1 : Measure ℝ)
    [IsProbabilityMeasure ν0] [IsProbabilityMeasure ν1]
    (π : ℕ → ℝ) (n k : ℕ) (hk : k ≤ n)
    (a0 a1 O0 Δ h t : ℝ) (ha0 : 0 ≤ a0) (ha1 : 0 ≤ a1) (hO0 : 0 ≤ O0)
    (hcap : a0 + a1 ≤ Δ) (hΔ : Δ < 1) (hh : 0 < h)
    (hSq0 : Integrable (fun u : ℝ => u ^ 2) ν0) (hSq1 : Integrable (fun u : ℝ => u ^ 2) ν1)
    (hm0 : (∫ u : ℝ, u ∂ν0) = 0) (hm1 : (∫ u : ℝ, u ∂ν1) = 0)
    (hinner0 : ∀ᵐ u ∂ν0, u ≤ a0) (hinner1 : ∀ᵐ u ∂ν1, -a1 ≤ u)
    (houter0 : ∀ᵐ u ∂ν0, -O0 ≤ u)
    (hπ : ∀ j, 0 ≤ π j) (hπk : 0 < π k)
    (hGate : ∀ r : ℕ, 1 ≤ r → r ≤ n - k →
      Staircase.prefixMass (fun j => π (k + j)) r / π k ≤
        2 * (r : ℝ) * (1 - Δ) / h + (r : ℝ) ^ 2 * (1 - Δ) ^ 2 / h ^ 2) :
    Staircase.closedMixtureCDF (CommonProduct.pairProduct ν0 ν1 n) π (CommonProduct.W n)
      n ((k : ℝ) + t) ≤
      Staircase.lowerMass π k - π k + (π k / h ^ 2) *
        clippedReferencePrice ν0 ν1 O0 a1 n k (t + h) := by
  have hkn : k + (n - k) = n := Nat.add_sub_of_le hk
  have hmom := CommonProductMoments.moments_W ν0 ν1
    (TwoMoment.integrable_of_integrable_sq ν0 id measurable_id hSq0) hSq0
    (TwoMoment.integrable_of_integrable_sq ν1 id measurable_id hSq1) hSq1 hm0 hm1 n k hk
  have hbase := Staircase.coupledMixtureCDF_le_clippedSquare
    (CommonProduct.pairProduct ν0 ν1 n) π (CommonProduct.W n) k (n - k) Δ h t
    hπ hπk (by linarith) hh
    (by
      intro j hj
      exact measurableSet_le (measurable_const.add
        (CommonProduct.measurable_W n j (by simpa only [hkn] using hj))) measurable_const)
    (CommonProduct.measurable_W n k hk) hmom.2.1
    (ae_common_staircaseCoupling ν0 ν1 n k hk a0 a1 Δ ha0 ha1 hinner0 hinner1 hcap) hGate
  rw [hkn] at hbase
  have hprice :
      (∫ ω, (max (t + h - CommonProduct.W n k ω) 0) ^ 2 ∂CommonProduct.pairProduct ν0 ν1 n) ≤
        clippedReferencePrice ν0 ν1 O0 a1 n k (t + h) := by
    have hp := TwoMoment.integral_neg_W_squarePositivePart_le_reference
      ν0 ν1 O0 a1 (-(t + h)) hO0 ha1 hSq0 hSq1 hm0 hm1 houter0 hinner1 n k hk
    unfold TwoMoment.coupledReferencePrice at hp
    have hleft : (fun ω : CommonProduct.Space n => (max (-CommonProduct.W n k ω - -(t + h)) 0) ^ 2) =
        (fun ω => (max (t + h - CommonProduct.W n k ω) 0) ^ 2) := by
      funext ω
      rw [show -CommonProduct.W n k ω - -(t + h) = t + h - CommonProduct.W n k ω by ring]
    have hright : (fun z : ℝ => (max (z - -(t + h)) 0) ^ 2) =
        (fun z => (max (t + h + z) 0) ^ 2) := by
      funext z
      rw [show z - -(t + h) = t + h + z by ring]
    rw [hleft, hright] at hp
    exact hp
  have hcoef : 0 ≤ π k / h ^ 2 := div_nonneg hπk.le (sq_nonneg _)
  exact hbase.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hprice hcoef))

/-- The actual binomial masses of the canonical sign decomposition. -/
def canonicalBinomialWeight (μ : ProbabilityMeasure ℝ) (n j : ℕ) : ℝ :=
  (n.choose j : ℝ) * CanonicalSign.p μ ^ j * CanonicalSign.q μ ^ (n - j)

theorem canonicalBinomialWeight_nonneg (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (n j : ℕ) : 0 ≤ canonicalBinomialWeight μ n j := by
  unfold canonicalBinomialWeight
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (CanonicalSign.p_pos μ hμ).le _))
    (pow_nonneg (CanonicalSign.q_pos μ hμ).le _)

theorem canonicalBinomialWeight_pos (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (n k : ℕ) (hk : k ≤ n) : 0 < canonicalBinomialWeight μ n k := by
  unfold canonicalBinomialWeight
  exact mul_pos (mul_pos (Nat.cast_pos.mpr (Nat.choose_pos hk)) (pow_pos (CanonicalSign.p_pos μ hμ) _))
    (pow_pos (CanonicalSign.q_pos μ hμ) _)

/-- The common-staircase reference price bounds the original target
law's normalized closed CDF at its exact canonical affine threshold.
The prefix-ratio gate is an explicit premise, not an automatic property. -/
theorem canonical_normalized_closedCDF_le_clippedReferencePrice
    (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ) (n k : ℕ) (hn : 0 < n) (hk : k ≤ n)
    (a0 a1 O0 Δ h t : ℝ) (ha0 : 0 ≤ a0) (ha1 : 0 ≤ a1) (hO0 : 0 ≤ O0)
    (hcap : a0 + a1 ≤ Δ) (hΔ : Δ < 1) (hh : 0 < h)
    (hinner0 : ∀ᵐ u ∂(CanonicalSign.residual0 μ hμ : Measure ℝ), u ≤ a0)
    (hinner1 : ∀ᵐ u ∂(CanonicalSign.residual1 μ hμ : Measure ℝ), -a1 ≤ u)
    (houter0 : ∀ᵐ u ∂(CanonicalSign.residual0 μ hμ : Measure ℝ), -O0 ≤ u)
    (hGate : ∀ r : ℕ, 1 ≤ r → r ≤ n - k →
      Staircase.prefixMass (fun j => canonicalBinomialWeight μ n (k + j)) r /
          canonicalBinomialWeight μ n k ≤
        2 * (r : ℝ) * (1 - Δ) / h + (r : ℝ) ^ 2 * (1 - Δ) ^ 2 / h ^ 2) :
    (normalizedIidSumLaw μ n).real
      (Set.Iic (((k : ℝ) + t - (n : ℝ) * CanonicalSign.p μ) /
        (CanonicalSign.scale μ hμ * Real.sqrt (n : ℝ)))) ≤
      Staircase.lowerMass (canonicalBinomialWeight μ n) k - canonicalBinomialWeight μ n k +
        (canonicalBinomialWeight μ n k / h ^ 2) *
          clippedReferencePrice (CanonicalSign.residual0 μ hμ : Measure ℝ)
            (CanonicalSign.residual1 μ hμ : Measure ℝ) O0 a1 n k (t + h) := by
  have h0 := CanonicalSign.residual0_centered μ hμ
  have h1 := CanonicalSign.residual1_centered μ hμ
  have hraw := closedMixtureCDF_le_clippedReferencePrice
    (CanonicalSign.residual0 μ hμ : Measure ℝ) (CanonicalSign.residual1 μ hμ : Measure ℝ)
    (canonicalBinomialWeight μ n) n k hk a0 a1 O0 Δ h t ha0 ha1 hO0 hcap hΔ hh
    h0.integrable_second h1.integrable_second h0.mean_zero h1.mean_zero
    hinner0 hinner1 houter0 (canonicalBinomialWeight_nonneg μ hμ n)
    (canonicalBinomialWeight_pos μ hμ n k hk) hGate
  have hCDF := AffineSum.canonical_normalized_closedCDF μ hμ n hn
    (((k : ℝ) + t - (n : ℝ) * CanonicalSign.p μ) /
      (CanonicalSign.scale μ hμ * Real.sqrt (n : ℝ)))
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
  rw [hCDF]
  exact hraw

end

end BerryEsseen.CoupledPrice

#print axioms BerryEsseen.CoupledPrice.ae_common_staircaseCoupling
#print axioms BerryEsseen.CoupledPrice.closedMixtureCDF_le_clippedReferencePrice
#print axioms BerryEsseen.CoupledPrice.canonical_normalized_closedCDF_le_clippedReferencePrice
