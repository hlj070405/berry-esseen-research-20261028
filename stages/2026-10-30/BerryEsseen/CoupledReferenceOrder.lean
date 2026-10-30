module

public import BerryEsseen.ReferenceSumPrice

@[expose] public section

/-!
Two-group reference orders for the actual residual W on CommonProduct.
Each group's cap and actual second moment are retained separately.
Zero caps are represented by a Dirac law only after the source law's
centering and one-sided support have forced its second moment to vanish.
-/

namespace BerryEsseen.TwoMoment

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

/-- The actual second moment of a real residual law. -/
def lawSecondMoment (ν : Measure ℝ) : ℝ := ∫ u : ℝ, u ^ 2 ∂ν

lemma lawSecondMoment_nonneg (ν : Measure ℝ) : 0 ≤ lawSecondMoment ν :=
  integral_nonneg (fun u => sq_nonneg u)

private lemma law_eq_dirac_zero_of_ae (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hz : (fun u : ℝ => u) =ᵐ[ν] (fun _ => 0)) : ν = Measure.dirac 0 := by
  calc
    ν = ν.map id := (Measure.map_id).symm
    _ = ν.map (fun _ : ℝ => (0 : ℝ)) := Measure.map_congr hz
    _ = Measure.dirac 0 := by simp

/-- A centered law with upper cap zero is the zero law, with its
actual second moment zero; no reference variance is assigned freely. -/
theorem centered_nonpos_law_eq_dirac (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hSq : Integrable (fun u : ℝ => u ^ 2) ν) (hm : (∫ u : ℝ, u ∂ν) = 0)
    (hu : ∀ᵐ u ∂ν, u ≤ 0) : ν = Measure.dirac 0 ∧ lawSecondMoment ν = 0 := by
  have hI := integrable_of_integrable_sq ν id measurable_id hSq
  have hz := MomentBudget.centered_nonpos_ae_zero ν id hI hm hu
  have hν := law_eq_dirac_zero_of_ae ν hz
  exact ⟨hν, by rw [hν]; simp [lawSecondMoment]⟩

/-- The corresponding zero lower-cap boundary, needed for -W. -/
theorem centered_nonneg_law_eq_dirac (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hSq : Integrable (fun u : ℝ => u ^ 2) ν) (hm : (∫ u : ℝ, u ∂ν) = 0)
    (hu : ∀ᵐ u ∂ν, 0 ≤ u) : ν = Measure.dirac 0 ∧ lawSecondMoment ν = 0 := by
  have hI := integrable_of_integrable_sq ν id measurable_id hSq
  have hmneg : (∫ u : ℝ, -u ∂ν) = 0 := by rw [integral_neg, hm, neg_zero]
  have hneg : ∀ᵐ u ∂ν, -u ≤ 0 := hu.mono (fun u h => neg_nonpos.mpr h)
  have hzneg := MomentBudget.centered_nonpos_ae_zero ν (fun u : ℝ => -u) hI.neg hmneg hneg
  have hz : (fun u : ℝ => u) =ᵐ[ν] (fun _ => 0) := hzneg.mono (fun u h => by
    change -u = 0 at h
    linarith)
  have hν := law_eq_dirac_zero_of_ae ν hz
  exact ⟨hν, by rw [hν]; simp [lawSecondMoment]⟩

/-- Positive caps use the exact two-point reference at the source's
actual second moment. A zero cap uses the zero law; the lemmas above
prove that its source second moment is then necessarily zero. -/
def endpointReferenceLaw (ν : Measure ℝ) (b : ℝ) : Measure ℝ :=
  if b = 0 then Measure.dirac 0 else referenceLaw b (lawSecondMoment ν)

instance endpointReferenceLaw_isFiniteMeasure (ν : Measure ℝ) (b : ℝ) :
    IsFiniteMeasure (endpointReferenceLaw ν b) := by
  unfold endpointReferenceLaw
  split_ifs <;> infer_instance

theorem endpointReferenceLaw_zero (ν : Measure ℝ) :
    endpointReferenceLaw ν 0 = Measure.dirac 0 := by simp [endpointReferenceLaw]

theorem endpointReferenceLaw_of_pos (ν : Measure ℝ) (b : ℝ) (hb : 0 < b) :
    endpointReferenceLaw ν b = referenceLaw b (lawSecondMoment ν) := by
  simp [endpointReferenceLaw, hb.ne']

theorem endpointReferenceLaw_isProbabilityMeasure (ν : Measure ℝ) (b : ℝ) (hb : 0 ≤ b) :
    IsProbabilityMeasure (endpointReferenceLaw ν b) := by
  by_cases hzero : b = 0
  · rw [hzero, endpointReferenceLaw_zero]
    infer_instance
  · rw [endpointReferenceLaw_of_pos ν b (lt_of_le_of_ne hb (Ne.symm hzero))]
    exact referenceLaw_isProbabilityMeasure b _ (lt_of_le_of_ne hb (Ne.symm hzero))
      (lawSecondMoment_nonneg ν)

theorem squarePositiveOrder_endpointReferenceLaw (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (b : ℝ) (hb : 0 ≤ b) (hSq : Integrable (fun u : ℝ => u ^ 2) ν)
    (hm : (∫ u : ℝ, u ∂ν) = 0) (hu : ∀ᵐ u ∂ν, u ≤ b) :
    SquarePositiveOrder ν (endpointReferenceLaw ν b) := by
  by_cases hzero : b = 0
  · have hz := centered_nonpos_law_eq_dirac ν hSq hm (by simpa only [hzero] using hu)
    rw [hzero, endpointReferenceLaw_zero, hz.1]
    exact squarePositiveOrder_refl _
  · have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hzero)
    rw [endpointReferenceLaw_of_pos ν b hbpos]
    have h := squarePositiveOrder_map_referenceLaw ν id b (lawSecondMoment ν) hbpos
      (lawSecondMoment_nonneg ν) measurable_id hSq hm le_rfl hu
    simpa only [Measure.map_id] using h

theorem endpointReferenceLaw_moments (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (b : ℝ) (hb : 0 ≤ b) (hSq : Integrable (fun u : ℝ => u ^ 2) ν)
    (hm : (∫ u : ℝ, u ∂ν) = 0) (hu : ∀ᵐ u ∂ν, u ≤ b) :
    Integrable (fun u : ℝ => u) (endpointReferenceLaw ν b) ∧
    Integrable (fun u : ℝ => u ^ 2) (endpointReferenceLaw ν b) ∧
    (∫ u : ℝ, u ∂endpointReferenceLaw ν b) = 0 ∧
    (∫ u : ℝ, u ^ 2 ∂endpointReferenceLaw ν b) = lawSecondMoment ν := by
  by_cases hzero : b = 0
  · have hz := centered_nonpos_law_eq_dirac ν hSq hm (by simpa only [hzero] using hu)
    rw [hzero, endpointReferenceLaw_zero, hz.2]
    exact ⟨integrable_dirac (by simp), integrable_dirac (by simp), by simp, by simp⟩
  · have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hzero)
    rw [endpointReferenceLaw_of_pos ν b hbpos]
    exact ⟨integrable_referenceLaw b _ _, integrable_referenceLaw b _ _,
      integral_referenceLaw_id b _ hbpos (lawSecondMoment_nonneg ν),
      integral_referenceLaw_sq b _ hbpos (lawSecondMoment_nonneg ν)⟩

/-- The exact two-group reference law. Neither cap is replaced by a
common maximum, and the actual second moments remain attached to each group. -/
def coupledReferenceLaw (ν0 ν1 : Measure ℝ) (b0 b1 : ℝ) (n k : ℕ) : Measure ℝ :=
  MixtureSum.convPower (endpointReferenceLaw ν1 b1) k ∗
    MixtureSum.convPower (endpointReferenceLaw ν0 b0) (n - k)

instance coupledReferenceLaw_isFiniteMeasure (ν0 ν1 : Measure ℝ) (b0 b1 : ℝ) (n k : ℕ) :
    IsFiniteMeasure (coupledReferenceLaw ν0 ν1 b0 b1 n k) := by
  unfold coupledReferenceLaw
  infer_instance

theorem coupledReferenceLaw_isProbabilityMeasure (ν0 ν1 : Measure ℝ)
    (b0 b1 : ℝ) (hb0 : 0 ≤ b0) (hb1 : 0 ≤ b1) (n k : ℕ) :
    IsProbabilityMeasure (coupledReferenceLaw ν0 ν1 b0 b1 n k) := by
  have := endpointReferenceLaw_isProbabilityMeasure ν0 b0 hb0
  have := endpointReferenceLaw_isProbabilityMeasure ν1 b1 hb1
  unfold coupledReferenceLaw
  infer_instance

theorem coupledReferenceLaw_of_pos (ν0 ν1 : Measure ℝ) (b0 b1 : ℝ)
    (hb0 : 0 < b0) (hb1 : 0 < b1) (n k : ℕ) :
    coupledReferenceLaw ν0 ν1 b0 b1 n k =
      MixtureSum.convPower (referenceLaw b1 (lawSecondMoment ν1)) k ∗
        MixtureSum.convPower (referenceLaw b0 (lawSecondMoment ν0)) (n - k) := by
  simp only [coupledReferenceLaw, endpointReferenceLaw_of_pos ν0 b0 hb0,
    endpointReferenceLaw_of_pos ν1 b1 hb1]

theorem coupledReferenceLaw_moments (ν0 ν1 : Measure ℝ)
    [IsProbabilityMeasure ν0] [IsProbabilityMeasure ν1]
    (b0 b1 : ℝ) (hb0 : 0 ≤ b0) (hb1 : 0 ≤ b1)
    (hSq0 : Integrable (fun u : ℝ => u ^ 2) ν0) (hSq1 : Integrable (fun u : ℝ => u ^ 2) ν1)
    (hm0 : (∫ u : ℝ, u ∂ν0) = 0) (hm1 : (∫ u : ℝ, u ∂ν1) = 0)
    (hu0 : ∀ᵐ u ∂ν0, u ≤ b0) (hu1 : ∀ᵐ u ∂ν1, u ≤ b1) (n k : ℕ) :
    Integrable (fun u : ℝ => u) (coupledReferenceLaw ν0 ν1 b0 b1 n k) ∧
    Integrable (fun u : ℝ => u ^ 2) (coupledReferenceLaw ν0 ν1 b0 b1 n k) ∧
    (∫ u : ℝ, u ∂coupledReferenceLaw ν0 ν1 b0 b1 n k) = 0 ∧
    (∫ u : ℝ, u ^ 2 ∂coupledReferenceLaw ν0 ν1 b0 b1 n k) =
      ((n - k : ℕ) : ℝ) * lawSecondMoment ν0 + (k : ℝ) * lawSecondMoment ν1 := by
  have := endpointReferenceLaw_isProbabilityMeasure ν0 b0 hb0
  have := endpointReferenceLaw_isProbabilityMeasure ν1 b1 hb1
  obtain ⟨h01, h02, hm0', hv0⟩ := endpointReferenceLaw_moments ν0 b0 hb0 hSq0 hm0 hu0
  obtain ⟨h11, h12, hm1', hv1⟩ := endpointReferenceLaw_moments ν1 b1 hb1 hSq1 hm1 hu1
  obtain ⟨hA1, hA2, hmA, hvA⟩ := CommonProductMoments.convPower_moments
    (endpointReferenceLaw ν1 b1) h11 h12 hm1' k
  obtain ⟨hB1, hB2, hmB, hvB⟩ := CommonProductMoments.convPower_moments
    (endpointReferenceLaw ν0 b0) h01 h02 hm0' (n - k)
  refine ⟨CommonProductMoments.conv_integrable_first _ _ hA1 hB1,
    CommonProductMoments.conv_integrable_square _ _ hA1 hA2 hB1 hB2, ?_, ?_⟩
  · unfold coupledReferenceLaw
    rw [CommonProductMoments.integral_conv_first _ _ hA1 hB1, hmA, hmB]
    ring
  · unfold coupledReferenceLaw
    rw [CommonProductMoments.integral_conv_square _ _ hA1 hA2 hB1 hB2 hmA hmB,
      hvA, hvB, hv0, hv1]
    ring

theorem squarePositiveOrder_convPower (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (horder : SquarePositiveOrder μ ν) (m : ℕ) :
    SquarePositiveOrder (MixtureSum.convPower μ m) (MixtureSum.convPower ν m) := by
  have h := @squarePositiveOrder_finiteIndependentSumLaw (fun _ => μ) (fun _ => ν)
    (fun _ => inferInstance) (fun _ => inferInstance) (fun _ => horder) m
  simpa only [finiteIndependentSumLaw_const_eq_convPower] using h

theorem squarePositiveOrder_twoGroup (ν0 ν1 : Measure ℝ)
    [IsProbabilityMeasure ν0] [IsProbabilityMeasure ν1]
    (b0 b1 : ℝ) (hb0 : 0 ≤ b0) (hb1 : 0 ≤ b1)
    (hSq0 : Integrable (fun u : ℝ => u ^ 2) ν0) (hSq1 : Integrable (fun u : ℝ => u ^ 2) ν1)
    (hm0 : (∫ u : ℝ, u ∂ν0) = 0) (hm1 : (∫ u : ℝ, u ∂ν1) = 0)
    (hu0 : ∀ᵐ u ∂ν0, u ≤ b0) (hu1 : ∀ᵐ u ∂ν1, u ≤ b1) (n k : ℕ) :
    SquarePositiveOrder (MixtureSum.convPower ν1 k ∗ MixtureSum.convPower ν0 (n - k))
      (coupledReferenceLaw ν0 ν1 b0 b1 n k) := by
  have := endpointReferenceLaw_isProbabilityMeasure ν0 b0 hb0
  have := endpointReferenceLaw_isProbabilityMeasure ν1 b1 hb1
  exact squarePositiveOrder_conv _ _ _ _
    (squarePositiveOrder_convPower ν1 _ (squarePositiveOrder_endpointReferenceLaw ν1 b1 hb1 hSq1 hm1 hu1) k)
    (squarePositiveOrder_convPower ν0 _ (squarePositiveOrder_endpointReferenceLaw ν0 b0 hb0 hSq0 hm0 hu0) (n - k))

/-- The actual W on the original shared pair product is dominated by
the two-group reference law. Its distribution identification is proved,
not a premise of this theorem. -/
theorem squarePositiveOrder_map_W (ν0 ν1 : Measure ℝ)
    [IsProbabilityMeasure ν0] [IsProbabilityMeasure ν1]
    (b0 b1 : ℝ) (hb0 : 0 ≤ b0) (hb1 : 0 ≤ b1)
    (hSq0 : Integrable (fun u : ℝ => u ^ 2) ν0) (hSq1 : Integrable (fun u : ℝ => u ^ 2) ν1)
    (hm0 : (∫ u : ℝ, u ∂ν0) = 0) (hm1 : (∫ u : ℝ, u ∂ν1) = 0)
    (hu0 : ∀ᵐ u ∂ν0, u ≤ b0) (hu1 : ∀ᵐ u ∂ν1, u ≤ b1)
    (n k : ℕ) (hk : k ≤ n) :
    SquarePositiveOrder ((CommonProduct.pairProduct ν0 ν1 n).map (CommonProduct.W n k))
      (coupledReferenceLaw ν0 ν1 b0 b1 n k) := by
  rw [CommonProduct.map_W ν0 ν1 n k hk]
  exact squarePositiveOrder_twoGroup ν0 ν1 b0 b1 hb0 hb1 hSq0 hSq1 hm0 hm1 hu0 hu1 n k

theorem lawSecondMoment_map_neg (ν : Measure ℝ) :
    lawSecondMoment (ν.map (fun u : ℝ => -u)) = lawSecondMoment ν := by
  unfold lawSecondMoment
  rw [integral_map (f := fun u : ℝ => u ^ 2) measurable_neg.aemeasurable (by fun_prop)]
  simp only [neg_sq]

theorem reflected_residual_moments (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hSq : Integrable (fun u : ℝ => u ^ 2) ν) (hm : (∫ u : ℝ, u ∂ν) = 0) :
    Integrable (fun u : ℝ => u) (ν.map (fun u : ℝ => -u)) ∧
    Integrable (fun u : ℝ => u ^ 2) (ν.map (fun u : ℝ => -u)) ∧
    (∫ u : ℝ, u ∂ν.map (fun u : ℝ => -u)) = 0 ∧
    lawSecondMoment (ν.map (fun u : ℝ => -u)) = lawSecondMoment ν := by
  have hI := integrable_of_integrable_sq ν id measurable_id hSq
  refine ⟨?_, ?_, ?_, lawSecondMoment_map_neg ν⟩
  · exact (integrable_map_measure measurable_id.aestronglyMeasurable
      measurable_neg.aemeasurable).mpr hI.neg
  · apply (integrable_map_measure (by fun_prop) measurable_neg.aemeasurable).mpr
    change Integrable (fun u : ℝ => (-u) ^ 2) ν
    simpa only [neg_sq] using hSq
  · rw [integral_map (f := fun u : ℝ => u) measurable_neg.aemeasurable
      measurable_id.aestronglyMeasurable, integral_neg, hm, neg_zero]

theorem reflected_upper_of_lower (ν : Measure ℝ) (b : ℝ)
    (hu : ∀ᵐ u ∂ν, -b ≤ u) :
    ∀ᵐ u ∂ν.map (fun u : ℝ => -u), u ≤ b := by
  apply (ae_map_iff measurable_neg.aemeasurable measurableSet_Iic).mpr
  filter_upwards [hu] with u hu
  change -u ≤ b
  linarith

theorem endpointReferenceLaw_map_neg_inputs (ν : Measure ℝ) (b : ℝ) :
    endpointReferenceLaw (ν.map (fun u : ℝ => -u)) b = endpointReferenceLaw ν b := by
  unfold endpointReferenceLaw
  rw [lawSecondMoment_map_neg]

theorem coupledReferenceLaw_map_neg_inputs (ν0 ν1 : Measure ℝ) (b0 b1 : ℝ) (n k : ℕ) :
    coupledReferenceLaw (ν0.map (fun u : ℝ => -u)) (ν1.map (fun u : ℝ => -u)) b0 b1 n k =
      coupledReferenceLaw ν0 ν1 b0 b1 n k := by
  simp only [coupledReferenceLaw, endpointReferenceLaw_map_neg_inputs]

private theorem map_neg_convolution (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    (μ ∗ ν).map (fun u : ℝ => -u) =
      (μ.map (fun u : ℝ => -u)) ∗ (ν.map (fun u : ℝ => -u)) := by
  unfold Measure.conv
  rw [Measure.map_prod_map μ ν measurable_neg measurable_neg,
    Measure.map_map measurable_add (measurable_neg.prodMap measurable_neg),
    Measure.map_map measurable_neg measurable_add]
  congr 1
  funext p
  dsimp
  ring

theorem convPower_map_neg (ν : Measure ℝ) [IsFiniteMeasure ν] (m : ℕ) :
    (MixtureSum.convPower ν m).map (fun u : ℝ => -u) =
      MixtureSum.convPower (ν.map (fun u : ℝ => -u)) m := by
  rw [← finiteIndependentSumLaw_const_eq_convPower ν m,
    finiteIndependentSumLaw_const_map_neg, finiteIndependentSumLaw_const_eq_convPower]

/-- The reflected W is identified under the original shared product,
not merely under a separate product with reflected marginals. -/
theorem map_neg_W (ν0 ν1 : Measure ℝ) [IsProbabilityMeasure ν0] [IsProbabilityMeasure ν1]
    (n k : ℕ) (hk : k ≤ n) :
    (CommonProduct.pairProduct ν0 ν1 n).map (fun ω => -CommonProduct.W n k ω) =
      MixtureSum.convPower (ν1.map (fun u : ℝ => -u)) k ∗
        MixtureSum.convPower (ν0.map (fun u : ℝ => -u)) (n - k) := by
  have hcomp : (fun ω : CommonProduct.Space n => -CommonProduct.W n k ω) =
      (fun u : ℝ => -u) ∘ CommonProduct.W n k := rfl
  rw [hcomp, ← Measure.map_map measurable_neg (CommonProduct.measurable_W n k hk),
    CommonProduct.map_W ν0 ν1 n k hk, map_neg_convolution, convPower_map_neg, convPower_map_neg]

/-- Negative-side order, retaining the original actual second moments
and the two lower-cap sizes separately. -/
theorem squarePositiveOrder_map_neg_W (ν0 ν1 : Measure ℝ)
    [IsProbabilityMeasure ν0] [IsProbabilityMeasure ν1]
    (b0 b1 : ℝ) (hb0 : 0 ≤ b0) (hb1 : 0 ≤ b1)
    (hSq0 : Integrable (fun u : ℝ => u ^ 2) ν0) (hSq1 : Integrable (fun u : ℝ => u ^ 2) ν1)
    (hm0 : (∫ u : ℝ, u ∂ν0) = 0) (hm1 : (∫ u : ℝ, u ∂ν1) = 0)
    (hu0 : ∀ᵐ u ∂ν0, -b0 ≤ u) (hu1 : ∀ᵐ u ∂ν1, -b1 ≤ u)
    (n k : ℕ) (hk : k ≤ n) :
    SquarePositiveOrder
      ((CommonProduct.pairProduct ν0 ν1 n).map (fun ω => -CommonProduct.W n k ω))
      (coupledReferenceLaw ν0 ν1 b0 b1 n k) := by
  have h0 := reflected_residual_moments ν0 hSq0 hm0
  have h1 := reflected_residual_moments ν1 hSq1 hm1
  have h := squarePositiveOrder_twoGroup
    (ν0.map (fun u : ℝ => -u)) (ν1.map (fun u : ℝ => -u)) b0 b1 hb0 hb1
    h0.2.1 h1.2.1 h0.2.2.1 h1.2.2.1
    (reflected_upper_of_lower ν0 b0 hu0) (reflected_upper_of_lower ν1 b1 hu1) n k
  rw [← map_neg_W ν0 ν1 n k hk, coupledReferenceLaw_map_neg_inputs] at h
  exact h

theorem coupledReferenceLaw_moments_of_lower (ν0 ν1 : Measure ℝ)
    [IsProbabilityMeasure ν0] [IsProbabilityMeasure ν1]
    (b0 b1 : ℝ) (hb0 : 0 ≤ b0) (hb1 : 0 ≤ b1)
    (hSq0 : Integrable (fun u : ℝ => u ^ 2) ν0) (hSq1 : Integrable (fun u : ℝ => u ^ 2) ν1)
    (hm0 : (∫ u : ℝ, u ∂ν0) = 0) (hm1 : (∫ u : ℝ, u ∂ν1) = 0)
    (hu0 : ∀ᵐ u ∂ν0, -b0 ≤ u) (hu1 : ∀ᵐ u ∂ν1, -b1 ≤ u) (n k : ℕ) :
    Integrable (fun u : ℝ => u) (coupledReferenceLaw ν0 ν1 b0 b1 n k) ∧
    Integrable (fun u : ℝ => u ^ 2) (coupledReferenceLaw ν0 ν1 b0 b1 n k) ∧
    (∫ u : ℝ, u ∂coupledReferenceLaw ν0 ν1 b0 b1 n k) = 0 ∧
    (∫ u : ℝ, u ^ 2 ∂coupledReferenceLaw ν0 ν1 b0 b1 n k) =
      ((n - k : ℕ) : ℝ) * lawSecondMoment ν0 + (k : ℝ) * lawSecondMoment ν1 := by
  have h0 := reflected_residual_moments ν0 hSq0 hm0
  have h1 := reflected_residual_moments ν1 hSq1 hm1
  have h := coupledReferenceLaw_moments
    (ν0.map (fun u : ℝ => -u)) (ν1.map (fun u : ℝ => -u)) b0 b1 hb0 hb1
    h0.2.1 h1.2.1 h0.2.2.1 h1.2.2.1
    (reflected_upper_of_lower ν0 b0 hu0) (reflected_upper_of_lower ν1 b1 hu1) n k
  simpa only [coupledReferenceLaw_map_neg_inputs, lawSecondMoment_map_neg] using h

private lemma convPower_dirac_zero (m : ℕ) :
    MixtureSum.convPower (Measure.dirac (0 : ℝ)) m = Measure.dirac 0 := by
  induction m with
  | zero => rfl
  | succ m ih => simp [MixtureSum.convPower, ih]

theorem coupledReferenceLaw_zero_cap0 (ν0 ν1 : Measure ℝ) (b1 : ℝ) (n k : ℕ) :
    coupledReferenceLaw ν0 ν1 0 b1 n k = MixtureSum.convPower (endpointReferenceLaw ν1 b1) k := by
  rw [coupledReferenceLaw, endpointReferenceLaw_zero, convPower_dirac_zero, Measure.conv_dirac_zero]

theorem coupledReferenceLaw_zero_cap1 (ν0 ν1 : Measure ℝ) (b0 : ℝ) (n k : ℕ) :
    coupledReferenceLaw ν0 ν1 b0 0 n k = MixtureSum.convPower (endpointReferenceLaw ν0 b0) (n - k) := by
  rw [coupledReferenceLaw, endpointReferenceLaw_zero, convPower_dirac_zero, Measure.dirac_zero_conv]

theorem coupledReferenceLaw_count_zero (ν0 ν1 : Measure ℝ) (b0 b1 : ℝ) (n : ℕ) :
    coupledReferenceLaw ν0 ν1 b0 b1 n 0 = MixtureSum.convPower (endpointReferenceLaw ν0 b0) n := by
  simp [coupledReferenceLaw, MixtureSum.convPower]

theorem coupledReferenceLaw_count_all (ν0 ν1 : Measure ℝ) (b0 b1 : ℝ) (n : ℕ) :
    coupledReferenceLaw ν0 ν1 b0 b1 n n = MixtureSum.convPower (endpointReferenceLaw ν1 b1) n := by
  simp [coupledReferenceLaw, MixtureSum.convPower]

/-- Actual Bochner reference price, retaining both caps and both variances. -/
def coupledReferencePrice (ν0 ν1 : Measure ℝ) (b0 b1 : ℝ) (n k : ℕ) (c : ℝ) : ℝ :=
  ∫ u : ℝ, (max (u - c) 0) ^ 2 ∂coupledReferenceLaw ν0 ν1 b0 b1 n k

private theorem integrable_W_square (ν0 ν1 : Measure ℝ)
    [IsProbabilityMeasure ν0] [IsProbabilityMeasure ν1]
    (hSq0 : Integrable (fun u : ℝ => u ^ 2) ν0) (hSq1 : Integrable (fun u : ℝ => u ^ 2) ν1)
    (hm0 : (∫ u : ℝ, u ∂ν0) = 0) (hm1 : (∫ u : ℝ, u ∂ν1) = 0)
    (n k : ℕ) (hk : k ≤ n) :
    Integrable (fun ω => CommonProduct.W n k ω ^ 2) (CommonProduct.pairProduct ν0 ν1 n) :=
  (CommonProductMoments.moments_W ν0 ν1
    (integrable_of_integrable_sq ν0 id measurable_id hSq0) hSq0
    (integrable_of_integrable_sq ν1 id measurable_id hSq1) hSq1 hm0 hm1 n k hk).2.1

/-- Ordinary expectations are legitimate on both sides, by the proved
second-moment integrability of the actual W and reference law. -/
theorem integral_W_squarePositivePart_le_reference (ν0 ν1 : Measure ℝ)
    [IsProbabilityMeasure ν0] [IsProbabilityMeasure ν1]
    (b0 b1 c : ℝ) (hb0 : 0 ≤ b0) (hb1 : 0 ≤ b1)
    (hSq0 : Integrable (fun u : ℝ => u ^ 2) ν0) (hSq1 : Integrable (fun u : ℝ => u ^ 2) ν1)
    (hm0 : (∫ u : ℝ, u ∂ν0) = 0) (hm1 : (∫ u : ℝ, u ∂ν1) = 0)
    (hu0 : ∀ᵐ u ∂ν0, u ≤ b0) (hu1 : ∀ᵐ u ∂ν1, u ≤ b1)
    (n k : ℕ) (hk : k ≤ n) :
    (∫ ω, (max (CommonProduct.W n k ω - c) 0) ^ 2 ∂CommonProduct.pairProduct ν0 ν1 n) ≤
      coupledReferencePrice ν0 ν1 b0 b1 n k c := by
  have hW := integrable_squarePositivePart _ (CommonProduct.W n k) c
    (CommonProduct.measurable_W n k hk) (integrable_W_square ν0 ν1 hSq0 hSq1 hm0 hm1 n k hk)
  have hR : Integrable (fun u : ℝ => (max (u - c) 0) ^ 2)
      (coupledReferenceLaw ν0 ν1 b0 b1 n k) :=
    integrable_squarePositivePart _ id c measurable_id
      (coupledReferenceLaw_moments ν0 ν1 b0 b1 hb0 hb1 hSq0 hSq1 hm0 hm1 hu0 hu1 n k).2.1
  have horder := squarePositiveOrder_map_W ν0 ν1 b0 b1 hb0 hb1 hSq0 hSq1 hm0 hm1 hu0 hu1 n k hk c
  have hphi : Measurable (fun u : ℝ => ENNReal.ofReal ((max (u - c) 0) ^ 2)) := by fun_prop
  rw [lintegral_map hphi (CommonProduct.measurable_W n k hk),
    ← ofReal_integral_eq_lintegral_ofReal hW (Filter.Eventually.of_forall (fun ω => sq_nonneg _)),
    ← ofReal_integral_eq_lintegral_ofReal hR (Filter.Eventually.of_forall (fun u => sq_nonneg _))] at horder
  exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg (fun u => sq_nonneg _))).mp horder

theorem integral_neg_W_squarePositivePart_le_reference (ν0 ν1 : Measure ℝ)
    [IsProbabilityMeasure ν0] [IsProbabilityMeasure ν1]
    (b0 b1 c : ℝ) (hb0 : 0 ≤ b0) (hb1 : 0 ≤ b1)
    (hSq0 : Integrable (fun u : ℝ => u ^ 2) ν0) (hSq1 : Integrable (fun u : ℝ => u ^ 2) ν1)
    (hm0 : (∫ u : ℝ, u ∂ν0) = 0) (hm1 : (∫ u : ℝ, u ∂ν1) = 0)
    (hu0 : ∀ᵐ u ∂ν0, -b0 ≤ u) (hu1 : ∀ᵐ u ∂ν1, -b1 ≤ u)
    (n k : ℕ) (hk : k ≤ n) :
    (∫ ω, (max (-CommonProduct.W n k ω - c) 0) ^ 2 ∂CommonProduct.pairProduct ν0 ν1 n) ≤
      coupledReferencePrice ν0 ν1 b0 b1 n k c := by
  have hnegW : Measurable (fun ω => -CommonProduct.W n k ω) := (CommonProduct.measurable_W n k hk).neg
  have hnegSq : Integrable (fun ω => (-CommonProduct.W n k ω) ^ 2)
      (CommonProduct.pairProduct ν0 ν1 n) := by
    simpa only [neg_sq] using integrable_W_square ν0 ν1 hSq0 hSq1 hm0 hm1 n k hk
  have hW := integrable_squarePositivePart _ (fun ω => -CommonProduct.W n k ω) c hnegW hnegSq
  have hR : Integrable (fun u : ℝ => (max (u - c) 0) ^ 2)
      (coupledReferenceLaw ν0 ν1 b0 b1 n k) :=
    integrable_squarePositivePart _ id c measurable_id
      (coupledReferenceLaw_moments_of_lower ν0 ν1 b0 b1 hb0 hb1 hSq0 hSq1 hm0 hm1 hu0 hu1 n k).2.1
  have horder := squarePositiveOrder_map_neg_W ν0 ν1 b0 b1 hb0 hb1 hSq0 hSq1 hm0 hm1 hu0 hu1 n k hk c
  have hphi : Measurable (fun u : ℝ => ENNReal.ofReal ((max (u - c) 0) ^ 2)) := by fun_prop
  rw [lintegral_map hphi hnegW,
    ← ofReal_integral_eq_lintegral_ofReal hW (Filter.Eventually.of_forall (fun ω => sq_nonneg _)),
    ← ofReal_integral_eq_lintegral_ofReal hR (Filter.Eventually.of_forall (fun u => sq_nonneg _))] at horder
  exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg (fun u => sq_nonneg _))).mp horder

end

end BerryEsseen.TwoMoment

#print axioms BerryEsseen.TwoMoment.centered_nonpos_law_eq_dirac
#print axioms BerryEsseen.TwoMoment.coupledReferenceLaw_moments
#print axioms BerryEsseen.TwoMoment.squarePositiveOrder_map_W
#print axioms BerryEsseen.TwoMoment.map_neg_W
#print axioms BerryEsseen.TwoMoment.squarePositiveOrder_map_neg_W
#print axioms BerryEsseen.TwoMoment.integral_W_squarePositivePart_le_reference
#print axioms BerryEsseen.TwoMoment.integral_neg_W_squarePositivePart_le_reference
