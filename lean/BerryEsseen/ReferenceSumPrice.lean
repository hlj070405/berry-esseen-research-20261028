module

public import BerryEsseen.FiniteVarianceEqualization
public import BerryEsseen.CommonProductMoments

@[expose] public section

/-!
The finite independent-law Bentkus comparison and the actual reference
price K. Its moments, integrability and variance increments refer to
one and the same uniform product/convolution reference measure.
-/

namespace BerryEsseen.TwoMoment

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

/-- The genuine sum of `n` independent copies of `T_{b,V/n}`. -/
def uniformReferenceSumLaw (b : ℝ) (n : ℕ) (V : ℝ) : Measure ℝ :=
  finiteIndependentSumLaw (fun _ => referenceLaw b (V / (n : ℝ))) n

private theorem squarePositiveOrder_finiteIndependentSumLaw_of_range
    (μ ν : ℕ → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    [∀ i, IsProbabilityMeasure (ν i)] (n : ℕ)
    (horder : ∀ i, i < n → SquarePositiveOrder (μ i) (ν i)) :
    SquarePositiveOrder (finiteIndependentSumLaw μ n) (finiteIndependentSumLaw ν n) := by
  induction n with
  | zero => exact squarePositiveOrder_refl _
  | succ n ih =>
    exact squarePositiveOrder_add (μ n) (ν n) (finiteIndependentSumLaw μ n)
      (finiteIndependentSumLaw ν n) (horder n (Nat.lt_succ_self _))
      (ih (fun i hi => horder i (Nat.lt_succ_of_lt hi)))

/-- Full independent-law comparison with the actual second moments.
Moment, centering and upper-support assumptions concern only the `n`
coordinates that occur in the sum, with no support restriction otherwise. -/
theorem finiteIndependentSumLaw_le_uniformReferenceSumLaw
    (μ : ℕ → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (b V : ℝ) (n : ℕ) (hb : 0 < b) (hn : 0 < n)
    (hSq : ∀ i, i < n → Integrable (fun x : ℝ => x ^ 2) (μ i))
    (hcenter : ∀ i, i < n → (∫ x : ℝ, x ∂μ i) = 0)
    (hupper : ∀ i, i < n → ∀ᵐ x ∂μ i, x ≤ b)
    (hV : (∑ i ∈ Finset.range n, ∫ x : ℝ, x ^ 2 ∂μ i) ≤ V) :
    SquarePositiveOrder (finiteIndependentSumLaw μ n) (uniformReferenceSumLaw b n V) := by
  let z : ℕ → ℝ := fun i => ∫ x : ℝ, x ^ 2 ∂μ i
  have hz : ∀ i, 0 ≤ z i := fun i => integral_nonneg (fun x => sq_nonneg _)
  have hprob : ∀ i, IsProbabilityMeasure (referenceLaw b (z i)) :=
    fun i => referenceLaw_isProbabilityMeasure b (z i) hb (hz i)
  have hcoord : ∀ i, i < n → SquarePositiveOrder (μ i) (referenceLaw b (z i)) := by
    intro i hi
    have h := squarePositiveOrder_map_referenceLaw (μ i) id b (z i) hb (hz i)
      measurable_id (hSq i hi) (hcenter i hi) le_rfl (hupper i hi)
    simpa only [Measure.map_id] using h
  have hreplace := @squarePositiveOrder_finiteIndependentSumLaw_of_range
    μ (fun i => referenceLaw b (z i)) (by infer_instance) hprob n hcoord
  exact squarePositiveOrder_trans hreplace
    (finiteIndependentSumLaw_reference_le_uniform_budget b V z n hb hn (fun i _ => hz i) hV)

theorem finiteIndependentSumLaw_const_eq_convPower (μ : Measure ℝ) (n : ℕ) :
    finiteIndependentSumLaw (fun _ => μ) n = MixtureSum.convPower μ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change μ ∗ finiteIndependentSumLaw (fun _ => μ) n = μ ∗ MixtureSum.convPower μ n
    rw [ih]

theorem uniformReferenceSumLaw_isProbabilityMeasure (b : ℝ) (n : ℕ) (V : ℝ)
    (hb : 0 < b) (hV : 0 ≤ V) : IsProbabilityMeasure (uniformReferenceSumLaw b n V) := by
  have hz : 0 ≤ V / (n : ℝ) := div_nonneg hV (Nat.cast_nonneg _)
  exact @finiteIndependentSumLaw_isProbabilityMeasure (fun _ => referenceLaw b (V / (n : ℝ)))
    (fun _ => referenceLaw_isProbabilityMeasure b (V / (n : ℝ)) hb hz) n

/-- Integrability and moments of the same actual uniform reference law.
The total second moment is `V`, with `n > 0` explicit. -/
theorem uniformReferenceSumLaw_moments (b : ℝ) (n : ℕ) (V : ℝ)
    (hb : 0 < b) (hn : 0 < n) (hV : 0 ≤ V) :
    Integrable (fun x : ℝ => x) (uniformReferenceSumLaw b n V) ∧
    Integrable (fun x : ℝ => x ^ 2) (uniformReferenceSumLaw b n V) ∧
    (∫ x : ℝ, x ∂uniformReferenceSumLaw b n V) = 0 ∧
    (∫ x : ℝ, x ^ 2 ∂uniformReferenceSumLaw b n V) = V := by
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hz := div_nonneg hV hnR.le
  have := referenceLaw_isProbabilityMeasure b (V / (n : ℝ)) hb hz
  have h := CommonProductMoments.convPower_moments (referenceLaw b (V / (n : ℝ)))
    (integrable_referenceLaw b _ _) (integrable_referenceLaw b _ _)
    (integral_referenceLaw_id b _ hb hz) n
  rw [← finiteIndependentSumLaw_const_eq_convPower] at h
  obtain ⟨hI, hSq, hm, hv⟩ := h
  refine ⟨hI, hSq, hm, ?_⟩
  unfold uniformReferenceSumLaw
  rw [hv, integral_referenceLaw_sq b _ hb hz]
  field_simp [hnR.ne']

/-- The true finite reference price K_b,n(V,c). -/
def referenceSumPrice (b : ℝ) (n : ℕ) (V c : ℝ) : ℝ :=
  ∫ x : ℝ, (max (x - c) 0) ^ 2 ∂uniformReferenceSumLaw b n V

/-- The opposite squared positive part under exactly the same law. -/
def referenceSumLowerPrice (b : ℝ) (n : ℕ) (V c : ℝ) : ℝ :=
  ∫ x : ℝ, (max (c - x) 0) ^ 2 ∂uniformReferenceSumLaw b n V

theorem integrable_referenceSumPrice (b : ℝ) (n : ℕ) (V c : ℝ)
    (hb : 0 < b) (hn : 0 < n) (hV : 0 ≤ V) :
    Integrable (fun x : ℝ => (max (x - c) 0) ^ 2) (uniformReferenceSumLaw b n V) := by
  have := uniformReferenceSumLaw_isProbabilityMeasure b n V hb hV
  exact integrable_squarePositivePart _ id c measurable_id
    (uniformReferenceSumLaw_moments b n V hb hn hV).2.1

theorem integrable_referenceSumLowerPrice (b : ℝ) (n : ℕ) (V c : ℝ)
    (hb : 0 < b) (hn : 0 < n) (hV : 0 ≤ V) :
    Integrable (fun x : ℝ => (max (c - x) 0) ^ 2) (uniformReferenceSumLaw b n V) := by
  have := uniformReferenceSumLaw_isProbabilityMeasure b n V hb hV
  exact Staircase.integrable_clippedSquare_of_integrable_sq _ id c measurable_id
    (uniformReferenceSumLaw_moments b n V hb hn hV).2.1

theorem referenceSumPrice_add_lowerPrice (b : ℝ) (n : ℕ) (V c : ℝ)
    (hb : 0 < b) (hn : 0 < n) (hV : 0 ≤ V) :
    referenceSumPrice b n V c + referenceSumLowerPrice b n V c = V + c ^ 2 := by
  have := uniformReferenceSumLaw_isProbabilityMeasure b n V hb hV
  obtain ⟨hI, hSq, hm, hv⟩ := uniformReferenceSumLaw_moments b n V hb hn hV
  calc
    _ = ∫ x : ℝ, (max (x - c) 0) ^ 2 + (max (c - x) 0) ^ 2
        ∂uniformReferenceSumLaw b n V :=
      (integral_add (integrable_referenceSumPrice b n V c hb hn hV)
        (integrable_referenceSumLowerPrice b n V c hb hn hV)).symm
    _ = ∫ x : ℝ, (x - c) ^ 2 ∂uniformReferenceSumLaw b n V := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [show c - x = -(x - c) by ring]
      exact positivePart_sq_add_negativePart_sq (x - c)
    _ = (∫ x : ℝ, x ^ 2 ∂uniformReferenceSumLaw b n V) + c ^ 2 :=
      integral_shift_sq _ id c hI hSq hm
    _ = V + c ^ 2 := by rw [hv]

theorem squarePositiveOrder_referenceLaw_parameters_mono (b₁ b₂ z₁ z₂ : ℝ)
    (hb₁ : 0 < b₁) (hb : b₁ ≤ b₂) (hz₁ : 0 ≤ z₁) (hz : z₁ ≤ z₂) :
    SquarePositiveOrder (referenceLaw b₁ z₁) (referenceLaw b₂ z₂) := by
  intro c
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_referenceLaw b₁ z₁ _)
      (Filter.Eventually.of_forall (fun x => sq_nonneg _)),
    ← ofReal_integral_eq_lintegral_ofReal (integrable_referenceLaw b₂ z₂ _)
      (Filter.Eventually.of_forall (fun x => sq_nonneg _)),
    integral_referenceLaw_squarePositivePart b₁ z₁ c hb₁ hz₁,
    integral_referenceLaw_squarePositivePart b₂ z₂ c (hb₁.trans_le hb) (hz₁.trans hz)]
  exact ENNReal.ofReal_le_ofReal (referencePrice_mono b₁ b₂ z₁ z₂ c hb₁ hb hz₁ hz)

theorem squarePositiveOrder_uniformReferenceSumLaw_mono
    (b₁ b₂ : ℝ) (n : ℕ) (V₁ V₂ : ℝ)
    (hb₁ : 0 < b₁) (hb : b₁ ≤ b₂) (hV₁ : 0 ≤ V₁) (hV : V₁ ≤ V₂) :
    SquarePositiveOrder (uniformReferenceSumLaw b₁ n V₁) (uniformReferenceSumLaw b₂ n V₂) := by
  have hz₁ := div_nonneg hV₁ (Nat.cast_nonneg n)
  have hz₂ := div_nonneg (hV₁.trans hV) (Nat.cast_nonneg n)
  have hz := div_le_div_of_nonneg_right hV (Nat.cast_nonneg n : 0 ≤ (n : ℝ))
  exact @squarePositiveOrder_finiteIndependentSumLaw
    (fun _ => referenceLaw b₁ (V₁ / (n : ℝ))) (fun _ => referenceLaw b₂ (V₂ / (n : ℝ)))
    (fun _ => referenceLaw_isProbabilityMeasure b₁ _ hb₁ hz₁)
    (fun _ => referenceLaw_isProbabilityMeasure b₂ _ (hb₁.trans_le hb) hz₂)
    (fun _ => squarePositiveOrder_referenceLaw_parameters_mono b₁ b₂ _ _ hb₁ hb hz₁ hz) n

private theorem integral_squarePrice_mono {μ ν : Measure ℝ} (horder : SquarePositiveOrder μ ν)
    (c : ℝ) (hμ : Integrable (fun x : ℝ => (max (x - c) 0) ^ 2) μ)
    (hν : Integrable (fun x : ℝ => (max (x - c) 0) ^ 2) ν) :
    (∫ x : ℝ, (max (x - c) 0) ^ 2 ∂μ) ≤ ∫ x : ℝ, (max (x - c) 0) ^ 2 ∂ν := by
  have h := horder c
  rw [← ofReal_integral_eq_lintegral_ofReal hμ (Filter.Eventually.of_forall (fun x => sq_nonneg _)),
    ← ofReal_integral_eq_lintegral_ofReal hν (Filter.Eventually.of_forall (fun x => sq_nonneg _))] at h
  exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg (fun x => sq_nonneg _))).mp h

theorem referenceSumPrice_mono (b₁ b₂ : ℝ) (n : ℕ) (V₁ V₂ c : ℝ)
    (hb₁ : 0 < b₁) (hb : b₁ ≤ b₂) (hn : 0 < n) (hV₁ : 0 ≤ V₁) (hV : V₁ ≤ V₂) :
    referenceSumPrice b₁ n V₁ c ≤ referenceSumPrice b₂ n V₂ c :=
  integral_squarePrice_mono (squarePositiveOrder_uniformReferenceSumLaw_mono b₁ b₂ n V₁ V₂
    hb₁ hb hV₁ hV) c (integrable_referenceSumPrice b₁ n V₁ c hb₁ hn hV₁)
      (integrable_referenceSumPrice b₂ n V₂ c (hb₁.trans_le hb) hn (hV₁.trans hV))

/-- Reflection of the actual two-point measure. Positive variance is
explicit; its zero-variance boundary is the Dirac law, treated separately. -/
theorem referenceLaw_map_neg (b z : ℝ) (hb : 0 < b) (hz : 0 < z) :
    (referenceLaw b z).map (fun x : ℝ => -x) = referenceLaw (z / b) z := by
  have hd : 0 < b ^ 2 + z := add_pos (sq_pos_of_pos hb) hz
  have hb' : 0 < z / b := div_pos hz hb
  have hd' : 0 < (z / b) ^ 2 + z := add_pos (sq_pos_of_pos hb') hz
  have hl : -z / (z / b) = -b := by field_simp [hb.ne', hz.ne']
  have hw₁ : z / ((z / b) ^ 2 + z) = b ^ 2 / (b ^ 2 + z) := by
    field_simp [hb.ne', hz.ne', hd.ne', hd'.ne'] ; ring
  have hw₂ : (z / b) ^ 2 / ((z / b) ^ 2 + z) = z / (b ^ 2 + z) := by
    field_simp [hb.ne', hz.ne', hd.ne', hd'.ne'] ; ring
  unfold referenceLaw
  rw [Measure.map_add _ _ measurable_neg,
    Measure.map_smul _ measurable_neg.aemeasurable,
    Measure.map_smul _ measurable_neg.aemeasurable,
    Measure.map_dirac' measurable_neg, Measure.map_dirac' measurable_neg,
    show -(-z / b) = z / b by ring, hl, hw₁, hw₂]
  exact add_comm _ _

private theorem map_neg_conv (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    (μ ∗ ν).map (fun x : ℝ => -x) =
      (μ.map (fun x : ℝ => -x)) ∗ (ν.map (fun x : ℝ => -x)) := by
  unfold Measure.conv
  rw [Measure.map_prod_map μ ν measurable_neg measurable_neg,
    Measure.map_map measurable_add (measurable_neg.prodMap measurable_neg),
    Measure.map_map measurable_neg measurable_add]
  congr 1
  funext p
  dsimp
  ring

private theorem finiteIndependentSumLaw_const_isFiniteMeasure
    (μ : Measure ℝ) [IsFiniteMeasure μ] (n : ℕ) :
    IsFiniteMeasure (finiteIndependentSumLaw (fun _ => μ) n) := by
  induction n with
  | zero => dsimp [finiteIndependentSumLaw]; infer_instance
  | succ n ih =>
    have := ih
    change IsFiniteMeasure (μ ∗ finiteIndependentSumLaw (fun _ => μ) n)
    infer_instance

theorem finiteIndependentSumLaw_const_map_neg (μ : Measure ℝ) [IsFiniteMeasure μ] (n : ℕ) :
    (finiteIndependentSumLaw (fun _ => μ) n).map (fun x : ℝ => -x) =
      finiteIndependentSumLaw (fun _ => μ.map (fun x : ℝ => -x)) n := by
  induction n with
  | zero => simp [finiteIndependentSumLaw, Measure.map_dirac' measurable_neg]
  | succ n ih =>
    have := finiteIndependentSumLaw_const_isFiniteMeasure μ n
    change (μ ∗ finiteIndependentSumLaw (fun _ => μ) n).map (fun x : ℝ => -x) =
      (μ.map (fun x : ℝ => -x)) ∗
        finiteIndependentSumLaw (fun _ => μ.map (fun x : ℝ => -x)) n
    rw [map_neg_conv, ih]

private theorem finiteIndependentSumLaw_const_dirac_zero (n : ℕ) :
    finiteIndependentSumLaw (fun _ => Measure.dirac (0 : ℝ)) n = Measure.dirac 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (Measure.dirac (0 : ℝ)) ∗
      finiteIndependentSumLaw (fun _ => Measure.dirac (0 : ℝ)) n = Measure.dirac 0
    rw [ih]
    simp

theorem uniformReferenceSumLaw_zero (b : ℝ) (n : ℕ) (hb : 0 < b) :
    uniformReferenceSumLaw b n 0 = Measure.dirac 0 := by
  unfold uniformReferenceSumLaw
  simp only [zero_div, referenceLaw_zero b hb]
  exact finiteIndependentSumLaw_const_dirac_zero n

theorem uniformReferenceSumLaw_map_neg (b : ℝ) (n : ℕ) (V : ℝ)
    (hb : 0 < b) (hn : 0 < n) (hV : 0 < V) :
    (uniformReferenceSumLaw b n V).map (fun x : ℝ => -x) =
      uniformReferenceSumLaw ((V / (n : ℝ)) / b) n V := by
  have hz : 0 < V / (n : ℝ) := div_pos hV (Nat.cast_pos.mpr hn)
  unfold uniformReferenceSumLaw
  rw [finiteIndependentSumLaw_const_map_neg, referenceLaw_map_neg b _ hb hz]

theorem referenceSumPrice_zero (b : ℝ) (n : ℕ) (c : ℝ) (hb : 0 < b) :
    referenceSumPrice b n 0 c = (max (-c) 0) ^ 2 := by
  unfold referenceSumPrice
  rw [uniformReferenceSumLaw_zero b n hb, integral_dirac]
  simp

theorem referenceSumLowerPrice_zero (b : ℝ) (n : ℕ) (c : ℝ) (hb : 0 < b) :
    referenceSumLowerPrice b n 0 c = (max c 0) ^ 2 := by
  unfold referenceSumLowerPrice
  rw [uniformReferenceSumLaw_zero b n hb, integral_dirac]
  simp

theorem referenceSumLowerPrice_eq_reflected (b : ℝ) (n : ℕ) (V c : ℝ)
    (hb : 0 < b) (hn : 0 < n) (hV : 0 < V) :
    referenceSumLowerPrice b n V c =
      referenceSumPrice ((V / (n : ℝ)) / b) n V (-c) := by
  unfold referenceSumLowerPrice referenceSumPrice
  rw [← uniformReferenceSumLaw_map_neg b n V hb hn hV,
    integral_map (f := fun x : ℝ => (max (x - -c) 0) ^ 2)
      measurable_neg.aemeasurable (by fun_prop)]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [show -x - -c = c - x by ring]

/-- The negative-side price also increases with total variance. At zero
variance the measure is handled as a Dirac mass; no positive-variance
reference with upper endpoint zero is introduced. -/
theorem referenceSumLowerPrice_variance_mono (b : ℝ) (n : ℕ) (V₁ V₂ c : ℝ)
    (hb : 0 < b) (hn : 0 < n) (hV₁ : 0 ≤ V₁) (hV : V₁ ≤ V₂) :
    referenceSumLowerPrice b n V₁ c ≤ referenceSumLowerPrice b n V₂ c := by
  have hV₂ : 0 ≤ V₂ := hV₁.trans hV
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  by_cases hzero₂ : V₂ = 0
  · have hzero₁ : V₁ = 0 := by linarith
    subst V₁
    subst V₂
    exact le_rfl
  have hpos₂ : 0 < V₂ := lt_of_le_of_ne hV₂ (Ne.symm hzero₂)
  have hb₂ : 0 < (V₂ / (n : ℝ)) / b := div_pos (div_pos hpos₂ hnR) hb
  by_cases hzero₁ : V₁ = 0
  · rw [hzero₁, referenceSumLowerPrice_zero b n c hb,
      referenceSumLowerPrice_eq_reflected b n V₂ c hb hn hpos₂]
    have h := referenceSumPrice_mono ((V₂ / (n : ℝ)) / b) ((V₂ / (n : ℝ)) / b)
      n 0 V₂ (-c) hb₂ le_rfl hn le_rfl hV₂
    rw [referenceSumPrice_zero _ n (-c) hb₂] at h
    simpa only [neg_neg] using h
  have hpos₁ : 0 < V₁ := lt_of_le_of_ne hV₁ (Ne.symm hzero₁)
  have hb₁ : 0 < (V₁ / (n : ℝ)) / b := div_pos (div_pos hpos₁ hnR) hb
  have hbounds : (V₁ / (n : ℝ)) / b ≤ (V₂ / (n : ℝ)) / b :=
    div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hV hnR.le) hb.le
  rw [referenceSumLowerPrice_eq_reflected b n V₁ c hb hn hpos₁,
    referenceSumLowerPrice_eq_reflected b n V₂ c hb hn hpos₂]
  exact referenceSumPrice_mono _ _ n V₁ V₂ (-c) hb₁ hbounds hn hV₁ hV

/-- The true finite reference price is increasing and 1-Lipschitz in
total variance, including the zero-variance boundary. This statement
does not assume or assert differentiability. -/
theorem referenceSumPrice_variance_increment (b : ℝ) (n : ℕ) (V₁ V₂ c : ℝ)
    (hb : 0 < b) (hn : 0 < n) (hV₁ : 0 ≤ V₁) (hV : V₁ ≤ V₂) :
    0 ≤ referenceSumPrice b n V₂ c - referenceSumPrice b n V₁ c ∧
      referenceSumPrice b n V₂ c - referenceSumPrice b n V₁ c ≤ V₂ - V₁ := by
  have hpositive := referenceSumPrice_mono b b n V₁ V₂ c hb le_rfl hn hV₁ hV
  have hnegative := referenceSumLowerPrice_variance_mono b n V₁ V₂ c hb hn hV₁ hV
  have hsum₁ := referenceSumPrice_add_lowerPrice b n V₁ c hb hn hV₁
  have hsum₂ := referenceSumPrice_add_lowerPrice b n V₂ c hb hn (hV₁.trans hV)
  constructor <;> linarith

end

end BerryEsseen.TwoMoment

#print axioms BerryEsseen.TwoMoment.finiteIndependentSumLaw_le_uniformReferenceSumLaw
#print axioms BerryEsseen.TwoMoment.uniformReferenceSumLaw_moments
#print axioms BerryEsseen.TwoMoment.referenceSumPrice_add_lowerPrice
#print axioms BerryEsseen.TwoMoment.referenceSumPrice_mono
#print axioms BerryEsseen.TwoMoment.referenceLaw_map_neg
#print axioms BerryEsseen.TwoMoment.uniformReferenceSumLaw_map_neg
#print axioms BerryEsseen.TwoMoment.referenceSumPrice_variance_increment
