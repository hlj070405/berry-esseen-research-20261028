module

public import BerryEsseen.CommonProduct
public import BerryEsseen.MomentBudget
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

noncomputable section

namespace BerryEsseen.CommonProductMoments

open MeasureTheory

instance convPower_isProbability (ν : Measure ℝ) [IsProbabilityMeasure ν] (n : ℕ) :
    IsProbabilityMeasure (MixtureSum.convPower ν n) := by
  induction n with
  | zero => dsimp [MixtureSum.convPower]; infer_instance
  | succ n ih => dsimp [MixtureSum.convPower]; infer_instance

private theorem integral_fst (ν μ : Measure ℝ) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    (f : ℝ → ℝ) (hf : Integrable f ν) :
    (∫ z : ℝ × ℝ, f z.1 ∂(ν.prod μ)) = ∫ x, f x ∂ν := by
  rw [integral_prod _ (hf.comp_fst μ)]
  simp

private theorem integral_snd (ν μ : Measure ℝ) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    (f : ℝ → ℝ) (hf : Integrable f μ) :
    (∫ z : ℝ × ℝ, f z.2 ∂(ν.prod μ)) = ∫ x, f x ∂μ := by
  rw [integral_prod _ (hf.comp_snd ν)]
  simp

theorem conv_integrable_first (ν μ : Measure ℝ)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    (hν : Integrable (fun x : ℝ => x) ν) (hμ : Integrable (fun x : ℝ => x) μ) :
    Integrable (fun x : ℝ => x) (ν ∗ μ) := by
  unfold Measure.conv
  exact (integrable_map_measure measurable_id.aestronglyMeasurable
    measurable_add.aemeasurable).mpr ((hν.comp_fst μ).add (hμ.comp_snd ν))

theorem conv_integrable_square (ν μ : Measure ℝ)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    (hν : Integrable (fun x : ℝ => x) ν)
    (hν2 : Integrable (fun x : ℝ => x ^ 2) ν)
    (hμ : Integrable (fun x : ℝ => x) μ)
    (hμ2 : Integrable (fun x : ℝ => x ^ 2) μ) :
    Integrable (fun x : ℝ => x ^ 2) (ν ∗ μ) := by
  have hx := hν2.comp_fst μ
  have hy := hμ2.comp_snd ν
  have hxy := (hν.mul_prod hμ).const_mul 2
  have hi := (hx.add hxy).add hy
  unfold Measure.conv
  apply (integrable_map_measure (by fun_prop) measurable_add.aemeasurable).mpr
  exact hi.congr (Filter.Eventually.of_forall fun z => by
    simp only [Pi.add_apply]
    change z.1 ^ 2 + 2 * (z.1 * z.2) + z.2 ^ 2 = (z.1 + z.2) ^ 2
    ring)

theorem integral_conv_first (ν μ : Measure ℝ)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    (hν : Integrable (fun x : ℝ => x) ν) (hμ : Integrable (fun x : ℝ => x) μ) :
    (∫ x : ℝ, x ∂(ν ∗ μ)) = (∫ x : ℝ, x ∂ν) + ∫ x : ℝ, x ∂μ := by
  unfold Measure.conv
  rw [integral_map (f := fun x : ℝ => x) measurable_add.aemeasurable
      measurable_id.aestronglyMeasurable,
    integral_add (hν.comp_fst μ) (hμ.comp_snd ν),
    integral_fst ν μ _ hν, integral_snd ν μ _ hμ]

theorem integral_conv_square (ν μ : Measure ℝ)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    (hν : Integrable (fun x : ℝ => x) ν)
    (hν2 : Integrable (fun x : ℝ => x ^ 2) ν)
    (hμ : Integrable (fun x : ℝ => x) μ)
    (hμ2 : Integrable (fun x : ℝ => x ^ 2) μ)
    (hmν : (∫ x : ℝ, x ∂ν) = 0) (hmμ : (∫ x : ℝ, x ∂μ) = 0) :
    (∫ x : ℝ, x ^ 2 ∂(ν ∗ μ)) = (∫ x : ℝ, x ^ 2 ∂ν) + ∫ x : ℝ, x ^ 2 ∂μ := by
  have hx := hν2.comp_fst μ
  have hy := hμ2.comp_snd ν
  have hxy := (hν.mul_prod hμ).const_mul 2
  have hA : Integrable (fun z : ℝ × ℝ => z.1 ^ 2 + 2 * (z.1 * z.2)) (ν.prod μ) :=
    hx.add hxy
  have heq : (fun z : ℝ × ℝ => (z.1 + z.2) ^ 2) =
      (fun z => z.1 ^ 2 + 2 * (z.1 * z.2) + z.2 ^ 2) := by funext z; ring
  unfold Measure.conv
  rw [integral_map (f := fun x : ℝ => x ^ 2) measurable_add.aemeasurable (by fun_prop),
    heq, integral_add hA hy, integral_add hx hxy, integral_const_mul,
    integral_fst ν μ _ hν2, integral_snd ν μ _ hμ2,
    integral_prod_mul (μ := ν) (ν := μ) (fun x : ℝ => x) (fun x : ℝ => x), hmν, hmμ]
  ring

/-- The actual moments of every independent repeated sum, including the empty sum. -/
theorem convPower_moments (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h1 : Integrable (fun x : ℝ => x) ν)
    (h2 : Integrable (fun x : ℝ => x ^ 2) ν)
    (hm : (∫ x : ℝ, x ∂ν) = 0) (n : ℕ) :
    Integrable (fun x : ℝ => x) (MixtureSum.convPower ν n) ∧
    Integrable (fun x : ℝ => x ^ 2) (MixtureSum.convPower ν n) ∧
    (∫ x : ℝ, x ∂(MixtureSum.convPower ν n)) = 0 ∧
    (∫ x : ℝ, x ^ 2 ∂(MixtureSum.convPower ν n)) = (n : ℝ) * ∫ x : ℝ, x ^ 2 ∂ν := by
  induction n with
  | zero =>
    dsimp only [MixtureSum.convPower]
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact integrable_dirac (a := (0 : ℝ)) (f := fun x : ℝ => x) (by simp)
    · exact integrable_dirac (a := (0 : ℝ)) (f := fun x : ℝ => x ^ 2) (by simp)
    · simp
    · simp
  | succ n ih =>
    obtain ⟨hn1, hn2, hnm, hnv⟩ := ih
    dsimp only [MixtureSum.convPower]
    refine ⟨conv_integrable_first ν _ h1 hn1,
      conv_integrable_square ν _ h1 h2 hn1 hn2, ?_, ?_⟩
    · rw [integral_conv_first ν _ h1 hn1, hm, hnm]
      ring
    · rw [integral_conv_square ν _ h1 h2 hn1 hn2 hm hnm, hnv]
      push_cast
      ring

/-- Integrability, centering and the square integral of the same shared
`CommonProduct.W` used by the staircase CDF. -/
theorem moments_W (ν0 ν1 : Measure ℝ)
    [IsProbabilityMeasure ν0] [IsProbabilityMeasure ν1]
    (h01 : Integrable (fun x : ℝ => x) ν0)
    (h02 : Integrable (fun x : ℝ => x ^ 2) ν0)
    (h11 : Integrable (fun x : ℝ => x) ν1)
    (h12 : Integrable (fun x : ℝ => x ^ 2) ν1)
    (hm0 : (∫ x : ℝ, x ∂ν0) = 0) (hm1 : (∫ x : ℝ, x ∂ν1) = 0)
    (n k : ℕ) (hk : k ≤ n) :
    Integrable (CommonProduct.W n k) (CommonProduct.pairProduct ν0 ν1 n) ∧
    Integrable (fun ω => CommonProduct.W n k ω ^ 2) (CommonProduct.pairProduct ν0 ν1 n) ∧
    (∫ ω, CommonProduct.W n k ω ∂CommonProduct.pairProduct ν0 ν1 n) = 0 ∧
    (∫ ω, CommonProduct.W n k ω ^ 2 ∂CommonProduct.pairProduct ν0 ν1 n) =
      ((n - k : ℕ) : ℝ) * (∫ x : ℝ, x ^ 2 ∂ν0) + (k : ℝ) * ∫ x : ℝ, x ^ 2 ∂ν1 := by
  obtain ⟨ha1, ha2, ham, hav⟩ := convPower_moments ν1 h11 h12 hm1 k
  obtain ⟨hb1, hb2, hbm, hbv⟩ := convPower_moments ν0 h01 h02 hm0 (n - k)
  have hi1 := conv_integrable_first _ _ ha1 hb1
  have hi2 := conv_integrable_square _ _ ha1 ha2 hb1 hb2
  have hm := integral_conv_first _ _ ha1 hb1
  have hv := integral_conv_square _ _ ha1 ha2 hb1 hb2 ham hbm
  have hmap := CommonProduct.map_W ν0 ν1 n k hk
  have hW : AEMeasurable (CommonProduct.W n k) (CommonProduct.pairProduct ν0 ν1 n) :=
    (CommonProduct.measurable_W n k hk).aemeasurable
  rw [← hmap] at hi1 hi2 hm hv
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (integrable_map_measure measurable_id.aestronglyMeasurable hW).mp hi1
  · exact (integrable_map_measure (by fun_prop) hW).mp hi2
  · rw [integral_map (f := fun x : ℝ => x) hW measurable_id.aestronglyMeasurable,
      ham, hbm] at hm
    simpa using hm
  · rw [integral_map (f := fun x : ℝ => x ^ 2) hW (by fun_prop), hav, hbv] at hv
    linarith

theorem integral_W_sq_of_centered (ν0 ν1 : ProbabilityMeasure ℝ)
    (h0 : MomentBudget.CenteredResidualLaw ν0) (h1 : MomentBudget.CenteredResidualLaw ν1)
    (n k : ℕ) (hk : k ≤ n) :
    (∫ ω, CommonProduct.W n k ω
        ^ 2 ∂CommonProduct.pairProduct (ν0 : Measure ℝ) (ν1 : Measure ℝ) n) =
      ((n - k : ℕ) : ℝ) * MomentBudget.residualSecondMoment ν0 +
        (k : ℝ) * MomentBudget.residualSecondMoment ν1 :=
  (moments_W (ν0 : Measure ℝ) (ν1 : Measure ℝ)
    h0.integrable_first h0.integrable_second h1.integrable_first h1.integrable_second
    h0.mean_zero h1.mean_zero n k hk).2.2.2

/-- Allocation coordinates price the actual shared count variance. -/
theorem actual_allocation_count_variance (ν0 ν1 : ProbabilityMeasure ℝ)
    (h0 : MomentBudget.CenteredResidualLaw ν0) (h1 : MomentBudget.CenteredResidualLaw ν1)
    (p s α : ℝ) (hp : 0 < p) (hp1 : p < 1) (hs : 0 < s)
    (hsecond : s = (1 - p) * MomentBudget.residualSecondMoment ν0 +
      p * MomentBudget.residualSecondMoment ν1)
    (hα : α = p * MomentBudget.residualSecondMoment ν1 / s)
    (n k : ℕ) (hk : k ≤ n) :
    (∫ ω, CommonProduct.W n k ω
        ^ 2 ∂CommonProduct.pairProduct (ν0 : Measure ℝ) (ν1 : Measure ℝ) n) =
      s * (((n - k : ℕ) : ℝ) * (1 - α) / (1 - p) + (k : ℝ) * α / p) := by
  rw [integral_W_sq_of_centered ν0 ν1 h0 h1 n k hk]
  exact MomentBudget.allocation_count_variance p _ _ s α _ _ hp hp1 hs hsecond hα

end BerryEsseen.CommonProductMoments

#print axioms BerryEsseen.CommonProductMoments.integral_conv_square
#print axioms BerryEsseen.CommonProductMoments.convPower_moments
#print axioms BerryEsseen.CommonProductMoments.moments_W
#print axioms BerryEsseen.CommonProductMoments.integral_W_sq_of_centered
#print axioms BerryEsseen.CommonProductMoments.actual_allocation_count_variance
