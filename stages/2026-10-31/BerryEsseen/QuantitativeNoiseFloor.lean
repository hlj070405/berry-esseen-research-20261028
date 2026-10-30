module

public import BerryEsseen.NoiseFloorCriterion

@[expose] public section

/-! 2026-10-29: Analytic quantitative derivative prices for the actual
gDelta function. The variance-plus-noise gate is an explicit hypothesis;
this module does not acquire that gate from a probability estimate. -/

noncomputable section

namespace BerryEsseen.QuantitativeNoiseFloor

open MeasureTheory MomentBudgetNoise

private theorem variance_lower {p : ℝ}
    (hp : p ∈ Set.Icc (39 / 100 : ℝ) (1 / 2)) : (7 / 30 : ℝ) ≤ variance p := by
  have hprod := mul_nonneg (sub_nonneg.mpr hp.1)
    (show 0 ≤ 61 / 100 - p by linarith [hp.2])
  dsimp only [variance, P39Reference.v]
  nlinarith only [hprod]

private theorem denominator_prices {R : ℝ} (hR : 0 < R) (hRhi : R ≤ 1 / 4) :
    0 < R ^ 2 * Real.sqrt R ∧ R ^ 2 * Real.sqrt R ≤ 1 / 32 := by
  have hsq : R ^ 2 ≤ (1 / 16 : ℝ) := by
    have h := pow_le_pow_left₀ hR.le hRhi 2
    norm_num at h
    exact h
  have hroot : Real.sqrt R ≤ (1 / 2 : ℝ) := by
    calc
      _ ≤ Real.sqrt (1 / 4 : ℝ) := Real.sqrt_le_sqrt hRhi
      _ = _ := by
        rw [show (1 / 4 : ℝ) = (1 / 2 : ℝ) ^ 2 by norm_num,
          Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  refine ⟨mul_pos (sq_pos_of_pos hR) (Real.sqrt_pos.mpr hR), ?_⟩
  calc
    _ ≤ (1 / 16 : ℝ) * (1 / 2) :=
      mul_le_mul hsq hroot (Real.sqrt_nonneg R) (by norm_num)
    _ = _ := by norm_num

theorem firstNoise_ge_56_25 {p s δ α : ℝ}
    (hp : p ∈ Set.Icc (39 / 100 : ℝ) (1 / 2))
    (hα : α ∈ Set.Icc (0 : ℝ) 1) (hδ : 0 < δ) (hδhi : δ ≤ 7 / 100)
    (hs : 0 ≤ s) (hRhi : variance p + s ≤ 1 / 4) :
    (56 / 25 : ℝ) ≤ firstNoise p δ α s := by
  have hp' : p ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [hp.1], by linarith [hp.2]⟩
  have hv := P39Reference.v_pos hp'.1 hp'.2
  have hvlo := variance_lower hp
  have hk : NoiseFloorCriterion.k p ≤ (8 / 15 : ℝ) := by
    unfold NoiseFloorCriterion.k
    linarith only [hvlo]
  have hαterm := mul_nonneg hα.1 (show 0 ≤ (1 - p) - p by linarith [hp.2])
  have hB : (11 / 10 : ℝ) ≤ B p δ α := by
    unfold B
    linarith [hp.1]
  have hgap : (3 / 10 : ℝ) ≤ B p δ α - 3 * NoiseFloorCriterion.k p / 2 := by
    linarith only [hB, hk]
  have hconstant : (7 / 100 : ℝ) ≤ B p δ α * variance p - 3 * A p / 2 := by
    calc
      _ = (7 / 30 : ℝ) * (3 / 10) := by norm_num
      _ ≤ variance p * (B p δ α - 3 * NoiseFloorCriterion.k p / 2) :=
        mul_le_mul hvlo hgap (by norm_num) hv.le
      _ = _ := by unfold A NoiseFloorCriterion.k; ring
  have hgate := NoiseFloorCriterion.automatic_linear_gate hp' hα hδ
  have hlinear : 0 ≤ 2 * C p δ α * variance p - B p δ α / 2 := by
    linarith only [hgate]
  have hC : 0 ≤ C p δ α := div_nonneg (sq_nonneg _) hδ.le
  have hnoise1 := mul_nonneg hlinear hs
  have hnoise2 := div_nonneg (mul_nonneg hC (sq_nonneg s)) (by norm_num : (0 : ℝ) ≤ 2)
  have hnum : (7 / 100 : ℝ) ≤ B p δ α * variance p - 3 * A p / 2 +
      (2 * C p δ α * variance p - B p δ α / 2) * s + C p δ α * s ^ 2 / 2 := by
    linarith only [hconstant, hnoise1, hnoise2]
  have hR : 0 < variance p + s := add_pos_of_pos_of_nonneg hv hs
  obtain ⟨hDpos, hDhi⟩ := denominator_prices hR hRhi
  unfold firstNoise first
  apply (le_div_iff₀ hDpos).mpr
  calc
    _ ≤ (56 / 25 : ℝ) * (1 / 32) := mul_le_mul_of_nonneg_left hDhi (by norm_num)
    _ = (7 / 100 : ℝ) := by norm_num
    _ ≤ _ := hnum

theorem firstNoise_ge_two {p s δ α : ℝ}
    (hp : p ∈ Set.Icc (39 / 100 : ℝ) (1 / 2))
    (hα : α ∈ Set.Icc (0 : ℝ) 1) (hδ : 0 < δ) (hδhi : δ ≤ 7 / 100)
    (hs : 0 ≤ s) (hRhi : variance p + s ≤ 1 / 4) :
    (2 : ℝ) ≤ firstNoise p δ α s :=
  (by norm_num : (2 : ℝ) ≤ 56 / 25).trans (firstNoise_ge_56_25 hp hα hδ hδhi hs hRhi)

/-- Both the actual derivative and its quantitative price are supplied. -/
theorem hasDerivAt_with_lower_bound {p s δ α : ℝ}
    (hp : p ∈ Set.Icc (39 / 100 : ℝ) (1 / 2))
    (hα : α ∈ Set.Icc (0 : ℝ) 1) (hδ : 0 < δ) (hδhi : δ ≤ 7 / 100)
    (hs : 0 ≤ s) (hRhi : variance p + s ≤ 1 / 4) :
    HasDerivAt (fun t => MomentBudget.gDelta p t δ α) (firstNoise p δ α s) s ∧
      (56 / 25 : ℝ) ≤ firstNoise p δ α s := by
  have hp0 : 0 < p := by linarith [hp.1]
  have hp1 : p < 1 := by linarith [hp.2]
  exact ⟨MomentBudgetNoise.hasDerivAt_gDelta hp0 hp1 hs hδ,
    firstNoise_ge_56_25 hp hα hδ hδhi hs hRhi⟩

theorem deriv_gDelta_ge_56_25 {p s δ α : ℝ}
    (hp : p ∈ Set.Icc (39 / 100 : ℝ) (1 / 2))
    (hα : α ∈ Set.Icc (0 : ℝ) 1) (hδ : 0 < δ) (hδhi : δ ≤ 7 / 100)
    (hs : 0 ≤ s) (hRhi : variance p + s ≤ 1 / 4) :
    (56 / 25 : ℝ) ≤ deriv (fun t => MomentBudget.gDelta p t δ α) s := by
  obtain ⟨hd, hbound⟩ := hasDerivAt_with_lower_bound hp hα hδ hδhi hs hRhi
  rw [hd.deriv]
  exact hbound

/-- The same original law's actual allocation and noise satisfy the price
once the displayed variance gate has been acquired separately. -/
theorem canonical_firstNoise_ge_56_25 (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (δ : ℝ) (hp : CanonicalSign.p μ ∈ Set.Icc (39 / 100 : ℝ) (1 / 2))
    (hδ : 0 < δ) (hδhi : δ ≤ 7 / 100)
    (hRhi : variance (CanonicalSign.p μ) + CanonicalSign.noiseVariance μ hμ ≤ 1 / 4) :
    (56 / 25 : ℝ) ≤ firstNoise (CanonicalSign.p μ) δ
      (ConditionalResidual.actualAllocation μ hμ) (CanonicalSign.noiseVariance μ hμ) :=
  firstNoise_ge_56_25 hp (BernoulliMomentFloor.canonical_allocation_mem_Icc μ hμ)
    hδ hδhi (CanonicalSign.noiseVariance_nonneg μ hμ) hRhi

theorem canonical_deriv_gDelta_ge_56_25 (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (δ : ℝ) (hp : CanonicalSign.p μ ∈ Set.Icc (39 / 100 : ℝ) (1 / 2))
    (hδ : 0 < δ) (hδhi : δ ≤ 7 / 100)
    (hRhi : variance (CanonicalSign.p μ) + CanonicalSign.noiseVariance μ hμ ≤ 1 / 4) :
    (56 / 25 : ℝ) ≤ deriv (fun s => MomentBudget.gDelta (CanonicalSign.p μ) s δ
      (ConditionalResidual.actualAllocation μ hμ)) (CanonicalSign.noiseVariance μ hμ) :=
  deriv_gDelta_ge_56_25 hp (BernoulliMomentFloor.canonical_allocation_mem_Icc μ hμ)
    hδ hδhi (CanonicalSign.noiseVariance_nonneg μ hμ) hRhi

end BerryEsseen.QuantitativeNoiseFloor

#print axioms BerryEsseen.QuantitativeNoiseFloor.firstNoise_ge_56_25
#print axioms BerryEsseen.QuantitativeNoiseFloor.firstNoise_ge_two
#print axioms BerryEsseen.QuantitativeNoiseFloor.hasDerivAt_with_lower_bound
#print axioms BerryEsseen.QuantitativeNoiseFloor.deriv_gDelta_ge_56_25
#print axioms BerryEsseen.QuantitativeNoiseFloor.canonical_firstNoise_ge_56_25
#print axioms BerryEsseen.QuantitativeNoiseFloor.canonical_deriv_gDelta_ge_56_25
