module

public import BerryEsseen.Target
public import BerryEsseen.CommonProduct
public import BerryEsseen.CanonicalSign

@[expose] public section

/-! 2026-10-28: affine changes of coordinates for the actual product sum.
The closed-CDF identity retains threshold atoms and uses a positive scale.
-/

noncomputable section

open MeasureTheory

namespace BerryEsseen.AffineSum

open scoped NNReal ENNReal

theorem normalizedIidSumLaw_eq_map (μ : ProbabilityMeasure ℝ) (ν : Measure ℝ)
    [IsFiniteMeasure ν] (p c : ℝ)
    (hμ : (μ : Measure ℝ) = ν.map (fun u : ℝ => (u - p) / c)) (n : ℕ) :
    normalizedIidSumLaw μ n =
      (MixtureSum.iidSumLaw ν n).map
        (fun u : ℝ => (u - (n : ℝ) * p) / (c * Real.sqrt n)) := by
  have hf : Measurable (fun u : ℝ => (u - p) / c) := by fun_prop
  have hcoord : Measurable (fun z : Fin n → ℝ => fun i => (z i - p) / c) := by
    apply measurable_pi_iff.mpr
    intro i
    fun_prop
  have hpi := Measure.pi_map_pi (μ := fun _ : Fin n => ν)
    (f := fun _ => fun u : ℝ => (u - p) / c) (fun _ => hf.aemeasurable)
  have hfun : (normalizedIidSum n) ∘
      (fun z : Fin n → ℝ => fun i => (z i - p) / c) =
      (fun u : ℝ => (u - (n : ℝ) * p) / (c * Real.sqrt n)) ∘
        (fun z : Fin n → ℝ => ∑ i, z i) := by
    funext z
    change (∑ i, (z i - p) / c) / Real.sqrt n = _
    rw [← Finset.sum_div, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, div_div, Function.comp_apply]
  unfold normalizedIidSumLaw MixtureSum.iidSumLaw
  rw [hμ, ← hpi, Measure.map_map (measurable_normalizedIidSum n) hcoord, hfun,
    ← Measure.map_map (by fun_prop) (by fun_prop)]

theorem normalizedIidSumLaw_closedCDF (μ : ProbabilityMeasure ℝ) (ν : Measure ℝ)
    [IsFiniteMeasure ν] (p c : ℝ) (hc : 0 < c)
    (hμ : (μ : Measure ℝ) = ν.map (fun u : ℝ => (u - p) / c))
    (n : ℕ) (hn : 0 < n) (x : ℝ) :
    (normalizedIidSumLaw μ n).real (Set.Iic x) =
      (MixtureSum.iidSumLaw ν n).real
        (Set.Iic ((n : ℝ) * p + c * Real.sqrt n * x)) := by
  have hs : 0 < c * Real.sqrt (n : ℝ) :=
    mul_pos hc (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn))
  rw [normalizedIidSumLaw_eq_map μ ν p c hμ n]
  unfold Measure.real
  rw [Measure.map_apply (by fun_prop) measurableSet_Iic]
  have hevent : (fun u : ℝ => (u - (n : ℝ) * p) / (c * Real.sqrt n)) ⁻¹'
      Set.Iic x = Set.Iic ((n : ℝ) * p + c * Real.sqrt n * x) := by
    ext u
    simp only [Set.mem_preimage, Set.mem_Iic]
    rw [div_le_iff₀ hs]
    constructor <;> intro h <;> nlinarith
  rw [hevent]

/-- The Bernoulli-coordinate mixture, before centering and rescaling. -/
def residualSumMeasure (ν0 ν1 : ProbabilityMeasure ℝ) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : Measure ℝ :=
  (NNReal.mk (1 - p) (sub_nonneg.mpr hp1) • (ν0 : Measure ℝ) : Measure ℝ) +
    (NNReal.mk p hp0 • (ν1 : Measure ℝ).map (1 + ·) : Measure ℝ)

instance residualSumMeasure_isFinite (ν0 ν1 : ProbabilityMeasure ℝ) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsFiniteMeasure (residualSumMeasure ν0 ν1 p hp0 hp1) := by
  unfold residualSumMeasure
  infer_instance

theorem residualMixtureLaw_eq_map (ν0 ν1 : ProbabilityMeasure ℝ) (p c : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (MomentBudget.residualMixtureLaw ν0 ν1 p c hp0 hp1 : Measure ℝ) =
      (residualSumMeasure ν0 ν1 p hp0 hp1).map (fun u : ℝ => (u - p) / c) := by
  have hf : Measurable (fun u : ℝ => (u - p) / c) := by fun_prop
  have hg : Measurable (fun u : ℝ => 1 + u) := by fun_prop
  rw [residualSumMeasure, Measure.map_add _ _ hf,
    Measure.map_smul _ hf.aemeasurable,
    Measure.map_smul _ hf.aemeasurable, Measure.map_map hf hg]
  rw [MomentBudget.coe_residualMixtureLaw, MomentBudget.residualMixtureMeasure,
    ENNReal.ofReal_eq_coe_nnreal (sub_nonneg.mpr hp1),
    ENNReal.ofReal_eq_coe_nnreal hp0]
  have hcomp : (fun u : ℝ => (u - p) / c) ∘ (fun u : ℝ => 1 + u) =
      (fun u : ℝ => (u + (1 - p)) / c) := by
    funext u
    dsimp
    congr 1
    ring
  rw [hcomp]
  rfl

/-- Actual normalized i.i.d. sums have the coupled residual closed CDF. -/
theorem residualMixture_normalized_closedCDF (ν0 ν1 : ProbabilityMeasure ℝ)
    (p c : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hc : 0 < c)
    (n : ℕ) (hn : 0 < n) (x : ℝ) :
    (normalizedIidSumLaw (MomentBudget.residualMixtureLaw ν0 ν1 p c hp0 hp1) n).real
        (Set.Iic x) =
      Staircase.closedMixtureCDF (CommonProduct.pairProduct (ν0 : Measure ℝ)
        (ν1 : Measure ℝ) n)
        (fun j => (n.choose j : ℝ) * p ^ j * (1 - p) ^ (n - j))
        (CommonProduct.W n) n ((n : ℝ) * p + c * Real.sqrt n * x) := by
  rw [normalizedIidSumLaw_closedCDF _ _ p c hc
    (residualMixtureLaw_eq_map ν0 ν1 p c hp0 hp1) n hn x]
  simpa only [residualSumMeasure, NNReal.coe_mk] using
    CommonProduct.iidSumLaw_eq_staircaseCDF (ν0 : Measure ℝ) (ν1 : Measure ℝ)
      (NNReal.mk (1 - p) (sub_nonneg.mpr hp1)) (NNReal.mk p hp0) n
      ((n : ℝ) * p + c * Real.sqrt n * x)

/-- The same identity for every original target law, using its actual
sign-conditional residuals. No residual representation is assumed. -/
theorem canonical_normalized_closedCDF (μ : ProbabilityMeasure ℝ)
    (h : StandardizedLaw μ) (n : ℕ) (hn : 0 < n) (x : ℝ) :
    (normalizedIidSumLaw μ n).real (Set.Iic x) =
      Staircase.closedMixtureCDF
        (CommonProduct.pairProduct (CanonicalSign.residual0 μ h : Measure ℝ)
          (CanonicalSign.residual1 μ h : Measure ℝ) n)
        (fun j => (n.choose j : ℝ) * CanonicalSign.p μ ^ j *
          CanonicalSign.q μ ^ (n - j))
        (CommonProduct.W n) n ((n : ℝ) * CanonicalSign.p μ +
          CanonicalSign.scale μ h * Real.sqrt n * x) := by
  have ht := residualMixture_normalized_closedCDF
    (CanonicalSign.residual0 μ h) (CanonicalSign.residual1 μ h)
    (CanonicalSign.p μ) (CanonicalSign.scale μ h)
    (le_of_lt (CanonicalSign.p_pos μ h)) (le_of_lt (CanonicalSign.p_lt_one μ h))
    (CanonicalSign.scale_pos μ h) n hn x
  rw [← CanonicalSign.law_eq_residualMixture μ h] at ht
  exact ht

end BerryEsseen.AffineSum

#print axioms BerryEsseen.AffineSum.normalizedIidSumLaw_eq_map
#print axioms BerryEsseen.AffineSum.normalizedIidSumLaw_closedCDF
#print axioms BerryEsseen.AffineSum.residualMixtureLaw_eq_map
#print axioms BerryEsseen.AffineSum.residualMixture_normalized_closedCDF
#print axioms BerryEsseen.AffineSum.canonical_normalized_closedCDF
