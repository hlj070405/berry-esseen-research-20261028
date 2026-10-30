module

public import BerryEsseen.MomentBudgetNoise
public import Mathlib.Analysis.Calculus.Deriv.Slope

@[expose] public section

/-! 2026-10-29: an exact all-noise criterion for the original gDelta price.
The criterion concerns this moment-floor price. Its failure does not assert
that an original law's actual third absolute moment violates the Bernoulli floor.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace BerryEsseen.NoiseFloorCriterion

open MomentBudgetNoise

def k (p : ℝ) : ℝ := 1 - 2 * variance p
def u (p α : ℝ) : ℝ := p + α * ((1 - p) - p)
def L (p α : ℝ) : ℝ := (1 - α) / Real.sqrt (1 - p) + α / Real.sqrt p

def Gate (p δ α : ℝ) : Prop := δ ≤ 3 * u p α - 3 * k p / 2

/-- The square-root mixture retains the actual allocation weights. -/
theorem weighted_sqrt_square_lower {p α : ℝ} (hp : p ∈ Ioo 0 1) (hα : α ∈ Icc (0 : ℝ) 1) :
    (u p α) ^ 2 ≤ variance p * (L p α) ^ 2 := by
  have hq : 0 < 1 - p := sub_pos.mpr hp.2
  have hprod := mul_nonneg hp.1.le hq.le
  have hsp : p ≤ Real.sqrt p := Real.le_sqrt_of_sq_le (by nlinarith only [hprod])
  have hsq : 1 - p ≤ Real.sqrt (1 - p) := Real.le_sqrt_of_sq_le (by nlinarith only [hprod])
  let Z := (1 - α) * Real.sqrt p + α * Real.sqrt (1 - p)
  have hu0 : 0 ≤ u p α := by
    have h0 := mul_nonneg (sub_nonneg.mpr hα.2) hp.1.le
    have h1 := mul_nonneg hα.1 hq.le
    dsimp only [u]
    nlinarith only [h0, h1]
  have hmix : u p α ≤ Z := by
    have h0 := mul_le_mul_of_nonneg_left hsp (sub_nonneg.mpr hα.2)
    have h1 := mul_le_mul_of_nonneg_left hsq hα.1
    dsimp only [u, Z]
    linarith only [h0, h1]
  have hcancel : Real.sqrt p * Real.sqrt (1 - p) * L p α = Z := by
    dsimp only [L, Z]
    field_simp [(Real.sqrt_pos.mpr hp.1).ne', (Real.sqrt_pos.mpr hq).ne'] <;> ring
  calc
    (u p α) ^ 2 ≤ Z ^ 2 := (sq_le_sq₀ hu0 (hu0.trans hmix)).mpr hmix
    _ = (Real.sqrt p * Real.sqrt (1 - p) * L p α) ^ 2 := by rw [hcancel]
    _ = variance p * (L p α) ^ 2 := by
      simp only [mul_pow, Real.sq_sqrt hp.1.le, Real.sq_sqrt hq.le]
      rfl

/-- The linear coefficient of the noise derivative is automatically nonnegative.
This needs no critical gate and no restriction to a small probability strip. -/
theorem automatic_linear_gate {p δ α : ℝ} (hp : p ∈ Ioo 0 1)
    (hα : α ∈ Icc (0 : ℝ) 1) (hδ : 0 < δ) :
    B p δ α ≤ 4 * C p δ α * variance p := by
  have hL := weighted_sqrt_square_lower hp hα
  have hpoly : 0 ≤ 4 * (u p α) ^ 2 - 3 * u p α * δ + δ ^ 2 := by
    nlinarith only [sq_nonneg (δ - 3 * u p α / 2), sq_nonneg (u p α)]
  have hraw : (3 * u p α - δ) * δ ≤ 4 * (L p α) ^ 2 * variance p := by
    nlinarith only [hL, hpoly]
  have hdiv := (le_div_iff₀ hδ).mpr hraw
  change 3 * u p α - δ ≤ 4 * ((L p α) ^ 2 / δ) * variance p
  convert hdiv using 1 <;> ring

lemma constant_gate {p δ α : ℝ} (hp : p ∈ Ioo 0 1) (hg : Gate p δ α) :
    3 * A p ≤ 2 * variance p * B p δ α := by
  have hv := P39Reference.v_pos hp.1 hp.2
  have hm := mul_le_mul_of_nonneg_left hg (show 0 ≤ 2 * variance p by positivity)
  change 3 * (variance p * k p) ≤ 2 * variance p * (3 * u p α - δ)
  nlinarith only [hm]

theorem firstNoise_nonneg_of_gate {p s δ α : ℝ} (hp : p ∈ Ioo 0 1)
    (hα : α ∈ Icc (0 : ℝ) 1) (hs : 0 ≤ s) (hδ : 0 < δ) (hg : Gate p δ α) :
    0 ≤ firstNoise p δ α s := by
  have hconstant : 0 ≤ B p δ α * variance p - 3 * A p / 2 := by
    linarith only [constant_gate hp hg]
  have hlinear : 0 ≤ 2 * C p δ α * variance p - B p δ α / 2 := by
    linarith only [automatic_linear_gate hp hα hδ]
  have hC : 0 ≤ C p δ α := div_nonneg (sq_nonneg _) hδ.le
  unfold firstNoise first
  exact div_nonneg (by positivity) (by positivity)

theorem monotoneOn_noise_of_gate {p δ α : ℝ} (hp : p ∈ Ioo 0 1)
    (hα : α ∈ Icc (0 : ℝ) 1) (hδ : 0 < δ) (hg : Gate p δ α) :
    MonotoneOn (fun s => MomentBudget.gDelta p s δ α) (Ici 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
  · exact (MomentBudgetNoise.contDiffOn_gDelta hp.1 hp.2 hδ).continuousOn
  · intro s hs
    exact (MomentBudgetNoise.hasDerivAt_gDelta hp.1 hp.2 (interior_subset hs) hδ).differentiableAt.differentiableWithinAt
  · intro s hs
    rw [(MomentBudgetNoise.hasDerivAt_gDelta hp.1 hp.2 (interior_subset hs) hδ).deriv]
    exact firstNoise_nonneg_of_gate hp hα (interior_subset hs) hδ hg

lemma zero_noise_eq_rho0 {p δ α : ℝ} (hp : p ∈ Ioo 0 1) :
    MomentBudget.gDelta p 0 δ α = P39Reference.rho0 p := by
  have hv := P39Reference.v_pos hp.1 hp.2
  rw [MomentBudgetNoise.gDelta_eq_value]
  simp only [value, mul_zero, zero_pow (by decide : 2 ≠ 0), zero_div, add_zero]
  change variance p * k p / (Real.sqrt (variance p)) ^ 3 = k p / Real.sqrt (variance p)
  rw [pow_succ, Real.sq_sqrt hv.le]
  field_simp [hv.ne', (Real.sqrt_pos.mpr hv).ne']

theorem gDelta_ge_rho0_of_gate {p s δ α : ℝ} (hp : p ∈ Ioo 0 1)
    (hα : α ∈ Icc (0 : ℝ) 1) (hs : 0 ≤ s) (hδ : 0 < δ) (hg : Gate p δ α) :
    P39Reference.rho0 p ≤ MomentBudget.gDelta p s δ α := by
  rw [← zero_noise_eq_rho0 (δ := δ) (α := α) hp]
  exact monotoneOn_noise_of_gate hp hα hδ hg (show (0 : ℝ) ∈ Ici 0 from le_rfl) hs hs

/-- Necessity uses the genuine right derivative at zero noise. -/
theorem gate_of_all_noise_floor {p δ α : ℝ} (hp : p ∈ Ioo 0 1) (hδ : 0 < δ)
    (hfloor : ∀ s : ℝ, 0 ≤ s → P39Reference.rho0 p ≤ MomentBudget.gDelta p s δ α) :
    Gate p δ α := by
  have hd := MomentBudgetNoise.hasDerivAt_gDelta (p := p) (δ := δ) (α := α) (s := 0)
    hp.1 hp.2 le_rfl hδ
  have hfilter : (𝓝[>] (0 : ℝ)) ≤ (𝓝[≠] (0 : ℝ)) := by
    apply nhdsWithin_mono
    intro s hs
    change s ≠ 0
    exact ne_of_gt hs
  have hlim := (hasDerivAt_iff_tendsto_slope.mp hd).mono_left hfilter
  have hnonneg : 0 ≤ firstNoise p δ α 0 := by
    apply ge_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin] with s hs
    change 0 < s at hs
    rw [slope_def_field]
    simp only [sub_zero]
    have hf := hfloor s hs.le
    rw [← zero_noise_eq_rho0 (δ := δ) (α := α) hp] at hf
    exact div_nonneg (sub_nonneg.mpr hf) hs.le
  have hv := P39Reference.v_pos hp.1 hp.2
  have hden : 0 < (variance p) ^ 2 * Real.sqrt (variance p) :=
    mul_pos (sq_pos_of_pos hv) (Real.sqrt_pos.mpr hv)
  simp only [firstNoise, first, mul_zero, zero_pow (by decide : 2 ≠ 0), zero_div, add_zero] at hnonneg
  have hnum := mul_nonneg hnonneg hden.le
  rw [div_mul_cancel₀ _ hden.ne'] at hnum
  have hmul : (3 * k p / 2) * variance p ≤ (3 * u p α - δ) * variance p := by
    change 0 ≤ (3 * u p α - δ) * variance p - 3 * (variance p * k p) / 2 at hnum
    nlinarith only [hnum]
  have hmul' : variance p * (3 * k p / 2) ≤ variance p * (3 * u p α - δ) := by
    nlinarith only [hmul]
  have h := (mul_le_mul_iff_right₀ hv).mp hmul'
  change δ ≤ 3 * u p α - 3 * k p / 2
  linarith only [h]

theorem gate_iff_all_noise_floor {p δ α : ℝ} (hp : p ∈ Ioo 0 1)
    (hα : α ∈ Icc (0 : ℝ) 1) (hδ : 0 < δ) :
    Gate p δ α ↔ ∀ s : ℝ, 0 ≤ s → P39Reference.rho0 p ≤ MomentBudget.gDelta p s δ α :=
  ⟨fun hg s hs => gDelta_ge_rho0_of_gate hp hα hs hδ hg, gate_of_all_noise_floor hp hδ⟩

theorem gate_iff_monotone_noise {p δ α : ℝ} (hp : p ∈ Ioo 0 1)
    (hα : α ∈ Icc (0 : ℝ) 1) (hδ : 0 < δ) :
    Gate p δ α ↔ MonotoneOn (fun s => MomentBudget.gDelta p s δ α) (Ici 0) := by
  refine ⟨monotoneOn_noise_of_gate hp hα hδ, ?_⟩
  intro hm
  apply gate_of_all_noise_floor hp hδ
  intro s hs
  rw [← zero_noise_eq_rho0 (δ := δ) (α := α) hp]
  exact hm (show (0 : ℝ) ∈ Ici 0 from le_rfl) hs hs

theorem monotone_noise_iff_all_noise_floor {p δ α : ℝ} (hp : p ∈ Ioo 0 1)
    (hα : α ∈ Icc (0 : ℝ) 1) (hδ : 0 < δ) :
    MonotoneOn (fun s => MomentBudget.gDelta p s δ α) (Ici 0) ↔
      ∀ s : ℝ, 0 ≤ s → P39Reference.rho0 p ≤ MomentBudget.gDelta p s δ α :=
  (gate_iff_monotone_noise hp hα hδ).symm.trans (gate_iff_all_noise_floor hp hα hδ)
/-- The cap 1/6 is uniform over the whole allocation interval. -/
theorem gate_of_one_sixth {p δ α : ℝ} (hp : p ∈ Icc (1 / 3 : ℝ) (1 / 2))
    (hα : α ∈ Icc (0 : ℝ) 1) (hδhi : δ ≤ 1 / 6) : Gate p δ α := by
  have hmix := mul_nonneg hα.1 (show 0 ≤ (1 - p) - p by linarith only [hp.2])
  have hpoly := mul_nonneg (sub_nonneg.mpr hp.1) (show 0 ≤ 5 - 3 * p by linarith only [hp.2])
  dsimp only [Gate, u, k, variance, P39Reference.v]
  nlinarith only [hmix, hpoly, hδhi]

theorem gDelta_ge_rho0_one_sixth {p s δ α : ℝ}
    (hp : p ∈ Icc (1 / 3 : ℝ) (1 / 2)) (hα : α ∈ Icc (0 : ℝ) 1)
    (hs : 0 ≤ s) (hδ : 0 < δ) (hδhi : δ ≤ 1 / 6) :
    P39Reference.rho0 p ≤ MomentBudget.gDelta p s δ α :=
  gDelta_ge_rho0_of_gate ⟨by linarith only [hp.1], by linarith only [hp.2]⟩
    hα hs hδ (gate_of_one_sixth hp hα hδhi)

theorem boundary_gate (δ : ℝ) : Gate (1 / 3) δ 0 ↔ δ ≤ 1 / 6 := by
  norm_num [Gate, u, k, variance, P39Reference.v]

/-- Same original law and actual allocation; all support and cap assumptions remain. -/
theorem canonical_thirdMoment_floor_of_gate
    (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ) (a0 a1 δ : ℝ)
    (ha0 : 0 ≤ a0) (ha1 : 0 ≤ a1) (hδ : 0 < δ) (hcap : a0 + a1 ≤ δ)
    (hg : Gate (CanonicalSign.p μ) δ (ConditionalResidual.actualAllocation μ hμ))
    (hupper0 : ∀ᵐ z ∂(CanonicalSign.residual0 μ hμ : Measure ℝ), z ≤ a0)
    (hlower1 : ∀ᵐ z ∂(CanonicalSign.residual1 μ hμ : Measure ℝ), -a1 ≤ z) :
    P39Reference.rho0 (CanonicalSign.p μ) ≤ thirdAbsoluteMoment μ := by
  exact (gDelta_ge_rho0_of_gate
    ⟨CanonicalSign.p_pos μ hμ, CanonicalSign.p_lt_one μ hμ⟩
    (BernoulliMomentFloor.canonical_allocation_mem_Icc μ hμ)
    (CanonicalSign.noiseVariance_nonneg μ hμ) hδ hg).trans
    (ConditionalResidual.canonical_actual_allocation_floor μ hμ a0 a1 δ
      ha0 ha1 hδ hcap hupper0 hlower1)

theorem canonical_thirdMoment_floor_one_sixth
    (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ) (a0 a1 δ : ℝ)
    (hp : CanonicalSign.p μ ∈ Icc (1 / 3 : ℝ) (1 / 2))
    (ha0 : 0 ≤ a0) (ha1 : 0 ≤ a1) (hδ : 0 < δ) (hδhi : δ ≤ 1 / 6)
    (hcap : a0 + a1 ≤ δ)
    (hupper0 : ∀ᵐ z ∂(CanonicalSign.residual0 μ hμ : Measure ℝ), z ≤ a0)
    (hlower1 : ∀ᵐ z ∂(CanonicalSign.residual1 μ hμ : Measure ℝ), -a1 ≤ z) :
    P39Reference.rho0 (CanonicalSign.p μ) ≤ thirdAbsoluteMoment μ :=
  canonical_thirdMoment_floor_of_gate μ hμ a0 a1 δ ha0 ha1 hδ hcap
    (gate_of_one_sixth hp (BernoulliMomentFloor.canonical_allocation_mem_Icc μ hμ) hδhi)
    hupper0 hlower1

end BerryEsseen.NoiseFloorCriterion

#print axioms BerryEsseen.NoiseFloorCriterion.weighted_sqrt_square_lower
#print axioms BerryEsseen.NoiseFloorCriterion.automatic_linear_gate
#print axioms BerryEsseen.NoiseFloorCriterion.gate_iff_all_noise_floor
#print axioms BerryEsseen.NoiseFloorCriterion.gate_iff_monotone_noise
#print axioms BerryEsseen.NoiseFloorCriterion.gDelta_ge_rho0_one_sixth
#print axioms BerryEsseen.NoiseFloorCriterion.canonical_thirdMoment_floor_one_sixth
#print axioms BerryEsseen.NoiseFloorCriterion.monotone_noise_iff_all_noise_floor


