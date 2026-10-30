module

public import BerryEsseen.QuantitativeNoiseFloor
public import BerryEsseen.GaussianPrices
public import BerryEsseen.AnalyticConstants

@[expose] public section

/-! 2026-10-29: an analytic noise gate on the original P39 probability strip.
The reference price is held fixed on this slice. This does not assert
monotonicity of a reference price whose law also varies with the noise. -/

noncomputable section
open Set MeasureTheory
open scoped Topology

namespace BerryEsseen.P39NoiseGate

open GaussianTools MomentBudgetNoise

def noiseArgument (p r l : ℝ) : ℝ := (r - 26 * p) / Real.sqrt (26 * variance p + l)

def gaussianSlope (p r l : ℝ) : ℝ :=
  phi (noiseArgument p r l) * (r - 26 * p) /
    (2 * (26 * variance p + l) * Real.sqrt (26 * variance p + l))

def price (p r c δ α l : ℝ) : ℝ :=
  -Phi (noiseArgument p r l) - c * MomentBudget.gDelta p (l / 26) δ α

def priceSlope (p r c δ α l : ℝ) : ℝ :=
  gaussianSlope p r l - c * firstNoise p δ α (l / 26) / 26

lemma variance_bounds {p : ℝ} (hp : p ∈ Icc (39 / 100 : ℝ) (2 / 5)) :
    7 / 30 ≤ variance p ∧ variance p ≤ 6 / 25 := by
  have hlow := mul_nonneg (sub_nonneg.mpr hp.1)
    (show 0 ≤ 61 / 100 - p by linarith only [hp.2])
  have hhigh := mul_nonneg (sub_nonneg.mpr hp.2)
    (show 0 ≤ 3 / 5 - p by linarith only [hp.2])
  dsimp only [variance, P39Reference.v]
  constructor <;> nlinarith only [hlow, hhigh]

lemma actual_variance_pos {p l : ℝ}
    (hp : p ∈ Icc (39 / 100 : ℝ) (2 / 5)) (hl : 0 ≤ l) :
    0 < 26 * variance p + l := by linarith only [(variance_bounds hp).1, hl]

lemma hasDerivAt_noiseArgument {p r l : ℝ}
    (hV : 0 < 26 * variance p + l) :
    HasDerivAt (noiseArgument p r)
      (-(r - 26 * p) /
        (2 * (26 * variance p + l) * Real.sqrt (26 * variance p + l))) l := by
  have hlin : HasDerivAt (fun z : ℝ => 26 * variance p + z) 1 l := by
    simpa using (hasDerivAt_id l).const_add (26 * variance p)
  have hr := (Real.sqrt_pos.mpr hV).ne'
  have hd := (hasDerivAt_const l (r - 26 * p)).div (hlin.sqrt hV.ne') hr
  convert hd using 1
  · funext z
    rfl
  · have hs := Real.sq_sqrt hV.le
    field_simp [hr, hV.ne']
    rw [hs]
    ring

theorem hasDerivAt_price {p r c δ α l : ℝ}
    (hp : p ∈ Icc (39 / 100 : ℝ) (2 / 5)) (hl : 0 ≤ l) (hδ : 0 < δ) :
    HasDerivAt (price p r c δ α) (priceSlope p r c δ α l) l := by
  have hV := actual_variance_pos hp hl
  have hG := ((hasDerivAt_Phi (noiseArgument p r l)).comp l
    (hasDerivAt_noiseArgument hV)).neg
  have hg := (MomentBudgetNoise.hasDerivAt_gDelta (p := p) (s := l / 26)
    (δ := δ) (α := α) (by linarith only [hp.1]) (by linarith only [hp.2])
    (by positivity) hδ).comp l ((hasDerivAt_id l).div_const 26)
  convert hG.sub (hg.const_mul c) using 1
  · funext z
    rfl
  · dsimp only [priceSlope, gaussianSlope]
    ring

lemma gaussian_noise_slope_le {p r l : ℝ}
    (hp : p ∈ Icc (39 / 100 : ℝ) (2 / 5)) (hl : 0 ≤ l)
    (hr : r ≤ 21 / 2) : gaussianSlope p r l ≤ 1 / 200 := by
  let V := 26 * variance p + l
  have hV : 6 ≤ V := by dsimp only [V]; linarith only [(variance_bounds hp).1, hl]
  have hVpos : 0 < V := by linarith only [hV]
  have hs : 12 / 5 ≤ Real.sqrt V := by
    apply Real.le_sqrt_of_sq_le
    norm_num at *
    linarith only [hV]
  have hphi : phi (noiseArgument p r l) ≤ 2 / 5 := by
    calc
      _ ≤ phi 0 := by
        rw [GaussianPrices.phi_eq_phi_zero_mul_exp]
        have he : Real.exp (-(noiseArgument p r l ^ 2 / 2)) ≤ 1 :=
          Real.exp_le_one_iff.mpr (by nlinarith only [sq_nonneg (noiseArgument p r l)])
        simpa only [mul_one] using mul_le_mul_of_nonneg_left he (phi_nonneg 0)
      _ ≤ 2 / 5 := GaussianPrices.phi_zero_lt_2_5.le
  have hn : r - 26 * p ≤ 9 / 25 := by linarith only [hr, hp.1]
  have hnum : phi (noiseArgument p r l) * (r - 26 * p) ≤ 18 / 125 := by
    calc
      _ ≤ phi (noiseArgument p r l) * (9 / 25) :=
        mul_le_mul_of_nonneg_left hn (phi_nonneg _)
      _ ≤ (2 / 5) * (9 / 25) := mul_le_mul_of_nonneg_right hphi (by norm_num)
      _ = _ := by norm_num
  have hden : 144 / 5 ≤ 2 * V * Real.sqrt V := by
    have hh := mul_le_mul hV hs (by norm_num : (0 : ℝ) ≤ 12 / 5) hVpos.le
    nlinarith only [hh]
  change phi (noiseArgument p r l) * (r - 26 * p) /
    (2 * V * Real.sqrt V) ≤ 1 / 200
  apply (div_le_iff₀ (by positivity : 0 < 2 * V * Real.sqrt V)).mpr
  nlinarith only [hnum, hden]

lemma scaledNoise_mem {p l : ℝ}
    (hp : p ∈ Icc (39 / 100 : ℝ) (2 / 5)) (hl : l ∈ Icc (0 : ℝ) (1 / 4)) :
    0 ≤ l / 26 ∧ variance p + l / 26 ≤ 1 / 4 := by
  constructor
  · exact div_nonneg hl.1 (by norm_num)
  · linarith only [(variance_bounds hp).2, hl.2]

/-- The complete price decreases along the whole noise interval; no noise
mesh or subdivision is used. -/
theorem priceSlope_le {p r c δ α l : ℝ}
    (hp : p ∈ Icc (39 / 100 : ℝ) (2 / 5)) (hr : r ≤ 21 / 2)
    (hc : 2 / 25 ≤ c) (hδ : 0 < δ) (hδhi : δ ≤ 7 / 100)
    (hα : α ∈ Icc (0 : ℝ) 1) (hl : l ∈ Icc (0 : ℝ) (1 / 4)) :
    priceSlope p r c δ α l ≤ -3 / 2600 := by
  have hG := gaussian_noise_slope_le hp hl.1 hr
  have hs := scaledNoise_mem hp hl
  have hf := QuantitativeNoiseFloor.firstNoise_ge_two
    (p := p) (s := l / 26) (δ := δ) (α := α)
    ⟨hp.1, by linarith only [hp.2]⟩ hα hδ hδhi hs.1 hs.2
  have hprod := mul_le_mul hc hf (by norm_num : (0 : ℝ) ≤ 2)
    (show 0 ≤ c by linarith only [hc])
  dsimp only [priceSlope]
  nlinarith only [hG, hprod]

theorem compensated_price_antitone {p r c δ α : ℝ}
    (hp : p ∈ Icc (39 / 100 : ℝ) (2 / 5)) (hr : r ≤ 21 / 2)
    (hc : 2 / 25 ≤ c) (hδ : 0 < δ) (hδhi : δ ≤ 7 / 100)
    (hα : α ∈ Icc (0 : ℝ) 1) :
    AntitoneOn (fun l => price p r c δ α l + 3 / 2600 * l) (Icc 0 (1 / 4)) := by
  have hd (l : ℝ) (hl : l ∈ Icc (0 : ℝ) (1 / 4)) :
      HasDerivAt (fun u => price p r c δ α u + 3 / 2600 * u)
        (priceSlope p r c δ α l + 3 / 2600) l := by
    simpa only [mul_one] using
      (hasDerivAt_price (p := p) (r := r) (c := c) (δ := δ) (α := α) hp hl.1 hδ).fun_add
        ((hasDerivAt_id' l).const_mul (3 / 2600 : ℝ))
  apply antitoneOn_of_hasDerivWithinAt_nonpos
    (f' := fun l => priceSlope p r c δ α l + 3 / 2600) (convex_Icc _ _)
  · exact fun l hl => (hd l hl).continuousAt.continuousWithinAt
  · exact fun l hl => (hd l (interior_subset hl)).hasDerivWithinAt
  · intro l hl
    have h := priceSlope_le hp hr hc hδ hδhi hα (interior_subset hl)
    linarith only [h]

/-- The extra summand can represent a price fixed on this noise slice.
No monotonicity is asserted for a reference law varying with l. -/
theorem frozen_reference_endpoint {p r c δ α l0 l1 E : ℝ}
    (hp : p ∈ Icc (39 / 100 : ℝ) (2 / 5)) (hr : r ≤ 21 / 2)
    (hc : 2 / 25 ≤ c) (hδ : 0 < δ) (hδhi : δ ≤ 7 / 100)
    (hα : α ∈ Icc (0 : ℝ) 1) (hl0 : l0 ∈ Icc (0 : ℝ) (1 / 4))
    (hl1 : l1 ∈ Icc (0 : ℝ) (1 / 4)) (horder : l0 ≤ l1) :
    E + price p r c δ α l1 ≤
      E + price p r c δ α l0 - 3 / 2600 * (l1 - l0) := by
  have hm := compensated_price_antitone hp hr hc hδ hδhi hα hl0 hl1 horder
  linarith only [hm]

theorem actual_cost_lower : (2 / 25 : ℝ) ≤ esseenConstant / Real.sqrt 26 := by
  have hs : Real.sqrt (26 : ℝ) ≤ 51 / 10 := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 26), Real.sqrt_nonneg (26 : ℝ)]
  apply (le_div_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 26))).mpr
  linarith only [hs, AnalyticConstants.esseenConstant_gt_819_2000]

theorem canonical_frozen_reference_endpoint
    (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ) (r δ l0 E : ℝ)
    (hp : CanonicalSign.p μ ∈ Icc (39 / 100 : ℝ) (2 / 5))
    (hr : r ≤ 21 / 2) (hδ : 0 < δ) (hδhi : δ ≤ 7 / 100)
    (hl0 : l0 ∈ Icc (0 : ℝ) (1 / 4))
    (hAcquired : l0 ≤ 26 * CanonicalSign.noiseVariance μ hμ)
    (hNoise : 26 * CanonicalSign.noiseVariance μ hμ ≤ 1 / 4) :
    E + price (CanonicalSign.p μ) r (esseenConstant / Real.sqrt 26) δ
        (ConditionalResidual.actualAllocation μ hμ) (26 * CanonicalSign.noiseVariance μ hμ) ≤
      E + price (CanonicalSign.p μ) r (esseenConstant / Real.sqrt 26) δ
        (ConditionalResidual.actualAllocation μ hμ) l0 -
          3 / 2600 * (26 * CanonicalSign.noiseVariance μ hμ - l0) :=
  frozen_reference_endpoint hp hr actual_cost_lower hδ hδhi
    (BernoulliMomentFloor.canonical_allocation_mem_Icc μ hμ) hl0
    ⟨mul_nonneg (by norm_num) (CanonicalSign.noiseVariance_nonneg μ hμ), hNoise⟩ hAcquired

end BerryEsseen.P39NoiseGate

#print axioms BerryEsseen.P39NoiseGate.hasDerivAt_price
#print axioms BerryEsseen.P39NoiseGate.gaussian_noise_slope_le
#print axioms BerryEsseen.P39NoiseGate.priceSlope_le
#print axioms BerryEsseen.P39NoiseGate.frozen_reference_endpoint
#print axioms BerryEsseen.P39NoiseGate.canonical_frozen_reference_endpoint
