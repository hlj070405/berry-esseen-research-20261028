module

public import BerryEsseen.BernoulliMomentFloor

@[expose] public section

/-! 2026-10-28: Actual noise derivatives and monotonicity of gDelta.
The second derivative retains its negative quadratic term. Endpoint
acquisition and the original same-law support/cap hypotheses stay explicit. -/

namespace BerryEsseen.MomentBudgetNoise

open MeasureTheory

noncomputable section

abbrev variance := P39Reference.v
def A (p : ℝ) : ℝ := variance p * (1 - 2 * variance p)
def B (p δ α : ℝ) : ℝ := 3 * (p + α * ((1 - p) - p)) - δ
def C (p δ α : ℝ) : ℝ :=
  ((1 - α) / Real.sqrt (1 - p) + α / Real.sqrt p) ^ 2 / δ

def value (v a b c s : ℝ) : ℝ := (a + b * s + c * s ^ 2) / (Real.sqrt (v + s)) ^ 3
def first (v a b c s : ℝ) : ℝ :=
  (b * v - 3 * a / 2 + (2 * c * v - b / 2) * s + c * s ^ 2 / 2) /
    ((v + s) ^ 2 * Real.sqrt (v + s))
def second (v a b c s : ℝ) : ℝ :=
  (2 * c * v ^ 2 - 3 * b * v + 15 * a / 4 +
    (-2 * c * v + 3 * b / 4) * s - c * s ^ 2 / 4) /
    ((v + s) ^ 3 * Real.sqrt (v + s))

def firstNoise (p δ α s : ℝ) : ℝ := first (variance p) (A p) (B p δ α) (C p δ α) s
def secondNoise (p δ α s : ℝ) : ℝ := second (variance p) (A p) (B p δ α) (C p δ α) s

private theorem hasDerivAt_polynomial (a b c s : ℝ) :
    HasDerivAt (fun t : ℝ => a + b * t + c * t ^ 2) (b + 2 * c * s) s := by
  convert ((hasDerivAt_const s a).add ((hasDerivAt_id s).const_mul b)).add
    (((hasDerivAt_id s).pow 2).const_mul c) using 1
  · funext t
    rfl
  · simp only [id_eq]
    ring

theorem hasDerivAt_value {v a b c s : ℝ} (hR : 0 < v + s) :
    HasDerivAt (value v a b c) (first v a b c s) s := by
  have hlinear : HasDerivAt (fun t : ℝ => v + t) 1 s := by
    simpa using (hasDerivAt_id s).const_add v
  have hr := Real.sqrt_pos.mpr hR
  have hd := (hasDerivAt_polynomial a b c s).div
    ((hlinear.sqrt hR.ne').pow 3) (pow_ne_zero 3 hr.ne')
  convert hd using 1
  · funext t
    rfl
  · simp only [first, Pi.mul_apply, Pi.div_apply, Pi.pow_apply]
    generalize hz : Real.sqrt (v + s) = r
    have hr0 : r ≠ 0 := by simpa [hz] using hr.ne'
    have hsq : r ^ 2 = v + s := by rw [← hz, Real.sq_sqrt hR.le]
    have hv : v = r ^ 2 - s := by linarith only [hsq]
    rw [hv]
    simp only [sub_add_cancel]
    field_simp [hr0]
    ring

theorem hasDerivAt_first {v a b c s : ℝ} (hR : 0 < v + s) :
    HasDerivAt (first v a b c) (second v a b c s) s := by
  have hlinear : HasDerivAt (fun t : ℝ => v + t) 1 s := by
    simpa using (hasDerivAt_id s).const_add v
  have hr := Real.sqrt_pos.mpr hR
  have hn := hasDerivAt_polynomial (b * v - 3 * a / 2) (2 * c * v - b / 2) (c / 2) s
  have hd := hn.div ((hlinear.pow 2).mul (hlinear.sqrt hR.ne'))
    (mul_ne_zero (pow_ne_zero 2 hR.ne') hr.ne')
  convert hd using 1
  · funext t
    simp only [first, Pi.div_apply, Pi.mul_apply, Pi.pow_apply]
    ring
  · simp only [second, Pi.mul_apply, Pi.div_apply, Pi.pow_apply]
    generalize hz : Real.sqrt (v + s) = r
    have hr0 : r ≠ 0 := by simpa [hz] using hr.ne'
    have hsq : r ^ 2 = v + s := by rw [← hz, Real.sq_sqrt hR.le]
    have hv : v = r ^ 2 - s := by linarith only [hsq]
    rw [hv]
    simp only [sub_add_cancel]
    field_simp [hr0]
    ring

theorem gDelta_eq_value (p s δ α : ℝ) :
    MomentBudget.gDelta p s δ α = value (variance p) (A p) (B p δ α) (C p δ α) s := by
  dsimp only [MomentBudget.gDelta, value, A, B, C, variance, P39Reference.v]
  ring

private theorem gDelta_fun_eq (p δ α : ℝ) :
    (fun s => MomentBudget.gDelta p s δ α) = value (variance p) (A p) (B p δ α) (C p δ α) :=
  funext (fun s => gDelta_eq_value p s δ α)

private theorem hasDerivAt_gDelta_of_pos {p s δ α : ℝ} (hR : 0 < variance p + s) :
    HasDerivAt (fun t => MomentBudget.gDelta p t δ α) (firstNoise p δ α s) s := by
  rw [gDelta_fun_eq]
  exact hasDerivAt_value hR

theorem hasDerivAt_gDelta {p s δ α : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hs : 0 ≤ s) (_hδ : 0 < δ) :
    HasDerivAt (fun t => MomentBudget.gDelta p t δ α) (firstNoise p δ α s) s :=
  hasDerivAt_gDelta_of_pos (add_pos_of_pos_of_nonneg (P39Reference.v_pos hp0 hp1) hs)

theorem hasDerivAt_deriv_gDelta {p s δ α : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hs : 0 ≤ s) (_hδ : 0 < δ) :
    HasDerivAt (deriv (fun t => MomentBudget.gDelta p t δ α)) (secondNoise p δ α s) s := by
  have hR : 0 < variance p + s := add_pos_of_pos_of_nonneg (P39Reference.v_pos hp0 hp1) hs
  have hd : HasDerivAt (firstNoise p δ α) (secondNoise p δ α s) s := hasDerivAt_first hR
  apply hd.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds (show -variance p < s by linarith only [hR])] with t ht
  change -variance p < t at ht
  exact (hasDerivAt_gDelta_of_pos (p := p) (δ := δ) (α := α) (s := t)
    (by linarith only [ht])).deriv

theorem deriv2_gDelta {p s δ α : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hs : 0 ≤ s) (hδ : 0 < δ) :
    deriv (deriv (fun t => MomentBudget.gDelta p t δ α)) s = secondNoise p δ α s :=
  (hasDerivAt_deriv_gDelta hp0 hp1 hs hδ).deriv

theorem contDiffAt_gDelta {p s δ α : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hs : 0 ≤ s) (_hδ : 0 < δ) :
    ContDiffAt ℝ 2 (fun t => MomentBudget.gDelta p t δ α) s := by
  have hR : 0 < variance p + s := add_pos_of_pos_of_nonneg (P39Reference.v_pos hp0 hp1) hs
  rw [gDelta_fun_eq]
  unfold value
  have hn : ContDiff ℝ 2 (fun t : ℝ => A p + B p δ α * t + C p δ α * t ^ 2) := by fun_prop
  have hlinear : ContDiffAt ℝ 2 (fun t : ℝ => variance p + t) s := by fun_prop
  exact hn.contDiffAt.div ((hlinear.sqrt hR.ne').pow 3)
    (pow_ne_zero 3 (Real.sqrt_pos.mpr hR).ne')

theorem contDiffOn_gDelta {p δ α : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hδ : 0 < δ) :
    ContDiffOn ℝ 2 (fun s => MomentBudget.gDelta p s δ α) (Set.Ici 0) :=
  fun _ hs => (contDiffAt_gDelta hp0 hp1 hs hδ).contDiffWithinAt

/-- These gates concern first-derivative monotonicity, not global convexity. -/
theorem coefficient_noise_gates {p δ α : ℝ}
    (hp : p ∈ Set.Icc (1 / 3 : ℝ) (1 / 2)) (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) :
    3 * A p ≤ 2 * variance p * B p δ α ∧
      B p δ α ≤ 4 * C p δ α * variance p ∧ 0 ≤ C p δ α := by
  have hp0 : 0 < p := by linarith [hp.1]
  have hp1 : p < 1 := by linarith [hp.2]
  have hv := P39Reference.v_pos hp0 hp1
  have hvlo : (2 / 9 : ℝ) ≤ variance p := by
    have hprod := mul_nonneg (sub_nonneg.mpr hp.1)
      (show 0 ≤ 2 / 3 - p by linarith [hp.2])
    dsimp only [variance, P39Reference.v]
    nlinarith only [hprod]
  have hαprod := mul_nonneg hα.1 (show 0 ≤ (1 - p) - p by linarith [hp.2])
  have hBlo : (9 / 10 : ℝ) ≤ B p δ α := by dsimp only [B]; linarith [hp.1]
  have hBhi : B p δ α ≤ 2 := by
    have hαupper := mul_le_mul_of_nonneg_right hα.2
      (show 0 ≤ (1 - p) - p by linarith [hp.2])
    dsimp only [B]
    linarith [hp.1]
  have hvsq := mul_nonneg hv.le (sub_nonneg.mpr hvlo)
  have hB : 3 * A p ≤ 2 * variance p * B p δ α := by
    have hb := mul_le_mul_of_nonneg_left hBlo (show 0 ≤ 2 * variance p by positivity)
    dsimp only [A]
    nlinarith only [hb, hvsq, hv.le]
  let L := (1 - α) / Real.sqrt (1 - p) + α / Real.sqrt p
  have hsp := Real.sqrt_pos.mpr hp0
  have hsq := Real.sqrt_pos.mpr (sub_pos.mpr hp1)
  have hsp1 : Real.sqrt p ≤ 1 := by simpa using Real.sqrt_le_sqrt hp1.le
  have hsq1 : Real.sqrt (1 - p) ≤ 1 := by
    simpa using Real.sqrt_le_sqrt (show 1 - p ≤ 1 by linarith [hp.1])
  have htermP : α ≤ α / Real.sqrt p := by
    apply (le_div_iff₀ hsp).mpr
    nlinarith only [mul_nonneg hα.1 (sub_nonneg.mpr hsp1)]
  have htermQ : 1 - α ≤ (1 - α) / Real.sqrt (1 - p) := by
    apply (le_div_iff₀ hsq).mpr
    nlinarith only [mul_nonneg (sub_nonneg.mpr hα.2) (sub_nonneg.mpr hsq1)]
  have hL : 1 ≤ L := by dsimp only [L]; linarith
  have hClo : (10 : ℝ) ≤ C p δ α := by
    change 10 ≤ L ^ 2 / δ
    apply (le_div_iff₀ hδ).mpr
    nlinarith only [hδhi, hL, sq_nonneg (L - 1)]
  have hCgate : B p δ α ≤ 4 * C p δ α * variance p := by
    have hc := mul_le_mul_of_nonneg_right hClo hv.le
    nlinarith only [hc, hvlo, hBhi]
  exact ⟨hB, hCgate, by linarith only [hClo]⟩

theorem firstNoise_nonneg {p s δ α : ℝ}
    (hp : p ∈ Set.Icc (1 / 3 : ℝ) (1 / 2)) (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (hs : 0 ≤ s) (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) : 0 ≤ firstNoise p δ α s := by
  obtain ⟨hB, hCgate, hC⟩ := coefficient_noise_gates hp hα hδ hδhi
  have hconstant : 0 ≤ B p δ α * variance p - 3 * A p / 2 := by linarith only [hB]
  have hlinear : 0 ≤ 2 * C p δ α * variance p - B p δ α / 2 := by linarith only [hCgate]
  unfold firstNoise first
  exact div_nonneg (by positivity) (by positivity)

theorem monotoneOn_noise {p δ α : ℝ}
    (hp : p ∈ Set.Icc (1 / 3 : ℝ) (1 / 2)) (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) :
    MonotoneOn (fun s => MomentBudget.gDelta p s δ α) (Set.Ici 0) := by
  have hp0 : 0 < p := by linarith [hp.1]
  have hp1 : p < 1 := by linarith [hp.2]
  apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
  · exact (contDiffOn_gDelta hp0 hp1 hδ).continuousOn
  · intro s hs
    exact (hasDerivAt_gDelta hp0 hp1 (interior_subset hs) hδ).differentiableAt.differentiableWithinAt
  · intro s hs
    rw [(hasDerivAt_gDelta hp0 hp1 (interior_subset hs) hδ).deriv]
    exact firstNoise_nonneg hp hα (interior_subset hs) hδ hδhi

theorem gDelta_mono_noise {p δ α s0 s1 : ℝ}
    (hp : p ∈ Set.Icc (1 / 3 : ℝ) (1 / 2)) (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hs0 : 0 ≤ s0) (hs01 : s0 ≤ s1) :
    MomentBudget.gDelta p s0 δ α ≤ MomentBudget.gDelta p s1 δ α :=
  monotoneOn_noise hp hα hδ hδhi hs0 (hs0.trans hs01) hs01

/-- Acquired lower noise is substituted only into the same original law's
budget. Neither acquisition nor the support/cap conditions are inferred. -/
theorem canonical_thirdMoment_floor_of_noise_lower
    (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ) (a0 a1 δ sLower : ℝ)
    (hp : CanonicalSign.p μ ∈ Set.Icc (1 / 3 : ℝ) (1 / 2))
    (ha0 : 0 ≤ a0) (ha1 : 0 ≤ a1) (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10)
    (hcap : a0 + a1 ≤ δ) (hsLower : 0 ≤ sLower)
    (hAcquired : sLower ≤ CanonicalSign.noiseVariance μ hμ)
    (hupper0 : ∀ᵐ u ∂(CanonicalSign.residual0 μ hμ : Measure ℝ), u ≤ a0)
    (hlower1 : ∀ᵐ u ∂(CanonicalSign.residual1 μ hμ : Measure ℝ), -a1 ≤ u) :
    MomentBudget.gDelta (CanonicalSign.p μ) sLower δ (ConditionalResidual.actualAllocation μ hμ) ≤
      thirdAbsoluteMoment μ := by
  exact (gDelta_mono_noise hp (BernoulliMomentFloor.canonical_allocation_mem_Icc μ hμ)
    hδ hδhi hsLower hAcquired).trans
    (ConditionalResidual.canonical_actual_allocation_floor μ hμ a0 a1 δ
      ha0 ha1 hδ hcap hupper0 hlower1)

end
end BerryEsseen.MomentBudgetNoise

#print axioms BerryEsseen.MomentBudgetNoise.hasDerivAt_value
#print axioms BerryEsseen.MomentBudgetNoise.hasDerivAt_first
#print axioms BerryEsseen.MomentBudgetNoise.hasDerivAt_gDelta
#print axioms BerryEsseen.MomentBudgetNoise.hasDerivAt_deriv_gDelta
#print axioms BerryEsseen.MomentBudgetNoise.deriv2_gDelta
#print axioms BerryEsseen.MomentBudgetNoise.contDiffOn_gDelta
#print axioms BerryEsseen.MomentBudgetNoise.firstNoise_nonneg
#print axioms BerryEsseen.MomentBudgetNoise.gDelta_mono_noise
#print axioms BerryEsseen.MomentBudgetNoise.canonical_thirdMoment_floor_of_noise_lower
