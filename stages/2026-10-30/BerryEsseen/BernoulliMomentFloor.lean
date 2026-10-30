module

public import BerryEsseen.P39Reference

@[expose] public section

/-! 2026-10-28: An analytic Bernoulli floor for the original allocation
budget, uniform over nonnegative noise. The same-law consequences retain
the actual canonical allocation and the support/cap hypotheses. -/

namespace BerryEsseen.BernoulliMomentFloor

open MeasureTheory

theorem sqrt_cubic_envelope {v s : ℝ} (hv : 0 ≤ v) (hs : 0 ≤ s) :
    Real.sqrt v * (Real.sqrt (v + s)) ^ 3 ≤ v ^ 2 + 3 * v * s / 2 + 3 * s ^ 2 / 8 := by
  have hleft : 0 ≤ Real.sqrt v * (Real.sqrt (v + s)) ^ 3 := by positivity
  have hright : 0 ≤ v ^ 2 + 3 * v * s / 2 + 3 * s ^ 2 / 8 := by positivity
  have hsq : (Real.sqrt v * (Real.sqrt (v + s)) ^ 3) ^ 2 = v * (v + s) ^ 3 := by
    calc
      _ = (Real.sqrt v) ^ 2 * ((Real.sqrt (v + s)) ^ 2) ^ 3 := by ring
      _ = _ := by rw [Real.sq_sqrt hv, Real.sq_sqrt (add_nonneg hv hs)]
  have hidentity :
      (v ^ 2 + 3 * v * s / 2 + 3 * s ^ 2 / 8) ^ 2 -
        (Real.sqrt v * (Real.sqrt (v + s)) ^ 3) ^ 2 =
      v * s ^ 3 / 8 + 9 * s ^ 4 / 64 := by rw [hsq]; ring
  have htail : 0 ≤ v * s ^ 3 / 8 + 9 * s ^ 4 / 64 := by positivity
  exact (sq_le_sq₀ hleft hright).mp (by nlinarith only [hidentity, htail])

/-- Cross-multiplied coefficient gates avoid any normalization by the noise. -/
theorem quadratic_over_sqrt_cube_floor {v A B C s : ℝ}
    (hv : 0 < v) (hs : 0 ≤ s) (hA : 0 ≤ A)
    (hB : 3 * A ≤ 2 * v * B) (hC : 3 * A ≤ 8 * v ^ 2 * C) :
    A / (Real.sqrt v) ^ 3 ≤ (A + B * s + C * s ^ 2) / (Real.sqrt (v + s)) ^ 3 := by
  have hr := Real.sqrt_pos.mpr hv
  have hrs := Real.sqrt_pos.mpr (hv.trans_le (le_add_of_nonneg_right hs))
  have hpoly : A * (v ^ 2 + 3 * v * s / 2 + 3 * s ^ 2 / 8) ≤
      (A + B * s + C * s ^ 2) * v ^ 2 := by
    have hlin := mul_nonneg (sub_nonneg.mpr hB) (mul_nonneg hv.le hs)
    have hquad := mul_nonneg (sub_nonneg.mpr hC) (sq_nonneg s)
    nlinarith only [hlin, hquad]
  have hprice : A * (Real.sqrt v * (Real.sqrt (v + s)) ^ 3) ≤
      (A + B * s + C * s ^ 2) * v ^ 2 :=
    (mul_le_mul_of_nonneg_left (sqrt_cubic_envelope hv.le hs) hA).trans hpoly
  have hfour : (Real.sqrt v) ^ 3 * Real.sqrt v = v ^ 2 := by
    calc
      _ = ((Real.sqrt v) ^ 2) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt hv.le]
  apply (div_le_div_iff₀ (pow_pos hr 3) (pow_pos hrs 3)).mpr
  apply (mul_le_mul_iff_right₀ hr).mp
  calc
    Real.sqrt v * (A * (Real.sqrt (v + s)) ^ 3) =
        A * (Real.sqrt v * (Real.sqrt (v + s)) ^ 3) := by ring
    _ ≤ (A + B * s + C * s ^ 2) * v ^ 2 := hprice
    _ = Real.sqrt v * ((A + B * s + C * s ^ 2) * (Real.sqrt v) ^ 3) := by
      rw [← hfour]
      ring

/-- The original gDelta expression dominates its Bernoulli value for every
nonnegative noise; the positive cap delta remains a hypothesis. -/
theorem gDelta_ge_rho0 {p s δ α : ℝ}
    (hp : p ∈ Set.Icc (1 / 3 : ℝ) (1 / 2))
    (hα : α ∈ Set.Icc (0 : ℝ) 1) (hs : 0 ≤ s) (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) :
    P39Reference.rho0 p ≤ MomentBudget.gDelta p s δ α := by
  let v := p * (1 - p)
  let A := v * (1 - 2 * v)
  let B := 3 * (p + α * ((1 - p) - p)) - δ
  let L := (1 - α) / Real.sqrt (1 - p) + α / Real.sqrt p
  let C := L ^ 2 / δ
  have hp0 : 0 < p := by linarith [hp.1]
  have hp1 : p < 1 := by linarith [hp.2]
  have hv : 0 < v := mul_pos hp0 (sub_pos.mpr hp1)
  have hvlo : (2 / 9 : ℝ) ≤ v := by
    have hprod := mul_nonneg (sub_nonneg.mpr hp.1)
      (show 0 ≤ 2 / 3 - p by linarith [hp.2])
    dsimp only [v]
    nlinarith only [hprod]
  have hvhi : v ≤ 1 / 4 := by
    dsimp only [v]
    nlinarith only [sq_nonneg (p - 1 / 2)]
  have hA : 0 ≤ A := mul_nonneg hv.le (by linarith [hvhi])
  have hBlo : (9 / 10 : ℝ) ≤ B := by
    have hprod := mul_nonneg hα.1 (show 0 ≤ (1 - p) - p by linarith [hp.2])
    dsimp only [B]
    linarith [hp.1]
  have hvsq := mul_nonneg hv.le (sub_nonneg.mpr hvlo)
  have hB : 3 * A ≤ 2 * v * B := by
    have hb := mul_le_mul_of_nonneg_left hBlo (show 0 ≤ 2 * v by positivity)
    dsimp only [A]
    nlinarith only [hb, hvsq, hv.le]
  have hsp := Real.sqrt_pos.mpr hp0
  have hsq := Real.sqrt_pos.mpr (sub_pos.mpr hp1)
  have hsp1 : Real.sqrt p ≤ 1 := by
    simpa using Real.sqrt_le_sqrt (show p ≤ 1 by linarith [hp.2])
  have hsq1 : Real.sqrt (1 - p) ≤ 1 := by
    simpa using Real.sqrt_le_sqrt (show 1 - p ≤ 1 by linarith [hp.1])
  have htermP : α ≤ α / Real.sqrt p := by
    apply (le_div_iff₀ hsp).mpr
    nlinarith only [mul_nonneg hα.1 (sub_nonneg.mpr hsp1)]
  have htermQ : 1 - α ≤ (1 - α) / Real.sqrt (1 - p) := by
    apply (le_div_iff₀ hsq).mpr
    nlinarith only [mul_nonneg (sub_nonneg.mpr hα.2) (sub_nonneg.mpr hsq1)]
  have hL : 1 ≤ L := by dsimp only [L]; linarith
  have hClo : (10 : ℝ) ≤ C := by
    dsimp only [C]
    apply (le_div_iff₀ hδ).mpr
    nlinarith only [hδhi, hL, sq_nonneg (L - 1)]
  have hC : 3 * A ≤ 8 * v ^ 2 * C := by
    have hc := mul_le_mul_of_nonneg_left hClo (show 0 ≤ 8 * v ^ 2 by positivity)
    dsimp only [A]
    nlinarith only [hc, hvsq, hv.le, sq_nonneg v]
  have hBernoulli : P39Reference.rho0 p = A / (Real.sqrt v) ^ 3 := by
    change (1 - 2 * v) / Real.sqrt v = A / (Real.sqrt v) ^ 3
    dsimp only [A]
    rw [pow_succ, Real.sq_sqrt hv.le]
    field_simp [hv.ne', hsp.ne', (Real.sqrt_pos.mpr hv).ne']
  calc
    P39Reference.rho0 p = A / (Real.sqrt v) ^ 3 := hBernoulli
    _ ≤ (A + B * s + C * s ^ 2) / (Real.sqrt (v + s)) ^ 3 :=
      quadratic_over_sqrt_cube_floor hv hs hA hB hC
    _ = MomentBudget.gDelta p s δ α := by
      dsimp only [A, B, C, L, v, MomentBudget.gDelta]
      ring

theorem canonical_allocation_mem_Icc (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ) :
    ConditionalResidual.actualAllocation μ hμ ∈ Set.Icc (0 : ℝ) 1 := by
  by_cases hs : CanonicalSign.noiseVariance μ hμ = 0
  · simp [ConditionalResidual.actualAllocation, hs]
  · exact MomentBudget.actual_allocation_mem_Icc
      (CanonicalSign.residual0 μ hμ) (CanonicalSign.residual1 μ hμ)
      (CanonicalSign.p μ) (CanonicalSign.noiseVariance μ hμ)
      (ConditionalResidual.actualAllocation μ hμ)
      (CanonicalSign.p_pos μ hμ).le (CanonicalSign.p_lt_one μ hμ).le
      (lt_of_le_of_ne (CanonicalSign.noiseVariance_nonneg μ hμ) (Ne.symm hs)) rfl rfl

/-- Same original law, actual noise and allocation, including zero noise. -/
theorem canonical_thirdMoment_floor
    (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ) (a0 a1 δ : ℝ)
    (hp : CanonicalSign.p μ ∈ Set.Icc (1 / 3 : ℝ) (1 / 2))
    (ha0 : 0 ≤ a0) (ha1 : 0 ≤ a1) (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10)
    (hcap : a0 + a1 ≤ δ)
    (hupper0 : ∀ᵐ u ∂(CanonicalSign.residual0 μ hμ : Measure ℝ), u ≤ a0)
    (hlower1 : ∀ᵐ u ∂(CanonicalSign.residual1 μ hμ : Measure ℝ), -a1 ≤ u) :
    P39Reference.rho0 (CanonicalSign.p μ) ≤ thirdAbsoluteMoment μ := by
  exact (gDelta_ge_rho0 hp (canonical_allocation_mem_Icc μ hμ)
    (CanonicalSign.noiseVariance_nonneg μ hμ) hδ hδhi).trans
      (ConditionalResidual.canonical_actual_allocation_floor
        μ hμ a0 a1 δ ha0 ha1 hδ hcap hupper0 hlower1)

/-- The certified P39 price now applies to positive as well as zero actual
noise, under the same support and positive-cap hypotheses. -/
theorem canonical_P39_floor_all_noise
    (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ) (a0 a1 δ : ℝ)
    (hp : CanonicalSign.p μ ∈ Set.Icc (39 / 100 : ℝ) (2 / 5))
    (ha0 : 0 ≤ a0) (ha1 : 0 ≤ a1) (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10)
    (hcap : a0 + a1 ≤ δ)
    (hupper0 : ∀ᵐ u ∂(CanonicalSign.residual0 μ hμ : Measure ℝ), u ≤ a0)
    (hlower1 : ∀ᵐ u ∂(CanonicalSign.residual1 μ hμ : Measure ℝ), -a1 ≤ u) :
    (530722777603 / 500000000000 : ℝ) ≤ thirdAbsoluteMoment μ := by
  have hpwide : CanonicalSign.p μ ∈ Set.Icc (1 / 3 : ℝ) (1 / 2) :=
    ⟨by linarith [hp.1], by linarith [hp.2]⟩
  exact (P39Reference.rho0_floor hp).trans
    (canonical_thirdMoment_floor μ hμ a0 a1 δ hpwide ha0 ha1 hδ hδhi hcap hupper0 hlower1)

end BerryEsseen.BernoulliMomentFloor

#print axioms BerryEsseen.BernoulliMomentFloor.sqrt_cubic_envelope
#print axioms BerryEsseen.BernoulliMomentFloor.quadratic_over_sqrt_cube_floor
#print axioms BerryEsseen.BernoulliMomentFloor.gDelta_ge_rho0
#print axioms BerryEsseen.BernoulliMomentFloor.canonical_allocation_mem_Icc
#print axioms BerryEsseen.BernoulliMomentFloor.canonical_thirdMoment_floor
#print axioms BerryEsseen.BernoulliMomentFloor.canonical_P39_floor_all_noise
