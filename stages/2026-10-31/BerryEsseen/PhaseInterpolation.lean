module

public import BerryEsseen.GaussianPrices
public import Mathlib.Analysis.Convex.Function

@[expose] public section

/-! 2026-10-28: continuous phase control from price faces and actual CDF
monotonicity. Semiconvexity is imposed on the price, never on the original CDF.
-/

noncomputable section

open MeasureTheory Set

namespace BerryEsseen.PhaseInterpolation

open GaussianTools

theorem semiconvex_chord (E : ℝ → ℝ) (a b M L U y : ℝ) (hab : a < b)
    (hconv : ConvexOn ℝ (Icc a b) (fun t => E t + M * t ^ 2 / 2))
    (hL : E a ≤ L) (hU : E b ≤ U) (hy0 : 0 ≤ y) (hy1 : y ≤ b - a) :
    E (a + y) ≤ L + (U - L) / (b - a) * y + M / 2 * y * (b - a - y) := by
  let θ := y / (b - a)
  have hH : 0 < b - a := sub_pos.mpr hab
  have hθ0 : 0 ≤ θ := div_nonneg hy0 hH.le
  have hθ1 : θ ≤ 1 := (div_le_one₀ hH).mpr hy1
  have hlin : (1 - θ) * a + θ * b = a + y := by
    dsimp [θ]
    field_simp [hH.ne']
    ring
  have hc := hconv.2 (show a ∈ Icc a b from ⟨le_rfl, hab.le⟩)
    (show b ∈ Icc a b from ⟨hab.le, le_rfl⟩)
    (show 0 ≤ 1 - θ by linarith) hθ0 (by ring : (1 - θ) + θ = 1)
  change E ((1 - θ) * a + θ * b) + M * ((1 - θ) * a + θ * b) ^ 2 / 2 ≤
    (1 - θ) * (E a + M * a ^ 2 / 2) + θ * (E b + M * b ^ 2 / 2) at hc
  rw [hlin] at hc
  have h0 := mul_le_mul_of_nonneg_left
    (show E a + M * a ^ 2 / 2 ≤ L + M * a ^ 2 / 2 by linarith)
    (show 0 ≤ 1 - θ by linarith)
  have h1 := mul_le_mul_of_nonneg_left
    (show E b + M * b ^ 2 / 2 ≤ U + M * b ^ 2 / 2 by linarith) hθ0
  have hface := hc.trans (add_le_add h0 h1)
  have heq : (1 - θ) * (L + M * a ^ 2 / 2) + θ * (U + M * b ^ 2 / 2) -
      M * (a + y) ^ 2 / 2 = L + (U - L) / (b - a) * y + M / 2 * y * (b - a - y) := by
    dsimp [θ]
    field_simp [hH.ne']
    ring
  calc
    _ ≤ (1 - θ) * (L + M * a ^ 2 / 2) + θ * (U + M * b ^ 2 / 2) -
        M * (a + y) ^ 2 / 2 := by linarith
    _ = _ := heq

theorem residual_le_chord (R E : ℝ → ℝ) (a b M L U y : ℝ) (hab : a < b)
    (hRE : ∀ t ∈ Icc a b, R t ≤ E t)
    (hconv : ConvexOn ℝ (Icc a b) (fun t => E t + M * t ^ 2 / 2))
    (hL : E a ≤ L) (hU : E b ≤ U) (hy0 : 0 ≤ y) (hy1 : y ≤ b - a) :
    R (a + y) ≤ L + (U - L) / (b - a) * y + M / 2 * y * (b - a - y) :=
  (hRE _ ⟨by linarith, by linarith⟩).trans (semiconvex_chord E a b M L U y hab hconv hL hU hy0 hy1)

lemma phi_le_phi_zero (t : ℝ) : phi t ≤ phi 0 := by
  rw [GaussianPrices.phi_eq_phi_zero_mul_exp]
  have he : Real.exp (-(t ^ 2 / 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg t])
  simpa only [mul_one] using mul_le_mul_of_nonneg_left he (phi_nonneg 0)

theorem Phi_difference_le (a b : ℝ) (hab : a ≤ b) : Phi b - Phi a ≤ phi 0 * (b - a) := by
  have hconst : IntervalIntegrable (fun _ : ℝ => phi 0) volume a b :=
    continuous_const.intervalIntegrable a b
  have hmono := intervalIntegral.integral_mono_on (μ := volume) hab
    (continuous_phi.intervalIntegrable a b) hconst (fun t _ => phi_le_phi_zero t)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hasDerivAt_Phi t)
    (continuous_phi.intervalIntegrable a b), intervalIntegral.integral_const] at hmono
  simpa only [smul_eq_mul, mul_comm] using hmono

def phaseResidual (ν : ProbabilityMeasure ℝ) (k center A penalty t : ℝ) : ℝ :=
  (ν : Measure ℝ).real (Iic (k + t)) - Phi ((k + t - center) / Real.sqrt A) - penalty

/-- Only the endpoint price is used; the original CDF may have arbitrary atoms. -/
theorem cdf_bridge (ν : ProbabilityMeasure ℝ) (k center A Astar penalty b t U : ℝ)
    (hAstar : 0 < Astar) (hA : Astar ≤ A) (ht : t ≤ b)
    (hU : phaseResidual ν k center A penalty b ≤ U) :
    phaseResidual ν k center A penalty t ≤ U + phi 0 / Real.sqrt Astar * (b - t) := by
  have hs0 : 0 < Real.sqrt Astar := Real.sqrt_pos.mpr hAstar
  have hs : 0 < Real.sqrt A := Real.sqrt_pos.mpr (hAstar.trans_le hA)
  have hCDF : (ν : Measure ℝ).real (Iic (k + t)) ≤ (ν : Measure ℝ).real (Iic (k + b)) :=
    measureReal_mono (Iic_subset_Iic.mpr (by linarith))
  have hphase : (k + t - center) / Real.sqrt A ≤ (k + b - center) / Real.sqrt A :=
    div_le_div_of_nonneg_right (by linarith) hs.le
  have hPhi := Phi_difference_le _ _ hphase
  have hPhi' : Phi ((k + b - center) / Real.sqrt A) - Phi ((k + t - center) / Real.sqrt A) ≤
      phi 0 / Real.sqrt A * (b - t) := by
    have heq : phi 0 * ((k + b - center) / Real.sqrt A - (k + t - center) / Real.sqrt A) =
        phi 0 / Real.sqrt A * (b - t) := by ring
    rw [heq] at hPhi
    exact hPhi
  have hscale : phi 0 / Real.sqrt A ≤ phi 0 / Real.sqrt Astar :=
    div_le_div_of_nonneg_left (phi_nonneg 0) hs0 (Real.sqrt_le_sqrt hA)
  have hstep := mul_le_mul_of_nonneg_right hscale (sub_nonneg.mpr ht)
  unfold phaseResidual at hU ⊢
  linarith

end BerryEsseen.PhaseInterpolation

#print axioms BerryEsseen.PhaseInterpolation.semiconvex_chord
#print axioms BerryEsseen.PhaseInterpolation.residual_le_chord
#print axioms BerryEsseen.PhaseInterpolation.cdf_bridge
