module

public import BerryEsseen.ControlFirstIntegralRows
public import BerryEsseen.ControlRemainingIntegralRows
public import BerryEsseen.ControlEndpointBudget
public import BerryEsseen.FiniteHighMomentTails

@[expose] public section

/-! 2026-10-29: join the actual three finite integrals, their unchanged
integer rows and the analytic infinite Gaussian tail at the control point.
This is a single spectral endpoint, not a completed compact-domain cover. -/

noncomputable section

open MeasureTheory Set

namespace BerryEsseen.ControlCertifiedEndpoint

open ControlEndpointParameters CoefficientPhysicalProfile

theorem physical_profile_lt : physicalProfile 42 c beta U0 U < 4071 / 10000 := by
  have h1 := ControlFirstIntegralRows.actual_first_integral_le_rows
  have h2 := ControlRemainingIntegralRows.actual_second_integral_le_rows
  have h3 := ControlRemainingIntegralRows.actual_third_integral_le_rows
  have h4 := ControlEndpointBudget.fourth_integral_le
  have hb := beta_pos
  have hu := U_pos
  have hc1 : 0 ≤ 2 / U := by positivity
  have hc2 : 0 ≤ 2 / (U * beta) := by positivity
  have hbudget := ControlEndpointBudget.normalized_row_budget
  unfold ControlEndpointBudget.rowSum at hbudget
  exact (add_le_add (add_le_add
    (add_le_add (mul_le_mul_of_nonneg_left h1 hc1)
      (mul_le_mul_of_nonneg_left h2 hc2))
    (mul_le_mul_of_nonneg_left h3 hc2)) h4).trans_lt hbudget

theorem spectral_profile_lt :
    CoefficientRaySpectral.spectralProfile 42 c A 4 s < 4071 / 10000 := by
  have he := physicalProfile_scale_eq_spectral 42 (by decide) c beta A 4 beta_pos
    A_pos A_lt_four.le
  rw [← U0_eq, ← U_eq, spectral_eq] at he
  rw [← he]
  exact physical_profile_lt

/-- The same original law and every threshold at this fixed beta satisfy
a strict bound below the Esseen target. No finite-support restriction is
introduced, and the sample size remains any actual n>=42. -/
theorem actual_cdf_lt_at_control_beta (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (hn : 42 ≤ n) (hρ : HighMomentRayDamping.rho0 ≤ thirdAbsoluteMoment μ)
    (hbeta : HighMomentRayDamping.beta μ n = beta) (x : ℝ) :
    |(normalizedIidSumLaw μ n).real (Iic x) - GaussianTools.Phi x| <
      (4071 / 10000) * HighMomentRayDamping.beta μ n := by
  have hC : thirdAbsoluteMoment μ + 1 ≤ c * thirdAbsoluteMoment μ := by
    rw [c_eq_old]
    have hh : (1 : ℝ) ≤ thirdAbsoluteMoment μ / HighMomentRayDamping.rho0 :=
      (le_div_iff₀ HighMomentRayDamping.rho0_pos).mpr (by simpa using hρ)
    unfold CoefficientRayPrice.oldCoefficient
    calc
      _ ≤ thirdAbsoluteMoment μ + thirdAbsoluteMoment μ / HighMomentRayDamping.rho0 := by
        linarith only [hh]
      _ = _ := by ring
  have ht := normalized_actual_cdf_le_beta_physicalProfile μ h n 42 (by decide) hn
    hρ c hC A 4 A_pos A_lt_four.le x
  rw [hbeta, ← U0_eq, ← U_eq] at ht
  calc
    _ ≤ beta * physicalProfile 42 c beta U0 U := ht
    _ < beta * (4071 / 10000) := mul_lt_mul_of_pos_left physical_profile_lt beta_pos
    _ = _ := by rw [hbeta]; ring

theorem sharp_at_control_beta (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (hn : 42 ≤ n) (hρ : HighMomentRayDamping.rho0 ≤ thirdAbsoluteMoment μ)
    (hbeta : HighMomentRayDamping.beta μ n = beta) (x : ℝ) :
    |(normalizedIidSumLaw μ n).real (Iic x) - GaussianTools.Phi x| <
      esseenConstant * HighMomentRayDamping.beta μ n := by
  have htarget : (4071 : ℝ) / 10000 < esseenConstant :=
    lt_trans (by norm_num : (4071 : ℝ) / 10000 < 4097 / 10000)
      FiniteHighMomentTails.target4097_lt_esseen
  have hb : 0 < HighMomentRayDamping.beta μ n := hbeta.symm ▸ beta_pos
  exact (actual_cdf_lt_at_control_beta μ h n hn hρ hbeta x).trans
    (mul_lt_mul_of_pos_right htarget hb)

end BerryEsseen.ControlCertifiedEndpoint

#print axioms BerryEsseen.ControlCertifiedEndpoint.physical_profile_lt
#print axioms BerryEsseen.ControlCertifiedEndpoint.spectral_profile_lt
#print axioms BerryEsseen.ControlCertifiedEndpoint.actual_cdf_lt_at_control_beta
#print axioms BerryEsseen.ControlCertifiedEndpoint.sharp_at_control_beta
