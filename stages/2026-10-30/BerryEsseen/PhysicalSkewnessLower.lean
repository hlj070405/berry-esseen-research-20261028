module

public import BerryEsseen.PhysicalDefect
public import BerryEsseen.SignedMoment

@[expose] public section

/-! 2026-10-28: support-free physical lower prices for the actual signed
third moment. The original gap series satisfies J <= rho + 1, using the
actual central endpoints, first moment and standardized second moment.
Incoming rho and defect prices remain explicit assumptions on the same law. -/

noncomputable section

open MeasureTheory Set

namespace BerryEsseen.PhysicalSkewnessLower

open CentralGap NoiseCoordinates ZeroBias ZeroBiasStopLoss GapDefect PhysicalDefect

theorem central_product_nonneg_ae (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    ∀ᵐ x ∂(μ : Measure ℝ), 0 ≤ (x + Aminus μ) * (x - Aplus μ) := by
  filter_upwards [(μ : Measure ℝ).support_mem_ae] with x hx
  have ha := Aminus_nonneg μ h
  have hb := Aplus_nonneg μ h
  by_cases hleft : x ≤ -Aminus μ
  · apply mul_nonneg_of_nonpos_of_nonpos <;> linarith
  · have hright : Aplus μ ≤ x := by
      by_contra hn
      exact (Set.disjoint_left.mp (support_disjoint_openGap μ)) hx
        ⟨lt_of_not_ge hleft, lt_of_not_ge hn⟩
    apply mul_nonneg <;> linarith

/-- Integration uses the original mean and second moment; endpoint atoms are allowed. -/
theorem central_endpoints_product_le_one (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    Aminus μ * Aplus μ ≤ 1 := by
  have heq : (fun x : ℝ => (x + Aminus μ) * (x - Aplus μ)) =
      (fun x : ℝ => x ^ 2 + (Aminus μ - Aplus μ) * x - Aminus μ * Aplus μ) := by
    ext x
    ring
  have hB : Integrable (fun x : ℝ => (Aminus μ - Aplus μ) * x) (μ : Measure ℝ) :=
    h.integrable_mean.const_mul _
  have hAB : Integrable (fun x : ℝ => x ^ 2 + (Aminus μ - Aplus μ) * x) (μ : Measure ℝ) :=
    h.integrable_square.add hB
  have hi : (∫ x : ℝ, (x + Aminus μ) * (x - Aplus μ) ∂(μ : Measure ℝ)) =
      1 - Aminus μ * Aplus μ := by
    rw [heq, integral_sub hAB (integrable_const _), integral_add h.integrable_square hB,
      integral_const_mul, h.second_moment_one, h.mean_zero, integral_const, probReal_univ, one_smul]
    ring
  have hn := integral_nonneg_of_ae (central_product_nonneg_ae μ h)
  rw [hi] at hn
  linarith only [hn]

theorem firstAbsoluteMoment_eq_twice_positive (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    SignedMoment.firstAbsoluteMoment μ = 2 * positiveFirstMoment μ := by
  have heq : (fun x : ℝ => |x|) = (fun x : ℝ => positivePart x + negativePart x) := by
    ext x
    rcases le_total 0 x with hx | hx
    · simp [positivePart, negativePart, max_eq_left hx, max_eq_right (neg_nonpos.mpr hx), abs_of_nonneg hx]
    · simp [positivePart, negativePart, max_eq_right hx, max_eq_left (neg_nonneg.mpr hx), abs_of_nonpos hx]
  unfold SignedMoment.firstAbsoluteMoment
  rw [heq, integral_add (integrable_positivePart μ h) (integrable_negativePart μ h),
    negative_firstMoment_eq_positive μ h]
  change positiveFirstMoment μ + positiveFirstMoment μ = 2 * positiveFirstMoment μ
  ring

theorem positiveFirstMoment_le_half (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    positiveFirstMoment μ ≤ (1 : ℝ) / 2 := by
  have hbound := SignedMoment.first_sq_add_signed_sq_le_one μ h
  have hsquare : SignedMoment.firstAbsoluteMoment μ ^ 2 ≤ (1 : ℝ) ^ 2 := by
    nlinarith only [hbound, sq_nonneg (SignedMoment.signedSecondMoment μ)]
  have ha : SignedMoment.firstAbsoluteMoment μ ≤ 1 :=
    (sq_le_sq₀ (SignedMoment.firstAbsoluteMoment_pos μ h).le (by norm_num : (0 : ℝ) ≤ 1)).mp hsquare
  have heq := firstAbsoluteMoment_eq_twice_positive μ h
  linarith only [ha, heq]

theorem central_correction_le_one (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    2 * positiveFirstMoment μ * Aminus μ * Aplus μ ≤ 1 := by
  have hm := positiveFirstMoment_le_half μ h
  have ha := central_endpoints_product_le_one μ h
  have hn := mul_nonneg (Aminus_nonneg μ h) (Aplus_nonneg μ h)
  calc
    2 * positiveFirstMoment μ * Aminus μ * Aplus μ =
        (2 * positiveFirstMoment μ) * (Aminus μ * Aplus μ) := by ring
    _ ≤ 1 * (Aminus μ * Aplus μ) :=
      mul_le_mul_of_nonneg_right (by linarith : 2 * positiveFirstMoment μ ≤ 1) hn
    _ ≤ 1 := by simpa only [one_mul] using ha

/-- The bound holds for every original standardized law, including unbounded and atomic support. -/
theorem actualJ_le_rho_add_one (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    actualJ μ ≤ thirdAbsoluteMoment μ + 1 := by
  by_cases hz : (0 : ℝ) ∈ (μ : Measure ℝ).support
  · have hj := actualJ_le_rho_of_zero_mem μ h hz
    linarith only [hj]
  · have hj := actualJ_le_central_correction μ h hz
    have hc := central_correction_le_one μ h
    linarith only [hj, hc]

theorem gamma_lower (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    Real.sqrt 10 * thirdAbsoluteMoment μ - 3 - actualPhysicalDefect μ ≤ gamma μ := by
  have hj := actualJ_le_rho_add_one μ h
  unfold actualPhysicalDefect
  nlinarith only [hj]

/-- Acquired rho and defect bounds are inputs on this same original law. -/
theorem gamma_lower_of_bounds (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (rhoLower dD sigmaLower : ℝ) (hρ : rhoLower ≤ thirdAbsoluteMoment μ)
    (hD : actualPhysicalDefect μ ≤ dD) (hσ0 : 0 ≤ sigmaLower) (hσ : sigmaLower ≤ Real.sqrt 10) :
    sigmaLower * rhoLower - 3 - dD ≤ gamma μ := by
  have hρ0 : 0 ≤ thirdAbsoluteMoment μ := integral_nonneg fun x => pow_nonneg (abs_nonneg x) 3
  have h1 := mul_le_mul_of_nonneg_left hρ hσ0
  have h2 := mul_le_mul_of_nonneg_right hσ hρ0
  have hg := gamma_lower μ h
  linarith only [h1, h2, hg, hD]

theorem abs_gamma_lower_of_bounds (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (rhoLower dD sigmaLower : ℝ) (hρ : rhoLower ≤ thirdAbsoluteMoment μ)
    (hD : actualPhysicalDefect μ ≤ dD) (hσ0 : 0 ≤ sigmaLower) (hσ : sigmaLower ≤ Real.sqrt 10) :
    max 0 (sigmaLower * rhoLower - 3 - dD) ≤ |gamma μ| := by
  apply max_le (abs_nonneg _)
  exact (gamma_lower_of_bounds μ h rhoLower dD sigmaLower hρ hD hσ0 hσ).trans (le_abs_self _)

end BerryEsseen.PhysicalSkewnessLower

#print axioms BerryEsseen.PhysicalSkewnessLower.central_endpoints_product_le_one
#print axioms BerryEsseen.PhysicalSkewnessLower.firstAbsoluteMoment_eq_twice_positive
#print axioms BerryEsseen.PhysicalSkewnessLower.positiveFirstMoment_le_half
#print axioms BerryEsseen.PhysicalSkewnessLower.actualJ_le_rho_add_one
#print axioms BerryEsseen.PhysicalSkewnessLower.gamma_lower
#print axioms BerryEsseen.PhysicalSkewnessLower.abs_gamma_lower_of_bounds
