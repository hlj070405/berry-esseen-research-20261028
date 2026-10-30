module

public import BerryEsseen.Reflection
public import BerryEsseen.CommonProductMoments
public import BerryEsseen.GaussianPrices
public import BerryEsseen.AnalyticConstants
public import BerryEsseen.TwoMoment

@[expose] public section

/-! 2026-10-29: a universal closed-CDF comparison from actual first and
second moments, and the resulting high-third-moment branch at index two. -/

noncomputable section

open MeasureTheory Set

namespace BerryEsseen.UniversalCDFBound

open GaussianTools GaussianPrices GaussianMills

/-- The closed Cantelli event is bounded by an integrable square, also at `a=0`. -/
theorem closedCDF_neg_le_cantelli (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h2 : Integrable (fun y : ℝ => y ^ 2) ν)
    (hm : (∫ y : ℝ, y ∂ν) = 0) (hv : (∫ y : ℝ, y ^ 2 ∂ν) = 1)
    (a : ℝ) (ha : 0 ≤ a) : ν.real (Iic (-a)) ≤ 1 / (1 + a ^ 2) := by
  have h1 := TwoMoment.integrable_of_integrable_sq ν (fun y : ℝ => y) measurable_id h2
  have hA : Integrable (fun y : ℝ => (a * y) ^ 2) ν := by
    simpa only [mul_pow] using h2.const_mul (a ^ 2)
  have hmean : (∫ y : ℝ, a * y ∂ν) = 0 := by rw [integral_const_mul, hm, mul_zero]
  have hI := TwoMoment.integrable_shift_sq ν (fun y : ℝ => a * y) 1 (h1.const_mul a) hA
  have hInt := TwoMoment.integral_shift_sq ν (fun y : ℝ => a * y) 1
    (h1.const_mul a) hA hmean
  have hSquare : (∫ y : ℝ, (a * y - 1) ^ 2 ∂ν) = 1 + a ^ 2 := by
    rw [hInt]
    simp only [mul_pow, integral_const_mul, hv, mul_one, one_pow]
    ring
  have hden : 0 < 1 + a ^ 2 := by positivity
  have hbound : ν.real (Iic (-a)) ≤
      ∫ y : ℝ, (a * y - 1) ^ 2 / (1 + a ^ 2) ^ 2 ∂ν := by
    rw [← integral_indicator_one measurableSet_Iic]
    apply integral_mono ((integrable_const (1 : ℝ)).indicator measurableSet_Iic) (hI.div_const _)
    intro y
    by_cases hy : y ∈ Iic (-a)
    · rw [indicator_of_mem hy]
      have hxy := mul_le_mul_of_nonneg_left hy ha
      have hs : (1 + a ^ 2) ^ 2 ≤ (1 - a * y) ^ 2 :=
        (sq_le_sq₀ hden.le (by nlinarith only [hxy, hden])).mpr (by nlinarith only [hxy])
      apply (le_div_iff₀ (sq_pos_of_pos hden)).mpr
      nlinarith only [hs]
    · rw [indicator_of_notMem hy]
      exact div_nonneg (sq_nonneg _) (sq_nonneg _)
  rw [integral_div, hSquare] at hbound
  have heq : (1 + a ^ 2) / (1 + a ^ 2) ^ 2 = 1 / (1 + a ^ 2) := by
    field_simp [hden.ne']
  rwa [heq] at hbound

private lemma density_upper (t : ℝ) : phi t ≤ (2 : ℝ) / 5 := by
  have he : Real.exp (-(t ^ 2 / 2)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg t])
  rw [phi_eq_phi_zero_mul_exp]
  exact (mul_le_mul_of_nonneg_left he (phi_nonneg 0)).trans
    (by simpa only [mul_one] using phi_zero_lt_2_5.le)

/-- A whole half-line bound obtained from the actual Gaussian CDF integral. -/
theorem Phi_upper_nonneg (a : ℝ) (ha : 0 ≤ a) :
    Phi a ≤ (1 : ℝ) / 2 + (2 : ℝ) / 5 * a := by
  have hc : Continuous (fun _ : ℝ => (2 : ℝ) / 5) := continuous_const
  have hi : (∫ t in (0 : ℝ)..a, phi t) ≤ a * ((2 : ℝ) / 5) := by
    calc
      _ ≤ ∫ _ in (0 : ℝ)..a, (2 : ℝ) / 5 :=
        intervalIntegral.integral_mono_on ha (continuous_phi.intervalIntegrable 0 a)
          (hc.intervalIntegrable 0 a) (fun t _ => density_upper t)
      _ = _ := by
        simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  rw [Phi_eq_const_add_intervalIntegral, Phi_zero]
  linarith

/-- Exact rational inequalities cover all three Cantelli/Gaussian ranges. -/
theorem cantelli_gap_le (a : ℝ) (ha : 0 ≤ a) :
    1 / (1 + a ^ 2) - Phi (-a) ≤ (11 : ℝ) / 20 := by
  have hden : 0 < 1 + a ^ 2 := by positivity
  have hPhi : 0 ≤ Phi (-a) := measureReal_nonneg
  by_cases ha0 : a ≤ (1 : ℝ) / 2
  · have hsq : a ^ 2 ≤ (1 : ℝ) / 4 := by nlinarith
    have hr : 1 / (1 + a ^ 2) ≤ 1 - (4 : ℝ) / 5 * a ^ 2 := by
      apply (div_le_iff₀ hden).mpr
      nlinarith [mul_nonneg (sq_nonneg a) (show 0 ≤ (1 : ℝ) / 4 - a ^ 2 by linarith)]
    have hp := Phi_upper_nonneg a ha
    rw [Phi_neg, tail]
    nlinarith [sq_nonneg (a - 1 / 4)]
  by_cases ha1 : a ≤ 1
  · have hf : 0 ≤ a * (a - 1 / 2) * (2 - a) :=
      mul_nonneg (mul_nonneg ha (by linarith)) (by linarith)
    have hr : 1 / (1 + a ^ 2) ≤ 1 - (2 : ℝ) / 5 * a := by
      apply (div_le_iff₀ hden).mpr
      nlinarith only [hf]
    have hp := Phi_upper_nonneg a ha
    rw [Phi_neg, tail]
    linarith
  · have hr : 1 / (1 + a ^ 2) ≤ (1 : ℝ) / 2 := by
      apply (div_le_iff₀ hden).mpr
      nlinarith
    linarith

/-- No third moment, support bound, or absence of atoms is required. -/
theorem positive_closed_error (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h2 : Integrable (fun y : ℝ => y ^ 2) ν)
    (hm : (∫ y : ℝ, y ∂ν) = 0) (hv : (∫ y : ℝ, y ^ 2 ∂ν) = 1) (x : ℝ) :
    ν.real (Iic x) - Phi x ≤ (11 : ℝ) / 20 := by
  by_cases hx : 0 ≤ x
  · have hF : ν.real (Iic x) ≤ 1 := measureReal_le_one
    have hP : Phi 0 ≤ Phi x := measureReal_mono (Iic_subset_Iic.mpr hx)
    rw [Phi_zero] at hP
    linarith
  · have hc := closedCDF_neg_le_cantelli ν h2 hm hv (-x) (by linarith)
    have hg := cantelli_gap_le (-x) (by linarith)
    simp only [neg_neg] at hc hg
    linarith

/-- The actual reflected law retains both finite second moment and the two exact moments. -/
theorem reflected_moments (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h2 : Integrable (fun y : ℝ => y ^ 2) ν)
    (hm : (∫ y : ℝ, y ∂ν) = 0) (hv : (∫ y : ℝ, y ^ 2 ∂ν) = 1) :
    Integrable (fun y : ℝ => y ^ 2) (ν.map (fun y : ℝ => -y)) ∧
      (∫ y : ℝ, y ∂ν.map (fun y : ℝ => -y)) = 0 ∧
      (∫ y : ℝ, y ^ 2 ∂ν.map (fun y : ℝ => -y)) = 1 := by
  have hf : Measurable (fun y : ℝ => -y) := by fun_prop
  refine ⟨?_, ?_, ?_⟩
  · apply (integrable_map_measure (by fun_prop) hf.aemeasurable).mpr
    simpa only [Function.comp_def, neg_sq] using h2
  · rw [integral_map (f := fun y : ℝ => y) hf.aemeasurable
      measurable_id.aestronglyMeasurable, integral_neg, hm, neg_zero]
  · rw [integral_map (f := fun y : ℝ => y ^ 2) hf.aemeasurable (by fun_prop)]
    simpa only [neg_sq] using hv

/-- The open original complement is contained in the reflected closed event. -/
theorem negative_error_le_reflected_positive (ν : Measure ℝ) [IsProbabilityMeasure ν] (x : ℝ) :
    Phi x - ν.real (Iic x) ≤ (ν.map (fun y : ℝ => -y)).real (Iic (-x)) - Phi (-x) := by
  have hf : Measurable (fun y : ℝ => -y) := by fun_prop
  rw [map_measureReal_apply hf measurableSet_Iic]
  have hevent : (fun y : ℝ => -y) ⁻¹' Iic (-x) = Ici x := by ext y; simp
  rw [hevent, Phi_neg, tail]
  have hc := probReal_add_probReal_compl (μ := ν) (s := Iic x) measurableSet_Iic
  simp only [compl_Iic] at hc
  have hmono : ν.real (Ioi x) ≤ ν.real (Ici x) := measureReal_mono Ioi_subset_Ici_self
  linarith

/-- A universal bound for the actual closed CDF of any centered variance-one law. -/
theorem closedCDF_abs_error_le (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h2 : Integrable (fun y : ℝ => y ^ 2) ν)
    (hm : (∫ y : ℝ, y ∂ν) = 0) (hv : (∫ y : ℝ, y ^ 2 ∂ν) = 1) (x : ℝ) :
    |ν.real (Iic x) - Phi x| ≤ (11 : ℝ) / 20 := by
  have hp := positive_closed_error ν h2 hm hv x
  obtain ⟨hr2, hrm, hrv⟩ := reflected_moments ν h2 hm hv
  have hr := positive_closed_error (ν.map (fun y : ℝ => -y)) hr2 hrm hrv (-x)
  have hn := (negative_error_le_reflected_positive ν x).trans hr
  exact abs_le.mpr ⟨by linarith, hp⟩

/-- These moments are proved from the actual independent sum and its normalization. -/
theorem normalizedIidSumLaw_moments (μ : ProbabilityMeasure ℝ)
    (h2 : Integrable (fun y : ℝ => y ^ 2) (μ : Measure ℝ))
    (hm : (∫ y : ℝ, y ∂(μ : Measure ℝ)) = 0)
    (hv : (∫ y : ℝ, y ^ 2 ∂(μ : Measure ℝ)) = 1) (n : ℕ) (hn : 0 < n) :
    Integrable (fun y : ℝ => y) (normalizedIidSumLaw μ n) ∧
      Integrable (fun y : ℝ => y ^ 2) (normalizedIidSumLaw μ n) ∧
      (∫ y : ℝ, y ∂normalizedIidSumLaw μ n) = 0 ∧
      (∫ y : ℝ, y ^ 2 ∂normalizedIidSumLaw μ n) = 1 := by
  have h1 := TwoMoment.integrable_of_integrable_sq (μ : Measure ℝ)
    (fun y : ℝ => y) measurable_id h2
  obtain ⟨hi1, hi2, him, hiv⟩ :=
    CommonProductMoments.convPower_moments (μ : Measure ℝ) h1 h2 hm n
  rw [← MixtureSum.iidSumLaw_eq_convPower] at hi1 hi2 him hiv
  rw [hv, mul_one] at hiv
  have hid : (μ : Measure ℝ) = (μ : Measure ℝ).map (fun u : ℝ => (u - 0) / 1) := by
    simp only [sub_zero, div_one, Measure.map_id']
  have hmap : normalizedIidSumLaw μ n = (MixtureSum.iidSumLaw (μ : Measure ℝ) n).map
      (fun u : ℝ => u / Real.sqrt n) := by
    simpa only [mul_zero, sub_zero, one_mul] using
      AffineSum.normalizedIidSumLaw_eq_map μ (μ : Measure ℝ) 0 1 hid n
  have hf : Measurable (fun u : ℝ => u / Real.sqrt n) := by fun_prop
  have hs : (Real.sqrt (n : ℝ)) ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg n)
  have hn0 : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
  rw [hmap]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (integrable_map_measure measurable_id.aestronglyMeasurable hf.aemeasurable).mpr
      (hi1.div_const _)
  · apply (integrable_map_measure (by fun_prop) hf.aemeasurable).mpr
    simpa only [Function.comp_def, div_pow] using hi2.div_const ((Real.sqrt (n : ℝ)) ^ 2)
  · rw [integral_map (f := fun y : ℝ => y) hf.aemeasurable
      measurable_id.aestronglyMeasurable, integral_div, him, zero_div]
  · rw [integral_map (f := fun y : ℝ => y ^ 2) hf.aemeasurable (by fun_prop)]
    simp only [div_pow]
    rw [integral_div, hiv, hs, div_self hn0]

theorem normalizedIidSumLaw_abs_error_le (μ : ProbabilityMeasure ℝ)
    (h2 : Integrable (fun y : ℝ => y ^ 2) (μ : Measure ℝ))
    (hm : (∫ y : ℝ, y ∂(μ : Measure ℝ)) = 0)
    (hv : (∫ y : ℝ, y ^ 2 ∂(μ : Measure ℝ)) = 1) (n : ℕ) (hn : 0 < n) (x : ℝ) :
    |(normalizedIidSumLaw μ n).real (Iic x) - Phi x| ≤ (11 : ℝ) / 20 := by
  obtain ⟨_, hi2, him, hiv⟩ := normalizedIidSumLaw_moments μ h2 hm hv n hn
  exact closedCDF_abs_error_le (normalizedIidSumLaw μ n) hi2 him hiv x

theorem iid_abs_error_le (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (hn : 0 < n) (x : ℝ) :
    |(normalizedIidSumLaw μ n).real (Iic x) - Phi x| ≤ (11 : ℝ) / 20 :=
  normalizedIidSumLaw_abs_error_le μ h.integrable_square h.mean_zero h.second_moment_one n hn x

theorem two_sevenths_sqrt_two_lt_esseen : (2 : ℝ) / 7 * Real.sqrt 2 < esseenConstant := by
  have hs : Real.sqrt (2 : ℝ) ≤ 10 / 7 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  calc
    (2 : ℝ) / 7 * Real.sqrt 2 ≤ 20 / 49 := by linarith
    _ < 819 / 2000 := by norm_num
    _ < esseenConstant := AnalyticConstants.esseenConstant_gt_819_2000

/-- This covers precisely the actual `rho >= 2` branch of the original index-two target. -/
theorem high_moment_two_strict (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hρ : 2 ≤ thirdAbsoluteMoment μ) (x : ℝ) :
    |(normalizedIidSumLaw μ 2).real (Iic x) - Phi x| <
      (2 : ℝ) / 7 * thirdAbsoluteMoment μ := by
  have hu := iid_abs_error_le μ h 2 (by norm_num) x
  have hprice := mul_le_mul_of_nonneg_left hρ (by norm_num : (0 : ℝ) ≤ 2 / 7)
  linarith

theorem high_moment_two_esseen_strict (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hρ : 2 ≤ thirdAbsoluteMoment μ) (x : ℝ) :
    |(normalizedIidSumLaw μ 2).real (Iic x) - Phi x| <
      esseenConstant * thirdAbsoluteMoment μ / Real.sqrt 2 := by
  have hs : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hc : (2 : ℝ) / 7 < esseenConstant / Real.sqrt 2 :=
    (lt_div_iff₀ hs).mpr two_sevenths_sqrt_two_lt_esseen
  have hρ0 : 0 < thirdAbsoluteMoment μ := by linarith
  have hpaid := mul_lt_mul_of_pos_right hc hρ0
  calc
    _ < (2 : ℝ) / 7 * thirdAbsoluteMoment μ := high_moment_two_strict μ h hρ x
    _ < _ := by simpa only [div_mul_eq_mul_div] using hpaid

/-- The same strict branch in original, unnormalized threshold coordinates. -/
theorem high_moment_two_raw_strict (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hρ : 2 ≤ thirdAbsoluteMoment μ) (H : ℝ) :
    |(MixtureSum.iidSumLaw (μ : Measure ℝ) 2).real (Iic H) - Phi (H / Real.sqrt 2)| <
      (2 : ℝ) / 7 * thirdAbsoluteMoment μ := by
  have hb := high_moment_two_strict μ h hρ (H / Real.sqrt 2)
  rw [Reflection.normalized_closedCDF_eq_raw μ 2 (by norm_num)] at hb
  have hs : Real.sqrt (2 : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  simpa only [Nat.cast_ofNat, mul_div_cancel₀ H hs] using hb

/-- A one-sided cap wrapper with exactly the original index-two cost scale. -/
theorem high_moment_two_raw_cap (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hρ : 2 ≤ thirdAbsoluteMoment μ) (H C : ℝ)
    (hC : (2 : ℝ) / 7 * Real.sqrt 2 ≤ C) :
    (MixtureSum.iidSumLaw (μ : Measure ℝ) 2).real (Iic H) - Phi (H / Real.sqrt 2) <
      C * thirdAbsoluteMoment μ / Real.sqrt 2 := by
  have hb := high_moment_two_raw_strict μ h hρ H
  have hc : (2 : ℝ) / 7 ≤ C / Real.sqrt 2 :=
    (le_div_iff₀ (Real.sqrt_pos.mpr (by norm_num))).mpr hC
  have hpaid := mul_le_mul_of_nonneg_right hc (show 0 ≤ thirdAbsoluteMoment μ by linarith)
  have habs := le_abs_self
    ((MixtureSum.iidSumLaw (μ : Measure ℝ) 2).real (Iic H) - Phi (H / Real.sqrt 2))
  apply (habs.trans_lt hb).trans_le
  simpa only [div_mul_eq_mul_div] using hpaid

end BerryEsseen.UniversalCDFBound

#print axioms BerryEsseen.UniversalCDFBound.closedCDF_neg_le_cantelli
#print axioms BerryEsseen.UniversalCDFBound.cantelli_gap_le
#print axioms BerryEsseen.UniversalCDFBound.negative_error_le_reflected_positive
#print axioms BerryEsseen.UniversalCDFBound.closedCDF_abs_error_le
#print axioms BerryEsseen.UniversalCDFBound.normalizedIidSumLaw_moments
#print axioms BerryEsseen.UniversalCDFBound.normalizedIidSumLaw_abs_error_le
#print axioms BerryEsseen.UniversalCDFBound.high_moment_two_esseen_strict
#print axioms BerryEsseen.UniversalCDFBound.high_moment_two_raw_cap
