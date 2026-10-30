module

public import BerryEsseen.P39OppositeSignEvent
public import BerryEsseen.LowMomentSignProbabilityBand

@[expose] public section

/-! 2026-10-30: acquire the same actual independent opposite-sign event
on the entire low-third-moment domain. Both sign probabilities are
derived from the original moment bound, without an incoming sign row. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter

namespace BerryEsseen.LowMomentOppositeSignEvent

open CanonicalSign CentralGap NoiseCoordinates GapDefect HighFrequencyEvent

abbrev event : Set (ℝ × ℝ) := P39OppositeSignEvent.event

theorem mass_lower (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) :
    (2331 : ℝ) / 5000 ≤ eventProbability μ event := by
  rw [P39OppositeSignEvent.eventProbability_eq]
  have hp := LowMomentSignProbabilityBand.p_mem_Icc_37_100_63_100 μ h hρ
  have hm := mul_nonneg (sub_nonneg.mpr hp.1) (sub_nonneg.mpr hp.2)
  unfold q
  nlinarith only [hm]

theorem conditionalSecondMoment_le (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) :
    conditionalSecondMoment μ event ≤ (9 : ℝ) / 2 := by
  rw [P39OppositeSignEvent.conditionalSecondMoment_eq μ h]
  apply (div_le_iff₀ (show 0 < 2 * p μ * q μ by
    exact mul_pos (mul_pos (by norm_num) (p_pos μ h)) (q_pos μ h))).mpr
  have hp := LowMomentSignProbabilityBand.p_mem_Icc_37_100_63_100 μ h hρ
  have hdiff : |q μ - p μ| ≤ (13 : ℝ) / 50 := by
    apply abs_le.mpr
    unfold q
    constructor <;> linarith only [hp.1, hp.2]
  have hβ := (SignedMoment.abs_signed_lt_127_500 μ h hρ).le
  have hβdiff : SignedMoment.signedSecondMoment μ * (q μ - p μ) ≤
      (127 / 500 : ℝ) * (13 / 50) := by
    calc
      _ ≤ |SignedMoment.signedSecondMoment μ * (q μ - p μ)| := le_abs_self _
      _ = |SignedMoment.signedSecondMoment μ| * |q μ - p μ| := abs_mul _ _
      _ ≤ _ := mul_le_mul hβ hdiff (abs_nonneg _) (by norm_num)
  have hm := PhysicalSkewnessLower.positiveFirstMoment_le_half μ h
  have hm0 := positiveFirstMoment_pos μ h
  have hm2 : positiveFirstMoment μ ^ 2 ≤ (1 / 2 : ℝ) ^ 2 :=
    (sq_le_sq₀ hm0.le (by norm_num : (0 : ℝ) ≤ 1 / 2)).mpr hm
  have hmass := mass_lower μ h hρ
  rw [P39OppositeSignEvent.eventProbability_eq] at hmass
  nlinarith only [hβdiff, hm2, hmass]

theorem endpoints_of_defect_lt_one (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) (hD : actualPhysicalDefect μ < 1) :
    (55 : ℝ) / 189 < Aminus μ ∧ (55 : ℝ) / 189 < Aplus μ := by
  have hz := P39OppositeSignEvent.zero_absent_of_defect_lt_one μ h hD
  obtain ⟨hm, hp⟩ := N26P39ResourceAcquisition.endpoint_costs μ h hz
  have hr := Extremizer.thirdAbsoluteMoment_ge_one μ h
  have hs := N26P39ResourceAcquisition.sqrt_ten_lower
  have hbase : (21 : ℝ) / 10 ≤ (Real.sqrt 10 - 1) * thirdAbsoluteMoment μ := by
    nlinarith only [hs, mul_nonneg
      (show 0 ≤ Real.sqrt 10 - 1 by linarith only [hs]) (sub_nonneg.mpr hr)]
  have hpband := LowMomentSignProbabilityBand.p_mem_Icc_37_100_63_100 μ h hρ
  have hqband := LowMomentSignProbabilityBand.q_mem_Icc_37_100_63_100 μ h hρ
  have hqm := mul_le_mul_of_nonneg_right hqband.2 (Aminus_nonneg μ h)
  have hpp := mul_le_mul_of_nonneg_right hpband.2 (Aplus_nonneg μ h)
  constructor <;> nlinarith only [hm, hp, hbase, hD, hqm, hpp]

theorem conditional_distance_lower (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) (hD : actualPhysicalDefect μ < 1) :
    ∀ᵐ z ∂eventLaw μ event, (29 : ℝ) / 50 ≤ distance z := by
  have he := endpoints_of_defect_lt_one μ h hρ hD
  have hsep : (29 : ℝ) / 50 ≤ Aminus μ + Aplus μ := by linarith [he.1, he.2]
  have hsp : ∀ᵐ z ∂productLaw μ,
      z.1 ∈ (μ : Measure ℝ).support ∧ z.2 ∈ (μ : Measure ℝ).support := by
    apply (Measure.ae_prod_iff_ae_ae
      (((μ : Measure ℝ).isClosed_support.measurableSet.preimage measurable_fst).inter
        ((μ : Measure ℝ).isClosed_support.measurableSet.preimage measurable_snd))).mpr
    filter_upwards [(μ : Measure ℝ).support_mem_ae] with x hx
    filter_upwards [(μ : Measure ℝ).support_mem_ae] with y hy
    exact ⟨hx, hy⟩
  have hsp' : ∀ᵐ z ∂eventLaw μ event,
      z.1 ∈ (μ : Measure ℝ).support ∧ z.2 ∈ (μ : Measure ℝ).support :=
    ProbabilityTheory.cond_absolutelyContinuous.ae_le hsp
  have hmem : ∀ᵐ z ∂eventLaw μ event, z ∈ event :=
    ae_cond_mem P39OppositeSignEvent.measurable_event
  filter_upwards [hsp', hmem] with z hzsp hze
  rcases hze with hzxy | hzyx
  · have hx := support_nonpositive_le μ z.1 hzsp.1 hzxy.1
    have hy := Aplus_le_support_nonnegative μ z.2 hzsp.2 hzxy.2.le
    rw [distance, abs_of_nonpos (by linarith [hzxy.1, hzxy.2] : z.1 - z.2 ≤ 0)]
    linarith only [hx, hy, hsep]
  · have hx := Aplus_le_support_nonnegative μ z.1 hzsp.1 hzyx.1.le
    have hy := support_nonpositive_le μ z.2 hzsp.2 hzyx.2
    rw [distance, abs_of_nonneg (by linarith [hzyx.1, hzyx.2] : 0 ≤ z.1 - z.2)]
    linarith only [hx, hy, hsep]

structure Acquired (μ : ProbabilityMeasure ℝ) : Prop where
  measurable : MeasurableSet event
  mass_lower : (2331 : ℝ) / 5000 ≤ eventProbability μ event
  distance_lower : ∀ᵐ z ∂eventLaw μ event, (29 : ℝ) / 50 ≤ distance z
  square_integrable : Integrable (fun z : ℝ × ℝ => distance z ^ 2) (eventLaw μ event)
  second_moment_upper : conditionalSecondMoment μ event ≤ (9 : ℝ) / 2

/-- The event tuple needs no free sign-probability, mass or conditional-moment premise. -/
theorem acquire (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) (hD : actualPhysicalDefect μ < 1) :
    Acquired μ :=
  ⟨P39OppositeSignEvent.measurable_event, mass_lower μ h hρ,
    conditional_distance_lower μ h hρ hD,
    P39OppositeSignEvent.conditional_square_integrable μ h,
    conditionalSecondMoment_le μ h hρ⟩

end BerryEsseen.LowMomentOppositeSignEvent

#print axioms BerryEsseen.LowMomentOppositeSignEvent.mass_lower
#print axioms BerryEsseen.LowMomentOppositeSignEvent.conditionalSecondMoment_le
#print axioms BerryEsseen.LowMomentOppositeSignEvent.endpoints_of_defect_lt_one
#print axioms BerryEsseen.LowMomentOppositeSignEvent.acquire
