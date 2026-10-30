module

public import BerryEsseen.HighFrequencyEvent
public import BerryEsseen.N26P39ResourceAcquisition
public import BerryEsseen.PhysicalSkewnessLower
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-! 2026-10-30: acquire an actual independent opposite-sign event.
The nonpositive side includes zero. Its probability, restricted square
moment, conditional normalization and support separation are all obtained
from the same original standardized law. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter

namespace BerryEsseen.P39OppositeSignEvent

open CanonicalSign CentralGap NoiseCoordinates GapDefect HighFrequencyEvent

def event : Set (ℝ × ℝ) :=
  (Iic 0 ×ˢ Ioi 0) ∪ (Ioi 0 ×ˢ Iic 0)

theorem measurable_event : MeasurableSet event :=
  (measurableSet_Iic.prod measurableSet_Ioi).union
    (measurableSet_Ioi.prod measurableSet_Iic)

theorem rectangles_disjoint :
    Disjoint (Iic (0 : ℝ) ×ˢ Ioi (0 : ℝ)) (Ioi (0 : ℝ) ×ˢ Iic (0 : ℝ)) := by
  apply Set.disjoint_left.mpr
  intro z hz hw
  exact (not_lt_of_ge hz.1) hw.1

theorem eventProbability_eq (μ : ProbabilityMeasure ℝ) :
    eventProbability μ event = 2 * p μ * q μ := by
  unfold eventProbability productLaw event
  rw [measureReal_union rectangles_disjoint (measurableSet_Ioi.prod measurableSet_Iic),
    measureReal_prod_prod, measureReal_prod_prod]
  have hp : (μ : Measure ℝ).real (Ioi 0) = p μ := rfl
  have hq : (μ : Measure ℝ).real (Iic 0) = q μ :=
    (CanonicalSign.q_eq_nonpositiveWeight μ).symm
  rw [hp, hq]
  ring

theorem mass_lower (μ : ProbabilityMeasure ℝ)
    (hp : p μ ∈ Icc (39 / 100 : ℝ) (2 / 5)) :
    (2379 : ℝ) / 5000 ≤ eventProbability μ event := by
  rw [eventProbability_eq]
  have hm := mul_nonneg (sub_nonneg.mpr hp.1)
    (show 0 ≤ (61 / 100 : ℝ) - p μ by linarith [hp.2])
  unfold q
  nlinarith only [hm]

theorem eventProbability_pos (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    0 < eventProbability μ event := by
  rw [eventProbability_eq]
  exact mul_pos (mul_pos (by norm_num) (p_pos μ h)) (q_pos μ h)

theorem integrable_distance_square (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    Integrable (fun z : ℝ × ℝ => distance z ^ 2) (productLaw μ) := by
  unfold productLaw
  have hx := h.integrable_square.comp_fst (μ : Measure ℝ)
  have hy := h.integrable_square.comp_snd (μ : Measure ℝ)
  have hxy := h.integrable_mean.mul_prod h.integrable_mean
  convert (hx.add hy).sub (hxy.const_mul 2) using 1
  funext z
  dsimp [distance]
  rw [sq_abs]
  ring

theorem conditional_square_integrable (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    Integrable (fun z : ℝ × ℝ => distance z ^ 2) (eventLaw μ event) :=
  integrable_distance_square_event μ event (eventProbability_pos μ h)
    (integrable_distance_square μ h)

theorem positive_first_integral (μ : ProbabilityMeasure ℝ) :
    (∫ x in Ioi (0 : ℝ), x ∂(μ : Measure ℝ)) = positiveFirstMoment μ := by
  unfold NoiseCoordinates.positiveFirstMoment
  rw [← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    by_cases hx : 0 < x
    · simp [Set.indicator_apply, hx, max_eq_left hx.le]
    · have hn : x ≤ 0 := le_of_not_gt hx
      simp [Set.indicator_apply, hx, max_eq_right hn]

theorem nonpositive_first_integral (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    (∫ x in Iic (0 : ℝ), x ∂(μ : Measure ℝ)) = -positiveFirstMoment μ := by
  have hi := integral_add_compl (s := Ioi (0 : ℝ)) measurableSet_Ioi h.integrable_mean
  rw [compl_Ioi, positive_first_integral, h.mean_zero] at hi
  linarith only [hi]

theorem sign_second_integrals (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    (∫ x in Ioi (0 : ℝ), x ^ 2 ∂(μ : Measure ℝ)) =
        (1 + SignedMoment.signedSecondMoment μ) / 2 ∧
      (∫ x in Iic (0 : ℝ), x ^ 2 ∂(μ : Measure ℝ)) =
        (1 - SignedMoment.signedSecondMoment μ) / 2 := by
  have hsum := integral_add_compl (s := Ioi (0 : ℝ)) measurableSet_Ioi h.integrable_square
  rw [compl_Ioi, h.second_moment_one] at hsum
  have hsign := integral_add_compl (s := Ioi (0 : ℝ)) measurableSet_Ioi
    (SignedMoment.integrable_signedSecondMoment μ h)
  rw [compl_Ioi] at hsign
  have hp : (∫ x in Ioi (0 : ℝ), x * |x| ∂(μ : Measure ℝ)) =
      ∫ x in Ioi (0 : ℝ), x ^ 2 ∂(μ : Measure ℝ) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    change x * |x| = x ^ 2
    rw [abs_of_pos hx]
    ring
  have hn : (∫ x in Iic (0 : ℝ), x * |x| ∂(μ : Measure ℝ)) =
      -(∫ x in Iic (0 : ℝ), x ^ 2 ∂(μ : Measure ℝ)) := by
    rw [← integral_neg]
    apply setIntegral_congr_fun measurableSet_Iic
    intro x hx
    change x * |x| = -(x ^ 2)
    rw [abs_of_nonpos hx]
    ring
  rw [hp, hn] at hsign
  change _ = SignedMoment.signedSecondMoment μ at hsign
  constructor <;> linarith only [hsum, hsign]

theorem rectangle_distance_square_integral (μ : ProbabilityMeasure ℝ)
    (h : StandardizedLaw μ) (s t : Set ℝ) :
    (∫ z in s ×ˢ t, distance z ^ 2 ∂productLaw μ) =
      (∫ x in s, x ^ 2 ∂(μ : Measure ℝ)) * (μ : Measure ℝ).real t -
        2 * ((∫ x in s, x ∂(μ : Measure ℝ)) * (∫ y in t, y ∂(μ : Measure ℝ))) +
      (μ : Measure ℝ).real s * (∫ y in t, y ^ 2 ∂(μ : Measure ℝ)) := by
  unfold productLaw
  have hA := (h.integrable_square.mul_prod
    (integrable_const (1 : ℝ) : Integrable (fun _ : ℝ => (1 : ℝ)) (μ : Measure ℝ))).restrict
      (s := s ×ˢ t)
  have hB := (h.integrable_mean.mul_prod h.integrable_mean).const_mul (2 : ℝ)
  have hC := ((integrable_const (1 : ℝ) : Integrable (fun _ : ℝ => (1 : ℝ)) (μ : Measure ℝ)).mul_prod
    h.integrable_square).restrict (s := s ×ˢ t)
  have hAB : Integrable (fun z : ℝ × ℝ => z.1 ^ 2 * 1 - 2 * (z.1 * z.2))
      (((μ : Measure ℝ).prod (μ : Measure ℝ)).restrict (s ×ˢ t)) :=
    hA.sub hB.restrict
  have heq : (fun z : ℝ × ℝ => distance z ^ 2) =
      (fun z : ℝ × ℝ => z.1 ^ 2 * 1 - 2 * (z.1 * z.2) + 1 * z.2 ^ 2) := by
    funext z
    rw [distance, sq_abs]
    ring
  rw [heq, integral_add hAB hC, integral_sub hA hB.restrict, integral_const_mul]
  rw [setIntegral_prod_mul (μ := (μ : Measure ℝ)) (ν := (μ : Measure ℝ))
      (fun x : ℝ => x ^ 2) (fun _ : ℝ => 1) s t,
    setIntegral_prod_mul (μ := (μ : Measure ℝ)) (ν := (μ : Measure ℝ))
      (fun x : ℝ => x) (fun y : ℝ => y) s t,
    setIntegral_prod_mul (μ := (μ : Measure ℝ)) (ν := (μ : Measure ℝ))
      (fun _ : ℝ => 1) (fun y : ℝ => y ^ 2) s t]
  simp only [setIntegral_const, smul_eq_mul, mul_one]

/-- The cross term is positive: the nonpositive first moment equals -m. -/
theorem restricted_distance_square_integral (μ : ProbabilityMeasure ℝ)
    (h : StandardizedLaw μ) :
    (∫ z in event, distance z ^ 2 ∂productLaw μ) =
      1 + SignedMoment.signedSecondMoment μ * (q μ - p μ) +
        4 * positiveFirstMoment μ ^ 2 := by
  have hi := integrable_distance_square μ h
  unfold event
  rw [setIntegral_union rectangles_disjoint (measurableSet_Ioi.prod measurableSet_Iic)
    hi.integrableOn hi.integrableOn,
    rectangle_distance_square_integral μ h, rectangle_distance_square_integral μ h,
    positive_first_integral, nonpositive_first_integral μ h,
    (sign_second_integrals μ h).1, (sign_second_integrals μ h).2]
  have hp : (μ : Measure ℝ).real (Ioi 0) = p μ := rfl
  have hq : (μ : Measure ℝ).real (Iic 0) = q μ :=
    (CanonicalSign.q_eq_nonpositiveWeight μ).symm
  rw [hp, hq]
  unfold q
  ring

theorem conditionalSecondMoment_eq (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    conditionalSecondMoment μ event =
      (1 + SignedMoment.signedSecondMoment μ * (q μ - p μ) +
        4 * positiveFirstMoment μ ^ 2) / (2 * p μ * q μ) := by
  rw [conditionalSecondMoment_normalization, eventProbability_eq,
    restricted_distance_square_integral μ h, div_eq_mul_inv]
  ring

theorem conditionalSecondMoment_le (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10)
    (hp : p μ ∈ Icc (39 / 100 : ℝ) (2 / 5)) :
    conditionalSecondMoment μ event ≤ (13 : ℝ) / 3 := by
  rw [conditionalSecondMoment_eq μ h]
  apply (div_le_iff₀ (show 0 < 2 * p μ * q μ by
    exact mul_pos (mul_pos (by norm_num) (p_pos μ h)) (q_pos μ h))).mpr
  have hm := PhysicalSkewnessLower.positiveFirstMoment_le_half μ h
  have hm0 := positiveFirstMoment_pos μ h
  have hm2 : positiveFirstMoment μ ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
    exact (sq_le_sq₀ hm0.le (by norm_num : (0 : ℝ) ≤ 1 / 2)).mpr hm
  have hb := (SignedMoment.abs_signed_lt_127_500 μ h hρ).le
  have hqp0 : 0 ≤ q μ - p μ := by unfold q; linarith [hp.2]
  have hqp : q μ - p μ ≤ (11 : ℝ) / 50 := by unfold q; linarith [hp.1]
  have hβqp := mul_le_mul_of_nonneg_right ((le_abs_self _).trans hb) hqp0
  have hqp' := mul_le_mul_of_nonneg_left hqp (show 0 ≤ (127 : ℝ) / 500 by norm_num)
  have hmass := mass_lower μ hp
  rw [eventProbability_eq] at hmass
  nlinarith only [hm2, hβqp, hqp', hmass]

theorem zero_absent_of_defect_lt_one (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hD : actualPhysicalDefect μ < 1) : (0 : ℝ) ∉ (μ : Measure ℝ).support := by
  apply zero_notMem_support_of_defect_small μ h
  have hr := Extremizer.thirdAbsoluteMoment_ge_one μ h
  have hs := N26P39ResourceAcquisition.sqrt_ten_lower
  have hm := mul_nonneg (show 0 ≤ Real.sqrt 10 - 1 by linarith only [hs])
    (sub_nonneg.mpr hr)
  nlinarith only [hD, hs, hm]

theorem endpoints_of_defect_lt_one (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hp : p μ ∈ Icc (39 / 100 : ℝ) (2 / 5))
    (hz : (0 : ℝ) ∉ (μ : Measure ℝ).support) (hD : actualPhysicalDefect μ < 1) :
    (55 : ℝ) / 183 < Aminus μ ∧ (11 : ℝ) / 24 < Aplus μ := by
  obtain ⟨hm, hp'⟩ := N26P39ResourceAcquisition.endpoint_costs μ h hz
  have hr := Extremizer.thirdAbsoluteMoment_ge_one μ h
  have hs := N26P39ResourceAcquisition.sqrt_ten_lower
  have hbase : (21 : ℝ) / 10 ≤ (Real.sqrt 10 - 1) * thirdAbsoluteMoment μ := by
    nlinarith only [hs, mul_nonneg
      (show 0 ≤ Real.sqrt 10 - 1 by linarith only [hs]) (sub_nonneg.mpr hr)]
  have hq : q μ ≤ (61 : ℝ) / 100 := by unfold q; linarith [hp.1]
  have hqm := mul_le_mul_of_nonneg_right hq (Aminus_nonneg μ h)
  have hpp := mul_le_mul_of_nonneg_right hp.2 (Aplus_nonneg μ h)
  constructor <;> nlinarith only [hm, hp', hbase, hD, hqm, hpp]

theorem conditional_distance_lower (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hp : p μ ∈ Icc (39 / 100 : ℝ) (2 / 5))
    (hz : (0 : ℝ) ∉ (μ : Measure ℝ).support) (hD : actualPhysicalDefect μ < 1) :
    ∀ᵐ z ∂eventLaw μ event, (3 : ℝ) / 4 ≤ distance z := by
  have he := endpoints_of_defect_lt_one μ h hp hz hD
  have hsep : (3 : ℝ) / 4 ≤ Aminus μ + Aplus μ := by linarith [he.1, he.2]
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
  have hmem : ∀ᵐ z ∂eventLaw μ event, z ∈ event := ae_cond_mem measurable_event
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
  mass_lower : (2379 : ℝ) / 5000 ≤ eventProbability μ event
  distance_lower : ∀ᵐ z ∂eventLaw μ event, (3 : ℝ) / 4 ≤ distance z
  square_integrable : Integrable (fun z : ℝ × ℝ => distance z ^ 2) (eventLaw μ event)
  second_moment_upper : conditionalSecondMoment μ event ≤ (13 : ℝ) / 3

/-- All five event licenses are acquired from the original law. The actual
defect premise is explicit; no stored row or freely supplied event mass is used. -/
theorem acquire (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10)
    (hp : p μ ∈ Icc (39 / 100 : ℝ) (2 / 5)) (hD : actualPhysicalDefect μ < 1) :
    Acquired μ :=
  ⟨measurable_event, mass_lower μ hp,
    conditional_distance_lower μ h hp (zero_absent_of_defect_lt_one μ h hD) hD,
    conditional_square_integrable μ h, conditionalSecondMoment_le μ h hρ hp⟩

end BerryEsseen.P39OppositeSignEvent

#print axioms BerryEsseen.P39OppositeSignEvent.eventProbability_eq
#print axioms BerryEsseen.P39OppositeSignEvent.restricted_distance_square_integral
#print axioms BerryEsseen.P39OppositeSignEvent.conditionalSecondMoment_eq
#print axioms BerryEsseen.P39OppositeSignEvent.acquire
