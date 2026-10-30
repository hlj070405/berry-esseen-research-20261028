module

public import BerryEsseen.N26CubicHighTail
public import BerryEsseen.HighFrequencyTail
public import BerryEsseen.N26ProjectedRawAcquisition
public import BerryEsseen.P39OppositeSignEvent
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section

/-! 2026-10-30: one fixed N26/P39 periodic-tail price at b=9/4 and
w=1/4.  The actual opposite-sign event supplies mass, distance and its
conditional second moment. The two existing cubic bands are retained,
and the periodic estimate pays the entire remaining infinite ray. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators
open BerryEsseen.CharacteristicExpansion
open BerryEsseen.HighFrequencyCells BerryEsseen.HighFrequencySeries
open BerryEsseen.HighFrequencyDistance BerryEsseen.HighFrequencyZeroCell
open BerryEsseen.HighFrequencyEvent

namespace BerryEsseen.N26P39PeriodicHighTail

abbrev massFloor : ℝ := 2379 / 5000
abbrev distanceFloor : ℝ := 3 / 4
abbrev tailStart : ℝ := 9 / 4
abbrev cellWidth : ℝ := 1 / 4
abbrev secondCeiling : ℝ := 13 / 3

def cubicBandPrice : ℝ :=
  (51 / 10) * ((1 / 2) ^ 13 * (50 / 81 - 1 / 8) +
    (3 / 4) ^ 13 * (1 / 8 - 8 / 81))

lemma S3_cap : S3 ≤ (1203 : ℝ) / 1000 := by
  norm_num [S3, seriesTerm, powerKernel, Finset.sum_range_succ]

lemma S5_cap : S5 cellWidth ≤ (857 : ℝ) / 200 := by
  norm_num [S5, seriesTerm, powerKernel, cellWidth, Finset.sum_range_succ]

lemma pi_lower : (157 : ℝ) / 50 ≤ Real.pi := by
  linarith only [Real.pi_gt_d2]

lemma pi_square_lower : (157 / 50 : ℝ) ^ 2 ≤ Real.pi ^ 2 := by
  nlinarith only [pi_lower, Real.pi_pos]

lemma pi_three_halves_lower : (27789 : ℝ) / 5000 ≤ Real.pi ^ (3 / 2 : ℝ) := by
  have hs : (177 : ℝ) / 100 ≤ Real.sqrt Real.pi := by
    nlinarith only [Real.sq_sqrt Real.pi_nonneg, Real.sqrt_nonneg Real.pi, pi_lower]
  have hp := mul_le_mul pi_lower hs (by norm_num : (0 : ℝ) ≤ 177 / 100) Real.pi_nonneg
  rw [HighFrequencyPeriodic.pi_three_halves]
  norm_num at hp ⊢
  exact hp

lemma sqrt_mass_lower : (689 : ℝ) / 1000 ≤ Real.sqrt massFloor := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ massFloor)
  have hn := Real.sqrt_nonneg massFloor
  norm_num only [massFloor] at hs hn ⊢
  nlinarith only [hs, hn]

/-- Only twenty positive terms of each fixed exponential are used. -/
lemma exp_neg_periodic_le : Real.exp (-(307 : ℝ) / 50) ≤ 1 / 450 := by
  have hs := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 307 / 50) 20
  have hl : (450 : ℝ) ≤ Real.exp (307 / 50) := by
    norm_num [Finset.sum_range_succ] at hs
    linarith only [hs]
  have hm := mul_le_mul_of_nonneg_left hl (Real.exp_nonneg (-(307 : ℝ) / 50))
  have he : Real.exp (-(307 : ℝ) / 50) * Real.exp (307 / 50) = 1 := by
    rw [← Real.exp_add]
    norm_num
  rw [he] at hm
  linarith only [hm]

lemma exp_neg_eight_le : Real.exp (-(8 : ℝ)) ≤ 1 / 2800 := by
  have hs := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 8) 20
  have hl : (2800 : ℝ) ≤ Real.exp 8 := by
    norm_num [Finset.sum_range_succ] at hs
    linarith only [hs]
  have hm := mul_le_mul_of_nonneg_left hl (Real.exp_nonneg (-(8 : ℝ)))
  have he : Real.exp (-(8 : ℝ)) * Real.exp 8 = 1 := by
    rw [← Real.exp_add]
    norm_num
  rw [he] at hm
  linarith only [hm]

lemma exp_neg_zero_wing_le : Real.exp (-(71 : ℝ) / 25) ≤ 10 / 171 := by
  have hs := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 71 / 25) 20
  have hl : (171 : ℝ) / 10 ≤ Real.exp (71 / 25) := by
    norm_num [Finset.sum_range_succ] at hs
    linarith only [hs]
  have hm := mul_le_mul_of_nonneg_left hl (Real.exp_nonneg (-(71 : ℝ) / 25))
  have he : Real.exp (-(71 : ℝ) / 25) * Real.exp (71 / 25) = 1 := by
    rw [← Real.exp_add]
    norm_num
  rw [he] at hm
  linarith only [hm]

lemma periodic_main_le :
    secondCeiling / (4 * Real.pi ^ (3 / 2 : ℝ) * sineSlope cellWidth * Real.sqrt massFloor) *
      (S3 + 3 * S5 cellWidth / (26 * massFloor * sineSlope cellWidth ^ 2)) ≤ (67 : ℝ) / 500 := by
  have hh : 0 < sineSlope cellWidth := by norm_num [sineSlope, cellWidth]
  have hp : 0 < Real.pi ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos Real.pi_pos _
  have ha : 0 < Real.sqrt massFloor := Real.sqrt_pos.mpr (by norm_num)
  have hinner : S3 + 3 * S5 cellWidth / (26 * massFloor * sineSlope cellWidth ^ 2) ≤
      1203 / 1000 + 3 * (857 / 200 : ℝ) / (26 * massFloor * sineSlope cellWidth ^ 2) := by
    exact add_le_add S3_cap (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left S5_cap (by norm_num)) (by positivity))
  have hprod := mul_le_mul pi_three_halves_lower sqrt_mass_lower
    (by norm_num : (0 : ℝ) ≤ 689 / 1000) hp.le
  have hden : 4 * (27789 / 5000 : ℝ) * sineSlope cellWidth * (689 / 1000) ≤
      4 * Real.pi ^ (3 / 2 : ℝ) * sineSlope cellWidth * Real.sqrt massFloor := by
    have hm := mul_le_mul_of_nonneg_left hprod (show 0 ≤ 4 * sineSlope cellWidth by positivity)
    nlinarith only [hm]
  calc
    _ = secondCeiling *
        (S3 + 3 * S5 cellWidth / (26 * massFloor * sineSlope cellWidth ^ 2)) /
        (4 * Real.pi ^ (3 / 2 : ℝ) * sineSlope cellWidth * Real.sqrt massFloor) := by ring
    _ ≤ secondCeiling *
        (1203 / 1000 + 3 * (857 / 200 : ℝ) / (26 * massFloor * sineSlope cellWidth ^ 2)) /
        (4 * Real.pi ^ (3 / 2 : ℝ) * sineSlope cellWidth * Real.sqrt massFloor) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hinner (by norm_num)) (by positivity)
    _ ≤ secondCeiling *
        (1203 / 1000 + 3 * (857 / 200 : ℝ) / (26 * massFloor * sineSlope cellWidth ^ 2)) /
        (4 * (27789 / 5000 : ℝ) * sineSlope cellWidth * (689 / 1000)) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ ≤ _ := by norm_num [sineSlope, cellWidth, massFloor, secondCeiling]

lemma periodic_wing_le :
    secondCeiling * Real.sqrt 26 / (2 * Real.pi ^ 2) *
      Real.exp (-(26 * massFloor) * sineSlope cellWidth ^ 2 * cellWidth ^ 2) ≤ (1 : ℝ) / 400 := by
  have hrate : (307 : ℝ) / 50 ≤ 26 * massFloor * sineSlope cellWidth ^ 2 * cellWidth ^ 2 := by
    norm_num [massFloor, sineSlope, cellWidth]
  have he : Real.exp (-(26 * massFloor) * sineSlope cellWidth ^ 2 * cellWidth ^ 2) ≤ 1 / 450 := by
    apply le_trans (Real.exp_le_exp.mpr (by nlinarith only [hrate])) exp_neg_periodic_le
  have hnum := mul_le_mul_of_nonneg_left N26InitialFourierEnvelope.sqrt_twenty_six_upper
    (show (0 : ℝ) ≤ secondCeiling by norm_num)
  have hpre : secondCeiling * Real.sqrt 26 / (2 * Real.pi ^ 2) ≤
      secondCeiling * (51 / 10) / (2 * (157 / 50 : ℝ) ^ 2) := by
    calc
      _ ≤ secondCeiling * (51 / 10) / (2 * Real.pi ^ 2) :=
        div_le_div_of_nonneg_right hnum (by positivity)
      _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) (by norm_num)
        (mul_le_mul_of_nonneg_left pi_square_lower (by norm_num))
  calc
    _ ≤ (secondCeiling * (51 / 10) / (2 * (157 / 50 : ℝ) ^ 2)) * (1 / 450) :=
      mul_le_mul hpre he (Real.exp_nonneg _) (by norm_num)
    _ ≤ _ := by norm_num [secondCeiling]

lemma zero_basic_le : Zbasic 26 massFloor distanceFloor tailStart ≤ (1 : ℝ) / 40000 := by
  have hk : 0 < kappa massFloor distanceFloor := by norm_num [kappa, massFloor, distanceFloor]
  have hrate : (8 : ℝ) ≤ 26 * kappa massFloor distanceFloor * tailStart ^ 2 := by
    norm_num [kappa, massFloor, distanceFloor, tailStart]
  have he : Real.exp (-(26 * kappa massFloor distanceFloor) * tailStart ^ 2) ≤ 1 / 2800 := by
    apply le_trans (Real.exp_le_exp.mpr (by nlinarith only [hrate])) exp_neg_eight_le
  have hden := mul_le_mul_of_nonneg_left N26InitialFourierEnvelope.sqrt_twenty_six_lower
    (show 0 ≤ 2 * tailStart ^ 4 * kappa massFloor distanceFloor by positivity)
  unfold Zbasic
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 / 2800 : ℝ) /
        (2 * tailStart ^ 4 * kappa massFloor distanceFloor * Real.sqrt 26) :=
      div_le_div_of_nonneg_right he (by positivity)
    _ ≤ (1 / 2800 : ℝ) / (2 * tailStart ^ 4 * kappa massFloor distanceFloor * 5) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) hden
    _ ≤ _ := by norm_num [kappa, massFloor, distanceFloor, tailStart]

lemma zero_wing_le : wingPrice 26 massFloor tailStart ≤ (59 : ℝ) / 2000 := by
  have hrate : (71 : ℝ) / 25 ≤ 26 * massFloor * (23 / 48 : ℝ) ^ 2 := by norm_num [massFloor]
  have he : Real.exp (-(26 : ℝ) * massFloor * (23 / 48 : ℝ) ^ 2) ≤ 10 / 171 := by
    apply le_trans (Real.exp_le_exp.mpr (by nlinarith only [hrate])) exp_neg_zero_wing_le
  have hm := mul_le_mul N26InitialFourierEnvelope.sqrt_twenty_six_upper he
    (Real.exp_nonneg _) (by norm_num : (0 : ℝ) ≤ 51 / 10)
  unfold wingPrice
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ ((51 / 10 : ℝ) * (10 / 171)) / (2 * tailStart ^ 2) :=
      div_le_div_of_nonneg_right hm (by positivity)
    _ ≤ _ := by norm_num [tailStart]

/-- Four analytically proved fixed prices, with no numerical floor gate. -/
theorem periodic_basic_price_le :
    HighFrequencyTail.basicPrice 26 massFloor distanceFloor tailStart cellWidth secondCeiling ≤
      (333 : ℝ) / 2000 := by
  have hm := periodic_main_le
  have hp := periodic_wing_le
  have hz := zero_basic_le
  have hw := zero_wing_le
  unfold HighFrequencyTail.basicPrice nonzeroSlope
  simp only [Nat.cast_ofNat]
  have heq : secondCeiling *
      ((S3 + (3 / (26 * massFloor * sineSlope cellWidth ^ 2)) * S5 cellWidth) /
          (4 * Real.pi ^ (3 / 2 : ℝ) * sineSlope cellWidth * Real.sqrt massFloor) +
        Real.sqrt 26 / (2 * Real.pi ^ 2) *
          Real.exp (-(26 * massFloor) * sineSlope cellWidth ^ 2 * cellWidth ^ 2)) =
      secondCeiling / (4 * Real.pi ^ (3 / 2 : ℝ) * sineSlope cellWidth * Real.sqrt massFloor) *
        (S3 + 3 * S5 cellWidth / (26 * massFloor * sineSlope cellWidth ^ 2)) +
      secondCeiling * Real.sqrt 26 / (2 * Real.pi ^ 2) *
        Real.exp (-(26 * massFloor) * sineSlope cellWidth ^ 2 * cellWidth ^ 2) := by ring
  rw [heq]
  linarith only [hm, hp, hz, hw]

/-- Both frozen cubic bands are joined to any price on the entire far ray.
The deterministic band price is shared by the P39 and all-low-rho clients. -/
theorem cf_tail_le_two_bands_add_far (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10)
    (T : ℝ)
    (hfarPrice : Real.sqrt (26 : ℝ) * (∫ t in Ioi tailStart,
      HighFrequencyDamping.initialIntegrand μ 26 t) ≤ T) :
    IntegrableOn (HighFrequencyDamping.initialIntegrand μ 26) (Ioi HighFrequencyDamping.cutoff) ∧
      Real.sqrt (26 : ℝ) * (∫ t in Ioi HighFrequencyDamping.cutoff,
        HighFrequencyDamping.initialIntegrand μ 26 t) ≤ cubicBandPrice + T := by
  have hc : 0 < HighFrequencyDamping.cutoff := by norm_num [HighFrequencyDamping.cutoff]
  have hi := FourierSplit.integrableOn_cfQuotient_ray μ 26 HighFrequencyDamping.cutoff hc
  have hfirst := hi.mono_set
    (show Ioc HighFrequencyDamping.cutoff (2 : ℝ) ⊆ Ioi HighFrequencyDamping.cutoff from
      fun _ ht => ht.1)
  have htwo := FourierSplit.integrableOn_cfQuotient_ray μ 26 (2 : ℝ) (by norm_num)
  have hsecond := htwo.mono_set
    (show Ioc (2 : ℝ) tailStart ⊆ Ioi (2 : ℝ) from fun _ ht => ht.1)
  have hfar := FourierSplit.integrableOn_cfQuotient_ray μ 26 tailStart (by norm_num)
  have hinv := FourierSplit.integrableOn_inverse_cube_ray HighFrequencyDamping.cutoff hc
  have hinvFirst := hinv.mono_set
    (show Ioc HighFrequencyDamping.cutoff (2 : ℝ) ⊆ Ioi HighFrequencyDamping.cutoff from
      fun _ ht => ht.1)
  have hinvTwo := FourierSplit.integrableOn_inverse_cube_ray (2 : ℝ) (by norm_num)
  have hinvSecond := hinvTwo.mono_set
    (show Ioc (2 : ℝ) tailStart ⊆ Ioi (2 : ℝ) from fun _ ht => ht.1)
  have hb1 : (∫ t in Ioc HighFrequencyDamping.cutoff (2 : ℝ),
      HighFrequencyDamping.initialIntegrand μ 26 t) ≤
      (1 / 2 : ℝ) ^ 13 * ((50 : ℝ) / 81 - 1 / 8) := by
    rw [← N26CubicHighTail.inverse_cube_first_band_integral, ← integral_const_mul]
    apply integral_mono_ae hfirst (hinvFirst.const_mul ((1 / 2 : ℝ) ^ 13))
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ht0 : 0 < t := hc.trans ht.1
    have hp := N26CubicHighTail.norm_charFun_pow_le_first_band μ h hρ t
      (by exact ⟨by simpa only [HighFrequencyDamping.cutoff] using ht.1.le, ht.2⟩)
    have hd := div_le_div_of_nonneg_right hp (pow_nonneg ht0.le 3)
    change ‖charFun (μ : Measure ℝ) t ^ 26‖ / t ^ 3 ≤ (1 / 2 : ℝ) ^ 13 * (1 / t ^ 3)
    convert hd using 1 <;> ring
  have hb2 : (∫ t in Ioc (2 : ℝ) tailStart,
      HighFrequencyDamping.initialIntegrand μ 26 t) ≤
      (3 / 4 : ℝ) ^ 13 * ((1 : ℝ) / 8 - 8 / 81) := by
    rw [← N26CubicHighTail.inverse_cube_second_band_integral, ← integral_const_mul]
    apply integral_mono_ae hsecond (hinvSecond.const_mul ((3 / 4 : ℝ) ^ 13))
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ht0 : 0 < t := lt_trans (by norm_num : (0 : ℝ) < 2) ht.1
    have hp := N26CubicHighTail.norm_charFun_pow_le_second_band μ h hρ t ⟨ht.1.le, ht.2⟩
    have hd := div_le_div_of_nonneg_right hp (pow_nonneg ht0.le 3)
    change ‖charFun (μ : Measure ℝ) t ^ 26‖ / t ^ 3 ≤ (3 / 4 : ℝ) ^ 13 * (1 / t ^ 3)
    convert hd using 1 <;> ring
  have hp1 : Real.sqrt (26 : ℝ) * (∫ t in Ioc HighFrequencyDamping.cutoff (2 : ℝ),
      HighFrequencyDamping.initialIntegrand μ 26 t) ≤
      (51 / 10 : ℝ) * ((1 / 2 : ℝ) ^ 13 * ((50 : ℝ) / 81 - 1 / 8)) :=
    (mul_le_mul_of_nonneg_left hb1 (Real.sqrt_nonneg _)).trans
      (mul_le_mul_of_nonneg_right N26InitialFourierEnvelope.sqrt_twenty_six_upper (by norm_num))
  have hp2 : Real.sqrt (26 : ℝ) * (∫ t in Ioc (2 : ℝ) tailStart,
      HighFrequencyDamping.initialIntegrand μ 26 t) ≤
      (51 / 10 : ℝ) * ((3 / 4 : ℝ) ^ 13 * ((1 : ℝ) / 8 - 8 / 81)) :=
    (mul_le_mul_of_nonneg_left hb2 (Real.sqrt_nonneg _)).trans
      (mul_le_mul_of_nonneg_right N26InitialFourierEnvelope.sqrt_twenty_six_upper (by norm_num))
  have hsplit1 := setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hfirst htwo
  rw [Ioc_union_Ioi_eq_Ioi (by norm_num [HighFrequencyDamping.cutoff] :
    HighFrequencyDamping.cutoff ≤ (2 : ℝ))] at hsplit1
  have hsplit2 := setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hsecond hfar
  rw [Ioc_union_Ioi_eq_Ioi (by norm_num : (2 : ℝ) ≤ tailStart)] at hsplit2
  have htotal : Real.sqrt (26 : ℝ) * (∫ t in Ioi HighFrequencyDamping.cutoff,
      HighFrequencyDamping.initialIntegrand μ 26 t) ≤
      (51 / 10 : ℝ) * ((1 / 2 : ℝ) ^ 13 * ((50 : ℝ) / 81 - 1 / 8) +
        (3 / 4 : ℝ) ^ 13 * ((1 : ℝ) / 8 - 8 / 81)) + T := by
    rw [hsplit1, hsplit2]
    nlinarith only [hp1, hp2, hfarPrice]
  exact ⟨hi, htotal⟩

theorem cf_tail_bound_of_far_price (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10)
    (hfarPrice : Real.sqrt (26 : ℝ) * (∫ t in Ioi tailStart,
      HighFrequencyDamping.initialIntegrand μ 26 t) ≤ (333 : ℝ) / 2000) :
    IntegrableOn (HighFrequencyDamping.initialIntegrand μ 26) (Ioi HighFrequencyDamping.cutoff) ∧
      Real.sqrt (26 : ℝ) * (∫ t in Ioi HighFrequencyDamping.cutoff,
        HighFrequencyDamping.initialIntegrand μ 26 t) ≤ (17 : ℝ) / 100 := by
  have hb := cf_tail_le_two_bands_add_far μ h hρ (333 / 2000) hfarPrice
  refine ⟨hb.1, hb.2.trans ?_⟩
  norm_num [cubicBandPrice]

/-- Generic actual-event interface: all hypotheses concern the same μ,
its true product law, and its true event conditional distribution. -/
theorem cf_tail_bound_of_event (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10)
    (E : Set (ℝ × ℝ)) (hE : MeasurableSet E)
    (hpa : massFloor ≤ eventProbability μ E)
    (hD : ∀ᵐ p ∂eventLaw μ E, distanceFloor ≤ HighFrequencyEvent.distance p)
    (h2 : Integrable (fun p => HighFrequencyEvent.distance p ^ 2) (eventLaw μ E))
    (hmean : conditionalSecondMoment μ E ≤ secondCeiling) :
    IntegrableOn (HighFrequencyDamping.initialIntegrand μ 26) (Ioi HighFrequencyDamping.cutoff) ∧
      Real.sqrt (26 : ℝ) * (∫ t in Ioi HighFrequencyDamping.cutoff,
        HighFrequencyDamping.initialIntegrand μ 26 t) ≤ (17 : ℝ) / 100 := by
  have hb := (HighFrequencyTail.actual_event_tail_basic μ E hE 26 (by decide)
    massFloor distanceFloor tailStart cellWidth secondCeiling (by norm_num) hpa
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hD h2 hmean).2.2
  have hf : Real.sqrt (26 : ℝ) * (∫ t in Ioi tailStart,
      HighFrequencyDamping.initialIntegrand μ 26 t) ≤ (333 : ℝ) / 2000 :=
    hb.trans periodic_basic_price_le
  exact cf_tail_bound_of_far_price μ h hρ hf

/-- The original P39 law acquires its own defect and event; neither the
defect ceiling nor the conditional event inputs are free premises. -/
theorem original_cf_tail (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (H C : ℝ) (hm : ContactVariation.PositiveClosedMaximum μ 26 H C)
    (hprev : Extremizer.fixedNSup 25 ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10)
    (hp : CanonicalSign.p μ ∈ Icc (39 / 100 : ℝ) (2 / 5)) :
    IntegrableOn (HighFrequencyDamping.initialIntegrand μ 26) (Ioi HighFrequencyDamping.cutoff) ∧
      Real.sqrt (26 : ℝ) * (∫ t in Ioi HighFrequencyDamping.cutoff,
        HighFrequencyDamping.initialIntegrand μ 26 t) ≤ (17 : ℝ) / 100 := by
  have he := P39OppositeSignEvent.acquire μ h hρ hp
    (N26ProjectedRawAcquisition.original_defect_lt_one μ h H C hm hprev hC hρ)
  exact cf_tail_bound_of_event μ h hρ P39OppositeSignEvent.event
    he.measurable he.mass_lower he.distance_lower he.square_integrable he.second_moment_upper

theorem original_fourier_envelope (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (H C : ℝ) (hm : ContactVariation.PositiveClosedMaximum μ 26 H C)
    (hprev : Extremizer.fixedNSup 25 ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10)
    (hp : CanonicalSign.p μ ∈ Icc (39 / 100 : ℝ) (2 / 5)) :
    IntegrableOn (FourierRemainder.originalIntegrand μ 26 H) (Ioi 0) ∧
      |FourierRemainder.value μ 26 H| ≤ (509 : ℝ) / 1250 + (127 / 1500) * |H| := by
  refine ⟨FourierRemainder.integrable_originalIntegrand μ h 26 (by decide) H, ?_⟩
  have hb := N26InitialFourierEnvelope.original_value_le_of_tail μ h H C hm hprev hC hρ
    (17 / 100) (original_cf_tail μ h H C hm hprev hC hρ hp).2
  convert hb using 1 <;> ring

end BerryEsseen.N26P39PeriodicHighTail

#print axioms BerryEsseen.N26P39PeriodicHighTail.periodic_basic_price_le
#print axioms BerryEsseen.N26P39PeriodicHighTail.cf_tail_bound_of_event
#print axioms BerryEsseen.N26P39PeriodicHighTail.original_cf_tail
#print axioms BerryEsseen.N26P39PeriodicHighTail.original_fourier_envelope
