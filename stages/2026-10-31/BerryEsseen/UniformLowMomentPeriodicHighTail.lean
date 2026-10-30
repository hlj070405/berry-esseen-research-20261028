module

public import BerryEsseen.N26P39PeriodicHighTail
public import BerryEsseen.HighFrequencyTailFloor
public import BerryEsseen.ScaledPowerFloor
public import BerryEsseen.LowMomentOppositeSignEvent
public import BerryEsseen.UniformLowMomentRawAcquisition

@[expose] public section

/-! 2026-10-30: uniform periodic high tails for each actual integer n >= 26.
Only four deterministic prices use floor 26. The actual CF, opposite-sign
event, marginal, maximum and full predecessor keep the actual index n. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators
open BerryEsseen.CharacteristicExpansion
open BerryEsseen.HighFrequencyCells BerryEsseen.HighFrequencySeries
open BerryEsseen.HighFrequencyDistance BerryEsseen.HighFrequencyZeroCell
open BerryEsseen.HighFrequencyEvent

namespace BerryEsseen.UniformLowMomentPeriodicHighTail

abbrev massFloor : ℝ := 2331 / 5000
abbrev distanceFloor : ℝ := 29 / 50
abbrev tailStart : ℝ := 9 / 4
abbrev cellWidth : ℝ := 1 / 4
abbrev secondCeiling : ℝ := 9 / 2

def cubicBandPrice : ℝ :=
  (51 / 10) * ((1 / 2) ^ 13 * (50 / 81 - 1 / 8) +
    (3 / 4) ^ 13 * (1 / 8 - 8 / 81))

lemma S3_cap : S3 ≤ (1203 : ℝ) / 1000 := N26P39PeriodicHighTail.S3_cap
lemma S5_cap : S5 cellWidth ≤ (857 : ℝ) / 200 := N26P39PeriodicHighTail.S5_cap
lemma pi_lower : (157 : ℝ) / 50 ≤ Real.pi := N26P39PeriodicHighTail.pi_lower
lemma pi_square_lower : (157 / 50 : ℝ) ^ 2 ≤ Real.pi ^ 2 := N26P39PeriodicHighTail.pi_square_lower
lemma pi_three_halves_lower : (27789 : ℝ) / 5000 ≤ Real.pi ^ (3 / 2 : ℝ) :=
  N26P39PeriodicHighTail.pi_three_halves_lower

lemma sqrt_mass_lower : (682 : ℝ) / 1000 ≤ Real.sqrt massFloor := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ massFloor)
  have hn := Real.sqrt_nonneg massFloor
  norm_num only [massFloor] at hs hn ⊢
  nlinarith only [hs, hn]

/-- Only twenty positive terms of each fixed exponential are used. -/
lemma exp_neg_periodic_le : Real.exp (-(601 : ℝ) / 100) ≤ 1 / 400 := by
  have hs := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 601 / 100) 20
  have hl : (400 : ℝ) ≤ Real.exp (601 / 100) := by
    norm_num [Finset.sum_range_succ] at hs
    linarith only [hs]
  have hm := mul_le_mul_of_nonneg_left hl (Real.exp_nonneg (-(601 : ℝ) / 100))
  have he : Real.exp (-(601 : ℝ) / 100) * Real.exp (601 / 100) = 1 := by
    rw [← Real.exp_add]
    norm_num
  rw [he] at hm
  linarith only [hm]

lemma exp_neg_zero_le : Real.exp (-(47 : ℝ) / 10) ≤ 1 / 109 := by
  have hs := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 47 / 10) 20
  have hl : (109 : ℝ) ≤ Real.exp (47 / 10) := by
    norm_num [Finset.sum_range_succ] at hs
    linarith only [hs]
  have hm := mul_le_mul_of_nonneg_left hl (Real.exp_nonneg (-(47 : ℝ) / 10))
  have he : Real.exp (-(47 : ℝ) / 10) * Real.exp (47 / 10) = 1 := by
    rw [← Real.exp_add]
    norm_num
  rw [he] at hm
  linarith only [hm]

lemma exp_neg_zero_wing_le : Real.exp (-(139 : ℝ) / 50) ≤ 1 / 16 := by
  have hs := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 139 / 50) 20
  have hl : (16 : ℝ) ≤ Real.exp (139 / 50) := by
    norm_num [Finset.sum_range_succ] at hs
    linarith only [hs]
  have hm := mul_le_mul_of_nonneg_left hl (Real.exp_nonneg (-(139 : ℝ) / 50))
  have he : Real.exp (-(139 : ℝ) / 50) * Real.exp (139 / 50) = 1 := by
    rw [← Real.exp_add]
    norm_num
  rw [he] at hm
  linarith only [hm]

lemma periodic_main_le :
    secondCeiling / (4 * Real.pi ^ (3 / 2 : ℝ) * sineSlope cellWidth * Real.sqrt massFloor) *
      (S3 + 3 * S5 cellWidth / (26 * massFloor * sineSlope cellWidth ^ 2)) ≤ (141 : ℝ) / 1000 := by
  have hh : 0 < sineSlope cellWidth := by norm_num [sineSlope, cellWidth]
  have hp : 0 < Real.pi ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos Real.pi_pos _
  have ha : 0 < Real.sqrt massFloor := Real.sqrt_pos.mpr (by norm_num)
  have hinner : S3 + 3 * S5 cellWidth / (26 * massFloor * sineSlope cellWidth ^ 2) ≤
      1203 / 1000 + 3 * (857 / 200 : ℝ) / (26 * massFloor * sineSlope cellWidth ^ 2) := by
    exact add_le_add S3_cap (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left S5_cap (by norm_num)) (by positivity))
  have hprod := mul_le_mul pi_three_halves_lower sqrt_mass_lower
    (by norm_num : (0 : ℝ) ≤ 682 / 1000) hp.le
  have hden : 4 * (27789 / 5000 : ℝ) * sineSlope cellWidth * (682 / 1000) ≤
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
        (4 * (27789 / 5000 : ℝ) * sineSlope cellWidth * (682 / 1000)) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ ≤ _ := by norm_num [sineSlope, cellWidth, massFloor, secondCeiling]

lemma periodic_wing_le :
    secondCeiling * Real.sqrt 26 / (2 * Real.pi ^ 2) *
      Real.exp (-(26 * massFloor) * sineSlope cellWidth ^ 2 * cellWidth ^ 2) ≤ (3 : ℝ) / 1000 := by
  have hrate : (601 : ℝ) / 100 ≤ 26 * massFloor * sineSlope cellWidth ^ 2 * cellWidth ^ 2 := by
    norm_num [massFloor, sineSlope, cellWidth]
  have he : Real.exp (-(26 * massFloor) * sineSlope cellWidth ^ 2 * cellWidth ^ 2) ≤ 1 / 400 := by
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
    _ ≤ (secondCeiling * (51 / 10) / (2 * (157 / 50 : ℝ) ^ 2)) * (1 / 400) :=
      mul_le_mul hpre he (Real.exp_nonneg _) (by norm_num)
    _ ≤ _ := by norm_num [secondCeiling]

lemma zero_basic_le : Zbasic 26 massFloor distanceFloor tailStart ≤ (1 : ℝ) / 1000 := by
  have hk : 0 < kappa massFloor distanceFloor := by norm_num [kappa, massFloor, distanceFloor]
  have hrate : (47 : ℝ) / 10 ≤ 26 * kappa massFloor distanceFloor * tailStart ^ 2 := by
    norm_num [kappa, massFloor, distanceFloor, tailStart]
  have he : Real.exp (-(26 * kappa massFloor distanceFloor) * tailStart ^ 2) ≤ 1 / 109 := by
    apply le_trans (Real.exp_le_exp.mpr (by nlinarith only [hrate])) exp_neg_zero_le
  have hden := mul_le_mul_of_nonneg_left N26InitialFourierEnvelope.sqrt_twenty_six_lower
    (show 0 ≤ 2 * tailStart ^ 4 * kappa massFloor distanceFloor by positivity)
  unfold Zbasic
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 / 109 : ℝ) /
        (2 * tailStart ^ 4 * kappa massFloor distanceFloor * Real.sqrt 26) :=
      div_le_div_of_nonneg_right he (by positivity)
    _ ≤ (1 / 109 : ℝ) / (2 * tailStart ^ 4 * kappa massFloor distanceFloor * 5) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) hden
    _ ≤ _ := by norm_num [kappa, massFloor, distanceFloor, tailStart]

lemma zero_wing_le : wingPrice 26 massFloor tailStart ≤ (63 : ℝ) / 2000 := by
  have hrate : (139 : ℝ) / 50 ≤ 26 * massFloor * (23 / 48 : ℝ) ^ 2 := by norm_num [massFloor]
  have he : Real.exp (-(26 : ℝ) * massFloor * (23 / 48 : ℝ) ^ 2) ≤ 1 / 16 := by
    apply le_trans (Real.exp_le_exp.mpr (by nlinarith only [hrate])) exp_neg_zero_wing_le
  have hm := mul_le_mul N26InitialFourierEnvelope.sqrt_twenty_six_upper he
    (Real.exp_nonneg _) (by norm_num : (0 : ℝ) ≤ 51 / 10)
  unfold wingPrice
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ ((51 / 10 : ℝ) * (1 / 16)) / (2 * tailStart ^ 2) :=
      div_le_div_of_nonneg_right hm (by positivity)
    _ ≤ _ := by norm_num [tailStart]

/-- Four analytically proved fixed prices, with no numerical floor gate. -/
theorem periodic_basic_price_le :
    HighFrequencyTail.basicPrice 26 massFloor distanceFloor tailStart cellWidth secondCeiling ≤
      (353 : ℝ) / 2000 := by
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

/-- The square-root normalization is retained when the true modulus is
compared at floor 26. The index 26 is only a deterministic power price. -/
theorem scaled_norm_charFun_pow_le_floor (μ : ProbabilityMeasure ℝ)
    (n : ℕ) (hn : 26 ≤ n) (t : ℝ)
    (hq : ‖charFun (μ : Measure ℝ) t‖ ^ 2 ≤ 3 / 4) :
    Real.sqrt n * ‖charFun (μ : Measure ℝ) t ^ n‖ ≤
      Real.sqrt 26 * ‖charFun (μ : Measure ℝ) t ^ 26‖ := by
  simpa only [norm_pow, Nat.cast_ofNat] using ScaledPowerFloor.sqrt_mul_pow_le_floor
    ‖charFun (μ : Measure ℝ) t‖ (norm_nonneg _) hq 26 n (by decide) hn

theorem scaled_first_band (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10)
    (n : ℕ) (hn : 26 ≤ n) (t : ℝ) (ht : t ∈ Icc (9 / 10 : ℝ) 2) :
    Real.sqrt n * ‖charFun (μ : Measure ℝ) t ^ n‖ ≤
      (51 / 10 : ℝ) * (1 / 2 : ℝ) ^ 13 := by
  have hq := N26CubicHighTail.norm_charFun_sq_le_first_band μ h hρ t ht
  have hp := scaled_norm_charFun_pow_le_floor μ n hn t (hq.trans (by norm_num))
  exact hp.trans ((mul_le_mul_of_nonneg_left
    (N26CubicHighTail.norm_charFun_pow_le_first_band μ h hρ t ht) (Real.sqrt_nonneg _)).trans
      (mul_le_mul_of_nonneg_right N26InitialFourierEnvelope.sqrt_twenty_six_upper (by positivity)))

theorem scaled_second_band (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10)
    (n : ℕ) (hn : 26 ≤ n) (t : ℝ) (ht : t ∈ Icc (2 : ℝ) tailStart) :
    Real.sqrt n * ‖charFun (μ : Measure ℝ) t ^ n‖ ≤
      (51 / 10 : ℝ) * (3 / 4 : ℝ) ^ 13 := by
  have hq := N26CubicHighTail.norm_charFun_sq_le_second_band μ h hρ t ht
  have hp := scaled_norm_charFun_pow_le_floor μ n hn t hq
  exact hp.trans ((mul_le_mul_of_nonneg_left
    (N26CubicHighTail.norm_charFun_pow_le_second_band μ h hρ t ht) (Real.sqrt_nonneg _)).trans
      (mul_le_mul_of_nonneg_right N26InitialFourierEnvelope.sqrt_twenty_six_upper (by positivity)))

/-- The complete scaled actual CF tail includes both finite bands and the
entire far ray, all at the same actual n. -/
theorem cf_tail_bound_of_far_price (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) (n : ℕ) (hn : 26 ≤ n)
    (hfarPrice : Real.sqrt n * (∫ t in Ioi tailStart,
      HighFrequencyDamping.initialIntegrand μ n t) ≤ (353 : ℝ) / 2000) :
    IntegrableOn (HighFrequencyDamping.initialIntegrand μ n) (Ioi HighFrequencyDamping.cutoff) ∧
      Real.sqrt n * (∫ t in Ioi HighFrequencyDamping.cutoff,
        HighFrequencyDamping.initialIntegrand μ n t) ≤ (9 : ℝ) / 50 := by
  have hc : 0 < HighFrequencyDamping.cutoff := by norm_num [HighFrequencyDamping.cutoff]
  have hi := FourierSplit.integrableOn_cfQuotient_ray μ n HighFrequencyDamping.cutoff hc
  have hfirst := hi.mono_set
    (show Ioc HighFrequencyDamping.cutoff (2 : ℝ) ⊆ Ioi HighFrequencyDamping.cutoff from
      fun _ ht => ht.1)
  have htwo := FourierSplit.integrableOn_cfQuotient_ray μ n (2 : ℝ) (by norm_num)
  have hsecond := htwo.mono_set
    (show Ioc (2 : ℝ) tailStart ⊆ Ioi (2 : ℝ) from fun _ ht => ht.1)
  have hfar := FourierSplit.integrableOn_cfQuotient_ray μ n tailStart (by norm_num)
  have hinv := FourierSplit.integrableOn_inverse_cube_ray HighFrequencyDamping.cutoff hc
  have hinvFirst := hinv.mono_set
    (show Ioc HighFrequencyDamping.cutoff (2 : ℝ) ⊆ Ioi HighFrequencyDamping.cutoff from
      fun _ ht => ht.1)
  have hinvTwo := FourierSplit.integrableOn_inverse_cube_ray (2 : ℝ) (by norm_num)
  have hinvSecond := hinvTwo.mono_set
    (show Ioc (2 : ℝ) tailStart ⊆ Ioi (2 : ℝ) from fun _ ht => ht.1)
  have hp1 : Real.sqrt n * (∫ t in Ioc HighFrequencyDamping.cutoff (2 : ℝ),
      HighFrequencyDamping.initialIntegrand μ n t) ≤
      ((51 / 10 : ℝ) * (1 / 2 : ℝ) ^ 13) * ((50 : ℝ) / 81 - 1 / 8) := by
    calc
      _ = ∫ t in Ioc HighFrequencyDamping.cutoff (2 : ℝ),
          Real.sqrt n * HighFrequencyDamping.initialIntegrand μ n t := (integral_const_mul _ _).symm
      _ ≤ ∫ t in Ioc HighFrequencyDamping.cutoff (2 : ℝ),
          ((51 / 10 : ℝ) * (1 / 2 : ℝ) ^ 13) * (1 / t ^ 3) := by
        apply integral_mono_ae (hfirst.const_mul (Real.sqrt n)) (hinvFirst.const_mul _)
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        have ht0 : 0 < t := hc.trans ht.1
        have hp := scaled_first_band μ h hρ n hn t
          ⟨by simpa only [HighFrequencyDamping.cutoff] using ht.1.le, ht.2⟩
        have hd := div_le_div_of_nonneg_right hp (pow_nonneg ht0.le 3)
        change Real.sqrt n * (‖charFun (μ : Measure ℝ) t ^ n‖ / t ^ 3) ≤ _
        convert hd using 1 <;> ring
      _ = _ := by rw [integral_const_mul, N26CubicHighTail.inverse_cube_first_band_integral]
  have hp2 : Real.sqrt n * (∫ t in Ioc (2 : ℝ) tailStart,
      HighFrequencyDamping.initialIntegrand μ n t) ≤
      ((51 / 10 : ℝ) * (3 / 4 : ℝ) ^ 13) * ((1 : ℝ) / 8 - 8 / 81) := by
    calc
      _ = ∫ t in Ioc (2 : ℝ) tailStart,
          Real.sqrt n * HighFrequencyDamping.initialIntegrand μ n t := (integral_const_mul _ _).symm
      _ ≤ ∫ t in Ioc (2 : ℝ) tailStart,
          ((51 / 10 : ℝ) * (3 / 4 : ℝ) ^ 13) * (1 / t ^ 3) := by
        apply integral_mono_ae (hsecond.const_mul (Real.sqrt n)) (hinvSecond.const_mul _)
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        have ht0 : 0 < t := lt_trans (by norm_num : (0 : ℝ) < 2) ht.1
        have hp := scaled_second_band μ h hρ n hn t ⟨ht.1.le, ht.2⟩
        have hd := div_le_div_of_nonneg_right hp (pow_nonneg ht0.le 3)
        change Real.sqrt n * (‖charFun (μ : Measure ℝ) t ^ n‖ / t ^ 3) ≤ _
        convert hd using 1 <;> ring
      _ = _ := by rw [integral_const_mul, N26CubicHighTail.inverse_cube_second_band_integral]
  have hsplit1 := setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hfirst htwo
  rw [Ioc_union_Ioi_eq_Ioi (by norm_num [HighFrequencyDamping.cutoff] :
    HighFrequencyDamping.cutoff ≤ (2 : ℝ))] at hsplit1
  have hsplit2 := setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hsecond hfar
  rw [Ioc_union_Ioi_eq_Ioi (by norm_num : (2 : ℝ) ≤ tailStart)] at hsplit2
  have htotal : Real.sqrt n * (∫ t in Ioi HighFrequencyDamping.cutoff,
      HighFrequencyDamping.initialIntegrand μ n t) ≤ cubicBandPrice + 353 / 2000 := by
    rw [hsplit1, hsplit2]
    unfold cubicBandPrice
    nlinarith only [hp1, hp2, hfarPrice]
  refine ⟨hi, htotal.trans ?_⟩
  norm_num [cubicBandPrice]

/-- Event damping and both floors retain the actual law and actual n. -/
theorem cf_tail_bound_of_event (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) (n : ℕ) (hn : 26 ≤ n)
    (E : Set (ℝ × ℝ)) (hE : MeasurableSet E)
    (hpa : massFloor ≤ eventProbability μ E)
    (hD : ∀ᵐ p ∂eventLaw μ E, distanceFloor ≤ HighFrequencyEvent.distance p)
    (h2 : Integrable (fun p => HighFrequencyEvent.distance p ^ 2) (eventLaw μ E))
    (hmean : conditionalSecondMoment μ E ≤ secondCeiling) :
    IntegrableOn (HighFrequencyDamping.initialIntegrand μ n) (Ioi HighFrequencyDamping.cutoff) ∧
      Real.sqrt n * (∫ t in Ioi HighFrequencyDamping.cutoff,
        HighFrequencyDamping.initialIntegrand μ n t) ≤ (9 : ℝ) / 50 := by
  have hperiodic : 1 < 2 * (26 : ℝ) * massFloor * sineSlope cellWidth ^ 2 * cellWidth ^ 2 := by
    norm_num [massFloor, sineSlope, cellWidth]
  have hwing : 1 ≤ 2 * (26 : ℝ) * massFloor * (23 / 48 : ℝ) ^ 2 := by norm_num [massFloor]
  have hb := (HighFrequencyTailFloor.actual_event_tail_basic_floor μ E hE 26 n (by decide) hn
    massFloor distanceFloor tailStart cellWidth secondCeiling (by norm_num) hpa
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hD h2 hmean hperiodic hwing).2.2
  exact cf_tail_bound_of_far_price μ h hρ n hn (hb.trans periodic_basic_price_le)

/-- The same actual maximum and its full predecessor acquire D<1 before
the original opposite-sign event is used. No p or defect price is free. -/
theorem original_cf_tail (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (hn : 26 ≤ n) (H C : ℝ)
    (hm : ContactVariation.PositiveClosedMaximum μ n H C)
    (hprev : Extremizer.fixedNSup (n - 1) ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) :
    IntegrableOn (HighFrequencyDamping.initialIntegrand μ n) (Ioi HighFrequencyDamping.cutoff) ∧
      Real.sqrt n * (∫ t in Ioi HighFrequencyDamping.cutoff,
        HighFrequencyDamping.initialIntegrand μ n t) ≤ (9 : ℝ) / 50 := by
  have he := LowMomentOppositeSignEvent.acquire μ h hρ
    (UniformLowMomentRawAcquisition.original_defect_lt_one μ h n hn H C hm hprev hC hρ)
  exact cf_tail_bound_of_event μ h hρ n hn LowMomentOppositeSignEvent.event
    he.measurable he.mass_lower he.distance_lower he.square_integrable he.second_moment_upper

theorem original_fourier_envelope (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (hn : 26 ≤ n) (H C : ℝ)
    (hm : ContactVariation.PositiveClosedMaximum μ n H C)
    (hprev : Extremizer.fixedNSup (n - 1) ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) :
    IntegrableOn (FourierRemainder.originalIntegrand μ n H) (Ioi 0) ∧
      |FourierRemainder.value μ n H| ≤ (776 : ℝ) / 1875 + (127 / 1500) * |H| := by
  refine ⟨FourierRemainder.integrable_originalIntegrand μ h n (by omega) H, ?_⟩
  have hs := UniformLowMomentFourierInitial.original_support μ h n hn H C hm hprev hC hρ
  have hb := UniformLowMomentFourierInitial.value_le_of_support_and_tail μ h hs hρ n hn H
    (9 / 50) (original_cf_tail μ h n hn H C hm hprev hC hρ).2
  convert hb using 1 <;> ring

end BerryEsseen.UniformLowMomentPeriodicHighTail

#print axioms BerryEsseen.UniformLowMomentPeriodicHighTail.periodic_basic_price_le
#print axioms BerryEsseen.UniformLowMomentPeriodicHighTail.scaled_norm_charFun_pow_le_floor
#print axioms BerryEsseen.UniformLowMomentPeriodicHighTail.cf_tail_bound_of_event
#print axioms BerryEsseen.UniformLowMomentPeriodicHighTail.original_cf_tail
#print axioms BerryEsseen.UniformLowMomentPeriodicHighTail.original_fourier_envelope

