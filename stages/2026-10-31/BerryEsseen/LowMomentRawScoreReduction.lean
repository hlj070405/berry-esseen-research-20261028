module

public import BerryEsseen.RawResourceEnvelope
public import BerryEsseen.N26InitialLowFrequency
public import BerryEsseen.GapMomentGlobalBounds
public import BerryEsseen.ChargedConservedTransfer

@[expose] public section

/-! 2026-10-30: remove the numerical score dimension from a charged raw
price. The law, actual sample count and original H stay fixed throughout.
Changing the score here evaluates the already defined raw function; no
closed-maximum assertion at a changed score is used or concluded. -/

noncomputable section

open MeasureTheory Set

namespace BerryEsseen.LowMomentRawScoreReduction

/-- The literal coefficient of C in the actual raw resource. -/
def scoreCoefficient (μ : ProbabilityMeasure ℝ) (H : ℝ) : ℝ :=
  RawResourceEnvelope.baseBracket μ + H * ContactWeightedMoment.K1 μ -
    H ^ 2 * thirdAbsoluteMoment μ

/-- All Gaussian-density and Fourier terms cancel when only C changes. -/
theorem raw_score_difference (μ : ProbabilityMeasure ℝ) (n : ℕ) (H C₁ C₂ : ℝ) :
    ConservedResource.raw μ n H C₂ - ConservedResource.raw μ n H C₁ =
      (C₂ - C₁) * scoreCoefficient μ H := by
  unfold ConservedResource.raw scoreCoefficient RawResourceEnvelope.baseBracket
  ring

theorem raw_eq_score_affine (μ : ProbabilityMeasure ℝ) (n : ℕ) (H C₁ C₂ : ℝ) :
    ConservedResource.raw μ n H C₂ = ConservedResource.raw μ n H C₁ +
      (C₂ - C₁) * scoreCoefficient μ H := by
  linarith only [raw_score_difference μ n H C₁ C₂]

theorem fourthMoment_le_seven_fifths (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hs : (μ : Measure ℝ).support ⊆ Icc (-(12 / 5 : ℝ)) (12 / 5))
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) :
    ContactZeroBiasMoment.fourthMoment μ ≤ (7 : ℝ) / 5 := by
  have h4 := (N26P39ResourceAcquisition.moment_caps_of_support μ h hs hρ).1
  simp only [ZeroBiasHigherMoments.abs_pow_four] at h4
  unfold ContactZeroBiasMoment.fourthMoment
  linarith only [h4]

theorem abs_signedFourthMoment_le_fourthMoment (μ : ProbabilityMeasure ℝ)
    (_h4 : Integrable (fun x : ℝ => x ^ 4) (μ : Measure ℝ)) :
    |ContactWeightedMoment.signedFourthMoment μ| ≤ ContactZeroBiasMoment.fourthMoment μ := by
  unfold ContactWeightedMoment.signedFourthMoment ContactZeroBiasMoment.fourthMoment
  calc
    |∫ x : ℝ, x * |x| ^ 3 ∂(μ : Measure ℝ)| ≤
        ∫ x : ℝ, |x * |x| ^ 3| ∂(μ : Measure ℝ) := abs_integral_le_integral_abs
    _ = ∫ x : ℝ, x ^ 4 ∂(μ : Measure ℝ) := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [abs_mul, abs_pow, abs_abs]
      calc
        |x| * |x| ^ 3 = |x| ^ 4 := by ring
        _ = x ^ 4 := ZeroBiasHigherMoments.abs_pow_four x

/-- Coarse actual moment prices, all derived from the same original law. -/
theorem basic_caps (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hs : (μ : Measure ℝ).support ⊆ Icc (-(12 / 5 : ℝ)) (12 / 5))
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) :
    |SignedMoment.signedSecondMoment μ| ≤ (3 : ℝ) / 10 ∧
      |ZeroBias.gamma μ| ≤ (3 : ℝ) / 5 ∧
      |GapDefect.actualJ μ| ≤ (11 : ℝ) / 5 ∧
      |ContactGapSum.actualJ1 μ| ≤ (66 : ℝ) / 25 ∧
      |ContactGapSum.actualJ2 μ| ≤ (56 : ℝ) / 25 := by
  have hβ := SignedMoment.abs_signed_lt_127_500 μ h hρ
  have hγ := N26InitialLowFrequency.gamma_cap μ h hρ
  change |ZeroBias.gamma μ| ≤ (53 : ℝ) / 100 at hγ
  have hJ := GapDefect.actualJ_le_two_rho μ h
  have hJ1 := GapMomentGlobalBounds.abs_actualJ1_le_R_mul_rho μ h (12 / 5)
    (by norm_num) hs
  have hJ2 := GapMomentGlobalBounds.abs_actualJ2_le_two_R_mul_fourth_div_three μ h
    (12 / 5) (by norm_num) hs
  have h4 := fourthMoment_le_seven_fifths μ h hs hρ
  rw [abs_of_nonneg (GapDefect.actualJ_nonneg μ h)]
  change (∫ x : ℝ, x ^ 4 ∂(μ : Measure ℝ)) ≤ (7 : ℝ) / 5 at h4
  constructor
  · linarith only [hβ]
  constructor
  · linarith only [hγ]
  constructor
  · linarith only [hJ, hρ]
  constructor
  · linarith only [hJ1, hρ]
  · linarith only [hJ2, h4]

theorem neg_Kq_le_twenty_seven_fiftieths (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hs : (μ : Measure ℝ).support ⊆ Icc (-(12 / 5 : ℝ)) (12 / 5))
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) :
    -ContactZeroBiasMoment.Kq μ ≤ (27 : ℝ) / 50 := by
  obtain ⟨hβ, hγ, _, _, _⟩ := basic_caps μ h hs hρ
  have hρ1 := Extremizer.thirdAbsoluteMoment_ge_one μ h
  have h4 := fourthMoment_le_seven_fifths μ h hs hρ
  have h40 : 0 ≤ ContactZeroBiasMoment.fourthMoment μ :=
    integral_nonneg fun x => by positivity
  have h5 : 0 ≤ ZeroBiasHigherMoments.absoluteMoment μ 5 :=
    integral_nonneg fun x => pow_nonneg (abs_nonneg x) 5
  have hp := mul_le_mul hρ h4 h40 (by norm_num : (0 : ℝ) ≤ 11 / 10)
  have hβγ : SignedMoment.signedSecondMoment μ * ZeroBias.gamma μ ≤ (9 : ℝ) / 50 := by
    calc
      _ ≤ |SignedMoment.signedSecondMoment μ * ZeroBias.gamma μ| := le_abs_self _
      _ = |SignedMoment.signedSecondMoment μ| * |ZeroBias.gamma μ| := abs_mul _ _
      _ ≤ (3 / 10 : ℝ) * (3 / 5) :=
        mul_le_mul hβ hγ (abs_nonneg _) (by norm_num)
      _ = _ := by norm_num
  unfold ContactZeroBiasMoment.Kq
  nlinarith only [hp, hβγ, hρ1, h5]

theorem baseBracket_le_seventeen (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hs : (μ : Measure ℝ).support ⊆ Icc (-(12 / 5 : ℝ)) (12 / 5))
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) :
    RawResourceEnvelope.baseBracket μ ≤ 17 := by
  obtain ⟨hβ, _, hJ, hJ1, hJ2⟩ := basic_caps μ h hs hρ
  have hρ0 : 0 ≤ thirdAbsoluteMoment μ :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (Extremizer.thirdAbsoluteMoment_ge_one μ h)
  have hpβJ : SignedMoment.signedSecondMoment μ * GapDefect.actualJ μ ≤
      (3 / 10 : ℝ) * (11 / 5) := by
    calc
      _ ≤ |SignedMoment.signedSecondMoment μ * GapDefect.actualJ μ| := le_abs_self _
      _ = |SignedMoment.signedSecondMoment μ| * |GapDefect.actualJ μ| := abs_mul _ _
      _ ≤ _ := mul_le_mul hβ hJ (abs_nonneg _) (by norm_num)
  have hpρJ1 : thirdAbsoluteMoment μ * ContactGapSum.actualJ1 μ ≤
      (11 / 10 : ℝ) * (66 / 25) := by
    calc
      _ ≤ thirdAbsoluteMoment μ * |ContactGapSum.actualJ1 μ| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) hρ0
      _ ≤ _ := mul_le_mul hρ hJ1 (abs_nonneg _) (by norm_num)
  have hnJ2 := (neg_le_abs (ContactGapSum.actualJ2 μ)).trans hJ2
  have hnKq := neg_Kq_le_twenty_seven_fiftieths μ h hs hρ
  unfold RawResourceEnvelope.baseBracket
  nlinarith only [hpβJ, hpρJ1, hnJ2, hnKq]

theorem abs_K1_le_thirty_three_tenths (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hs : (μ : Measure ℝ).support ⊆ Icc (-(12 / 5 : ℝ)) (12 / 5))
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) :
    |ContactWeightedMoment.K1 μ| ≤ (33 : ℝ) / 10 := by
  obtain ⟨hβ, hγ, _, _, _⟩ := basic_caps μ h hs hρ
  have hρ0 : 0 ≤ thirdAbsoluteMoment μ :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (Extremizer.thirdAbsoluteMoment_ge_one μ h)
  have h4 := fourthMoment_le_seven_fifths μ h hs hρ
  have hs4 := (abs_signedFourthMoment_le_fourthMoment μ
    (ConservedResource.integrable_pow_of_bounded_support μ (12 / 5) hs 4)).trans h4
  have hp := mul_le_mul hρ hγ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 11 / 10)
  have hsub1 := abs_sub (ContactWeightedMoment.signedFourthMoment μ)
    (3 * SignedMoment.signedSecondMoment μ)
  have hsub2 := abs_sub
    (ContactWeightedMoment.signedFourthMoment μ - 3 * SignedMoment.signedSecondMoment μ)
    ((3 / 2 : ℝ) * thirdAbsoluteMoment μ * ZeroBias.gamma μ)
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)] at hsub1
  rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 2),
    abs_of_nonneg hρ0] at hsub2
  unfold ContactWeightedMoment.K1
  nlinarith only [hsub1, hsub2, hs4, hβ, hp]

/-- Uniform in the original real H and independent of the actual n. -/
theorem scoreCoefficient_le_twenty (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hs : (μ : Measure ℝ).support ⊆ Icc (-(12 / 5 : ℝ)) (12 / 5))
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) (H : ℝ) :
    scoreCoefficient μ H ≤ 20 := by
  have hbase := baseBracket_le_seventeen μ h hs hρ
  have hK1 := abs_K1_le_thirty_three_tenths μ h hs hρ
  have hρ1 := Extremizer.thirdAbsoluteMoment_ge_one μ h
  have hlinear : H * ContactWeightedMoment.K1 μ ≤ |H| * (33 / 10 : ℝ) := by
    calc
      _ ≤ |H * ContactWeightedMoment.K1 μ| := le_abs_self _
      _ = |H| * |ContactWeightedMoment.K1 μ| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hK1 (abs_nonneg H)
  have hquadratic := mul_le_mul_of_nonneg_right hρ1 (sq_nonneg H)
  have hsquare := sq_nonneg (|H| - (33 / 20 : ℝ))
  unfold scoreCoefficient
  nlinarith only [hbase, hlinear, hquadratic, hsquare, sq_abs H]

/-- The affine raw function has its interval maximum at an endpoint. -/
theorem raw_le_endpoints_of_between (μ : ProbabilityMeasure ℝ) (n : ℕ)
    (H c₀ cup C : ℝ) (hlo : c₀ ≤ C) (hhi : C ≤ cup) :
    ConservedResource.raw μ n H C ≤
      max (ConservedResource.raw μ n H c₀) (ConservedResource.raw μ n H cup) := by
  by_cases hB : 0 ≤ scoreCoefficient μ H
  · have hp := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hhi) hB
    have he := raw_score_difference μ n H cup C
    have hr : ConservedResource.raw μ n H C ≤ ConservedResource.raw μ n H cup := by
      linarith only [he, hp]
    exact hr.trans (le_max_right _ _)
  · have hp := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hlo) (le_of_not_ge hB)
    have he := raw_score_difference μ n H c₀ C
    have hr : ConservedResource.raw μ n H C ≤ ConservedResource.raw μ n H c₀ := by
      linarith only [he, hp]
    exact hr.trans (le_max_left _ _)

/-- Above cup the floor-charged actual raw is antitone in the score.
The law, actual n and H are fixed, with no maximum premise at a new score. -/
theorem floorChargedRaw_antitone_above_cup (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hs : (μ : Measure ℝ).support ⊆ Icc (-(12 / 5 : ℝ)) (12 / 5))
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10)
    (n N : ℕ) (hN : 25 ≤ N) (H C₁ C₂ cup : ℝ)
    (hcup : cup ≤ C₁) (hC : C₁ ≤ C₂) :
    ChargedConservedTransfer.floorChargedRaw μ n N H C₂ cup ≤
      ChargedConservedTransfer.floorChargedRaw μ n N H C₁ cup := by
  have hB := scoreCoefficient_le_twenty μ h hs hρ H
  have hρ1 := Extremizer.thirdAbsoluteMoment_ge_one μ h
  have hNr : (25 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hfee : scoreCoefficient μ H ≤ (N : ℝ) * thirdAbsoluteMoment μ := by
    have hp := mul_le_mul_of_nonneg_left hρ1 (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
    nlinarith only [hB, hNr, hp]
  have hp := mul_le_mul_of_nonneg_left hfee (sub_nonneg.mpr hC)
  have he := raw_score_difference μ n H C₁ C₂
  unfold ChargedConservedTransfer.floorChargedRaw
  rw [max_eq_right (sub_nonneg.mpr hcup),
    max_eq_right (sub_nonneg.mpr (hcup.trans hC))]
  nlinarith only [hp, he]

/-- The raw function remains evaluated at its original arbitrary actual n. -/
theorem floorChargedRaw_le_raw_cup (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hs : (μ : Measure ℝ).support ⊆ Icc (-(12 / 5 : ℝ)) (12 / 5))
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10)
    (n N : ℕ) (hN : 25 ≤ N) (H C cup : ℝ) (hC : cup ≤ C) :
    ChargedConservedTransfer.floorChargedRaw μ n N H C cup ≤
      ConservedResource.raw μ n H cup := by
  have hm := floorChargedRaw_antitone_above_cup μ h hs hρ n N hN H cup C cup le_rfl hC
  simpa only [ChargedConservedTransfer.floorChargedRaw, sub_self, max_self,
    mul_zero, zero_mul, sub_zero] using hm

/-- Remove the whole unbounded candidate-score dimension using two fixed
raw evaluations. No maximum premise is needed at either endpoint. -/
theorem floorChargedRaw_le_endpoints (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hs : (μ : Measure ℝ).support ⊆ Icc (-(12 / 5 : ℝ)) (12 / 5))
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10)
    (n N : ℕ) (hN : 25 ≤ N) (H c₀ cup C : ℝ)
    (_hc₀ : 0 ≤ c₀) (_horder : c₀ ≤ cup) (hC : c₀ ≤ C) :
    ChargedConservedTransfer.floorChargedRaw μ n N H C cup ≤
      max (ConservedResource.raw μ n H c₀) (ConservedResource.raw μ n H cup) := by
  by_cases hhi : C ≤ cup
  · simpa only [ChargedConservedTransfer.floorChargedRaw,
      max_eq_left (sub_nonpos.mpr hhi), mul_zero, zero_mul, sub_zero] using
      raw_le_endpoints_of_between μ n H c₀ cup C hC hhi
  · exact (floorChargedRaw_le_raw_cup μ h hs hρ n N hN H C cup
      (le_of_not_ge hhi)).trans (le_max_right _ _)

/-- The concrete floor-25 reduction keeps CE strictly above its rational
lower score; CE is not replaced by the rational upper-score endpoint. -/
theorem floor25_le_fixed_endpoints (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hs : (μ : Measure ℝ).support ⊆ Icc (-(12 / 5 : ℝ)) (12 / 5))
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10)
    (n : ℕ) (H C : ℝ) (hC : esseenConstant ≤ C) :
    ChargedConservedTransfer.floorChargedRaw μ n 25 H C (20487 / 50000) ≤
      max (ConservedResource.raw μ n H (819 / 2000))
        (ConservedResource.raw μ n H (20487 / 50000)) :=
  floorChargedRaw_le_endpoints μ h hs hρ n 25 (by decide) H (819 / 2000)
    (20487 / 50000) C (by norm_num) (by norm_num)
    (AnalyticConstants.esseenConstant_gt_819_2000.le.trans hC)

/-- Exact actual-n charging gives a single CE evaluation for n≥25.
This is solely a raw-function price, with no hm(CE) premise. -/
theorem chargedRaw_le_raw_esseenConstant (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hs : (μ : Measure ℝ).support ⊆ Icc (-(12 / 5 : ℝ)) (12 / 5))
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10)
    (n : ℕ) (hn : 25 ≤ n) (H C : ℝ) (hC : esseenConstant ≤ C) :
    ChargedConservedTransfer.chargedRaw μ n H C ≤
      ConservedResource.raw μ n H esseenConstant := by
  have hf := floorChargedRaw_le_raw_cup μ h hs hρ n n hn H C esseenConstant hC
  simpa only [ChargedConservedTransfer.floorChargedRaw,
    ChargedConservedTransfer.chargedRaw, max_eq_right (sub_nonneg.mpr hC)] using hf

end BerryEsseen.LowMomentRawScoreReduction

#print axioms BerryEsseen.LowMomentRawScoreReduction.raw_score_difference
#print axioms BerryEsseen.LowMomentRawScoreReduction.baseBracket_le_seventeen
#print axioms BerryEsseen.LowMomentRawScoreReduction.abs_K1_le_thirty_three_tenths
#print axioms BerryEsseen.LowMomentRawScoreReduction.scoreCoefficient_le_twenty
#print axioms BerryEsseen.LowMomentRawScoreReduction.floorChargedRaw_antitone_above_cup
#print axioms BerryEsseen.LowMomentRawScoreReduction.floorChargedRaw_le_endpoints
#print axioms BerryEsseen.LowMomentRawScoreReduction.floor25_le_fixed_endpoints
#print axioms BerryEsseen.LowMomentRawScoreReduction.chargedRaw_le_raw_esseenConstant
