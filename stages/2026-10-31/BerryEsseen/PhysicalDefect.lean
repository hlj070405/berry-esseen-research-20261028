module

public import BerryEsseen.GapDefect
public import BerryEsseen.NoiseCoordinates
public import BerryEsseen.ZeroBiasStopLoss

@[expose] public section

/-! 2026-10-28: nonnegativity of the original physical defect for every
standardized law with finite third absolute moment. All moments, gaps,
zero-bias constants and first moments belong to that same original law. -/

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace BerryEsseen.PhysicalDefect

open SupportGaps ZeroBias GapDefect CentralGap NoiseCoordinates ZeroBiasStopLoss

/-- The unique actual support gap which contains zero when zero is outside the support. -/
def centralGap (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hz : (0 : ℝ) ∉ (μ : Measure ℝ).support) : Gap μ := by
  refine ⟨(-Aminus μ, Aplus μ), (neg_Aminus_mem μ h).1, (Aplus_mem μ h).1, ?_,
    (support_disjoint_openGap μ).symm⟩
  linarith [Aminus_pos μ h hz, Aplus_pos μ h hz]

lemma zero_mem_centralGap (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hz : (0 : ℝ) ∉ (μ : Measure ℝ).support) :
    (0 : ℝ) ∈ Ioo (centralGap μ h hz).val.1 (centralGap μ h hz).val.2 := by
  change -Aminus μ < 0 ∧ 0 < Aplus μ
  constructor <;> linarith [Aminus_pos μ h hz, Aplus_pos μ h hz]

lemma tau_zero_eq_positiveFirstMoment (μ : ProbabilityMeasure ℝ) :
    tau μ 0 = positiveFirstMoment μ := by
  rw [tau_eq_integral_if, positiveFirstMoment]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    by_cases hx : 0 ≤ x
    · simp only [ite_eq_left hx, max_eq_left hx]
    · simp only [ite_eq_right hx, max_eq_right (lt_of_not_ge hx).le]

theorem centralGap_tau (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hz : (0 : ℝ) ∉ (μ : Measure ℝ).support) :
    tau μ (centralGap μ h hz).val.2 = positiveFirstMoment μ := by
  have hm := zero_mem_centralGap μ h hz
  have ht := (tau_constant_on_support_gap μ (centralGap μ h hz).val
    (centralGap μ h hz).property) ⟨hm.1, hm.2.le⟩
  exact ht.symm.trans (tau_zero_eq_positiveFirstMoment μ)

theorem noncentralGap_one_sign (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hz : (0 : ℝ) ∉ (μ : Measure ℝ).support) (g : Gap μ) (hne : g ≠ centralGap μ h hz) :
    g.val.2 ≤ 0 ∨ 0 ≤ g.val.1 := by
  by_cases hb : g.val.2 ≤ 0
  · exact Or.inl hb
  · right
    by_contra ha
    have heq := gap_eq_of_overlap (μ : Measure ℝ).support g.val (centralGap μ h hz).val 0
      g.property (centralGap μ h hz).property ⟨lt_of_not_ge ha, lt_of_not_ge hb⟩
      (zero_mem_centralGap μ h hz)
    exact hne (Subtype.ext heq)

/-- The single cross-zero gap has precisely this extra resource. -/
theorem centralGap_weight (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hz : (0 : ℝ) ∉ (μ : Measure ℝ).support) :
    gapWeight μ (centralGap μ h hz) = 2 * gapAbsTauIntegral μ (centralGap μ h hz) +
      2 * positiveFirstMoment μ * Aminus μ * Aplus μ := by
  have ht := centralGap_tau μ h hz
  change tau μ (Aplus μ) = positiveFirstMoment μ at ht
  rw [gapAbsTauIntegral_eq]
  change tau μ (Aplus μ) * (Aplus μ - -Aminus μ) ^ 2 =
    2 * (tau μ (Aplus μ) * absGapIntegral (-Aminus μ) (Aplus μ)) +
      2 * positiveFirstMoment μ * Aminus μ * Aplus μ
  rw [ht, absGapIntegral_across_zero (-Aminus μ) (Aplus μ)
    (neg_nonpos.mpr (Aminus_nonneg μ h)) (Aplus_nonneg μ h)]
  ring

lemma noncentralGap_weight_le (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hz : (0 : ℝ) ∉ (μ : Measure ℝ).support) (g : Gap μ) (hne : g ≠ centralGap μ h hz) :
    gapWeight μ g ≤ 2 * gapAbsTauIntegral μ g := by
  have hw := mul_le_mul_of_nonneg_left
    (width_sq_le_two_absGapIntegral g.val.1 g.val.2 g.property.2.2.1.le
      (noncentralGap_one_sign μ h hz g hne)) (tau_nonneg μ h g.val.2)
  rw [gapAbsTauIntegral_eq]
  unfold gapWeight
  nlinarith only [hw]

/-- All actual gaps are controlled, with only the genuine central-gap correction.
No compact support or full-hull coverage is used. -/
theorem actualJ_le_central_correction (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hz : (0 : ℝ) ∉ (μ : Measure ℝ).support) :
    actualJ μ ≤ thirdAbsoluteMoment μ + 2 * positiveFirstMoment μ * Aminus μ * Aplus μ := by
  classical
  let g0 := centralGap μ h hz
  let C := 2 * positiveFirstMoment μ * Aminus μ * Aplus μ
  have hp (g : Gap μ) : gapWeight μ g ≤
      2 * gapAbsTauIntegral μ g + (if g = g0 then C else 0) := by
    by_cases heq : g = g0
    · subst g
      rw [ite_eq_left rfl]
      exact (centralGap_weight μ h hz).le
    · rw [ite_eq_right heq, add_zero]
      exact noncentralGap_weight_le μ h hz g heq
  have hs : HasSum (fun g : Gap μ => if g = g0 then C else 0) C := hasSum_ite_eq g0 C
  have hsum := ((gapAbsTauIntegral_hasSum μ h).mul_left 2).add hs
  have hJ : actualJ μ ≤ 2 * (∫ t in gapUnion μ, |t| * tau μ t) + C :=
    hasSum_le hp (gapWeight_summable μ h).hasSum hsum
  have hI := gapAbsTauIntegral_tsum_le μ h
  rw [(gapAbsTauIntegral_hasSum μ h).tsum_eq] at hI
  dsimp only [C] at hJ
  linarith

def positiveThirdMoment (μ : ProbabilityMeasure ℝ) : ℝ :=
  ∫ x : ℝ, positivePart x ^ 3 ∂(μ : Measure ℝ)

def negativeThirdMoment (μ : ProbabilityMeasure ℝ) : ℝ :=
  ∫ x : ℝ, negativePart x ^ 3 ∂(μ : Measure ℝ)

lemma abs_cube_eq_parts (x : ℝ) :
    |x| ^ 3 = positivePart x ^ 3 + negativePart x ^ 3 := by
  rcases le_total 0 x with hx | hx
  · simp [positivePart, negativePart, max_eq_left hx, max_eq_right (neg_nonpos.mpr hx),
      abs_of_nonneg hx]
  · simp [positivePart, negativePart, max_eq_right hx, max_eq_left (neg_nonneg.mpr hx),
      abs_of_nonpos hx]

lemma cube_eq_parts (x : ℝ) :
    x ^ 3 = positivePart x ^ 3 - negativePart x ^ 3 := by
  rcases le_total 0 x with hx | hx
  · simp [positivePart, negativePart, max_eq_left hx, max_eq_right (neg_nonpos.mpr hx)]
  · simp only [positivePart, negativePart, max_eq_right hx, max_eq_left (neg_nonneg.mpr hx)]
    ring

theorem rho_eq_parts (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    thirdAbsoluteMoment μ = positiveThirdMoment μ + negativeThirdMoment μ := by
  unfold thirdAbsoluteMoment positiveThirdMoment negativeThirdMoment
  rw [← integral_add (integrable_positivePart_cube μ h) (integrable_negativePart_cube μ h)]
  exact integral_congr_ae (Filter.Eventually.of_forall abs_cube_eq_parts)

theorem gamma_eq_parts (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    gamma μ = positiveThirdMoment μ - negativeThirdMoment μ := by
  unfold gamma positiveThirdMoment negativeThirdMoment
  rw [← integral_sub (integrable_positivePart_cube μ h) (integrable_negativePart_cube μ h)]
  exact integral_congr_ae (Filter.Eventually.of_forall cube_eq_parts)

/-- The positive cube retains the original positive first moment, not just its mass. -/
theorem positiveThirdMoment_lower (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    positiveFirstMoment μ * Aplus μ ^ 2 ≤ positiveThirdMoment μ := by
  have ha := Aplus_nonneg μ h
  have hp : ∀ᵐ x ∂(μ : Measure ℝ),
      Aplus μ ^ 2 * positivePart x ≤ positivePart x ^ 3 := by
    filter_upwards [(μ : Measure ℝ).support_mem_ae] with x hx
    by_cases hx0 : 0 ≤ x
    · have hax := Aplus_le_support_nonnegative μ x hx hx0
      have hsq := (sq_le_sq₀ ha hx0).mpr hax
      have hm := mul_le_mul_of_nonneg_right hsq hx0
      simp only [positivePart, max_eq_left hx0]
      nlinarith only [hm]
    · simp [positivePart, max_eq_right (lt_of_not_ge hx0).le]
  have hi := integral_mono_ae ((integrable_positivePart μ h).const_mul (Aplus μ ^ 2))
    (integrable_positivePart_cube μ h) hp
  rw [integral_const_mul] at hi
  change Aplus μ ^ 2 * positiveFirstMoment μ ≤ positiveThirdMoment μ at hi
  nlinarith only [hi]

/-- Centering identifies the negative first moment with the same positive first moment. -/
theorem negativeThirdMoment_lower (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    positiveFirstMoment μ * Aminus μ ^ 2 ≤ negativeThirdMoment μ := by
  have ha := Aminus_nonneg μ h
  have hp : ∀ᵐ x ∂(μ : Measure ℝ),
      Aminus μ ^ 2 * negativePart x ≤ negativePart x ^ 3 := by
    filter_upwards [(μ : Measure ℝ).support_mem_ae] with x hx
    by_cases hx0 : x ≤ 0
    · have hax : Aminus μ ≤ -x := by linarith [support_nonpositive_le μ x hx hx0]
      have hnx : 0 ≤ -x := neg_nonneg.mpr hx0
      have hsq := (sq_le_sq₀ ha hnx).mpr hax
      have hm := mul_le_mul_of_nonneg_right hsq hnx
      simp only [negativePart, max_eq_left hnx]
      nlinarith only [hm]
    · simp [negativePart, max_eq_right (neg_nonpos.mpr (lt_of_not_ge hx0).le)]
  have hi := integral_mono_ae ((integrable_negativePart μ h).const_mul (Aminus μ ^ 2))
    (integrable_negativePart_cube μ h) hp
  rw [integral_const_mul, negative_firstMoment_eq_positive μ h] at hi
  change Aminus μ ^ 2 * positiveFirstMoment μ ≤ negativeThirdMoment μ at hi
  nlinarith only [hi]

lemma sqrt_ten_sub_one_pos : 0 < Real.sqrt 10 - 1 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 10)
  have hn := Real.sqrt_nonneg (10 : ℝ)
  nlinarith

/-- Multiplying the form by the positive `sqrt(10)-1` completes one exact square. -/
theorem central_quadratic_nonneg (am ap : ℝ) :
    0 ≤ (Real.sqrt 10 - 1) * ap ^ 2 + (Real.sqrt 10 + 1) * am ^ 2 - 6 * am * ap := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 10)
  have hid : (Real.sqrt 10 - 1) *
      ((Real.sqrt 10 - 1) * ap ^ 2 + (Real.sqrt 10 + 1) * am ^ 2 - 6 * am * ap) =
        ((Real.sqrt 10 - 1) * ap - 3 * am) ^ 2 := by
    have hmul := congrArg (fun z : ℝ => z * am ^ 2) hs
    nlinarith only [hmul]
  have hn : 0 ≤ (Real.sqrt 10 - 1) *
      ((Real.sqrt 10 - 1) * ap ^ 2 + (Real.sqrt 10 + 1) * am ^ 2 - 6 * am * ap) := by
    rw [hid]
    exact sq_nonneg _
  exact (mul_nonneg_iff_of_pos_left sqrt_ten_sub_one_pos).mp hn

theorem defect_ge_central_quadratic (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hz : (0 : ℝ) ∉ (μ : Measure ℝ).support) :
    positiveFirstMoment μ *
      ((Real.sqrt 10 - 1) * Aplus μ ^ 2 + (Real.sqrt 10 + 1) * Aminus μ ^ 2 -
        6 * Aminus μ * Aplus μ) ≤ actualPhysicalDefect μ := by
  have hJ := actualJ_le_central_correction μ h hz
  have hρ := rho_eq_parts μ h
  have hγ := gamma_eq_parts μ h
  have hP := mul_le_mul_of_nonneg_left (positiveThirdMoment_lower μ h) sqrt_ten_sub_one_pos.le
  have hN := mul_le_mul_of_nonneg_left (negativeThirdMoment_lower μ h)
    (show (0 : ℝ) ≤ Real.sqrt 10 + 1 by positivity)
  rw [hρ] at hJ
  unfold actualPhysicalDefect
  rw [hρ, hγ]
  nlinarith only [hJ, hP, hN]

/-- The original physical defect is nonnegative for all standardized finite-third-moment laws. -/
theorem actualPhysicalDefect_nonneg (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    0 ≤ actualPhysicalDefect μ := by
  by_cases hz : (0 : ℝ) ∈ (μ : Measure ℝ).support
  · have hρ : 0 ≤ thirdAbsoluteMoment μ := integral_nonneg fun x => pow_nonneg (abs_nonneg x) 3
    exact (mul_nonneg sqrt_ten_sub_one_pos.le hρ).trans (defect_lower_of_zero_mem μ h hz)
  · exact (mul_nonneg (positiveFirstMoment_pos μ h).le
      (central_quadratic_nonneg (Aminus μ) (Aplus μ))).trans (defect_ge_central_quadratic μ h hz)

end BerryEsseen.PhysicalDefect

#print axioms BerryEsseen.PhysicalDefect.centralGap_tau
#print axioms BerryEsseen.PhysicalDefect.centralGap_weight
#print axioms BerryEsseen.PhysicalDefect.actualJ_le_central_correction
#print axioms BerryEsseen.PhysicalDefect.rho_eq_parts
#print axioms BerryEsseen.PhysicalDefect.positiveThirdMoment_lower
#print axioms BerryEsseen.PhysicalDefect.negativeThirdMoment_lower
#print axioms BerryEsseen.PhysicalDefect.defect_ge_central_quadratic
#print axioms BerryEsseen.PhysicalDefect.actualPhysicalDefect_nonneg
