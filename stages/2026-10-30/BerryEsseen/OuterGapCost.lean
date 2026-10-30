module

public import BerryEsseen.PhysicalDefect

@[expose] public section

/-! 2026-10-28: the original outer-gap cost of the same standardized law.
The genuine central gap is removed from the convergent original gap series.
All other gaps are priced by actual zero-bias stop-loss integrals, with
original atoms and unbounded support allowed. -/

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace BerryEsseen.OuterGapCost

open SupportGaps ZeroBias GapDefect CentralGap NoiseCoordinates ZeroBiasStopLoss PhysicalDefect

def actualCentralJ (μ : ProbabilityMeasure ℝ) : ℝ :=
  positiveFirstMoment μ * (Aminus μ + Aplus μ) ^ 2

def actualOuterJ (μ : ProbabilityMeasure ℝ) : ℝ := actualJ μ - actualCentralJ μ

def outerGapWeight (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hz : (0 : ℝ) ∉ (μ : Measure ℝ).support) (g : Gap μ) : ℝ := by
  classical
  exact if g = centralGap μ h hz then 0 else gapWeight μ g

theorem actualCentralJ_eq_gapWeight (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hz : (0 : ℝ) ∉ (μ : Measure ℝ).support) :
    actualCentralJ μ = gapWeight μ (centralGap μ h hz) := by
  have ht := centralGap_tau μ h hz
  unfold actualCentralJ gapWeight
  rw [ht]
  change positiveFirstMoment μ * (Aminus μ + Aplus μ) ^ 2 =
    positiveFirstMoment μ * (Aplus μ - -Aminus μ) ^ 2
  ring

/-- The outer series is the original convergent series with its actual central singleton removed. -/
theorem outerGapWeight_hasSum (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hz : (0 : ℝ) ∉ (μ : Measure ℝ).support) :
    HasSum (outerGapWeight μ h hz) (actualOuterJ μ) := by
  classical
  have hs := (gapWeight_summable μ h).hasSum.sub
    (hasSum_ite_eq (centralGap μ h hz) (gapWeight μ (centralGap μ h hz)))
  convert hs using 1
  · ext g
    unfold outerGapWeight
    by_cases heq : g = centralGap μ h hz
    · subst g
      simp
    · simp [heq]
  · change actualJ μ - actualCentralJ μ = actualJ μ - gapWeight μ (centralGap μ h hz)
    rw [actualCentralJ_eq_gapWeight μ h hz]

theorem actualOuterJ_eq_tsum (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hz : (0 : ℝ) ∉ (μ : Measure ℝ).support) :
    actualOuterJ μ = ∑' g : Gap μ, outerGapWeight μ h hz g :=
  (outerGapWeight_hasSum μ h hz).tsum_eq.symm

lemma outerGapWeight_nonneg (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hz : (0 : ℝ) ∉ (μ : Measure ℝ).support) (g : Gap μ) :
    0 ≤ outerGapWeight μ h hz g := by
  classical
  unfold outerGapWeight
  split_ifs
  · exact le_rfl
  · exact gapWeight_nonneg μ h g

theorem actualOuterJ_nonneg (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hz : (0 : ℝ) ∉ (μ : Measure ℝ).support) : 0 ≤ actualOuterJ μ := by
  rw [actualOuterJ_eq_tsum μ h hz]
  exact tsum_nonneg (outerGapWeight_nonneg μ h hz)

def outerHinge (μ : ProbabilityMeasure ℝ) (t : ℝ) : ℝ :=
  positiveHinge (Aplus μ) t + negativeHinge (Aminus μ) t

def actualOuterCost (μ : ProbabilityMeasure ℝ) : ℝ := ∫ t : ℝ, tau μ t * outerHinge μ t

def gapOuterIntegral (μ : ProbabilityMeasure ℝ) (g : Gap μ) : ℝ :=
  ∫ t in Ioo g.val.1 g.val.2, tau μ t * outerHinge μ t

lemma outerHinge_nonneg (μ : ProbabilityMeasure ℝ) (t : ℝ) : 0 ≤ outerHinge μ t :=
  add_nonneg (le_max_right _ _) (le_max_right _ _)

lemma continuous_outerHinge (μ : ProbabilityMeasure ℝ) : Continuous (outerHinge μ) := by
  unfold outerHinge positiveHinge negativeHinge
  fun_prop

theorem integrable_outerCost (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    Integrable (fun t : ℝ => tau μ t * outerHinge μ t) := by
  have hi := (integrable_tau_positiveHinge μ h (Aplus μ) (Aplus_nonneg μ h)).add
    (integrable_tau_negativeHinge μ h (Aminus μ) (Aminus_nonneg μ h))
  convert hi using 1
  ext t
  change tau μ t * (positiveHinge (Aplus μ) t + negativeHinge (Aminus μ) t) =
    tau μ t * positiveHinge (Aplus μ) t + tau μ t * negativeHinge (Aminus μ) t
  ring

lemma gapOuterIntegral_nonneg (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (g : Gap μ) :
    0 ≤ gapOuterIntegral μ g :=
  integral_nonneg fun t => mul_nonneg (tau_nonneg μ h t) (outerHinge_nonneg μ t)

lemma gapOuterIntegral_eq (μ : ProbabilityMeasure ℝ) (g : Gap μ) :
    gapOuterIntegral μ g = tau μ g.val.2 * (∫ t in Ioo g.val.1 g.val.2, outerHinge μ t) := by
  unfold gapOuterIntegral
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro t ht
  dsimp only
  rw [tau_constant_on_openGap μ g.val.1 g.val.2 t
    (measure_gap_eq_zero (μ : Measure ℝ) g.val g.property) ht.1 ht.2.le]

lemma integral_gap_left (a b : ℝ) (hab : a ≤ b) :
    (∫ t in Ioo a b, t - a) = (b - a) ^ 2 / 2 := by
  have hd (t : ℝ) : HasDerivAt (fun x : ℝ => (x - a) ^ 2 / 2) (t - a) t := by
    convert (((hasDerivAt_id' t).sub_const a).fun_pow 2).div_const 2 using 1
    ring
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
      ((show Continuous (fun t : ℝ => t - a) by fun_prop).intervalIntegrable a b)]
  ring

lemma integral_gap_right (a b : ℝ) (hab : a ≤ b) :
    (∫ t in Ioo a b, b - t) = (b - a) ^ 2 / 2 := by
  have hd (t : ℝ) : HasDerivAt (fun x : ℝ => -(b - x) ^ 2 / 2) (b - t) t := by
    convert ((((hasDerivAt_const t b).fun_sub (hasDerivAt_id' t)).fun_pow 2).fun_neg).div_const 2 using 1
    ring
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
      ((show Continuous (fun t : ℝ => b - t) by fun_prop).intervalIntegrable a b)]
  ring

/-- A noncentral gap lies beyond an actual central support endpoint. -/
theorem noncentralGap_endpoints (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hz : (0 : ℝ) ∉ (μ : Measure ℝ).support) (g : Gap μ) (hne : g ≠ centralGap μ h hz) :
    g.val.2 ≤ -Aminus μ ∨ Aplus μ ≤ g.val.1 := by
  rcases noncentralGap_one_sign μ h hz g hne with hb | ha
  · exact Or.inl (support_nonpositive_le μ g.val.2 g.property.2.1 hb)
  · exact Or.inr (Aplus_le_support_nonnegative μ g.val.1 g.property.1 ha)

lemma noncentralGap_width_le_hinge (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hz : (0 : ℝ) ∉ (μ : Measure ℝ).support) (g : Gap μ) (hne : g ≠ centralGap μ h hz) :
    (g.val.2 - g.val.1) ^ 2 ≤ 2 * (∫ t in Ioo g.val.1 g.val.2, outerHinge μ t) := by
  have hab := g.property.2.2.1.le
  have hH : IntegrableOn (outerHinge μ) (Ioo g.val.1 g.val.2) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hab).mp
      ((continuous_outerHinge μ).intervalIntegrable _ _)
  rcases noncentralGap_endpoints μ h hz g hne with hb | ha
  · have hL : IntegrableOn (fun t : ℝ => g.val.2 - t) (Ioo g.val.1 g.val.2) :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le hab).mp
        ((show Continuous (fun t : ℝ => g.val.2 - t) by fun_prop).intervalIntegrable _ _)
    have hi := setIntegral_mono_on hL hH measurableSet_Ioo (fun t _ => by
      have hle : g.val.2 - t ≤ negativeHinge (Aminus μ) t :=
        (show g.val.2 - t ≤ -t - Aminus μ by linarith).trans (le_max_left _ _)
      have hp : 0 ≤ positiveHinge (Aplus μ) t := le_max_right _ _
      exact hle.trans (le_add_of_nonneg_left hp))
    rw [integral_gap_right _ _ hab] at hi
    linarith
  · have hL : IntegrableOn (fun t : ℝ => t - g.val.1) (Ioo g.val.1 g.val.2) :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le hab).mp
        ((show Continuous (fun t : ℝ => t - g.val.1) by fun_prop).intervalIntegrable _ _)
    have hi := setIntegral_mono_on hL hH measurableSet_Ioo (fun t _ => by
      have hle : t - g.val.1 ≤ positiveHinge (Aplus μ) t :=
        (show t - g.val.1 ≤ t - Aplus μ by linarith).trans (le_max_left _ _)
      have hn : 0 ≤ negativeHinge (Aminus μ) t := le_max_right _ _
      exact hle.trans (le_add_of_nonneg_right hn))
    rw [integral_gap_left _ _ hab] at hi
    linarith

lemma noncentralGap_weight_le_hinge (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hz : (0 : ℝ) ∉ (μ : Measure ℝ).support) (g : Gap μ) (hne : g ≠ centralGap μ h hz) :
    gapWeight μ g ≤ 2 * gapOuterIntegral μ g := by
  have hw := mul_le_mul_of_nonneg_left (noncentralGap_width_le_hinge μ h hz g hne)
    (tau_nonneg μ h g.val.2)
  rw [gapOuterIntegral_eq]
  unfold gapWeight
  nlinarith only [hw]

theorem gapOuterIntegral_hasSum (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    HasSum (gapOuterIntegral μ) (∫ t in gapUnion μ, tau μ t * outerHinge μ t) := by
  have hd : Pairwise (fun g k : Gap μ =>
      Disjoint (Ioo g.val.1 g.val.2) (Ioo k.val.1 k.val.2)) := by
    intro g k hne
    apply gapSet_pairwiseDisjoint (μ : Measure ℝ).support g.property k.property
    exact fun heq => hne (Subtype.ext heq)
  exact hasSum_integral_iUnion (fun _ => measurableSet_Ioo) hd (integrable_outerCost μ h).integrableOn

theorem actualOuterJ_le_cost (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hz : (0 : ℝ) ∉ (μ : Measure ℝ).support) : actualOuterJ μ ≤ 2 * actualOuterCost μ := by
  classical
  have hp (g : Gap μ) : outerGapWeight μ h hz g ≤ 2 * gapOuterIntegral μ g := by
    unfold outerGapWeight
    split_ifs with heq
    · have hn := gapOuterIntegral_nonneg μ h g
      linarith
    · exact noncentralGap_weight_le_hinge μ h hz g heq
  have hs := hasSum_le hp (outerGapWeight_hasSum μ h hz) ((gapOuterIntegral_hasSum μ h).mul_left 2)
  have hi : (∫ t in gapUnion μ, tau μ t * outerHinge μ t) ≤ actualOuterCost μ :=
    setIntegral_le_integral (integrable_outerCost μ h)
      (Filter.Eventually.of_forall fun t => mul_nonneg (tau_nonneg μ h t) (outerHinge_nonneg μ t))
  linarith

theorem actualJ_le_central_add_cost (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hz : (0 : ℝ) ∉ (μ : Measure ℝ).support) :
    actualJ μ ≤ actualCentralJ μ + 2 * actualOuterCost μ := by
  have hi := actualOuterJ_le_cost μ h hz
  unfold actualOuterJ at hi
  linarith

def positiveSecondMoment (μ : ProbabilityMeasure ℝ) : ℝ :=
  ∫ x : ℝ, positivePart x ^ 2 ∂(μ : Measure ℝ)

def negativeSecondMoment (μ : ProbabilityMeasure ℝ) : ℝ :=
  ∫ x : ℝ, negativePart x ^ 2 ∂(μ : Measure ℝ)

def Rplus (μ : ProbabilityMeasure ℝ) : ℝ :=
  positiveSecondMoment μ - positiveFirstMoment μ * Aplus μ

def Rminus (μ : ProbabilityMeasure ℝ) : ℝ :=
  negativeSecondMoment μ - positiveFirstMoment μ * Aminus μ

def Tplus (μ : ProbabilityMeasure ℝ) : ℝ :=
  positiveThirdMoment μ - positiveFirstMoment μ * Aplus μ ^ 2

def Tminus (μ : ProbabilityMeasure ℝ) : ℝ :=
  negativeThirdMoment μ - positiveFirstMoment μ * Aminus μ ^ 2

theorem Rplus_nonneg (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) : 0 ≤ Rplus μ := by
  have hp : ∀ᵐ x ∂(μ : Measure ℝ), Aplus μ * positivePart x ≤ positivePart x ^ 2 := by
    filter_upwards [(μ : Measure ℝ).support_mem_ae] with x hx
    by_cases hx0 : 0 ≤ x
    · have hm := mul_le_mul_of_nonneg_right (Aplus_le_support_nonnegative μ x hx hx0) hx0
      simp only [positivePart, max_eq_left hx0]
      nlinarith only [hm]
    · simp [positivePart, max_eq_right (lt_of_not_ge hx0).le]
  have hi := integral_mono_ae ((integrable_positivePart μ h).const_mul (Aplus μ))
    (integrable_positivePart_sq μ h) hp
  rw [integral_const_mul] at hi
  change Aplus μ * positiveFirstMoment μ ≤ positiveSecondMoment μ at hi
  unfold Rplus
  nlinarith only [hi]

theorem Rminus_nonneg (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) : 0 ≤ Rminus μ := by
  have hp : ∀ᵐ x ∂(μ : Measure ℝ), Aminus μ * negativePart x ≤ negativePart x ^ 2 := by
    filter_upwards [(μ : Measure ℝ).support_mem_ae] with x hx
    by_cases hx0 : x ≤ 0
    · have hax : Aminus μ ≤ -x := by linarith [support_nonpositive_le μ x hx hx0]
      have hnx : 0 ≤ -x := neg_nonneg.mpr hx0
      have hm := mul_le_mul_of_nonneg_right hax hnx
      simp only [negativePart, max_eq_left hnx]
      nlinarith only [hm]
    · simp [negativePart, max_eq_right (neg_nonpos.mpr (lt_of_not_ge hx0).le)]
  have hi := integral_mono_ae ((integrable_negativePart μ h).const_mul (Aminus μ))
    (integrable_negativePart_sq μ h) hp
  rw [integral_const_mul, negative_firstMoment_eq_positive μ h] at hi
  change Aminus μ * positiveFirstMoment μ ≤ negativeSecondMoment μ at hi
  unfold Rminus
  nlinarith only [hi]

theorem Tplus_nonneg (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) : 0 ≤ Tplus μ :=
  sub_nonneg.mpr (positiveThirdMoment_lower μ h)

theorem Tminus_nonneg (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) : 0 ≤ Tminus μ :=
  sub_nonneg.mpr (negativeThirdMoment_lower μ h)

/-- The exact outer stop-loss cost in the original second and third moments. -/
theorem actualOuterCost_eq_excess (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    2 * actualOuterCost μ =
      Tplus μ + Tminus μ - 2 * Aplus μ * Rplus μ - 2 * Aminus μ * Rminus μ := by
  have hgapP : ∀ᵐ x ∂(μ : Measure ℝ), 0 < x → Aplus μ ≤ x := by
    filter_upwards [(μ : Measure ℝ).support_mem_ae] with x hx
    intro hpos
    exact Aplus_le_support_nonnegative μ x hx hpos.le
  have hgapN : ∀ᵐ x ∂(μ : Measure ℝ), x < 0 → Aminus μ ≤ -x := by
    filter_upwards [(μ : Measure ℝ).support_mem_ae] with x hx
    intro hneg
    linarith [support_nonpositive_le μ x hx hneg.le]
  have hp := positive_stopLoss_gap_expansion μ h (Aplus μ) (Aplus_nonneg μ h) hgapP
  change 2 * (∫ t : ℝ, tau μ t * positiveHinge (Aplus μ) t) =
    positiveThirdMoment μ - (2 * Aplus μ) * positiveSecondMoment μ +
      Aplus μ ^ 2 * positiveFirstMoment μ at hp
  have hn := negative_stopLoss_gap_expansion μ h (Aminus μ) (Aminus_nonneg μ h) hgapN
  rw [negative_firstMoment_eq_positive μ h] at hn
  change 2 * (∫ t : ℝ, tau μ t * negativeHinge (Aminus μ) t) =
    negativeThirdMoment μ - (2 * Aminus μ) * negativeSecondMoment μ +
      Aminus μ ^ 2 * positiveFirstMoment μ at hn
  have hi : actualOuterCost μ =
      (∫ t : ℝ, tau μ t * positiveHinge (Aplus μ) t) +
        (∫ t : ℝ, tau μ t * negativeHinge (Aminus μ) t) := by
    have heq : (fun t : ℝ => tau μ t * outerHinge μ t) =
        (fun t : ℝ => tau μ t * positiveHinge (Aplus μ) t) +
          (fun t : ℝ => tau μ t * negativeHinge (Aminus μ) t) := by
      ext t
      change tau μ t * (positiveHinge (Aplus μ) t + negativeHinge (Aminus μ) t) =
        tau μ t * positiveHinge (Aplus μ) t + tau μ t * negativeHinge (Aminus μ) t
      ring
    unfold actualOuterCost
    rw [heq]
    exact integral_add (integrable_tau_positiveHinge μ h (Aplus μ) (Aplus_nonneg μ h))
      (integrable_tau_negativeHinge μ h (Aminus μ) (Aminus_nonneg μ h))
  rw [hi]
  unfold Tplus Tminus Rplus Rminus
  nlinarith only [hp, hn]

/-- The true external gap resource pays both original signed excess terms. -/
theorem actualOuterJ_le_excess (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hz : (0 : ℝ) ∉ (μ : Measure ℝ).support) :
    actualOuterJ μ ≤ Tplus μ + Tminus μ - 2 * Aplus μ * Rplus μ - 2 * Aminus μ * Rminus μ := by
  rw [← actualOuterCost_eq_excess μ h]
  exact actualOuterJ_le_cost μ h hz

theorem actualJ_le_central_add_excess (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hz : (0 : ℝ) ∉ (μ : Measure ℝ).support) :
    actualJ μ ≤ actualCentralJ μ + Tplus μ + Tminus μ -
      2 * Aplus μ * Rplus μ - 2 * Aminus μ * Rminus μ := by
  have hi := actualOuterJ_le_excess μ h hz
  unfold actualOuterJ at hi
  linarith

end BerryEsseen.OuterGapCost

#print axioms BerryEsseen.OuterGapCost.outerGapWeight_hasSum
#print axioms BerryEsseen.OuterGapCost.actualOuterJ_nonneg
#print axioms BerryEsseen.OuterGapCost.noncentralGap_weight_le_hinge
#print axioms BerryEsseen.OuterGapCost.actualOuterJ_le_cost
#print axioms BerryEsseen.OuterGapCost.actualJ_le_central_add_cost
#print axioms BerryEsseen.OuterGapCost.Rplus_nonneg
#print axioms BerryEsseen.OuterGapCost.Rminus_nonneg
#print axioms BerryEsseen.OuterGapCost.actualOuterCost_eq_excess
#print axioms BerryEsseen.OuterGapCost.actualOuterJ_le_excess
