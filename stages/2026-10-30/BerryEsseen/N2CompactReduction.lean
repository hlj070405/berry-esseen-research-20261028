module

public import BerryEsseen.GlobalReduction
public import BerryEsseen.SmallIndexSupport
public import BerryEsseen.UniversalCDFBound
public import BerryEsseen.N2ThresholdTails

@[expose] public section

/-! 2026-10-29: actual index-two reduction to bounded low-third-moment laws.
The finite-domain estimate remains an explicit hypothesis, not an axiom or
an assertion that the numerical majorants have already been checked. -/

noncomputable section
open MeasureTheory Set

namespace BerryEsseen.N2CompactReduction
open GaussianTools Extremizer

def CompactPositiveBound (L : ℝ) : Prop :=
  ∀ (μ : ProbabilityMeasure ℝ), StandardizedLaw μ → thirdAbsoluteMoment μ ≤ 2 →
    (∀ᵐ x ∂(μ : Measure ℝ), |x| ≤ 6) → ∀ H : ℝ,
      (MixtureSum.iidSumLaw (μ : Measure ℝ) 2).real (Iic H) - Phi (H / Real.sqrt 2) ≤
        L * thirdAbsoluteMoment μ

theorem lifted_price_lt_esseen :
    ((2 : ℝ) / 7 + 1 / 1000) * Real.sqrt 2 < esseenConstant := by
  have hs : Real.sqrt (2 : ℝ) < 99 / 70 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  have h := AnalyticConstants.esseenConstant_gt_819_2000
  nlinarith

theorem fixedNSup_le_of_compact (L : ℝ)
    (hprice : L * Real.sqrt 2 < esseenConstant)
    (hlocal : CompactPositiveBound L) : fixedNSup 2 ≤ esseenConstant := by
  by_contra hnot
  have hC : esseenConstant < fixedNSup 2 := lt_of_not_ge hnot
  have hCpos : 0 < fixedNSup 2 := by
    linarith [AnalyticConstants.esseenConstant_gt_819_2000]
  obtain ⟨μ, hμ, H, hm⟩ := exists_PositiveClosedMaximum 2 (by norm_num) hCpos
  have hatt : (MixtureSum.iidSumLaw (μ : Measure ℝ) 2).real (Iic H) -
      Phi (H / Real.sqrt 2) = fixedNSup 2 * thirdAbsoluteMoment μ / Real.sqrt 2 := by
    simpa only [Nat.cast_ofNat] using hm.attainment
  have hs : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hcost : (2 : ℝ) / 7 * Real.sqrt 2 ≤ fixedNSup 2 :=
    (UniversalCDFBound.two_sevenths_sqrt_two_lt_esseen.trans hC).le
  by_cases hρ : 2 ≤ thirdAbsoluteMoment μ
  · have hb := UniversalCDFBound.high_moment_two_raw_cap μ hμ hρ H (fixedNSup 2) hcost
    rw [hatt] at hb
    exact (lt_irrefl _) hb
  · have hρu : thirdAbsoluteMoment μ ≤ 2 := (lt_of_not_ge hρ).le
    have hsupport := SmallIndexSupport.support_two_of_C_lower μ hμ H (fixedNSup 2)
      hm hρu hcost
    have hAE : ∀ᵐ x ∂(μ : Measure ℝ), |x| ≤ 6 := by
      filter_upwards [(μ : Measure ℝ).support_mem_ae] with x hx
      exact (abs_lt.mpr (hsupport hx)).le
    have hb := hlocal μ hμ hρu hAE H
    have hL : L < fixedNSup 2 / Real.sqrt 2 :=
      (lt_div_iff₀ hs).mpr (hprice.trans hC)
    have hp := mul_lt_mul_of_pos_right hL (thirdAbsoluteMoment_pos μ hμ)
    rw [hatt] at hb
    have hp' : L * thirdAbsoluteMoment μ <
        fixedNSup 2 * thirdAbsoluteMoment μ / Real.sqrt 2 := by
      simpa only [div_mul_eq_mul_div] using hp
    exact (not_lt_of_ge hb) hp'

theorem positiveRawClosedBound_of_compact (L : ℝ)
    (hprice : L * Real.sqrt 2 < esseenConstant)
    (hlocal : CompactPositiveBound L) : Reflection.PositiveRawClosedBound 2 esseenConstant :=
  GlobalReduction.positiveRawClosedBound_of_sup_le 2 (by norm_num) esseenConstant
    (fixedNSup_le_of_compact L hprice hlocal)

theorem absoluteClosedBound_of_compact (L : ℝ)
    (hprice : L * Real.sqrt 2 < esseenConstant)
    (hlocal : CompactPositiveBound L) : Reflection.AbsoluteClosedBound 2 esseenConstant :=
  Reflection.absoluteClosedBound_of_raw 2 (by norm_num) esseenConstant
    (positiveRawClosedBound_of_compact L hprice hlocal)

def CompactMiddleBound (L : ℝ) : Prop :=
  ∀ (μ : ProbabilityMeasure ℝ), StandardizedLaw μ → thirdAbsoluteMoment μ ≤ 2 →
    (∀ᵐ x ∂(μ : Measure ℝ), |x| ≤ 6) → ∀ H ∈ Icc (-9 / 4 : ℝ) 1,
      (MixtureSum.iidSumLaw (μ : Measure ℝ) 2).real (Iic H) - Phi (H / Real.sqrt 2) ≤
        L * thirdAbsoluteMoment μ

/-- The finite work only concerns the middle thresholds of the same bounded law. -/
theorem compactPositiveBound_of_middle (L : ℝ) (hL : (2 : ℝ) / 7 ≤ L)
    (hmiddle : CompactMiddleBound L) : CompactPositiveBound L := by
  intro μ h hρ hR H
  exact N2ThresholdTails.per_law_positive_of_middle μ h L hL (hmiddle μ h hρ hR) H

theorem absoluteClosedBound_of_compact_middle (L : ℝ) (hL : (2 : ℝ) / 7 ≤ L)
    (hprice : L * Real.sqrt 2 < esseenConstant)
    (hmiddle : CompactMiddleBound L) : Reflection.AbsoluteClosedBound 2 esseenConstant :=
  absoluteClosedBound_of_compact L hprice (compactPositiveBound_of_middle L hL hmiddle)

end BerryEsseen.N2CompactReduction

#print axioms BerryEsseen.N2CompactReduction.lifted_price_lt_esseen
#print axioms BerryEsseen.N2CompactReduction.fixedNSup_le_of_compact
#print axioms BerryEsseen.N2CompactReduction.positiveRawClosedBound_of_compact
#print axioms BerryEsseen.N2CompactReduction.absoluteClosedBound_of_compact
#print axioms BerryEsseen.N2CompactReduction.compactPositiveBound_of_middle
#print axioms BerryEsseen.N2CompactReduction.absoluteClosedBound_of_compact_middle
