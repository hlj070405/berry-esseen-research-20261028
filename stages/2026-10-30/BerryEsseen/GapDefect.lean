module

public import BerryEsseen.SupportGaps
public import BerryEsseen.CentralGap
public import Mathlib.Topology.Algebra.InfiniteSum.Real

@[expose] public section

/-! 2026-10-28: the actual countable gap resource and physical defect of the
original standardized law. Summability uses the integrable zero-bias first
absolute moment, with no bounded-support or finite-gap assumption. -/

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace BerryEsseen.GapDefect

open SupportGaps ZeroBias

def absGapIntegral (a b : ℝ) : ℝ := ∫ t in Ioo a b, |t|

lemma absGapIntegral_nonneg (a b : ℝ) : 0 ≤ absGapIntegral a b :=
  integral_nonneg (fun t => abs_nonneg t)

lemma absGapIntegral_eq_interval (a b : ℝ) (hab : a ≤ b) :
    absGapIntegral a b = ∫ t in a..b, |t| := by
  unfold absGapIntegral
  rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]

lemma absGapIntegral_of_nonneg (a b : ℝ) (hab : a ≤ b) (ha : 0 ≤ a) :
    absGapIntegral a b = (b ^ 2 - a ^ 2) / 2 := by
  rw [absGapIntegral_eq_interval a b hab]
  calc
    (∫ t in a..b, |t|) = ∫ t in a..b, t := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hab] at ht
      exact abs_of_nonneg (ha.trans ht.1)
    _ = _ := integral_id

lemma absGapIntegral_of_nonpos (a b : ℝ) (hab : a ≤ b) (hb : b ≤ 0) :
    absGapIntegral a b = (a ^ 2 - b ^ 2) / 2 := by
  rw [absGapIntegral_eq_interval a b hab]
  calc
    (∫ t in a..b, |t|) = ∫ t in a..b, -t := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hab] at ht
      exact abs_of_nonpos (ht.2.trans hb)
    _ = -(∫ t in a..b, t) := intervalIntegral.integral_neg
    _ = _ := by rw [integral_id]; ring

lemma absGapIntegral_across_zero (a b : ℝ) (ha : a ≤ 0) (hb : 0 ≤ b) :
    absGapIntegral a b = (a ^ 2 + b ^ 2) / 2 := by
  have h := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (continuous_abs.intervalIntegrable a 0) (continuous_abs.intervalIntegrable 0 b)
  rw [← absGapIntegral_eq_interval a 0 ha, ← absGapIntegral_eq_interval 0 b hb,
    ← absGapIntegral_eq_interval a b (ha.trans hb),
    absGapIntegral_of_nonpos a 0 ha le_rfl, absGapIntegral_of_nonneg 0 b hb le_rfl] at h
  norm_num at h
  linarith

theorem width_sq_le_two_absGapIntegral (a b : ℝ) (hab : a ≤ b)
    (hsign : b ≤ 0 ∨ 0 ≤ a) : (b - a) ^ 2 ≤ 2 * absGapIntegral a b := by
  rcases hsign with hb | ha
  · rw [absGapIntegral_of_nonpos a b hab hb]
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hb (sub_nonneg.mpr hab)]
  · rw [absGapIntegral_of_nonneg a b hab ha]
    nlinarith [mul_nonneg ha (sub_nonneg.mpr hab)]

theorem width_sq_le_four_absGapIntegral (a b : ℝ) (hab : a ≤ b) :
    (b - a) ^ 2 ≤ 4 * absGapIntegral a b := by
  by_cases hsign : b ≤ 0 ∨ 0 ≤ a
  · have h := width_sq_le_two_absGapIntegral a b hab hsign
    have hn := absGapIntegral_nonneg a b
    linarith
  · rcases not_or.mp hsign with ⟨hb, ha⟩
    rw [absGapIntegral_across_zero a b (lt_of_not_ge ha).le (lt_of_not_ge hb).le]
    nlinarith [sq_nonneg (a + b)]

abbrev Gap (μ : ProbabilityMeasure ℝ) :=
  {g : ℝ × ℝ // g ∈ gapSet (μ : Measure ℝ).support}

instance (μ : ProbabilityMeasure ℝ) : Countable (Gap μ) :=
  (gapSet_countable (μ : Measure ℝ).support).to_subtype

def gapWeight (μ : ProbabilityMeasure ℝ) (g : Gap μ) : ℝ :=
  tau μ g.val.2 * (g.val.2 - g.val.1) ^ 2

def gapAbsTauIntegral (μ : ProbabilityMeasure ℝ) (g : Gap μ) : ℝ :=
  ∫ t in Ioo g.val.1 g.val.2, |t| * tau μ t

def gapUnion (μ : ProbabilityMeasure ℝ) : Set ℝ :=
  ⋃ g : Gap μ, Ioo g.val.1 g.val.2

/-- The original physical gap resource, summed over all actual support gaps. -/
def actualJ (μ : ProbabilityMeasure ℝ) : ℝ := ∑' g : Gap μ, gapWeight μ g

lemma gapWeight_nonneg (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (g : Gap μ) :
    0 ≤ gapWeight μ g := mul_nonneg (tau_nonneg μ h _) (sq_nonneg _)

lemma gapAbsTauIntegral_nonneg (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (g : Gap μ) :
    0 ≤ gapAbsTauIntegral μ g :=
  integral_nonneg fun t => mul_nonneg (abs_nonneg t) (tau_nonneg μ h t)

/-- Constancy uses the actual open gap's zero mass and its right endpoint. -/
lemma gapAbsTauIntegral_eq (μ : ProbabilityMeasure ℝ) (g : Gap μ) :
    gapAbsTauIntegral μ g = tau μ g.val.2 * absGapIntegral g.val.1 g.val.2 := by
  unfold gapAbsTauIntegral absGapIntegral
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro t ht
  dsimp only
  rw [tau_constant_on_openGap μ g.val.1 g.val.2 t
    (measure_gap_eq_zero (μ : Measure ℝ) g.val g.property) ht.1 ht.2.le]
  ring

lemma gapWeight_le_four_integral (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (g : Gap μ) :
    gapWeight μ g ≤ 4 * gapAbsTauIntegral μ g := by
  have hw := mul_le_mul_of_nonneg_left
    (width_sq_le_four_absGapIntegral g.val.1 g.val.2 g.property.2.2.1.le)
    (tau_nonneg μ h g.val.2)
  rw [gapAbsTauIntegral_eq]
  unfold gapWeight
  nlinarith only [hw]

lemma gap_one_sign_of_zero_mem (μ : ProbabilityMeasure ℝ)
    (hzero : (0 : ℝ) ∈ (μ : Measure ℝ).support) (g : Gap μ) :
    g.val.2 ≤ 0 ∨ 0 ≤ g.val.1 := by
  by_cases hb : g.val.2 ≤ 0
  · exact Or.inl hb
  · right
    by_contra ha
    exact (Set.disjoint_left.mp g.property.2.2.2)
      ⟨lt_of_not_ge ha, lt_of_not_ge hb⟩ hzero

lemma gapWeight_le_two_integral (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hzero : (0 : ℝ) ∈ (μ : Measure ℝ).support) (g : Gap μ) :
    gapWeight μ g ≤ 2 * gapAbsTauIntegral μ g := by
  have hw := mul_le_mul_of_nonneg_left
    (width_sq_le_two_absGapIntegral g.val.1 g.val.2 g.property.2.2.1.le
      (gap_one_sign_of_zero_mem μ hzero g)) (tau_nonneg μ h g.val.2)
  rw [gapAbsTauIntegral_eq]
  unfold gapWeight
  nlinarith only [hw]

theorem gapAbsTauIntegral_hasSum (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    HasSum (gapAbsTauIntegral μ) (∫ t in gapUnion μ, |t| * tau μ t) := by
  have hd : Pairwise (fun g k : Gap μ =>
      Disjoint (Ioo g.val.1 g.val.2) (Ioo k.val.1 k.val.2)) := by
    intro g k hne
    apply gapSet_pairwiseDisjoint (μ : Measure ℝ).support g.property k.property
    exact fun heq => hne (Subtype.ext heq)
  exact hasSum_integral_iUnion (fun _ => measurableSet_Ioo) hd
    (integrable_abs_mul_tau μ h).integrableOn

theorem gapAbsTauIntegral_tsum_le (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    (∑' g : Gap μ, gapAbsTauIntegral μ g) ≤ thirdAbsoluteMoment μ / 2 := by
  rw [(gapAbsTauIntegral_hasSum μ h).tsum_eq]
  calc
    (∫ t in gapUnion μ, |t| * tau μ t) ≤ ∫ t : ℝ, |t| * tau μ t :=
      setIntegral_le_integral (integrable_abs_mul_tau μ h)
        (Filter.Eventually.of_forall fun t => mul_nonneg (abs_nonneg t) (tau_nonneg μ h t))
    _ = _ := integral_abs_mul_tau μ h

/-- Genuine convergence of the actual gap series, derived from the same law. -/
theorem gapWeight_summable (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    Summable (gapWeight μ) :=
  ((gapAbsTauIntegral_hasSum μ h).summable.mul_left 4).of_nonneg_of_le
    (gapWeight_nonneg μ h) (gapWeight_le_four_integral μ h)

theorem actualJ_nonneg (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) : 0 ≤ actualJ μ :=
  tsum_nonneg (gapWeight_nonneg μ h)

theorem actualJ_le_two_rho (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    actualJ μ ≤ 2 * thirdAbsoluteMoment μ := by
  have hs := (gapWeight_summable μ h).tsum_le_tsum (gapWeight_le_four_integral μ h)
    ((gapAbsTauIntegral_hasSum μ h).summable.mul_left 4)
  rw [tsum_mul_left] at hs
  have hb := gapAbsTauIntegral_tsum_le μ h
  unfold actualJ
  linarith

theorem actualJ_le_rho_of_zero_mem (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hzero : (0 : ℝ) ∈ (μ : Measure ℝ).support) : actualJ μ ≤ thirdAbsoluteMoment μ := by
  have hs := (gapWeight_summable μ h).tsum_le_tsum (gapWeight_le_two_integral μ h hzero)
    ((gapAbsTauIntegral_hasSum μ h).summable.mul_left 2)
  rw [tsum_mul_left] at hs
  have hb := gapAbsTauIntegral_tsum_le μ h
  unfold actualJ
  linarith

lemma gamma_le_rho (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    gamma μ ≤ thirdAbsoluteMoment μ := by
  apply integral_mono (integrable_signed_cube μ h) h.integrable_cube
  intro x
  exact (le_abs_self (x ^ 3)).trans_eq (abs_pow x 3)

def actualPhysicalDefect (μ : ProbabilityMeasure ℝ) : ℝ :=
  (3 + Real.sqrt 10) * thirdAbsoluteMoment μ - gamma μ - 3 * actualJ μ

theorem defect_lower_of_zero_mem (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hzero : (0 : ℝ) ∈ (μ : Measure ℝ).support) :
    (Real.sqrt 10 - 1) * thirdAbsoluteMoment μ ≤ actualPhysicalDefect μ := by
  have hJ := actualJ_le_rho_of_zero_mem μ h hzero
  have hγ := gamma_le_rho μ h
  unfold actualPhysicalDefect
  nlinarith only [hJ, hγ]

/-- A small actual defect excludes zero from the original support. -/
theorem zero_notMem_support_of_defect_small (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hsmall : actualPhysicalDefect μ < (Real.sqrt 10 - 1) * thirdAbsoluteMoment μ) :
    (0 : ℝ) ∉ (μ : Measure ℝ).support := by
  intro hzero
  exact (not_lt_of_ge (defect_lower_of_zero_mem μ h hzero)) hsmall

theorem centralGap_pos_of_defect_small (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hsmall : actualPhysicalDefect μ < (Real.sqrt 10 - 1) * thirdAbsoluteMoment μ) :
    0 < CentralGap.Aminus μ ∧ 0 < CentralGap.Aplus μ := by
  have hz := zero_notMem_support_of_defect_small μ h hsmall
  exact ⟨CentralGap.Aminus_pos μ h hz, CentralGap.Aplus_pos μ h hz⟩

end BerryEsseen.GapDefect

#print axioms BerryEsseen.GapDefect.gapWeight_summable
#print axioms BerryEsseen.GapDefect.actualJ_nonneg
#print axioms BerryEsseen.GapDefect.actualJ_le_two_rho
#print axioms BerryEsseen.GapDefect.actualJ_le_rho_of_zero_mem
#print axioms BerryEsseen.GapDefect.defect_lower_of_zero_mem
#print axioms BerryEsseen.GapDefect.zero_notMem_support_of_defect_small
#print axioms BerryEsseen.GapDefect.centralGap_pos_of_defect_small
