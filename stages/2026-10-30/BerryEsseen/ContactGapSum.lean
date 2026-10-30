module

public import BerryEsseen.ContactGapResource
public import Mathlib.Analysis.Normed.Group.InfiniteSum

@[expose] public section

/-!
The first contact-resource evaluation over the complete genuine gap
family. All convergence and coverage statements in the final evaluation
retain an explicit bounded-support hypothesis on the original law.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology Interval BigOperators

namespace BerryEsseen.ContactGapSum

open ZeroBias GapDefect ContactPolynomial ContactGapResource SupportGaps

def actualJ1 (μ : ProbabilityMeasure ℝ) : ℝ := ∑' g : Gap μ, J1g μ g
def actualJ2 (μ : ProbabilityMeasure ℝ) : ℝ := ∑' g : Gap μ, J2g μ g
def actualL (μ : ProbabilityMeasure ℝ) (n : ℕ) (H : ℝ) : ℝ := ∑' g : Gap μ, Lg μ n H g

lemma gap_point_abs_le (μ : ProbabilityMeasure ℝ) (R : ℝ)
    (hbound : (μ : Measure ℝ).support ⊆ Icc (-R) R) (g : Gap μ) (t : ℝ)
    (ht : t ∈ Icc g.val.1 g.val.2) : |t| ≤ R := by
  apply abs_le.mpr
  exact ⟨le_trans (hbound g.property.1).1 ht.1,
    le_trans ht.2 (hbound g.property.2.1).2⟩

theorem abs_J1g_le (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (R : ℝ)
    (hbound : (μ : Measure ℝ).support ⊆ Icc (-R) R) (g : Gap μ) :
    |J1g μ g| ≤ R * Jg μ g / 2 := by
  let a := g.val.1
  let b := g.val.2
  have hab : a ≤ b := g.property.2.2.1.le
  have hd : IntervalIntegrable (fun t : ℝ => R * (t - a)) volume a b := by
    have hc : Continuous (fun t : ℝ => R * (t - a)) := by fun_prop
    exact hc.intervalIntegrable a b
  have hi := intervalIntegral.norm_integral_le_of_norm_le (f := fun t : ℝ => (t - a) * t) hab
    (Filter.Eventually.of_forall fun t ht => by
      change ‖(t - a) * t‖ ≤ R * (t - a)
      have htR := gap_point_abs_le μ R hbound g t ⟨ht.1.le, ht.2⟩
      have hs : 0 ≤ t - a := sub_nonneg.mpr ht.1.le
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hs]
      nlinarith [mul_le_mul_of_nonneg_left htR hs]) hd
  rw [intervalIntegral.integral_const_mul, integral_gap0] at hi
  calc
    |J1g μ g| = tau μ b * |∫ t in a..b, (t - a) * t| := by
      unfold J1g
      rw [abs_mul, abs_of_nonneg (tau_nonneg μ h g.val.2)]
    _ ≤ tau μ b * (R * ((b - a) ^ 2 / 2)) :=
      mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using hi) (tau_nonneg μ h b)
    _ = _ := by unfold Jg gapWeight; dsimp [a, b]; ring

theorem abs_J2g_le (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (R : ℝ) (hR : 0 ≤ R)
    (hbound : (μ : Measure ℝ).support ⊆ Icc (-R) R) (g : Gap μ) :
    |J2g μ g| ≤ R ^ 2 * Jg μ g / 2 := by
  let a := g.val.1
  let b := g.val.2
  have hab : a ≤ b := g.property.2.2.1.le
  have hd : IntervalIntegrable (fun t : ℝ => R ^ 2 * (t - a)) volume a b := by
    have hc : Continuous (fun t : ℝ => R ^ 2 * (t - a)) := by fun_prop
    exact hc.intervalIntegrable a b
  have hi := intervalIntegral.norm_integral_le_of_norm_le (f := fun t : ℝ => (t - a) * t * |t|) hab
    (Filter.Eventually.of_forall fun t ht => by
      change ‖(t - a) * t * |t|‖ ≤ R ^ 2 * (t - a)
      have htR := gap_point_abs_le μ R hbound g t ⟨ht.1.le, ht.2⟩
      have hs : 0 ≤ t - a := sub_nonneg.mpr ht.1.le
      have hsq := (sq_le_sq₀ (abs_nonneg t) hR).mpr htR
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_abs, abs_of_nonneg hs]
      nlinarith [mul_le_mul_of_nonneg_left hsq hs]) hd
  rw [intervalIntegral.integral_const_mul, integral_gap0] at hi
  calc
    |J2g μ g| = tau μ b * abs (∫ t in a..b, (t - a) * t * |t|) := by
      unfold J2g
      rw [abs_mul, abs_of_nonneg (tau_nonneg μ h g.val.2)]
    _ ≤ tau μ b * (R ^ 2 * ((b - a) ^ 2 / 2)) :=
      mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using hi) (tau_nonneg μ h b)
    _ = _ := by unfold Jg gapWeight; dsimp [a, b]; ring

theorem summable_J1g (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (R : ℝ)
    (hbound : (μ : Measure ℝ).support ⊆ Icc (-R) R) : Summable (J1g μ) := by
  apply ((gapWeight_summable μ h).mul_left (R / 2)).of_norm_bounded
  intro g
  calc
    ‖J1g μ g‖ = |J1g μ g| := Real.norm_eq_abs _
    _ ≤ R * Jg μ g / 2 := abs_J1g_le μ h R hbound g
    _ = _ := by unfold Jg; ring

theorem summable_J2g (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (R : ℝ) (hR : 0 ≤ R)
    (hbound : (μ : Measure ℝ).support ⊆ Icc (-R) R) : Summable (J2g μ) := by
  apply ((gapWeight_summable μ h).mul_left (R ^ 2 / 2)).of_norm_bounded
  intro g
  calc
    ‖J2g μ g‖ = |J2g μ g| := Real.norm_eq_abs _
    _ ≤ R ^ 2 * Jg μ g / 2 := abs_J2g_le μ h R hR hbound g
    _ = _ := by unfold Jg; ring

lemma hasSum_Ig_add_Lg (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (R : ℝ) (hR : 0 ≤ R) (hbound : (μ : Measure ℝ).support ⊆ Icc (-R) R)
    (n : ℕ) (hn : 0 < n) (H C : ℝ)
    (hm : ContactVariation.PositiveClosedMaximum μ n H C) :
    HasSum (fun g : Gap μ => Ig μ n H C g + Lg μ n H g)
      (GaussianTools.phi (H / Real.sqrt n) / (2 * Real.sqrt n) * actualJ μ +
        (((3 : ℝ) / 2) * C * SignedMoment.signedSecondMoment μ * actualJ μ +
          (H * GaussianTools.phi (H / Real.sqrt n) + 3 * C * thirdAbsoluteMoment μ) * actualJ1 μ -
          3 * C * actualJ2 μ) / ((n : ℝ) * Real.sqrt n)) := by
  have hJ : HasSum (Jg μ) (actualJ μ) := (gapWeight_summable μ h).hasSum
  have hJ1 : HasSum (J1g μ) (actualJ1 μ) := (summable_J1g μ h R hbound).hasSum
  have hJ2 : HasSum (J2g μ) (actualJ2 μ) := (summable_J2g μ h R hR hbound).hasSum
  have hs := (hJ.mul_left (GaussianTools.phi (H / Real.sqrt n) / (2 * Real.sqrt n))).add
    ((((hJ.mul_left (((3 : ℝ) / 2) * C * SignedMoment.signedSecondMoment μ)).add
      (hJ1.mul_left (H * GaussianTools.phi (H / Real.sqrt n) + 3 * C * thirdAbsoluteMoment μ))).sub
      (hJ2.mul_left (3 * C))).div_const ((n : ℝ) * Real.sqrt n))
  have heq : (fun g : Gap μ => Ig μ n H C g + Lg μ n H g) =
      (fun g : Gap μ => GaussianTools.phi (H / Real.sqrt n) / (2 * Real.sqrt n) * Jg μ g +
        ((((3 : ℝ) / 2) * C * SignedMoment.signedSecondMoment μ) * Jg μ g +
          (H * GaussianTools.phi (H / Real.sqrt n) + 3 * C * thirdAbsoluteMoment μ) * J1g μ g -
          (3 * C) * J2g μ g) / ((n : ℝ) * Real.sqrt n)) := by
    funext g
    have hg := single_gap_identity μ h n hn H C hm g
    linarith
  rw [heq]
  exact hs

theorem summable_Ig (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (R : ℝ) (hR : 0 ≤ R) (hbound : (μ : Measure ℝ).support ⊆ Icc (-R) R)
    (n : ℕ) (hn : 0 < n) (H C : ℝ)
    (hm : ContactVariation.PositiveClosedMaximum μ n H C) : Summable (Ig μ n H C) := by
  exact (hasSum_Ig_add_Lg μ h R hR hbound n hn H C hm).summable.of_nonneg_of_le
    (Ig_nonneg μ h n hn H C hm) (fun g => le_add_of_nonneg_right (Lg_nonneg μ h n H g))

theorem summable_Lg (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (R : ℝ) (hR : 0 ≤ R) (hbound : (μ : Measure ℝ).support ⊆ Icc (-R) R)
    (n : ℕ) (hn : 0 < n) (H C : ℝ)
    (hm : ContactVariation.PositiveClosedMaximum μ n H C) : Summable (Lg μ n H) := by
  exact (hasSum_Ig_add_Lg μ h R hR hbound n hn H C hm).summable.of_nonneg_of_le
    (Lg_nonneg μ h n H) (fun g => le_add_of_nonneg_left (Ig_nonneg μ h n hn H C hm g))

theorem actualL_nonneg (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (R : ℝ) (hR : 0 ≤ R) (hbound : (μ : Measure ℝ).support ⊆ Icc (-R) R)
    (n : ℕ) (hn : 0 < n) (H C : ℝ)
    (hm : ContactVariation.PositiveClosedMaximum μ n H C) : 0 ≤ actualL μ n H := by
  have hs := (summable_Lg μ h R hR hbound n hn H C hm).hasSum
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hs
  exact Filter.Eventually.of_forall fun s => Finset.sum_nonneg fun g _ => Lg_nonneg μ h n H g

lemma tau_zero_outside_interval (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (a b t : ℝ) (hbound : (μ : Measure ℝ).support ⊆ Icc a b) (ht : t < a ∨ b < t) : tau μ t = 0 := by
  have hsp : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ (μ : Measure ℝ).support := (μ : Measure ℝ).support_mem_ae
  rcases ht with ht | ht
  · rw [tau_eq_lower_tail μ h t, ← integral_indicator measurableSet_Iio]
    calc
      _ = ∫ _ : ℝ, (0 : ℝ) ∂(μ : Measure ℝ) := integral_congr_ae (hsp.mono fun x hx => by
        have hb := (hbound hx).1
        have hxt : ¬x < t := by linarith
        simp only [Set.indicator_apply, mem_Iio, ite_eq_right hxt])
      _ = 0 := integral_zero _ _
  · rw [tau_eq_integral_if]
    calc
      _ = ∫ _ : ℝ, (0 : ℝ) ∂(μ : Measure ℝ) := integral_congr_ae (hsp.mono fun x hx => by
        have hb := (hbound hx).2
        have htx : ¬t ≤ x := by linarith
        change (if t ≤ x then x else 0) = (0 : ℝ)
        rw [ite_eq_right htx])
      _ = 0 := integral_zero _ _

theorem integrand_zero_off_gapUnion (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (R : ℝ) (hbound : (μ : Measure ℝ).support ⊆ Icc (-R) R)
    (n : ℕ) (hn : 0 < n) (H C : ℝ)
    (hm : ContactVariation.PositiveClosedMaximum μ n H C) (t : ℝ) (ht : t ∉ gapUnion μ) :
    integrand μ n H C t = 0 := by
  have hc : IsCompact (μ : Measure ℝ).support :=
    isCompact_Icc.of_isClosed_subset (μ : Measure ℝ).isClosed_support hbound
  have hne := (μ : Measure ℝ).nonempty_support (IsProbabilityMeasure.ne_zero _)
  by_cases htS : t ∈ (μ : Measure ℝ).support
  · unfold integrand GapIntegration.closedTail
    rw [majorant_eq_closedTail_on_support μ h n hn H C hm t htS, sub_self, mul_zero]
  · by_cases htHull : t ∈ Icc (sInf (μ : Measure ℝ).support) (sSup (μ : Measure ℝ).support)
    · obtain ⟨g, hg, htg⟩ := exists_gap_of_mem_hull_diff (μ : Measure ℝ).support hc hne t ⟨htHull, htS⟩
      exfalso
      apply ht
      exact Set.mem_iUnion.mpr ⟨⟨g, hg⟩, htg⟩
    · have hsub : (μ : Measure ℝ).support ⊆ Icc (sInf (μ : Measure ℝ).support) (sSup (μ : Measure ℝ).support) :=
        fun x hx => ⟨csInf_le hc.bddBelow hx, le_csSup hc.bddAbove hx⟩
      have hout : t < sInf (μ : Measure ℝ).support ∨ sSup (μ : Measure ℝ).support < t := by
        by_cases hL : sInf (μ : Measure ℝ).support ≤ t
        · exact Or.inr (lt_of_not_ge fun hU => htHull ⟨hL, hU⟩)
        · exact Or.inl (lt_of_not_ge hL)
      have hz := tau_zero_outside_interval μ h _ _ t hsub hout
      unfold integrand
      rw [hz, zero_mul]

lemma measurable_closedTail (ν : ProbabilityMeasure ℝ) : Measurable (GapIntegration.closedTail ν) := by
  have heq : GapIntegration.closedTail ν =
      (fun t : ℝ => ∫ y : ℝ, GapIntegration.tailIndicator y t ∂(ν : Measure ℝ)) :=
    funext (GapIntegration.closedTail_eq_integral ν)
  rw [heq]
  exact GapIntegration.measurable_tailIndicator.stronglyMeasurable.integral_prod_left.measurable

theorem measurable_integrand (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (n : ℕ) (H C : ℝ) :
    Measurable (integrand μ n H C) := by
  unfold integrand
  exact (measurable_tau μ h).mul
    ((continuous_majorant μ n H C).measurable.sub (measurable_closedTail (predecessorTailLaw μ n H)))

lemma gapUnion_open (μ : ProbabilityMeasure ℝ) : IsOpen (gapUnion μ) :=
  isOpen_iUnion (fun _ => isOpen_Ioo)

lemma integrand_indicator_eq_self (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (R : ℝ) (hbound : (μ : Measure ℝ).support ⊆ Icc (-R) R)
    (n : ℕ) (hn : 0 < n) (H C : ℝ)
    (hm : ContactVariation.PositiveClosedMaximum μ n H C) :
    (gapUnion μ).indicator (integrand μ n H C) = integrand μ n H C := by
  funext t
  by_cases ht : t ∈ gapUnion μ
  · simp [ht]
  · simp [ht, integrand_zero_off_gapUnion μ h R hbound n hn H C hm t ht]

theorem integrable_full_integrand (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (R : ℝ) (hR : 0 ≤ R) (hbound : (μ : Measure ℝ).support ⊆ Icc (-R) R)
    (n : ℕ) (hn : 0 < n) (H C : ℝ)
    (hm : ContactVariation.PositiveClosedMaximum μ n H C) : Integrable (integrand μ n H C) := by
  have hnon : ∀ t : ℝ, 0 ≤ integrand μ n H C t := by
    intro t
    unfold integrand GapIntegration.closedTail
    exact mul_nonneg (tau_nonneg μ h t) (sub_nonneg.mpr (closedTail_le_majorant μ h n hn H C hm t))
  have hnorm : (fun g : Gap μ => ∫ t in Ioo g.val.1 g.val.2, ‖integrand μ n H C t‖) = Ig μ n H C := by
    funext g
    unfold Ig
    exact integral_congr_ae (Filter.Eventually.of_forall fun t => by
      change ‖integrand μ n H C t‖ = integrand μ n H C t
      rw [Real.norm_eq_abs, abs_of_nonneg (hnon t)])
  have hnormSum : Summable (fun g : Gap μ => ∫ t in Ioo g.val.1 g.val.2, ‖integrand μ n H C t‖) := by
    rw [hnorm]
    exact summable_Ig μ h R hR hbound n hn H C hm
  have hUnion : IntegrableOn (integrand μ n H C) (gapUnion μ) :=
    integrableOn_iUnion_of_summable_integral_norm (fun g => integrable_integrand_on_gap μ h n H C g) hnormSum
  have hi := hUnion.integrable_indicator (gapUnion_open μ).measurableSet
  rw [integrand_indicator_eq_self μ h R hbound n hn H C hm] at hi
  exact hi

theorem hasSum_Ig_full_integral (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (R : ℝ) (hR : 0 ≤ R) (hbound : (μ : Measure ℝ).support ⊆ Icc (-R) R)
    (n : ℕ) (hn : 0 < n) (H C : ℝ)
    (hm : ContactVariation.PositiveClosedMaximum μ n H C) :
    HasSum (Ig μ n H C) (∫ t : ℝ, integrand μ n H C t) := by
  have hd : Pairwise (fun g k : Gap μ => Disjoint (Ioo g.val.1 g.val.2) (Ioo k.val.1 k.val.2)) := by
    intro g k hne
    apply gapSet_pairwiseDisjoint (μ : Measure ℝ).support g.property k.property
    exact fun heq => hne (Subtype.ext heq)
  have hs : HasSum (Ig μ n H C) (∫ t in gapUnion μ, integrand μ n H C t) :=
    hasSum_integral_iUnion (fun _ => measurableSet_Ioo) hd
      (integrable_full_integrand μ h R hR hbound n hn H C hm).integrableOn
  have heq : (∫ t in gapUnion μ, integrand μ n H C t) = ∫ t : ℝ, integrand μ n H C t := by
    rw [← integral_indicator (gapUnion_open μ).measurableSet,
      integrand_indicator_eq_self μ h R hbound n hn H C hm]
  rw [heq] at hs
  exact hs

/-- The full first resource evaluation, with genuine convergent gap
series and a pointwise full-space coverage proof under bounded support. -/
theorem first_resource_identity (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (R : ℝ) (hR : 0 ≤ R) (hbound : (μ : Measure ℝ).support ⊆ Icc (-R) R)
    (n : ℕ) (hn : 0 < n) (H C : ℝ)
    (hm : ContactVariation.PositiveClosedMaximum μ n H C) :
    (∫ t : ℝ, integrand μ n H C t) =
      GaussianTools.phi (H / Real.sqrt n) / (2 * Real.sqrt n) * actualJ μ +
      (((3 : ℝ) / 2) * C * SignedMoment.signedSecondMoment μ * actualJ μ +
        (H * GaussianTools.phi (H / Real.sqrt n) + 3 * C * thirdAbsoluteMoment μ) * actualJ1 μ -
        3 * C * actualJ2 μ) / ((n : ℝ) * Real.sqrt n) - actualL μ n H := by
  have hI := hasSum_Ig_full_integral μ h R hR hbound n hn H C hm
  have hL : HasSum (Lg μ n H) (actualL μ n H) := (summable_Lg μ h R hR hbound n hn H C hm).hasSum
  have hsum := (hI.add hL).unique (hasSum_Ig_add_Lg μ h R hR hbound n hn H C hm)
  linarith

end BerryEsseen.ContactGapSum

#print axioms BerryEsseen.ContactGapSum.summable_J1g
#print axioms BerryEsseen.ContactGapSum.summable_J2g
#print axioms BerryEsseen.ContactGapSum.summable_Ig
#print axioms BerryEsseen.ContactGapSum.summable_Lg
#print axioms BerryEsseen.ContactGapSum.actualL_nonneg
#print axioms BerryEsseen.ContactGapSum.integrand_zero_off_gapUnion
#print axioms BerryEsseen.ContactGapSum.integrable_full_integrand
#print axioms BerryEsseen.ContactGapSum.hasSum_Ig_full_integral
#print axioms BerryEsseen.ContactGapSum.first_resource_identity
