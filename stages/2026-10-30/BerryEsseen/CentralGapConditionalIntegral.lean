module

public import BerryEsseen.ContactGapSum
public import BerryEsseen.PhysicalResourcePlane
public import BerryEsseen.AffineSum
public import BerryEsseen.CallRampMinorants

@[expose] public section

/-! 2026-10-30: the actual central gap cost as a finite binomial mixture
of the original law's canonical conditional residual sums. Reflection of
the physical Ico interval gives Ioc: its left endpoint stays excluded.
The predecessor has exactly n-1 coordinates; no reference law is used. -/

noncomputable section

open MeasureTheory Set
open scoped BigOperators NNReal ENNReal

namespace BerryEsseen.CentralGapConditionalIntegral

open CanonicalSign CentralGap NoiseCoordinates GapDefect ContactGapResource

def windowCost (a b x : ℝ) : ℝ := (Ico a b).indicator (fun y => y - a) x

def tailCost (l u r : ℝ) : ℝ := (Ioc l u).indicator (fun y => u - y) r

def residualCountLaw (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (N k : ℕ) : Measure ℝ :=
  MixtureSum.convPower (residual1 μ h : Measure ℝ) k ∗
    MixtureSum.convPower (residual0 μ h : Measure ℝ) (N - k)

instance residualCountLaw_isProbability (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (N k : ℕ) : IsProbabilityMeasure (residualCountLaw μ h N k) := by
  unfold residualCountLaw
  infer_instance

theorem residualCountLaw_eq_map_W (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (N k : ℕ) (hk : k ≤ N) :
    residualCountLaw μ h N k =
      (CommonProduct.pairProduct (residual0 μ h : Measure ℝ) (residual1 μ h : Measure ℝ) N).map
        (CommonProduct.W N k) :=
  (CommonProduct.map_W _ _ N k hk).symm

def countWeight (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (N k : ℕ) : ℝ≥0 :=
  (N.choose k : ℝ≥0) * (NNReal.mk (p μ) (p_pos μ h).le) ^ k *
    (NNReal.mk (q μ) (q_pos μ h).le) ^ (N - k)

lemma coe_countWeight (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (N k : ℕ) :
    (countWeight μ h N k : ℝ) = CoupledPrice.canonicalBinomialWeight μ N k := by
  simp [countWeight, CoupledPrice.canonicalBinomialWeight]

def canonicalHeight (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (n : ℕ) (H : ℝ) : ℝ :=
  scale μ h * H + (n : ℝ) * p μ

def conditionalCost (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (n : ℕ)
    (H : ℝ) (k : ℕ) (r : ℝ) : ℝ :=
  tailCost (canonicalHeight μ h n H - k - 1 + a1 μ h)
    (canonicalHeight μ h n H - k - a0 μ h) r

lemma measurable_windowCost (a b : ℝ) : Measurable (windowCost a b) :=
  ((measurable_id.sub measurable_const).indicator measurableSet_Ico)

lemma norm_windowCost_le (a b x : ℝ) : ‖windowCost a b x‖ ≤ |b - a| := by
  by_cases hx : x ∈ Ico a b
  · rw [windowCost, Set.indicator_of_mem hx, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hx.1)]
    linarith [le_abs_self (b - a), hx.2]
  · simp [windowCost, hx]

lemma integrable_windowCost (ν : Measure ℝ) [IsFiniteMeasure ν] (a b : ℝ) :
    Integrable (windowCost a b) ν :=
  (integrable_const (|b - a|)).mono' (measurable_windowCost a b).aestronglyMeasurable
    (Filter.Eventually.of_forall (norm_windowCost_le a b))

lemma tailCost_nonneg (l u r : ℝ) : 0 ≤ tailCost l u r := by
  by_cases hr : r ∈ Ioc l u
  · simp only [tailCost, Set.indicator_of_mem hr]
    exact sub_nonneg.mpr hr.2
  · simp [tailCost, hr]

/-- Affine transformation of the genuine, unnormalized product sum. -/
theorem iidSumLaw_affine_map (μ : ProbabilityMeasure ℝ) (ν : Measure ℝ)
    [IsFiniteMeasure ν] (p c : ℝ)
    (hμ : (μ : Measure ℝ) = ν.map (fun u : ℝ => (u - p) / c)) (N : ℕ) :
    MixtureSum.iidSumLaw (μ : Measure ℝ) N =
      (MixtureSum.iidSumLaw ν N).map (fun u : ℝ => (u - (N : ℝ) * p) / c) := by
  have hf : Measurable (fun u : ℝ => (u - p) / c) := by fun_prop
  have hcoord : Measurable (fun z : Fin N → ℝ => fun i => (z i - p) / c) := by
    apply measurable_pi_iff.mpr
    intro i
    fun_prop
  have hpi := Measure.pi_map_pi (μ := fun _ : Fin N => ν)
    (f := fun _ => fun u : ℝ => (u - p) / c) (fun _ => hf.aemeasurable)
  have hfun : (fun z : Fin N → ℝ => ∑ i, z i) ∘
      (fun z : Fin N → ℝ => fun i => (z i - p) / c) =
      (fun u : ℝ => (u - (N : ℝ) * p) / c) ∘ (fun z : Fin N → ℝ => ∑ i, z i) := by
    funext z
    change (∑ i, (z i - p) / c) = _
    rw [← Finset.sum_div, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Function.comp_apply]
  unfold MixtureSum.iidSumLaw
  rw [hμ, ← hpi, Measure.map_map (by fun_prop) hcoord, hfun,
    ← Measure.map_map (by fun_prop) (by fun_prop)]

/-- Measure identity for the actual original iid law, not only its CDF. -/
theorem canonical_iidSumLaw (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (N : ℕ) :
    MixtureSum.iidSumLaw (μ : Measure ℝ) N =
      ∑ k ∈ Finset.range (N + 1), countWeight μ h N k •
        (residualCountLaw μ h N k).map
          (fun r : ℝ => ((k : ℝ) + r - (N : ℝ) * p μ) / scale μ h) := by
  let ν := AffineSum.residualSumMeasure (residual0 μ h) (residual1 μ h) (p μ)
    (p_pos μ h).le (p_lt_one μ h).le
  have hμ : (μ : Measure ℝ) = ν.map (fun u : ℝ => (u - p μ) / scale μ h) := by
    exact (congrArg (fun τ : ProbabilityMeasure ℝ => (τ : Measure ℝ))
      (CanonicalSign.law_eq_residualMixture μ h)).trans
        (AffineSum.residualMixtureLaw_eq_map _ _ _ _ _ _)
  rw [iidSumLaw_affine_map μ ν (p μ) (scale μ h) hμ N]
  dsimp [ν, AffineSum.residualSumMeasure]
  rw [MixtureSum.iidSumLaw_residualMixture, Measure.map_finset_sum (by fun_prop)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Measure.map_smul _ (by fun_prop), Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- The actual reflected predecessor law, with exactly n-1 coordinates. -/
theorem predecessorTailLaw_eq_sum (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (H : ℝ) :
    (ContactPolynomial.predecessorTailLaw μ n H : Measure ℝ) =
      ∑ k ∈ Finset.range ((n - 1) + 1), countWeight μ h (n - 1) k •
        (residualCountLaw μ h (n - 1) k).map
          (fun r : ℝ => H - ((k : ℝ) + r - ((n - 1 : ℕ) : ℝ) * p μ) / scale μ h) := by
  change (MixtureSum.iidSumLaw (μ : Measure ℝ) (n - 1)).map (fun y : ℝ => H - y) = _
  rw [canonical_iidSumLaw μ h, Measure.map_finset_sum (by fun_prop)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Measure.map_smul _ (by fun_prop), Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

theorem predecessor_window_integral (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (H a b : ℝ) :
    (∫ y, windowCost a b y ∂(ContactPolynomial.predecessorTailLaw μ n H : Measure ℝ)) =
      ∑ k ∈ Finset.range ((n - 1) + 1), CoupledPrice.canonicalBinomialWeight μ (n - 1) k *
        ∫ r, windowCost a b
          (H - ((k : ℝ) + r - ((n - 1 : ℕ) : ℝ) * p μ) / scale μ h)
          ∂residualCountLaw μ h (n - 1) k := by
  rw [predecessorTailLaw_eq_sum μ h]
  rw [integral_finsetSum_measure (by intro k hk; exact integrable_windowCost _ a b)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [integral_smul_nnreal_measure,
    integral_map (by fun_prop) (measurable_windowCost a b).aestronglyMeasurable]
  simp only [NNReal.smul_def, smul_eq_mul, coe_countWeight]

lemma affine_windowCost (a b l u c y r : ℝ) (hc : 0 < c)
    (hleft : c * (y - a) = u - r) (hright : c * (b - y) = r - l) :
    windowCost a b y = (1 / c) * tailCost l u r := by
  have he : y ∈ Ico a b ↔ r ∈ Ioc l u := by
    constructor
    · rintro ⟨hay, hyb⟩
      constructor
      · have hp := mul_pos hc (sub_pos.mpr hyb)
        linarith
      · have hp := mul_nonneg hc.le (sub_nonneg.mpr hay)
        linarith
    · rintro ⟨hlr, hru⟩
      constructor
      · by_contra hay
        have hp := mul_neg_of_pos_of_neg hc (sub_neg.mpr (lt_of_not_ge hay))
        linarith
      · by_contra hyb
        have hp := mul_nonpos_of_nonneg_of_nonpos hc.le (sub_nonpos.mpr (le_of_not_gt hyb))
        linarith
  by_cases hy : y ∈ Ico a b
  · rw [windowCost, tailCost, Set.indicator_of_mem hy, Set.indicator_of_mem (he.mp hy)]
    field_simp [hc.ne']
    nlinarith [hleft]
  · simp [windowCost, tailCost, hy, show r ∉ Ioc l u from fun hr => hy (he.mpr hr)]

lemma physical_window_eq_conditionalCost (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (hn : 0 < n) (H : ℝ) (k : ℕ) (r : ℝ) :
    windowCost (-Aminus μ) (Aplus μ)
      (H - ((k : ℝ) + r - ((n - 1 : ℕ) : ℝ) * p μ) / scale μ h) =
      (1 / scale μ h) * conditionalCost μ h n H k r := by
  have hncast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  apply affine_windowCost _ _ _ _ _ _ _ (scale_pos μ h)
  · dsimp [conditionalCost, canonicalHeight, a0]
    rw [hncast]
    field_simp [(scale_pos μ h).ne']
    ring
  · dsimp [conditionalCost, canonicalHeight, a1, q]
    rw [hncast]
    field_simp [(scale_pos μ h).ne']
    ring

/-- Exact central cost: all terms are the true conditional laws of μ. -/
theorem central_Lg_eq_conditional_sum (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hz : (0 : ℝ) ∉ (μ : Measure ℝ).support) (n : ℕ) (hn : 0 < n) (H : ℝ) :
    Lg μ n H (PhysicalDefect.centralGap μ h hz) =
      (1 - theta μ h) *
        ∑ k ∈ Finset.range ((n - 1) + 1), CoupledPrice.canonicalBinomialWeight μ (n - 1) k *
          ∫ r, conditionalCost μ h n H k r ∂residualCountLaw μ h (n - 1) k := by
  rw [Lg, PhysicalDefect.centralGap_tau]
  change positiveFirstMoment μ * (∫ y in Ico (-Aminus μ) (Aplus μ), y - -Aminus μ
    ∂(ContactPolynomial.predecessorTailLaw μ n H : Measure ℝ)) = _
  rw [← integral_indicator measurableSet_Ico]
  change positiveFirstMoment μ * (∫ y, windowCost (-Aminus μ) (Aplus μ) y
    ∂(ContactPolynomial.predecessorTailLaw μ n H : Measure ℝ)) = _
  rw [predecessor_window_integral μ h]
  simp_rw [physical_window_eq_conditionalCost μ h n hn H, integral_const_mul]
  have he := positiveFirstMoment_div_scale μ h
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← he]
  simp only [div_eq_mul_inv]
  ring

/-- The whole actual gap sum dominates this genuine central term. -/
theorem conditional_sum_le_actualL (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (R : ℝ) (hR : 0 ≤ R) (hbound : (μ : Measure ℝ).support ⊆ Icc (-R) R)
    (hz : (0 : ℝ) ∉ (μ : Measure ℝ).support) (n : ℕ) (hn : 0 < n) (H C : ℝ)
    (hm : ContactVariation.PositiveClosedMaximum μ n H C) :
    (1 - theta μ h) *
      ∑ k ∈ Finset.range ((n - 1) + 1), CoupledPrice.canonicalBinomialWeight μ (n - 1) k *
        ∫ r, conditionalCost μ h n H k r ∂residualCountLaw μ h (n - 1) k ≤
      ContactGapSum.actualL μ n H := by
  rw [← central_Lg_eq_conditional_sum μ h hz n hn H]
  exact (ContactGapSum.summable_Lg μ h R hR hbound n hn H C hm).le_tsum
    (PhysicalDefect.centralGap μ h hz) (fun g hg => Lg_nonneg μ h n H g)

lemma tailCost_eq_positiveRamp (l u r : ℝ) :
    tailCost l u r = CallRampMinorants.positiveRamp (u - l) (r - l) := by
  have he : r ∈ Ioc l u ↔ 0 < r - l ∧ r - l ≤ u - l := by
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  by_cases hr : r ∈ Ioc l u
  · rw [tailCost, Set.indicator_of_mem hr, CallRampMinorants.positiveRamp, ite_eq_left (he.mp hr)]
    ring
  · rw [tailCost, Set.indicator_of_notMem hr, CallRampMinorants.positiveRamp,
      ite_eq_right (fun hx => hr (he.mpr hx))]

lemma tailCost_eq_negativeRamp (l u r : ℝ) :
    tailCost l u r = CallRampMinorants.negativeRamp (u - l) (u - r) := by
  have he : r ∈ Ioc l u ↔ 0 ≤ u - r ∧ u - r < u - l := by
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  by_cases hr : r ∈ Ioc l u
  · rw [tailCost, Set.indicator_of_mem hr, CallRampMinorants.negativeRamp, ite_eq_left (he.mp hr)]
  · rw [tailCost, Set.indicator_of_notMem hr, CallRampMinorants.negativeRamp,
      ite_eq_right (fun hx => hr (he.mpr hx))]

/-- Count j-1 is the positive ramp, with its zero endpoint excluded. -/
lemma conditionalCost_preceding_count (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (H : ℝ) (j : ℕ) (t : ℝ) (hj : 1 ≤ j)
    (hphase : canonicalHeight μ h n H = (j : ℝ) + t) (r : ℝ) :
    conditionalCost μ h n H (j - 1) r =
      CallRampMinorants.positiveRamp (1 - a0 μ h - a1 μ h) (r - t - a1 μ h) := by
  have hjcast : ((j - 1 : ℕ) : ℝ) = (j : ℝ) - 1 := by
    rw [Nat.cast_sub hj]
    norm_num
  unfold conditionalCost
  rw [tailCost_eq_positiveRamp]
  congr 1
  · ring
  · rw [hphase, hjcast]
    ring

/-- Count j is the negative ramp, with its g endpoint excluded. -/
lemma conditionalCost_current_count (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (H : ℝ) (j : ℕ) (t : ℝ)
    (hphase : canonicalHeight μ h n H = (j : ℝ) + t) (r : ℝ) :
    conditionalCost μ h n H j r =
      CallRampMinorants.negativeRamp (1 - a0 μ h - a1 μ h) (t - a0 μ h - r) := by
  unfold conditionalCost
  rw [tailCost_eq_negativeRamp]
  congr 1
  · ring
  · rw [hphase]
    ring

/-- Both adjacent counts come from the same original predecessor law.
The phase is arbitrary and neither conditional law is a two-point law. -/
theorem adjacent_ramps_le_actualL (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (R : ℝ) (hR : 0 ≤ R) (hbound : (μ : Measure ℝ).support ⊆ Icc (-R) R)
    (hz : (0 : ℝ) ∉ (μ : Measure ℝ).support) (n : ℕ) (hn : 2 ≤ n) (H C : ℝ)
    (hm : ContactVariation.PositiveClosedMaximum μ n H C) (j : ℕ) (hj : 1 ≤ j)
    (hjn : j ≤ n - 1) (t : ℝ) (hphase : canonicalHeight μ h n H = (j : ℝ) + t) :
    (1 - theta μ h) *
      (CoupledPrice.canonicalBinomialWeight μ (n - 1) (j - 1) *
          (∫ r, CallRampMinorants.positiveRamp (1 - a0 μ h - a1 μ h) (r - t - a1 μ h)
            ∂residualCountLaw μ h (n - 1) (j - 1)) +
        CoupledPrice.canonicalBinomialWeight μ (n - 1) j *
          (∫ r, CallRampMinorants.negativeRamp (1 - a0 μ h - a1 μ h) (t - a0 μ h - r)
            ∂residualCountLaw μ h (n - 1) j)) ≤ ContactGapSum.actualL μ n H := by
  let F : ℕ → ℝ := fun k => CoupledPrice.canonicalBinomialWeight μ (n - 1) k *
    ∫ r, conditionalCost μ h n H k r ∂residualCountLaw μ h (n - 1) k
  have hF : ∀ k, 0 ≤ F k := by
    intro k
    exact mul_nonneg (CoupledPrice.canonicalBinomialWeight_nonneg μ h (n - 1) k)
      (integral_nonneg (fun r => tailCost_nonneg _ _ _))
  have hsub : ({j - 1, j} : Finset ℕ) ⊆ Finset.range ((n - 1) + 1) := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl <;> simp only [Finset.mem_range] <;> omega
  have hpair : F (j - 1) + F j ≤ ∑ k ∈ Finset.range ((n - 1) + 1), F k := by
    have hs := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k hk hnot => hF k)
    simpa only [Finset.sum_pair (by omega : j - 1 ≠ j)] using hs
  have hmul := mul_le_mul_of_nonneg_left hpair (sub_pos.mpr (theta_lt_one μ h)).le
  have hfull := conditional_sum_le_actualL μ h R hR hbound hz n (by omega) H C hm
  apply le_trans ?_ hfull
  simpa only [F, conditionalCost_preceding_count μ h n H j t hj hphase,
    conditionalCost_current_count μ h n H j t hphase] using hmul

/-- The shifted variables to which the generic positive-ramp bound applies. -/
def positiveAdjacentLaw (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n j : ℕ) (t : ℝ) : Measure ℝ :=
  (residualCountLaw μ h (n - 1) (j - 1)).map (fun r : ℝ => r - t - a1 μ h)

/-- The reflected shifted variables to which the generic negative-ramp bound applies. -/
def negativeAdjacentLaw (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n j : ℕ) (t : ℝ) : Measure ℝ :=
  (residualCountLaw μ h (n - 1) j).map (fun r : ℝ => t - a0 μ h - r)

instance positiveAdjacentLaw_isProbability (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n j : ℕ) (t : ℝ) : IsProbabilityMeasure (positiveAdjacentLaw μ h n j t) := by
  unfold positiveAdjacentLaw
  infer_instance

instance negativeAdjacentLaw_isProbability (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n j : ℕ) (t : ℝ) : IsProbabilityMeasure (negativeAdjacentLaw μ h n j t) := by
  unfold negativeAdjacentLaw
  infer_instance

/-- Direct real-law API for the generic call/ramp moment and reference bounds. -/
theorem adjacent_laws_le_actualL (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (R : ℝ) (hR : 0 ≤ R) (hbound : (μ : Measure ℝ).support ⊆ Icc (-R) R)
    (hz : (0 : ℝ) ∉ (μ : Measure ℝ).support) (n : ℕ) (hn : 2 ≤ n) (H C : ℝ)
    (hm : ContactVariation.PositiveClosedMaximum μ n H C) (j : ℕ) (hj : 1 ≤ j)
    (hjn : j ≤ n - 1) (t : ℝ) (hphase : canonicalHeight μ h n H = (j : ℝ) + t) :
    (1 - theta μ h) *
      (CoupledPrice.canonicalBinomialWeight μ (n - 1) (j - 1) *
          (∫ x, CallRampMinorants.positiveRamp (1 - a0 μ h - a1 μ h) x
            ∂positiveAdjacentLaw μ h n j t) +
        CoupledPrice.canonicalBinomialWeight μ (n - 1) j *
          (∫ x, CallRampMinorants.negativeRamp (1 - a0 μ h - a1 μ h) x
            ∂negativeAdjacentLaw μ h n j t)) ≤ ContactGapSum.actualL μ n H := by
  unfold positiveAdjacentLaw negativeAdjacentLaw
  rw [integral_map (by fun_prop) (CallRampMinorants.measurable_positiveRamp _).aestronglyMeasurable,
    integral_map (by fun_prop) (CallRampMinorants.measurable_negativeRamp _).aestronglyMeasurable]
  exact adjacent_ramps_le_actualL μ h R hR hbound hz n hn H C hm j hj hjn t hphase

end BerryEsseen.CentralGapConditionalIntegral

#print axioms BerryEsseen.CentralGapConditionalIntegral.canonical_iidSumLaw
#print axioms BerryEsseen.CentralGapConditionalIntegral.predecessorTailLaw_eq_sum
#print axioms BerryEsseen.CentralGapConditionalIntegral.central_Lg_eq_conditional_sum
#print axioms BerryEsseen.CentralGapConditionalIntegral.conditional_sum_le_actualL
#print axioms BerryEsseen.CentralGapConditionalIntegral.adjacent_ramps_le_actualL
#print axioms BerryEsseen.CentralGapConditionalIntegral.adjacent_laws_le_actualL
