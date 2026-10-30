module

public import BerryEsseen.HighFrequencyDistance
public import BerryEsseen.HighFrequencyEvent
public import BerryEsseen.HighFrequencyCantelli

@[expose] public section

/-! 2026-10-29: actual conditional averaging of the original CF tail.
The product measure is the actual eventLaw times restricted Lebesgue measure.
Its joint L¹ hypothesis is proved before Fubini. This module covers the four
tail prices beyond b, without the middle segment, comparator, or floor gates. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open BerryEsseen.HighFrequencyCells BerryEsseen.HighFrequencyPeriodic
open BerryEsseen.HighFrequencyZeroCell BerryEsseen.HighFrequencyDistance
open BerryEsseen.HighFrequencyEvent

namespace BerryEsseen.HighFrequencyTail

def actualIntegrand (μ : ProbabilityMeasure ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  ‖charFun (μ : Measure ℝ) t ^ n‖ / t ^ 3

def complexIntegrand (μ : ProbabilityMeasure ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  charFun (μ : Measure ℝ) t ^ n / (t : ℂ) ^ 3

def jointKernel (n : ℕ) (a : ℝ) (z : (ℝ × ℝ) × ℝ) : ℝ :=
  fixedDistanceIntegrand n a (HighFrequencyEvent.distance z.1) z.2

lemma actualIntegrand_eq_norm_pow (μ : ProbabilityMeasure ℝ) (n : ℕ) (t : ℝ) :
    actualIntegrand μ n t = ‖charFun (μ : Measure ℝ) t‖ ^ n / t ^ 3 := by
  rw [actualIntegrand, norm_pow]

lemma norm_complexIntegrand (μ : ProbabilityMeasure ℝ) (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    ‖complexIntegrand μ n t‖ = actualIntegrand μ n t := by
  simp only [complexIntegrand, actualIntegrand, norm_div, norm_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht]

lemma measurable_actualIntegrand (μ : ProbabilityMeasure ℝ) (n : ℕ) : Measurable (actualIntegrand μ n) := by
  have hf := LowFrequencyError.measurable_actual_charFun μ
  unfold actualIntegrand
  fun_prop

lemma integrableOn_actualIntegrand (μ : ProbabilityMeasure ℝ) (n : ℕ) (b : ℝ) (hb : 0 < b) :
    IntegrableOn (actualIntegrand μ n) (Ioi b) := by
  apply (integrableOn_inverseCube b hb).mono' (measurable_actualIntegrand μ n).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 ≤ t := (hb.trans ht).le
  have hp : ‖charFun (μ : Measure ℝ) t‖ ^ n ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg _)
      (norm_charFun_le_one (μ := (μ : Measure ℝ)) t) n
  have hn0 : 0 ≤ actualIntegrand μ n t := div_nonneg (norm_nonneg _) (pow_nonneg ht0 3)
  rw [Real.norm_eq_abs, abs_of_nonneg hn0, actualIntegrand_eq_norm_pow]
  exact div_le_div_of_nonneg_right hp (pow_nonneg ht0 3)

lemma integrableOn_complexIntegrand (μ : ProbabilityMeasure ℝ) (n : ℕ) (b : ℝ) (hb : 0 < b) :
    IntegrableOn (complexIntegrand μ n) (Ioi b) := by
  have hf := LowFrequencyError.measurable_actual_charFun μ
  have hm : Measurable (complexIntegrand μ n) := by unfold complexIntegrand; fun_prop
  apply (integrable_norm_iff hm.aestronglyMeasurable).mp
  apply (integrableOn_actualIntegrand μ n b hb).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact (norm_complexIntegrand μ n t (hb.trans ht).le).symm

/-- Genuine joint L¹: the dominating function is 1/t³, independent of the
actual pair. No Fubini or conditional second-moment premise is assumed. -/
theorem integrable_jointKernel (μ : ProbabilityMeasure ℝ) (E : Set (ℝ × ℝ))
    (n : ℕ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 < b) :
    Integrable (jointKernel n a) ((eventLaw μ E).prod (volume.restrict (Ioi b))) := by
  have hm : Measurable (jointKernel n a) := by
    unfold jointKernel fixedDistanceIntegrand HighFrequencyEvent.distance
    fun_prop
  have hMajor : Integrable (fun z : (ℝ × ℝ) × ℝ => inverseCube z.2)
      ((eventLaw μ E).prod (volume.restrict (Ioi b))) := by
    simpa only [one_mul] using
      (integrable_const (1 : ℝ) : Integrable (fun _ : ℝ × ℝ => (1 : ℝ)) (eventLaw μ E)).mul_prod
        (integrableOn_inverseCube b hb)
  have htAE : ∀ᵐ z : (ℝ × ℝ) × ℝ ∂(eventLaw μ E).prod (volume.restrict (Ioi b)), b < z.2 := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_lt measurable_const measurable_snd)).mpr
    exact Eventually.of_forall fun _ => ae_restrict_mem measurableSet_Ioi
  apply hMajor.mono' hm.aestronglyMeasurable
  filter_upwards [htAE] with z hz
  have ht0 : 0 ≤ z.2 := (hb.trans hz).le
  have hn0 : 0 ≤ jointKernel n a z :=
    fixedDistanceIntegrand_nonneg n a (HighFrequencyEvent.distance z.1) z.2 ht0
  rw [Real.norm_eq_abs, abs_of_nonneg hn0]
  have hexp : Real.exp (-(n : ℝ) * a * Real.sin (z.2 * HighFrequencyEvent.distance z.1 / 2) ^ 2) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have hprod := mul_nonneg (mul_nonneg (Nat.cast_nonneg n) ha)
      (sq_nonneg (Real.sin (z.2 * HighFrequencyEvent.distance z.1 / 2)))
    nlinarith only [hprod]
  exact div_le_div_of_nonneg_right hexp (pow_nonneg ht0 3)

/-- Fubini is applied only after the proved joint L¹ bound. -/
theorem kernel_fubini (μ : ProbabilityMeasure ℝ) (E : Set (ℝ × ℝ))
    (n : ℕ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 < b) :
    (∫ t in Ioi b, ∫ p, fixedDistanceIntegrand n a (HighFrequencyEvent.distance p) t ∂eventLaw μ E) =
      ∫ p, (∫ t in Ioi b, fixedDistanceIntegrand n a (HighFrequencyEvent.distance p) t) ∂eventLaw μ E := by
  have hi := integrable_jointKernel μ E n a b ha hb
  exact (integral_integral_swap (f := fun p t =>
    fixedDistanceIntegrand n a (HighFrequencyEvent.distance p) t) hi).symm

lemma actualIntegrand_le_conditional_kernel (μ : ProbabilityMeasure ℝ) (E : Set (ℝ × ℝ))
    (hE : MeasurableSet E) (a : ℝ) (ha : 0 < a) (hpa : a ≤ eventProbability μ E)
    (n : ℕ) (hn : 0 < n) (t : ℝ) (ht : 0 < t) :
    actualIntegrand μ n t ≤ ∫ p, fixedDistanceIntegrand n a (HighFrequencyEvent.distance p) t ∂eventLaw μ E := by
  have hcf := (characteristic_event_damping μ E hE a ha hpa n hn t).2
  rw [actualIntegrand_eq_norm_pow]
  calc
    _ ≤ (∫ p, exponentialTest n a t p ∂eventLaw μ E) / t ^ 3 :=
      div_le_div_of_nonneg_right hcf (pow_nonneg ht.le 3)
    _ = _ := by
      rw [← integral_div]
      apply integral_congr_ae
      exact Eventually.of_forall fun _ => rfl

/-- The actual CF quotient is integrated against the same conditional law
that appears in the proved pointwise Jensen estimate. -/
theorem actual_tail_le_conditional_average (μ : ProbabilityMeasure ℝ) (E : Set (ℝ × ℝ))
    (hE : MeasurableSet E) (a : ℝ) (ha : 0 < a) (hpa : a ≤ eventProbability μ E)
    (n : ℕ) (hn : 0 < n) (b : ℝ) (hb : 0 < b) :
    Real.sqrt n * (∫ t in Ioi b, actualIntegrand μ n t) ≤
      ∫ p, Real.sqrt n * (∫ t in Ioi b,
        fixedDistanceIntegrand n a (HighFrequencyEvent.distance p) t) ∂eventLaw μ E := by
  have hj := integrable_jointKernel μ E n a b ha.le hb
  have hiR : IntegrableOn (fun t => ∫ p,
      fixedDistanceIntegrand n a (HighFrequencyEvent.distance p) t ∂eventLaw μ E) (Ioi b) :=
    hj.integral_prod_right
  have hI := setIntegral_mono_on (integrableOn_actualIntegrand μ n b hb) hiR measurableSet_Ioi
    (fun t ht => actualIntegrand_le_conditional_kernel μ E hE a ha hpa n hn t (hb.trans ht))
  calc
    _ ≤ Real.sqrt n * (∫ t in Ioi b, ∫ p,
        fixedDistanceIntegrand n a (HighFrequencyEvent.distance p) t ∂eventLaw μ E) :=
      mul_le_mul_of_nonneg_left hI (Real.sqrt_nonneg (n : ℝ))
    _ = Real.sqrt n * (∫ p, (∫ t in Ioi b,
        fixedDistanceIntegrand n a (HighFrequencyEvent.distance p) t) ∂eventLaw μ E) :=
      congrArg (fun x : ℝ => Real.sqrt n * x) (kernel_fubini μ E n a b ha.le hb)
    _ = _ := (integral_const_mul _ _).symm

private lemma average_price (μ : ProbabilityMeasure ℝ) (E : Set (ℝ × ℝ))
    [IsProbabilityMeasure (eventLaw μ E)] (n : ℕ) (a b m s B : ℝ)
    (ha : 0 ≤ a) (hb : 0 < b) (hs : 0 ≤ s)
    (h2 : Integrable (fun p => HighFrequencyEvent.distance p ^ 2) (eventLaw μ E))
    (hmean : conditionalSecondMoment μ E ≤ m)
    (hfib : ∀ᵐ p ∂eventLaw μ E, Real.sqrt n * (∫ t in Ioi b,
      fixedDistanceIntegrand n a (HighFrequencyEvent.distance p) t) ≤ HighFrequencyEvent.distance p ^ 2 * s + B) :
    (∫ p, Real.sqrt n * (∫ t in Ioi b,
      fixedDistanceIntegrand n a (HighFrequencyEvent.distance p) t) ∂eventLaw μ E) ≤ m * s + B := by
  have hiL := (integrable_jointKernel μ E n a b ha hb).integral_prod_left.const_mul (Real.sqrt n)
  have hiSq : Integrable (fun p => HighFrequencyEvent.distance p ^ 2 * s) (eventLaw μ E) := h2.mul_const s
  have hiR : Integrable (fun p => HighFrequencyEvent.distance p ^ 2 * s + B) (eventLaw μ E) :=
    hiSq.add (integrable_const B)
  calc
    _ ≤ ∫ p, HighFrequencyEvent.distance p ^ 2 * s + B ∂eventLaw μ E := integral_mono_ae hiL hiR hfib
    _ = conditionalSecondMoment μ E * s + B := by
      rw [integral_add hiSq (integrable_const B), integral_mul_const]
      simp only [integral_const, probReal_univ, one_smul, conditionalSecondMoment]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right hmean hs) le_rfl

def basicPrice (n : ℕ) (a d b w m : ℝ) : ℝ := m * nonzeroSlope n a w + Zbasic n a d b + wingPrice n a b
def improvedPrice (n : ℕ) (a d b w m : ℝ) : ℝ := m * nonzeroSlope n a w + Zimproved n a d b + wingPrice n a b
def minimumPrice (n : ℕ) (a d b w m : ℝ) : ℝ :=
  m * nonzeroSlope n a w + min (Zbasic n a d b) (Zimproved n a d b) + wingPrice n a b

/-- The original four-term actual CF tail price acquired by averaging. -/
theorem actual_event_tail_basic (μ : ProbabilityMeasure ℝ) (E : Set (ℝ × ℝ)) (hE : MeasurableSet E)
    (n : ℕ) (hn : 0 < n) (a d b w m : ℝ) (ha : 0 < a) (hpa : a ≤ eventProbability μ E)
    (hd : 0 < d) (hb : 0 < b) (hw : 0 < w) (hwcap : w ≤ 1 / 4)
    (hD : ∀ᵐ p ∂eventLaw μ E, d ≤ HighFrequencyEvent.distance p)
    (h2 : Integrable (fun p => HighFrequencyEvent.distance p ^ 2) (eventLaw μ E))
    (hmean : conditionalSecondMoment μ E ≤ m) :
    IntegrableOn (actualIntegrand μ n) (Ioi b) ∧ IntegrableOn (complexIntegrand μ n) (Ioi b) ∧
      Real.sqrt n * (∫ t in Ioi b, actualIntegrand μ n t) ≤ basicPrice n a d b w m := by
  letI : IsProbabilityMeasure (eventLaw μ E) := eventLaw_isProbability μ E (ha.trans_le hpa)
  have hfib : ∀ᵐ p ∂eventLaw μ E, Real.sqrt n * (∫ t in Ioi b,
      fixedDistanceIntegrand n a (HighFrequencyEvent.distance p) t) ≤
        HighFrequencyEvent.distance p ^ 2 * nonzeroSlope n a w + (Zbasic n a d b + wingPrice n a b) := by
    filter_upwards [hD] with p hp
    have h := (HighFrequencyDistance.fixedDistance_tail_basic n hn a (HighFrequencyEvent.distance p) d b w
      ha hd hp hb hw hwcap).2
    rw [HighFrequencyDistance.basicPrice_eq_affine] at h
    nlinarith only [h]
  have hAvg := average_price μ E n a b m (nonzeroSlope n a w) (Zbasic n a d b + wingPrice n a b)
    ha.le hb (nonzeroSlope_nonneg n a w ha hw hwcap) h2 hmean hfib
  refine ⟨integrableOn_actualIntegrand μ n b hb, integrableOn_complexIntegrand μ n b hb, ?_⟩
  have hCF := actual_tail_le_conditional_average μ E hE a ha hpa n hn b hb
  unfold basicPrice
  linarith

theorem actual_event_tail_improved (μ : ProbabilityMeasure ℝ) (E : Set (ℝ × ℝ)) (hE : MeasurableSet E)
    (n : ℕ) (hn : 0 < n) (a d b w m : ℝ) (ha : 0 < a) (hpa : a ≤ eventProbability μ E)
    (hd : 0 < d) (hb : 0 < b) (hw : 0 < w) (hwcap : w ≤ 1 / 4)
    (hD : ∀ᵐ p ∂eventLaw μ E, d ≤ HighFrequencyEvent.distance p)
    (h2 : Integrable (fun p => HighFrequencyEvent.distance p ^ 2) (eventLaw μ E))
    (hmean : conditionalSecondMoment μ E ≤ m) :
    IntegrableOn (actualIntegrand μ n) (Ioi b) ∧ IntegrableOn (complexIntegrand μ n) (Ioi b) ∧
      Real.sqrt n * (∫ t in Ioi b, actualIntegrand μ n t) ≤ improvedPrice n a d b w m := by
  letI : IsProbabilityMeasure (eventLaw μ E) := eventLaw_isProbability μ E (ha.trans_le hpa)
  have hfib : ∀ᵐ p ∂eventLaw μ E, Real.sqrt n * (∫ t in Ioi b,
      fixedDistanceIntegrand n a (HighFrequencyEvent.distance p) t) ≤
        HighFrequencyEvent.distance p ^ 2 * nonzeroSlope n a w + (Zimproved n a d b + wingPrice n a b) := by
    filter_upwards [hD] with p hp
    have h := (HighFrequencyDistance.fixedDistance_tail_improved n hn a (HighFrequencyEvent.distance p) d b w
      ha hd hp hb hw hwcap).2
    rw [HighFrequencyDistance.improvedPrice_eq_affine] at h
    nlinarith only [h]
  have hAvg := average_price μ E n a b m (nonzeroSlope n a w) (Zimproved n a d b + wingPrice n a b)
    ha.le hb (nonzeroSlope_nonneg n a w ha hw hwcap) h2 hmean hfib
  refine ⟨integrableOn_actualIntegrand μ n b hb, integrableOn_complexIntegrand μ n b hb, ?_⟩
  have hCF := actual_tail_le_conditional_average μ E hE a ha hpa n hn b hb
  unfold improvedPrice
  linarith

theorem actual_event_tail_min (μ : ProbabilityMeasure ℝ) (E : Set (ℝ × ℝ)) (hE : MeasurableSet E)
    (n : ℕ) (hn : 0 < n) (a d b w m : ℝ) (ha : 0 < a) (hpa : a ≤ eventProbability μ E)
    (hd : 0 < d) (hb : 0 < b) (hw : 0 < w) (hwcap : w ≤ 1 / 4)
    (hD : ∀ᵐ p ∂eventLaw μ E, d ≤ HighFrequencyEvent.distance p)
    (h2 : Integrable (fun p => HighFrequencyEvent.distance p ^ 2) (eventLaw μ E))
    (hmean : conditionalSecondMoment μ E ≤ m) :
    IntegrableOn (actualIntegrand μ n) (Ioi b) ∧ IntegrableOn (complexIntegrand μ n) (Ioi b) ∧
      Real.sqrt n * (∫ t in Ioi b, actualIntegrand μ n t) ≤ minimumPrice n a d b w m := by
  letI : IsProbabilityMeasure (eventLaw μ E) := eventLaw_isProbability μ E (ha.trans_le hpa)
  have hfib : ∀ᵐ p ∂eventLaw μ E, Real.sqrt n * (∫ t in Ioi b,
      fixedDistanceIntegrand n a (HighFrequencyEvent.distance p) t) ≤
        HighFrequencyEvent.distance p ^ 2 * nonzeroSlope n a w +
          (min (Zbasic n a d b) (Zimproved n a d b) + wingPrice n a b) := by
    filter_upwards [hD] with p hp
    have h := (HighFrequencyDistance.fixedDistance_tail_min n hn a (HighFrequencyEvent.distance p) d b w
      ha hd hp hb hw hwcap).2
    rw [HighFrequencyDistance.minimumPrice_eq_affine] at h
    nlinarith only [h]
  have hAvg := average_price μ E n a b m (nonzeroSlope n a w)
    (min (Zbasic n a d b) (Zimproved n a d b) + wingPrice n a b)
    ha.le hb (nonzeroSlope_nonneg n a w ha hw hwcap) h2 hmean hfib
  refine ⟨integrableOn_actualIntegrand μ n b hb, integrableOn_complexIntegrand μ n b hb, ?_⟩
  have hCF := actual_tail_le_conditional_average μ E hE a ha hpa n hn b hb
  unfold minimumPrice
  linarith

/-- The same actual standardized law supplies its Cantelli event and all
conditional inputs; no event mass or conditional law is substituted. -/
theorem cantelli_tail_basic (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (h4 : Integrable (fun x : ℝ => x ^ 4) (μ : Measure ℝ)) (M : ℝ)
    (hM : CharacteristicExpansion.moment μ 4 ≤ M) (d : ℝ) (hd : 0 < d) (hd2 : d ^ 2 < 2)
    (n : ℕ) (hn : 0 < n) (b w : ℝ) (hb : 0 < b) (hw : 0 < w) (hwcap : w ≤ 1 / 4) :
    IntegrableOn (actualIntegrand μ n) (Ioi b) ∧ IntegrableOn (complexIntegrand μ n) (Ioi b) ∧
      Real.sqrt n * (∫ t in Ioi b, actualIntegrand μ n t) ≤
        basicPrice n (HighFrequencyCantelli.probabilityPrice d M) d b w (HighFrequencyCantelli.secondMomentPrice d M) := by
  have h := HighFrequencyCantelli.acquire μ hμ h4 M hM d hd hd2
  exact actual_event_tail_basic μ (HighFrequencyCantelli.event d) (HighFrequencyCantelli.event_measurable d)
    n hn _ d b w _ h.price_pos h.mass_lower hd hb hw hwcap h.distance_lower h.square_integrable h.second_moment_upper

theorem cantelli_tail_improved (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (h4 : Integrable (fun x : ℝ => x ^ 4) (μ : Measure ℝ)) (M : ℝ)
    (hM : CharacteristicExpansion.moment μ 4 ≤ M) (d : ℝ) (hd : 0 < d) (hd2 : d ^ 2 < 2)
    (n : ℕ) (hn : 0 < n) (b w : ℝ) (hb : 0 < b) (hw : 0 < w) (hwcap : w ≤ 1 / 4) :
    IntegrableOn (actualIntegrand μ n) (Ioi b) ∧ IntegrableOn (complexIntegrand μ n) (Ioi b) ∧
      Real.sqrt n * (∫ t in Ioi b, actualIntegrand μ n t) ≤
        improvedPrice n (HighFrequencyCantelli.probabilityPrice d M) d b w (HighFrequencyCantelli.secondMomentPrice d M) := by
  have h := HighFrequencyCantelli.acquire μ hμ h4 M hM d hd hd2
  exact actual_event_tail_improved μ (HighFrequencyCantelli.event d) (HighFrequencyCantelli.event_measurable d)
    n hn _ d b w _ h.price_pos h.mass_lower hd hb hw hwcap h.distance_lower h.square_integrable h.second_moment_upper

theorem cantelli_tail_min (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (h4 : Integrable (fun x : ℝ => x ^ 4) (μ : Measure ℝ)) (M : ℝ)
    (hM : CharacteristicExpansion.moment μ 4 ≤ M) (d : ℝ) (hd : 0 < d) (hd2 : d ^ 2 < 2)
    (n : ℕ) (hn : 0 < n) (b w : ℝ) (hb : 0 < b) (hw : 0 < w) (hwcap : w ≤ 1 / 4) :
    IntegrableOn (actualIntegrand μ n) (Ioi b) ∧ IntegrableOn (complexIntegrand μ n) (Ioi b) ∧
      Real.sqrt n * (∫ t in Ioi b, actualIntegrand μ n t) ≤
        minimumPrice n (HighFrequencyCantelli.probabilityPrice d M) d b w (HighFrequencyCantelli.secondMomentPrice d M) := by
  have h := HighFrequencyCantelli.acquire μ hμ h4 M hM d hd hd2
  exact actual_event_tail_min μ (HighFrequencyCantelli.event d) (HighFrequencyCantelli.event_measurable d)
    n hn _ d b w _ h.price_pos h.mass_lower hd hb hw hwcap h.distance_lower h.square_integrable h.second_moment_upper

end BerryEsseen.HighFrequencyTail

#print axioms BerryEsseen.HighFrequencyTail.integrable_jointKernel
#print axioms BerryEsseen.HighFrequencyTail.kernel_fubini
#print axioms BerryEsseen.HighFrequencyTail.actual_event_tail_basic
#print axioms BerryEsseen.HighFrequencyTail.actual_event_tail_improved
#print axioms BerryEsseen.HighFrequencyTail.actual_event_tail_min
#print axioms BerryEsseen.HighFrequencyTail.cantelli_tail_basic
#print axioms BerryEsseen.HighFrequencyTail.cantelli_tail_improved
#print axioms BerryEsseen.HighFrequencyTail.cantelli_tail_min
