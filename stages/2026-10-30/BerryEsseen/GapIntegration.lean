module

public import BerryEsseen.SupportGaps
public import BerryEsseen.ZeroBiasTransport
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

@[expose] public section

/-!
The atom-faithful first evaluation of a gap resource. The actual closed
tail is integrated by finite-window Fubini, never differentiated. Its
endpoint term uses Ici b and its interior cost uses Ico a b.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology Interval

namespace BerryEsseen.GapIntegration

open ZeroBias

def closedTail (ν : ProbabilityMeasure ℝ) (t : ℝ) : ℝ :=
  (ν : Measure ℝ).real (Ici t)

def tailIndicator (y t : ℝ) : ℝ := if t ≤ y then 1 else 0

lemma measurable_tailIndicator : Measurable (fun p : ℝ × ℝ => tailIndicator p.1 p.2) := by
  unfold tailIndicator
  exact measurable_const.piecewise (measurableSet_le measurable_snd measurable_fst) measurable_const

lemma closedTail_eq_integral (ν : ProbabilityMeasure ℝ) (t : ℝ) :
    closedTail ν t = ∫ y : ℝ, tailIndicator y t ∂(ν : Measure ℝ) := by
  have heq : (fun y : ℝ => tailIndicator y t) = (Ici t).indicator (fun _ => (1 : ℝ)) := by
    funext y
    simp only [tailIndicator, Set.indicator_apply, mem_Ici]
  unfold closedTail
  rw [heq, integral_indicator_const (1 : ℝ) measurableSet_Ici, smul_eq_mul, mul_one]

theorem integrable_tailIndicator_prod (ν : ProbabilityMeasure ℝ) (a b : ℝ) :
    Integrable (fun p : ℝ × ℝ => tailIndicator p.1 p.2)
      ((ν : Measure ℝ).prod (volume.restrict (Ioo a b))) := by
  apply (integrable_const (1 : ℝ)).mono' measurable_tailIndicator.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun p => by
    by_cases hp : p.2 ≤ p.1 <;> simp [tailIndicator, hp]

theorem integrable_closedTail_on_gap (ν : ProbabilityMeasure ℝ) (a b : ℝ) :
    IntegrableOn (closedTail ν) (Ioo a b) := by
  have hi := (integrable_tailIndicator_prod ν a b).integral_prod_right
  have heq : (fun t : ℝ => ∫ y : ℝ, tailIndicator y t ∂(ν : Measure ℝ)) = closedTail ν :=
    (funext (closedTail_eq_integral ν)).symm
  rw [heq] at hi
  exact hi

/-- The gap cost is genuinely integrable even when ν has no first moment. -/
theorem integrable_gap_cost (ν : ProbabilityMeasure ℝ) (a b : ℝ) :
    IntegrableOn (fun y : ℝ => y - a) (Ico a b) (ν : Measure ℝ) := by
  apply (integrable_const (b - a) :
    Integrable (fun _ : ℝ => b - a) ((ν : Measure ℝ).restrict (Ico a b))).mono'
    (continuous_id.sub continuous_const).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ico] with y hy
  change ‖y - a‖ ≤ b - a
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hy.1)]
  linarith [hy.2]

lemma tailIndicator_as_indicator (y : ℝ) :
    tailIndicator y = (Iic y).indicator (fun _ => (1 : ℝ)) := by
  funext t
  simp only [tailIndicator, Set.indicator_apply, mem_Iic]

/-- A fixed atom y contributes its actual length below it in (a,b).
The case y=b goes to the closed right tail, not the Ico cost. -/
lemma tailIndicator_window_integral (a b y : ℝ) (hab : a < b) :
    (∫ t : ℝ in Ioo a b, tailIndicator y t) =
      (b - a) * (Ici b).indicator (fun _ => (1 : ℝ)) y +
        (Ico a b).indicator (fun z => z - a) y := by
  rw [tailIndicator_as_indicator, integral_indicator_const (1 : ℝ) measurableSet_Iic, smul_eq_mul, mul_one]
  unfold Measure.real
  rw [Measure.restrict_apply measurableSet_Iic]
  by_cases hby : b ≤ y
  · have hset : Iic y ∩ Ioo a b = Ioo a b := by
      apply inter_eq_right.mpr
      intro t ht
      exact le_trans ht.2.le hby
    rw [hset, Real.volume_Ioo, ENNReal.toReal_ofReal (sub_nonneg.mpr hab.le)]
    have hyb : ¬y < b := not_lt.mpr hby
    simp [hby, hyb]
  · have hyb : y < b := lt_of_not_ge hby
    have hset : Iic y ∩ Ioo a b = Ioc a y := by
      ext t
      constructor
      · intro ht
        exact ⟨ht.2.1, ht.1⟩
      · intro ht
        exact ⟨ht.2, ht.1, lt_of_le_of_lt ht.2 hyb⟩
    rw [hset, Real.volume_Ioc]
    by_cases hay : a ≤ y
    · rw [ENNReal.toReal_ofReal (sub_nonneg.mpr hay)]
      simp [hby, hay, hyb]
    · have hnon : y - a ≤ 0 := by linarith
      rw [ENNReal.ofReal_eq_zero.mpr hnon]
      simp [hby, hay]

/-- Exact tail-length Fubini for an arbitrary probability law, retaining
both endpoint conventions and requiring no density or moments for ν. -/
theorem closedTail_gap_integral (ν : ProbabilityMeasure ℝ) (a b : ℝ) (hab : a < b) :
    (∫ t : ℝ in Ioo a b, closedTail ν t) =
      (b - a) * closedTail ν b + ∫ y : ℝ in Ico a b, y - a ∂(ν : Measure ℝ) := by
  have hfirst : Integrable (fun y : ℝ => (b - a) * (Ici b).indicator (fun _ => (1 : ℝ)) y)
      (ν : Measure ℝ) := ((integrable_const (1 : ℝ)).indicator measurableSet_Ici).const_mul (b - a)
  have hsecond : Integrable ((Ico a b).indicator (fun y : ℝ => y - a)) (ν : Measure ℝ) :=
    (integrable_gap_cost ν a b).integrable_indicator measurableSet_Ico
  calc
    _ = ∫ t : ℝ in Ioo a b, ∫ y : ℝ, tailIndicator y t ∂(ν : Measure ℝ) :=
      integral_congr_ae (Filter.Eventually.of_forall (closedTail_eq_integral ν))
    _ = ∫ y : ℝ, (∫ t : ℝ in Ioo a b, tailIndicator y t) ∂(ν : Measure ℝ) :=
      (integral_integral_swap (integrable_tailIndicator_prod ν a b)).symm
    _ = ∫ y : ℝ, ((b - a) * (Ici b).indicator (fun _ => (1 : ℝ)) y +
        (Ico a b).indicator (fun z => z - a) y) ∂(ν : Measure ℝ) :=
      integral_congr_ae (Filter.Eventually.of_forall (fun y => tailIndicator_window_integral a b y hab))
    _ = (b - a) * (ν : Measure ℝ).real (Ici b) + ∫ y : ℝ in Ico a b, y - a ∂(ν : Measure ℝ) := by
      rw [integral_add hfirst hsecond, integral_const_mul, integral_indicator_const (1 : ℝ) measurableSet_Ici,
        smul_eq_mul, mul_one, integral_indicator measurableSet_Ico]
    _ = _ := rfl

lemma integrable_local_C1 (q : ℝ → ℝ) (U : Set ℝ)
    (hq : ContDiffOn ℝ 1 q U) (a b : ℝ) (hI : Icc a b ⊆ U) :
    IntegrableOn q (Ioo a b) := by
  exact (hq.continuousOn.mono hI).integrableOn_Icc.mono_set Ioo_subset_Icc_self

/-- Integration by parts uses only C1 regularity on an open neighborhood
of the closed segment; no global smoothness of q is required. -/
theorem local_C1_integral (q : ℝ → ℝ) (U : Set ℝ) (hU : IsOpen U)
    (hq : ContDiffOn ℝ 1 q U) (a b : ℝ) (hab : a < b) (hI : Icc a b ⊆ U) :
    (∫ t : ℝ in Ioo a b, q t) = (b - a) * q b -
      ∫ t in a..b, (t - a) * deriv q t := by
  have hqc : ContinuousOn q (Icc a b) := hq.continuousOn.mono hI
  have hdc : ContinuousOn (deriv q) (Icc a b) :=
    (hq.continuousOn_deriv_of_isOpen hU le_rfl).mono hI
  have hqcI : IntervalIntegrable q volume a b := hqc.intervalIntegrable_of_Icc hab.le
  have hdcI : IntervalIntegrable (fun t : ℝ => (t - a) * deriv q t) volume a b :=
    ((continuous_id.sub continuous_const).continuousOn.mul hdc).intervalIntegrable_of_Icc hab.le
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t : ℝ => (t - a) * q t) (f' := fun t : ℝ => q t + (t - a) * deriv q t)
    (a := a) (b := b) (fun t ht => by
      have htI : t ∈ Icc a b := by simpa only [uIcc_of_le hab.le] using ht
      have htU := hI htI
      have hdq := ((hq.differentiableOn_one t htU).differentiableAt (hU.mem_nhds htU)).hasDerivAt
      have hd := ((hasDerivAt_id' t).sub_const a).fun_mul hdq
      simpa only [one_mul] using hd) (hqcI.add hdcI)
  rw [intervalIntegral.integral_add hqcI hdcI] at hFTC
  simp only [sub_self, zero_mul, sub_zero] at hFTC
  have hop : (∫ t : ℝ in Ioo a b, q t) = ∫ t in a..b, q t := by
    rw [intervalIntegral.integral_of_le hab.le, integral_Ioc_eq_integral_Ioo]
  rw [hop]
  linarith

lemma tau_eq_on_open_gap (μ : ProbabilityMeasure ℝ) (a b : ℝ)
    (hg : (a, b) ∈ SupportGaps.gapSet (μ : Measure ℝ).support) :
    Set.EqOn (tau μ) (fun _ => tau μ b) (Ioo a b) := by
  intro t ht
  exact SupportGaps.tau_constant_on_support_gap μ (a, b) hg ⟨ht.1, ht.2.le⟩

theorem integrable_tau_mul_on_gap (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (a b : ℝ) (hg : (a, b) ∈ SupportGaps.gapSet (μ : Measure ℝ).support)
    (f : ℝ → ℝ) (hf : IntegrableOn f (Ioo a b)) :
    IntegrableOn (fun t : ℝ => tau μ t * f t) (Ioo a b) := by
  have hm : AEStronglyMeasurable (fun t : ℝ => tau μ t * f t) (volume.restrict (Ioo a b)) :=
    (measurable_tau μ h).aestronglyMeasurable.mul hf.aestronglyMeasurable
  have hi : Integrable (fun t : ℝ => tau μ b * f t) (volume.restrict (Ioo a b)) :=
    MeasureTheory.Integrable.const_mul hf (tau μ b)
  apply MeasureTheory.Integrable.mono (f := fun t : ℝ => tau μ t * f t)
    (g := fun t : ℝ => tau μ b * f t) hi hm
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  rw [tau_eq_on_open_gap μ a b hg ht]

lemma integral_tau_mul_on_gap (μ : ProbabilityMeasure ℝ) (a b : ℝ)
    (hg : (a, b) ∈ SupportGaps.gapSet (μ : Measure ℝ).support) (f : ℝ → ℝ) :
    (∫ t : ℝ in Ioo a b, tau μ t * f t) = tau μ b * ∫ t : ℝ in Ioo a b, f t := by
  calc
    _ = ∫ t : ℝ in Ioo a b, tau μ b * f t :=
      setIntegral_congr_fun measurableSet_Ioo (fun t ht => by rw [tau_eq_on_open_gap μ a b hg ht])
    _ = _ := integral_const_mul _ _

theorem integrable_gap_resource (μ ν : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (a b : ℝ) (hg : (a, b) ∈ SupportGaps.gapSet (μ : Measure ℝ).support)
    (q : ℝ → ℝ) (U : Set ℝ) (_hU : IsOpen U) (hq : ContDiffOn ℝ 1 q U)
    (hI : Icc a b ⊆ U) :
    IntegrableOn (fun t : ℝ => tau μ t * (q t - closedTail ν t)) (Ioo a b) := by
  exact integrable_tau_mul_on_gap μ h a b hg (fun t => q t - closedTail ν t)
    ((integrable_local_C1 q U hq a b hI).sub (integrable_closedTail_on_gap ν a b))

/-- The first gap-resource evaluation for the actual original μ and
an arbitrary atomic comparison law ν. Only q is differentiated. -/
theorem gap_resource_identity (μ ν : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (a b : ℝ) (hg : (a, b) ∈ SupportGaps.gapSet (μ : Measure ℝ).support)
    (q : ℝ → ℝ) (U : Set ℝ) (hU : IsOpen U) (hq : ContDiffOn ℝ 1 q U)
    (hI : Icc a b ⊆ U) (hqb : q b = closedTail ν b) :
    (∫ t : ℝ in Ioo a b, tau μ t * (q t - closedTail ν t)) =
      -tau μ b * (∫ t in a..b, (t - a) * deriv q t) -
        tau μ b * (∫ y : ℝ in Ico a b, y - a ∂(ν : Measure ℝ)) := by
  have hab : a < b := hg.2.2.1
  have hiq := integrable_local_C1 q U hq a b hI
  have hit := integrable_closedTail_on_gap ν a b
  have hiτq := integrable_tau_mul_on_gap μ h a b hg q hiq
  have hiτt := integrable_tau_mul_on_gap μ h a b hg (closedTail ν) hit
  have hfun : (fun t : ℝ => tau μ t * (q t - closedTail ν t)) =
      (fun t : ℝ => tau μ t * q t - tau μ t * closedTail ν t) := by funext t; ring
  rw [hfun, integral_sub hiτq hiτt, integral_tau_mul_on_gap μ a b hg q,
    integral_tau_mul_on_gap μ a b hg (closedTail ν), local_C1_integral q U hU hq a b hab hI,
    closedTail_gap_integral ν a b hab, hqb]
  ring

end BerryEsseen.GapIntegration

#print axioms BerryEsseen.GapIntegration.integrable_tailIndicator_prod
#print axioms BerryEsseen.GapIntegration.closedTail_gap_integral
#print axioms BerryEsseen.GapIntegration.local_C1_integral
#print axioms BerryEsseen.GapIntegration.integrable_gap_resource
#print axioms BerryEsseen.GapIntegration.gap_resource_identity
