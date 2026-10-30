module

public import BerryEsseen.Target
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
The actual zero-bias density of the original standardized law, with the
closed upper-tail convention. A nonnegative interval-transport kernel
supplies the Tonelli and Fubini justifications without assuming a density
for the original law or boundedness of its support.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ENNReal Interval

namespace BerryEsseen.ZeroBias

/-- The original closed-tail first moment. Atoms at the threshold are retained. -/
def tau (μ : ProbabilityMeasure ℝ) (t : ℝ) : ℝ :=
  ∫ x : ℝ in Ici t, x ∂(μ : Measure ℝ)

/-- For positive x this transports over (0,x]; for negative x over (x,0].
Its value at t=0 uses the negative side, matching tau by centering. -/
def kernel (x t : ℝ) : ℝ :=
  if 0 < t then (if t ≤ x then x else 0) else (if x < t then -x else 0)

lemma kernel_nonneg (x t : ℝ) : 0 ≤ kernel x t := by
  by_cases ht : 0 < t
  · rw [kernel, ite_eq_left ht]
    by_cases hx : t ≤ x
    · rw [ite_eq_left hx]
      linarith
    · rw [ite_eq_right hx]
  · rw [kernel, ite_eq_right ht]
    by_cases hx : x < t
    · rw [ite_eq_left hx]
      linarith
    · rw [ite_eq_right hx]

lemma kernel_le_abs (x t : ℝ) : kernel x t ≤ |x| := by
  by_cases ht : 0 < t
  · rw [kernel, ite_eq_left ht]
    by_cases hx : t ≤ x
    · rw [ite_eq_left hx]
      exact le_abs_self x
    · rw [ite_eq_right hx]
      exact abs_nonneg x
  · rw [kernel, ite_eq_right ht]
    by_cases hx : x < t
    · rw [ite_eq_left hx]
      exact neg_le_abs x
    · rw [ite_eq_right hx]
      exact abs_nonneg x

lemma measurable_kernel : Measurable (fun p : ℝ × ℝ => kernel p.1 p.2) := by
  unfold kernel
  exact (measurable_fst.piecewise (measurableSet_le measurable_snd measurable_fst) measurable_const).piecewise
    (measurableSet_lt measurable_const measurable_snd)
    (measurable_fst.neg.piecewise (measurableSet_lt measurable_fst measurable_snd) measurable_const)

lemma kernel_of_nonneg (x : ℝ) (hx : 0 ≤ x) :
    kernel x = (Ioc 0 x).indicator (fun _ => x) := by
  funext t
  by_cases ht : 0 < t
  · simp [kernel, ht, Set.indicator_apply]
  · have hxt : ¬ x < t := by linarith
    simp [kernel, ht, hxt]

lemma kernel_of_nonpos (x : ℝ) (hx : x ≤ 0) :
    kernel x = (Ioc x 0).indicator (fun _ => -x) := by
  funext t
  by_cases ht : 0 < t
  · have htx : ¬ t ≤ x := by linarith
    have ht0 : ¬ t ≤ 0 := by linarith
    simp only [kernel, ite_eq_left ht, ite_eq_right htx,
      Set.indicator_apply, mem_Ioc, ht0, and_false, ite_eq_right (by decide : ¬False)]
  · have ht0 : t ≤ 0 := le_of_not_gt ht
    simp only [kernel, ite_eq_right ht, Set.indicator_apply, mem_Ioc, ht0, and_true]

lemma kernel_interval (x : ℝ) :
    kernel x = (uIoc 0 x).indicator (fun _ => |x|) := by
  rcases le_total 0 x with hx | hx
  · rw [kernel_of_nonneg x hx, uIoc_of_le hx, abs_of_nonneg hx]
  · rw [kernel_of_nonpos x hx, uIoc_of_ge hx, abs_of_nonpos hx]

lemma mul_kernel_indicator (f : ℝ → ℝ) (x : ℝ) :
    (fun t => f t * kernel x t) = (uIoc 0 x).indicator (fun t => f t * |x|) := by
  rw [kernel_interval x]
  funext t
  exact (Set.indicator_mul_right (uIoc 0 x) f (fun _ => |x|) (i := t)).symm

lemma integrable_kernel_t (x : ℝ) : Integrable (kernel x) := by
  rw [kernel_interval]
  change Integrable ((Ioc (min 0 x) (max 0 x)).indicator (fun _ : ℝ => |x|))
  exact (continuous_const.integrableOn_Ioc).integrable_indicator measurableSet_Ioc

lemma integral_kernel_t (x : ℝ) : (∫ t : ℝ, kernel x t) = x ^ 2 := by
  rw [kernel_interval, integral_indicator_const _ measurableSet_uIoc]
  simp only [Measure.real, Real.volume_uIoc, sub_zero,
    ENNReal.toReal_ofReal (abs_nonneg x), smul_eq_mul, ← sq, sq_abs]

lemma integrable_abs_mul_kernel_t (x : ℝ) :
    Integrable (fun t : ℝ => |t| * kernel x t) := by
  rw [mul_kernel_indicator]
  change Integrable ((Ioc (min 0 x) (max 0 x)).indicator (fun t : ℝ => |t| * |x|))
  exact (continuous_abs.mul continuous_const).integrableOn_Ioc.integrable_indicator measurableSet_Ioc

lemma integral_abs_mul_kernel_t (x : ℝ) :
    (∫ t : ℝ, |t| * kernel x t) = |x| ^ 3 / 2 := by
  rw [mul_kernel_indicator, integral_indicator measurableSet_uIoc, integral_mul_const]
  have hp := integral_pow_abs_sub_uIoc (n := 1) (a := 0) (b := x)
  simp only [sub_zero, pow_one] at hp
  rw [hp]
  ring

lemma integral_mul_kernel_t (x : ℝ) :
    (∫ t : ℝ, t * kernel x t) = x ^ 3 / 2 := by
  rw [mul_kernel_indicator, integral_indicator measurableSet_uIoc, integral_mul_const]
  rcases le_total 0 x with hx | hx
  · rw [uIoc_of_le hx, ← intervalIntegral.integral_of_le hx,
      integral_id, abs_of_nonneg hx]
    ring
  · rw [uIoc_of_ge hx, ← intervalIntegral.integral_of_le hx,
      integral_id, abs_of_nonpos hx]
    ring

lemma tau_eq_integral_if (μ : ProbabilityMeasure ℝ) (t : ℝ) :
    tau μ t = ∫ x : ℝ, (if t ≤ x then x else 0) ∂(μ : Measure ℝ) := by
  unfold tau
  rw [← integral_indicator measurableSet_Ici]
  simp only [Set.indicator_apply, mem_Ici]

/-- Centering gives the exact complementary lower-tail formula, including atoms. -/
lemma tau_eq_lower_tail (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (t : ℝ) :
    tau μ t = ∫ x : ℝ in Iio t, -x ∂(μ : Measure ℝ) := by
  have hs := integral_add_compl (s := Iio t) measurableSet_Iio h.integrable_mean
  rw [compl_Iio, h.mean_zero] at hs
  unfold tau
  rw [integral_neg]
  linarith

lemma tau_eq_integral_kernel (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (t : ℝ) :
    tau μ t = ∫ x : ℝ, kernel x t ∂(μ : Measure ℝ) := by
  by_cases ht : 0 < t
  · rw [tau_eq_integral_if]
    simp only [kernel, ite_eq_left ht]
  · rw [tau_eq_lower_tail μ h t, ← integral_indicator measurableSet_Iio]
    simp only [Set.indicator_apply, mem_Iio, kernel, ite_eq_right ht]

lemma integrable_kernel_x (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (t : ℝ) :
    Integrable (fun x : ℝ => kernel x t) (μ : Measure ℝ) := by
  have hi : Integrable (fun x : ℝ => |x|) (μ : Measure ℝ) := by
    simpa only [Real.norm_eq_abs] using h.integrable_mean.norm
  have hm : Measurable (fun x : ℝ => kernel x t) :=
    measurable_kernel.comp (measurable_id.prodMk measurable_const)
  apply hi.mono' hm.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (kernel_nonneg x t)]
    exact kernel_le_abs x t)

theorem measurable_tau (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) : Measurable (tau μ) := by
  have heq : tau μ = (fun t => ∫ x : ℝ, kernel x t ∂(μ : Measure ℝ)) :=
    funext (tau_eq_integral_kernel μ h)
  rw [heq]
  exact measurable_kernel.stronglyMeasurable.integral_prod_left.measurable

theorem tau_nonneg (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (t : ℝ) : 0 ≤ tau μ t := by
  rw [tau_eq_integral_kernel μ h t]
  exact integral_nonneg (fun x => kernel_nonneg x t)

/-- Product integrability is established from Tonelli's criterion and
the original second moment, before Fubini is invoked. -/
lemma integrable_kernel_prod (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    Integrable (fun p : ℝ × ℝ => kernel p.1 p.2) ((μ : Measure ℝ).prod volume) := by
  apply (integrable_prod_iff measurable_kernel.aestronglyMeasurable).mpr
  refine ⟨Filter.Eventually.of_forall integrable_kernel_t, ?_⟩
  have heq : (fun x : ℝ => ∫ t : ℝ, ‖kernel x t‖) = (fun x : ℝ => x ^ 2) := by
    funext x
    calc
      _ = ∫ t : ℝ, kernel x t := integral_congr_ae (Filter.Eventually.of_forall fun t => by
        rw [Real.norm_eq_abs, abs_of_nonneg (kernel_nonneg x t)])
      _ = _ := integral_kernel_t x
  rw [heq]
  exact h.integrable_square

theorem integrable_tau (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) : Integrable (tau μ) := by
  have hi := (integrable_kernel_prod μ h).integral_prod_right
  have heq : (fun t => ∫ x : ℝ, kernel x t ∂(μ : Measure ℝ)) = tau μ :=
    (funext (tau_eq_integral_kernel μ h)).symm
  rw [heq] at hi
  exact hi

theorem integral_tau (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    (∫ t : ℝ, tau μ t) = 1 := by
  calc
    _ = ∫ t : ℝ, ∫ x : ℝ, kernel x t ∂(μ : Measure ℝ) :=
      integral_congr_ae (Filter.Eventually.of_forall (tau_eq_integral_kernel μ h))
    _ = ∫ x : ℝ, (∫ t : ℝ, kernel x t) ∂(μ : Measure ℝ) :=
      (integral_integral_swap (integrable_kernel_prod μ h)).symm
    _ = ∫ x : ℝ, x ^ 2 ∂(μ : Measure ℝ) :=
      integral_congr_ae (Filter.Eventually.of_forall integral_kernel_t)
    _ = 1 := h.second_moment_one

def zeroBiasMeasure (μ : ProbabilityMeasure ℝ) : Measure ℝ :=
  volume.withDensity (fun t => ENNReal.ofReal (tau μ t))

theorem zeroBiasMeasure_isProbability (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    IsProbabilityMeasure (zeroBiasMeasure μ) := by
  constructor
  unfold zeroBiasMeasure
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_tau μ h)
      (Filter.Eventually.of_forall (tau_nonneg μ h)), integral_tau μ h]
  norm_num

def zeroBiasLaw (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) : ProbabilityMeasure ℝ :=
  ⟨zeroBiasMeasure μ, zeroBiasMeasure_isProbability μ h⟩

/-- The actual signed third moment of the original law. -/
def gamma (μ : ProbabilityMeasure ℝ) : ℝ := ∫ x : ℝ, x ^ 3 ∂(μ : Measure ℝ)

lemma integrable_signed_cube (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    Integrable (fun x : ℝ => x ^ 3) (μ : Measure ℝ) := by
  apply (integrable_norm_iff (by fun_prop :
    AEStronglyMeasurable (fun x : ℝ => x ^ 3) (μ : Measure ℝ))).mp
  simpa only [Real.norm_eq_abs, abs_pow] using h.integrable_cube

lemma integrable_mul_kernel_t (x : ℝ) : Integrable (fun t : ℝ => t * kernel x t) := by
  rw [mul_kernel_indicator]
  change Integrable ((Ioc (min 0 x) (max 0 x)).indicator (fun t : ℝ => t * |x|))
  exact (continuous_id.mul continuous_const).integrableOn_Ioc.integrable_indicator measurableSet_Ioc

/-- The absolute-first-moment transport kernel is genuinely integrable
on the product, by the original finite absolute third moment. -/
lemma integrable_abs_kernel_prod (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    Integrable (fun p : ℝ × ℝ => |p.2| * kernel p.1 p.2) ((μ : Measure ℝ).prod volume) := by
  have habs : Measurable (fun p : ℝ × ℝ => |p.2|) :=
    (continuous_abs.comp continuous_snd).measurable
  have hm : Measurable (fun p : ℝ × ℝ => |p.2| * kernel p.1 p.2) := habs.mul measurable_kernel
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  refine ⟨Filter.Eventually.of_forall integrable_abs_mul_kernel_t, ?_⟩
  have heq : (fun x : ℝ => ∫ t : ℝ, ‖|t| * kernel x t‖) = (fun x : ℝ => |x| ^ 3 / 2) := by
    funext x
    calc
      _ = ∫ t : ℝ, |t| * kernel x t := integral_congr_ae (Filter.Eventually.of_forall fun t => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg t) (kernel_nonneg x t))])
      _ = _ := integral_abs_mul_kernel_t x
  rw [heq]
  exact h.integrable_cube.div_const 2

lemma integrable_signed_kernel_prod (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    Integrable (fun p : ℝ × ℝ => p.2 * kernel p.1 p.2) ((μ : Measure ℝ).prod volume) := by
  have hm : Measurable (fun p : ℝ × ℝ => p.2 * kernel p.1 p.2) :=
    measurable_snd.mul measurable_kernel
  apply (integrable_norm_iff hm.aestronglyMeasurable).mp
  have heq : (fun p : ℝ × ℝ => ‖p.2 * kernel p.1 p.2‖) =
      (fun p : ℝ × ℝ => |p.2| * kernel p.1 p.2) := by
    funext p
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (kernel_nonneg p.1 p.2)]
  rw [heq]
  exact integrable_abs_kernel_prod μ h

theorem integrable_abs_mul_tau (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    Integrable (fun t : ℝ => |t| * tau μ t) := by
  have hi := (integrable_abs_kernel_prod μ h).integral_prod_right
  have heq : (fun t : ℝ => ∫ x : ℝ, |t| * kernel x t ∂(μ : Measure ℝ)) =
      (fun t : ℝ => |t| * tau μ t) := by
    funext t
    rw [integral_const_mul, ← tau_eq_integral_kernel μ h t]
  rw [heq] at hi
  exact hi

theorem integral_abs_mul_tau (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    (∫ t : ℝ, |t| * tau μ t) = thirdAbsoluteMoment μ / 2 := by
  calc
    _ = ∫ t : ℝ, ∫ x : ℝ, |t| * kernel x t ∂(μ : Measure ℝ) :=
      integral_congr_ae (Filter.Eventually.of_forall fun t => by
        change |t| * tau μ t = ∫ x : ℝ, |t| * kernel x t ∂(μ : Measure ℝ)
        rw [integral_const_mul, ← tau_eq_integral_kernel μ h t])
    _ = ∫ x : ℝ, (∫ t : ℝ, |t| * kernel x t) ∂(μ : Measure ℝ) :=
      (integral_integral_swap (integrable_abs_kernel_prod μ h)).symm
    _ = ∫ x : ℝ, |x| ^ 3 / 2 ∂(μ : Measure ℝ) :=
      integral_congr_ae (Filter.Eventually.of_forall integral_abs_mul_kernel_t)
    _ = _ := by rw [integral_div]; rfl

theorem integrable_mul_tau (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    Integrable (fun t : ℝ => t * tau μ t) := by
  have hi := (integrable_signed_kernel_prod μ h).integral_prod_right
  have heq : (fun t : ℝ => ∫ x : ℝ, t * kernel x t ∂(μ : Measure ℝ)) =
      (fun t : ℝ => t * tau μ t) := by
    funext t
    rw [integral_const_mul, ← tau_eq_integral_kernel μ h t]
  rw [heq] at hi
  exact hi

theorem integral_mul_tau (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    (∫ t : ℝ, t * tau μ t) = gamma μ / 2 := by
  calc
    _ = ∫ t : ℝ, ∫ x : ℝ, t * kernel x t ∂(μ : Measure ℝ) :=
      integral_congr_ae (Filter.Eventually.of_forall fun t => by
        change t * tau μ t = ∫ x : ℝ, t * kernel x t ∂(μ : Measure ℝ)
        rw [integral_const_mul, ← tau_eq_integral_kernel μ h t])
    _ = ∫ x : ℝ, (∫ t : ℝ, t * kernel x t) ∂(μ : Measure ℝ) :=
      (integral_integral_swap (integrable_signed_kernel_prod μ h)).symm
    _ = ∫ x : ℝ, x ^ 3 / 2 ∂(μ : Measure ℝ) :=
      integral_congr_ae (Filter.Eventually.of_forall integral_mul_kernel_t)
    _ = _ := by rw [integral_div]; rfl

/-- For the Ici convention the constant value on an open mass-free gap
is tau at its right endpoint. The left endpoint is deliberately excluded. -/
theorem tau_constant_on_openGap (μ : ProbabilityMeasure ℝ) (a b t : ℝ)
    (hgap : (μ : Measure ℝ) (Ioo a b) = 0) (hat : a < t) (htb : t ≤ b) :
    tau μ t = tau μ b := by
  have hae : ∀ᵐ x ∂(μ : Measure ℝ), x ∉ Ioo a b := by
    apply ae_iff.mpr
    have hset : {x : ℝ | ¬x ∉ Ioo a b} = Ioo a b := by ext x; simp
    rw [hset]
    exact hgap
  rw [tau_eq_integral_if, tau_eq_integral_if]
  apply integral_congr_ae
  filter_upwards [hae] with x hx
  have hiff : (t ≤ x) ↔ (b ≤ x) := by
    constructor
    · intro htx
      by_contra hbx
      exact hx ⟨lt_of_lt_of_le hat htx, lt_of_not_ge hbx⟩
    · intro hbx
      exact le_trans htb hbx
  simp only [hiff]

theorem tau_zero_outside_closed_support (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (R t : ℝ) (hbound : (μ : Measure ℝ).support ⊆ Icc (-R) R)
    (ht : t < -R ∨ R < t) : tau μ t = 0 := by
  have hsp : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ (μ : Measure ℝ).support :=
    (μ : Measure ℝ).support_mem_ae
  rcases ht with ht | ht
  · rw [tau_eq_lower_tail μ h t, ← integral_indicator measurableSet_Iio]
    calc
      _ = ∫ _ : ℝ, (0 : ℝ) ∂(μ : Measure ℝ) :=
        integral_congr_ae (hsp.mono fun x hx => by
          have hb := (hbound hx).1
          have hxt : ¬x < t := by linarith
          simp only [Set.indicator_apply, mem_Iio, ite_eq_right hxt])
      _ = 0 := integral_zero _ _
  · rw [tau_eq_integral_if]
    calc
      _ = ∫ _ : ℝ, (0 : ℝ) ∂(μ : Measure ℝ) :=
        integral_congr_ae (hsp.mono fun x hx => by
          have hb := (hbound hx).2
          have htx : ¬t ≤ x := by linarith
          change (if t ≤ x then x else 0) = (0 : ℝ)
          rw [ite_eq_right htx])
      _ = 0 := integral_zero _ _

end BerryEsseen.ZeroBias

#print axioms BerryEsseen.ZeroBias.measurable_tau
#print axioms BerryEsseen.ZeroBias.tau_nonneg
#print axioms BerryEsseen.ZeroBias.integrable_tau
#print axioms BerryEsseen.ZeroBias.integral_tau
#print axioms BerryEsseen.ZeroBias.zeroBiasMeasure_isProbability
#print axioms BerryEsseen.ZeroBias.integrable_abs_mul_tau
#print axioms BerryEsseen.ZeroBias.integral_abs_mul_tau
#print axioms BerryEsseen.ZeroBias.integrable_mul_tau
#print axioms BerryEsseen.ZeroBias.integral_mul_tau
#print axioms BerryEsseen.ZeroBias.tau_constant_on_openGap
#print axioms BerryEsseen.ZeroBias.tau_zero_outside_closed_support
