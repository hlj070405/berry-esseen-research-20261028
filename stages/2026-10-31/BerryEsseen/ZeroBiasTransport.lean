module

public import BerryEsseen.ZeroBias
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic.FieldSimp

@[expose] public section

/-!
Primitive zero-bias transport for Borel test functions. Absolute product
integrability is proved from the actual weighted L1 condition before the
order of integration is changed. No differentiability of the original
CDF or absence of atoms is assumed.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology Interval

namespace BerryEsseen.ZeroBiasTransport

open ZeroBias

def primitive (g : ℝ → ℝ) (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, g t

lemma integral_kernel_primitive (g : ℝ → ℝ) (x : ℝ) :
    (∫ t : ℝ, g t * kernel x t) = x * primitive g x := by
  rw [mul_kernel_indicator, integral_indicator measurableSet_uIoc, integral_mul_const]
  rcases le_total 0 x with hx | hx
  · rw [uIoc_of_le hx, ← intervalIntegral.integral_of_le hx, abs_of_nonneg hx]
    unfold primitive
    ring
  · rw [uIoc_of_ge hx, ← intervalIntegral.integral_of_le hx, abs_of_nonpos hx,
      intervalIntegral.integral_symm 0 x]
    unfold primitive
    ring

/-- Tonelli's integrability criterion, applied in the direction where
the known marginal is |g(t)| tau(t). This is not a Fubini premise. -/
theorem integrable_weighted_kernel (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (g : ℝ → ℝ) (hg : Measurable g)
    (hweight : Integrable (fun t : ℝ => |g t| * tau μ t)) :
    Integrable (fun p : ℝ × ℝ => g p.2 * kernel p.1 p.2) ((μ : Measure ℝ).prod volume) := by
  have hm : Measurable (fun p : ℝ × ℝ => g p.2 * kernel p.1 p.2) :=
    (hg.comp measurable_snd).mul measurable_kernel
  apply (integrable_prod_iff' hm.aestronglyMeasurable).mpr
  refine ⟨Filter.Eventually.of_forall (fun t => (integrable_kernel_x μ h t).const_mul (g t)), ?_⟩
  have heq : (fun t : ℝ => ∫ x : ℝ, ‖g t * kernel x t‖ ∂(μ : Measure ℝ)) =
      (fun t : ℝ => |g t| * tau μ t) := by
    funext t
    calc
      _ = ∫ x : ℝ, |g t| * kernel x t ∂(μ : Measure ℝ) :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (kernel_nonneg x t)])
      _ = _ := by rw [integral_const_mul, ← tau_eq_integral_kernel μ h t]
  rw [heq]
  exact hweight

/-- The primitive intervals are actually integrable for almost every
original x; the transport identity does not exploit undefined integrals. -/
theorem ae_intervalIntegrable (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (g : ℝ → ℝ) (hg : Measurable g)
    (hweight : Integrable (fun t : ℝ => |g t| * tau μ t)) :
    ∀ᵐ x ∂(μ : Measure ℝ), IntervalIntegrable g volume 0 x := by
  filter_upwards [(integrable_weighted_kernel μ h g hg hweight).prod_right_ae] with x hx
  by_cases hx0 : x = 0
  · subst x
    exact IntervalIntegrable.refl
  · rw [mul_kernel_indicator] at hx
    have hOn : IntegrableOn (fun t : ℝ => g t * |x|) (uIoc 0 x) :=
      (integrable_indicator_iff measurableSet_uIoc).mp hx
    have hd := (hOn : Integrable (fun t : ℝ => g t * |x|) (volume.restrict (uIoc 0 x))).div_const |x|
    have heq : (fun t : ℝ => (g t * |x|) / |x|) = g := by
      funext t
      field_simp [abs_ne_zero.mpr hx0]
    rw [heq] at hd
    exact intervalIntegrable_iff.mpr hd

theorem integrable_tau_mul (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (g : ℝ → ℝ) (hg : Measurable g)
    (hweight : Integrable (fun t : ℝ => |g t| * tau μ t)) :
    Integrable (fun t : ℝ => tau μ t * g t) := by
  have hi := (integrable_weighted_kernel μ h g hg hweight).integral_prod_right
  have heq : (fun t : ℝ => ∫ x : ℝ, g t * kernel x t ∂(μ : Measure ℝ)) =
      (fun t : ℝ => tau μ t * g t) := by
    funext t
    rw [integral_const_mul, ← tau_eq_integral_kernel μ h t]
    ring
  rw [heq] at hi
  exact hi

theorem integrable_weighted_primitive (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (g : ℝ → ℝ) (hg : Measurable g)
    (hweight : Integrable (fun t : ℝ => |g t| * tau μ t)) :
    Integrable (fun x : ℝ => x * primitive g x) (μ : Measure ℝ) := by
  have hi := (integrable_weighted_kernel μ h g hg hweight).integral_prod_left
  have heq : (fun x : ℝ => ∫ t : ℝ, g t * kernel x t) =
      (fun x : ℝ => x * primitive g x) := funext (integral_kernel_primitive g)
  rw [heq] at hi
  exact hi

/-- Genuine primitive transport for measurable g and its natural
weighted L1 condition, with the original law allowed to have atoms. -/
theorem transport_identity (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (g : ℝ → ℝ) (hg : Measurable g)
    (hweight : Integrable (fun t : ℝ => |g t| * tau μ t)) :
    (∫ t : ℝ, tau μ t * g t) = ∫ x : ℝ, x * primitive g x ∂(μ : Measure ℝ) := by
  calc
    _ = ∫ t : ℝ, ∫ x : ℝ, g t * kernel x t ∂(μ : Measure ℝ) :=
      integral_congr_ae (Filter.Eventually.of_forall fun t => by
        change tau μ t * g t = ∫ x : ℝ, g t * kernel x t ∂(μ : Measure ℝ)
        rw [integral_const_mul, ← tau_eq_integral_kernel μ h t]
        ring)
    _ = ∫ x : ℝ, (∫ t : ℝ, g t * kernel x t) ∂(μ : Measure ℝ) :=
      (integral_integral_swap (integrable_weighted_kernel μ h g hg hweight)).symm
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall (integral_kernel_primitive g))

lemma integrable_linear_envelope (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (A B : ℝ) :
    Integrable (fun t : ℝ => (A + B * |t|) * tau μ t) := by
  have heq : (fun t : ℝ => (A + B * |t|) * tau μ t) =
      (fun t : ℝ => A * tau μ t + B * (|t| * tau μ t)) := by funext t; ring
  rw [heq]
  exact ((integrable_tau μ h).const_mul A).add ((integrable_abs_mul_tau μ h).const_mul B)

theorem integrable_abs_mul_tau_of_linear_growth (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (g : ℝ → ℝ) (hg : Measurable g) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hbound : ∀ t : ℝ, |g t| ≤ A + B * |t|) :
    Integrable (fun t : ℝ => |g t| * tau μ t) := by
  have hm : Measurable (fun t : ℝ => |g t| * tau μ t) :=
    ((continuous_abs.measurable).comp hg).mul (measurable_tau μ h)
  apply (integrable_linear_envelope μ h A B).mono hm.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun t => by
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (abs_nonneg (g t)) (tau_nonneg μ h t)),
      abs_of_nonneg (mul_nonneg (add_nonneg hA (mul_nonneg hB (abs_nonneg t))) (tau_nonneg μ h t))]
    exact mul_le_mul_of_nonneg_right (hbound t) (tau_nonneg μ h t)

theorem integrable_abs_mul_tau_of_bounded (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (g : ℝ → ℝ) (hg : Measurable g) (A : ℝ) (hA : 0 ≤ A)
    (hbound : ∀ t : ℝ, |g t| ≤ A) : Integrable (fun t : ℝ => |g t| * tau μ t) := by
  apply integrable_abs_mul_tau_of_linear_growth μ h g hg A 0 hA (by norm_num)
  simpa only [zero_mul, add_zero] using hbound

lemma abs_le_endpoints_of_mem_uIoc (a b t : ℝ) (ht : t ∈ uIoc a b) :
    |t| ≤ max |a| |b| := by
  rcases le_total a b with hab | hab
  · rw [uIoc_of_le hab] at ht
    apply abs_le.mpr
    constructor <;> linarith [ht.1, ht.2, neg_le_abs a, le_abs_self b,
      le_max_left |a| |b|, le_max_right |a| |b|]
  · rw [uIoc_of_ge hab] at ht
    apply abs_le.mpr
    constructor <;> linarith [ht.1, ht.2, neg_le_abs b, le_abs_self a,
      le_max_left |a| |b|, le_max_right |a| |b|]

lemma intervalIntegrable_of_linear_growth (g : ℝ → ℝ) (hg : Measurable g)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hbound : ∀ t : ℝ, |g t| ≤ A + B * |t|)
    (a b : ℝ) : IntervalIntegrable g volume a b := by
  let C := A + B * max |a| |b|
  have hC : 0 ≤ C := add_nonneg hA (mul_nonneg hB (le_trans (abs_nonneg a) (le_max_left _ _)))
  have hi : IntegrableOn (fun _ : ℝ => C) (uIoc a b) := continuous_const.integrableOn_Ioc
  apply intervalIntegrable_iff.mpr
  change Integrable g (volume.restrict (uIoc a b))
  apply MeasureTheory.Integrable.mono (f := g) (g := fun _ : ℝ => C)
    (μ := volume.restrict (uIoc a b)) hi hg.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hC]
  exact le_trans (hbound t) (add_le_add (le_refl A)
    (mul_le_mul_of_nonneg_left (abs_le_endpoints_of_mem_uIoc a b t ht) hB))

lemma norm_primitive_le_of_linear_growth (g : ℝ → ℝ) (A B : ℝ)
    (hB : 0 ≤ B) (hbound : ∀ t : ℝ, |g t| ≤ A + B * |t|) (x : ℝ) :
    ‖primitive g x‖ ≤ (A + B * |x|) * |x| := by
  have hb : ∀ t ∈ uIoc 0 x, ‖g t‖ ≤ A + B * |x| := by
    intro t ht
    rw [Real.norm_eq_abs]
    have ha := abs_le_endpoints_of_mem_uIoc 0 x t ht
    simp only [abs_zero, max_eq_right (abs_nonneg x)] at ha
    exact le_trans (hbound t) (add_le_add (le_refl A) (mul_le_mul_of_nonneg_left ha hB))
  simpa only [primitive, sub_zero] using intervalIntegral.norm_integral_le_of_norm_le_const hb

/-- For the concrete linear-growth tests, the primitive itself is also
genuinely L1 under the original law, not just after multiplication by X. -/
theorem integrable_primitive_of_linear_growth (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (g : ℝ → ℝ) (hg : Measurable g) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hbound : ∀ t : ℝ, |g t| ≤ A + B * |t|) :
    Integrable (primitive g) (μ : Measure ℝ) := by
  have hc : Continuous (primitive g) :=
    intervalIntegral.continuous_primitive (intervalIntegrable_of_linear_growth g hg A B hA hB hbound) 0
  have habs : Integrable (fun x : ℝ => |x|) (μ : Measure ℝ) := by
    simpa only [Real.norm_eq_abs] using h.integrable_mean.norm
  have hd : Integrable (fun x : ℝ => A * |x| + B * x ^ 2) (μ : Measure ℝ) :=
    (habs.const_mul A).add (h.integrable_square.const_mul B)
  apply hd.mono' hc.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x => by
    apply (norm_primitive_le_of_linear_growth g A B hB hbound x).trans_eq
    calc
      _ = A * |x| + B * |x| ^ 2 := by ring
      _ = _ := by rw [sq_abs]

theorem transport_of_linear_growth (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (g : ℝ → ℝ) (hg : Measurable g) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hbound : ∀ t : ℝ, |g t| ≤ A + B * |t|) :
    Integrable (primitive g) (μ : Measure ℝ) ∧
      Integrable (fun x : ℝ => x * primitive g x) (μ : Measure ℝ) ∧
      (∫ t : ℝ, tau μ t * g t) = ∫ x : ℝ, x * primitive g x ∂(μ : Measure ℝ) := by
  have hw := integrable_abs_mul_tau_of_linear_growth μ h g hg A B hA hB hbound
  exact ⟨integrable_primitive_of_linear_growth μ h g hg A B hA hB hbound,
    integrable_weighted_primitive μ h g hg hw, transport_identity μ h g hg hw⟩

theorem transport_of_bounded (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (g : ℝ → ℝ) (hg : Measurable g) (A : ℝ) (hA : 0 ≤ A) (hbound : ∀ t : ℝ, |g t| ≤ A) :
    Integrable (primitive g) (μ : Measure ℝ) ∧
      Integrable (fun x : ℝ => x * primitive g x) (μ : Measure ℝ) ∧
      (∫ t : ℝ, tau μ t * g t) = ∫ x : ℝ, x * primitive g x ∂(μ : Measure ℝ) := by
  apply transport_of_linear_growth μ h g hg A 0 hA (by norm_num)
  simpa only [zero_mul, add_zero] using hbound

/-- Compact support is used only in this explicitly conditional local
test theorem. Borel tests may be unbounded away from the actual support. -/
theorem integrable_abs_mul_tau_of_bounded_on_support (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (g : ℝ → ℝ) (hg : Measurable g) (R A : ℝ) (hA : 0 ≤ A)
    (hboundμ : (μ : Measure ℝ).support ⊆ Icc (-R) R)
    (hboundg : ∀ t ∈ Icc (-R) R, |g t| ≤ A) :
    Integrable (fun t : ℝ => |g t| * tau μ t) := by
  have hm : Measurable (fun t : ℝ => |g t| * tau μ t) :=
    ((continuous_abs.measurable).comp hg).mul (measurable_tau μ h)
  apply ((integrable_tau μ h).const_mul A).mono hm.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun t => by
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (abs_nonneg (g t)) (tau_nonneg μ h t)),
      abs_of_nonneg (mul_nonneg hA (tau_nonneg μ h t))]
    by_cases ht : t ∈ Icc (-R) R
    · exact mul_le_mul_of_nonneg_right (hboundg t ht) (tau_nonneg μ h t)
    · have hout : t < -R ∨ R < t := by
        by_cases hL : -R ≤ t
        · exact Or.inr (lt_of_not_ge (fun hU => ht ⟨hL, hU⟩))
        · exact Or.inl (lt_of_not_ge hL)
      rw [tau_zero_outside_closed_support μ h R t hboundμ hout]
      simp

theorem transport_of_bounded_on_support (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (g : ℝ → ℝ) (hg : Measurable g) (R A : ℝ) (hA : 0 ≤ A)
    (hboundμ : (μ : Measure ℝ).support ⊆ Icc (-R) R)
    (hboundg : ∀ t ∈ Icc (-R) R, |g t| ≤ A) :
    Integrable (fun x : ℝ => x * primitive g x) (μ : Measure ℝ) ∧
      (∀ᵐ x ∂(μ : Measure ℝ), IntervalIntegrable g volume 0 x) ∧
      (∫ t : ℝ, tau μ t * g t) = ∫ x : ℝ, x * primitive g x ∂(μ : Measure ℝ) := by
  have hw := integrable_abs_mul_tau_of_bounded_on_support μ h g hg R A hA hboundμ hboundg
  exact ⟨integrable_weighted_primitive μ h g hg hw, ae_intervalIntegrable μ h g hg hw,
    transport_identity μ h g hg hw⟩

lemma integral_linear_envelope (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (A B : ℝ) :
    (∫ t : ℝ, (A + B * |t|) * tau μ t) = A + B * (thirdAbsoluteMoment μ / 2) := by
  have heq : (fun t : ℝ => (A + B * |t|) * tau μ t) =
      (fun t : ℝ => A * tau μ t + B * (|t| * tau μ t)) := by funext t; ring
  rw [heq, integral_add ((integrable_tau μ h).const_mul A)
      ((integrable_abs_mul_tau μ h).const_mul B),
    integral_const_mul, integral_const_mul, integral_tau μ h, integral_abs_mul_tau μ h]
  ring

theorem integral_abs_mul_tau_le_linear_growth (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (g : ℝ → ℝ) (hg : Measurable g) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hbound : ∀ t : ℝ, |g t| ≤ A + B * |t|) :
    (∫ t : ℝ, |g t| * tau μ t) ≤ A + B * (thirdAbsoluteMoment μ / 2) := by
  calc
    _ ≤ ∫ t : ℝ, (A + B * |t|) * tau μ t :=
      integral_mono (integrable_abs_mul_tau_of_linear_growth μ h g hg A B hA hB hbound)
        (integrable_linear_envelope μ h A B)
        (fun t => mul_le_mul_of_nonneg_right (hbound t) (tau_nonneg μ h t))
    _ = _ := integral_linear_envelope μ h A B

lemma primitive_deriv_eq (f : ℝ → ℝ) (hf : Differentiable ℝ f)
    (hc : Continuous (deriv f)) (x : ℝ) : primitive (deriv f) x = f x - f 0 := by
  unfold primitive
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => (hf t).hasDerivAt)
    (hc.intervalIntegrable 0 x)

/-- The C1-test Stein identity follows by FTC from primitive transport.
The differentiability assumptions concern f, not the original closed CDF. -/
theorem stein_identity_of_continuous_deriv (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (f : ℝ → ℝ) (hf : Differentiable ℝ f) (hc : Continuous (deriv f))
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hbound : ∀ t : ℝ, |deriv f t| ≤ A + B * |t|) :
    Integrable f (μ : Measure ℝ) ∧ Integrable (fun x : ℝ => x * f x) (μ : Measure ℝ) ∧
      (∫ x : ℝ, x * f x ∂(μ : Measure ℝ)) = ∫ t : ℝ, tau μ t * deriv f t := by
  have hw := integrable_abs_mul_tau_of_linear_growth μ h (deriv f) hc.measurable A B hA hB hbound
  have hP := integrable_primitive_of_linear_growth μ h (deriv f) hc.measurable A B hA hB hbound
  have hXP := integrable_weighted_primitive μ h (deriv f) hc.measurable hw
  have hconst : Integrable (fun x : ℝ => f 0 * x) (μ : Measure ℝ) :=
    h.integrable_mean.const_mul (f 0)
  have hfun : f = (fun x : ℝ => primitive (deriv f) x + f 0) := by
    funext x
    rw [primitive_deriv_eq f hf hc x]
    ring
  have hXfun : (fun x : ℝ => x * f x) =
      (fun x : ℝ => x * primitive (deriv f) x + f 0 * x) := by
    funext x
    rw [primitive_deriv_eq f hf hc x]
    ring
  refine ⟨?_, ?_, ?_⟩
  · rw [hfun]
    exact hP.add (integrable_const (f 0))
  · rw [hXfun]
    exact hXP.add hconst
  · rw [hXfun, integral_add hXP hconst, integral_const_mul, h.mean_zero, mul_zero, add_zero]
    exact (transport_identity μ h (deriv f) hc.measurable hw).symm

end BerryEsseen.ZeroBiasTransport

#print axioms BerryEsseen.ZeroBiasTransport.integrable_weighted_kernel
#print axioms BerryEsseen.ZeroBiasTransport.ae_intervalIntegrable
#print axioms BerryEsseen.ZeroBiasTransport.transport_identity
#print axioms BerryEsseen.ZeroBiasTransport.integrable_primitive_of_linear_growth
#print axioms BerryEsseen.ZeroBiasTransport.transport_of_linear_growth
#print axioms BerryEsseen.ZeroBiasTransport.transport_of_bounded_on_support
#print axioms BerryEsseen.ZeroBiasTransport.integral_abs_mul_tau_le_linear_growth
#print axioms BerryEsseen.ZeroBiasTransport.stein_identity_of_continuous_deriv
