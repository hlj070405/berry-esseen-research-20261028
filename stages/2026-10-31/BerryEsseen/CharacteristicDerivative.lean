module

public import BerryEsseen.Target
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

@[expose] public section

/-! 2026-10-29: sharp sine bound for the actual radian characteristic-function
derivative under mean zero and variance one, requiring only finite second moment. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ComplexConjugate

namespace BerryEsseen.CharacteristicDerivative

lemma hasDerivAt_sin_sub_mul_cos (x : ℝ) :
    HasDerivAt (fun u : ℝ => Real.sin u - u * Real.cos u) (x * Real.sin x) x := by
  convert (Real.hasDerivAt_sin x).sub ((hasDerivAt_id' x).fun_mul (Real.hasDerivAt_cos x)) using 1
  ring

lemma sin_sub_mul_cos_nonneg (x : ℝ) (hx0 : 0 ≤ x) (hxπ : x ≤ Real.pi) :
    0 ≤ Real.sin x - x * Real.cos x := by
  have hm : MonotoneOn (fun u : ℝ => Real.sin u - u * Real.cos u) (Icc 0 Real.pi) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun u : ℝ => u * Real.sin u)
      (convex_Icc _ _) (by fun_prop)
    · exact fun u _ => (hasDerivAt_sin_sub_mul_cos u).hasDerivWithinAt
    · intro u hu
      have hu' : u ∈ Ioo (0 : ℝ) Real.pi := by simpa only [interior_Icc] using hu
      exact mul_nonneg hu'.1.le (Real.sin_nonneg_of_nonneg_of_le_pi hu'.1.le hu'.2.le)
  have h := hm ⟨le_rfl, Real.pi_pos.le⟩ ⟨hx0, hxπ⟩ hx0
  simpa only [Real.sin_zero, zero_mul, sub_zero] using h

lemma hasDerivAt_sin_div (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun u : ℝ => Real.sin u / u) ((Real.cos x * x - Real.sin x) / x ^ 2) x := by
  simpa only [mul_one] using (Real.hasDerivAt_sin x).fun_div (hasDerivAt_id' x) (ne_of_gt hx)

/-- The sinc ratio is antitone on (0,π], proved from its actual derivative. -/
lemma sine_ratio_antitone : AntitoneOn (fun u : ℝ => Real.sin u / u) (Ioc 0 Real.pi) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos
    (f' := fun u : ℝ => (Real.cos u * u - Real.sin u) / u ^ 2) (convex_Ioc _ _)
    (Real.continuous_sin.continuousOn.div continuousOn_id (fun u hu => ne_of_gt hu.1))
  · intro u hu
    have hu' : u ∈ Ioc (0 : ℝ) Real.pi := interior_subset hu
    exact (hasDerivAt_sin_div u hu'.1).hasDerivWithinAt
  · intro u hu
    have hu' : u ∈ Ioc (0 : ℝ) Real.pi := interior_subset hu
    exact div_nonpos_of_nonpos_of_nonneg
      (by nlinarith [sin_sub_mul_cos_nonneg u hu'.1.le hu'.2]) (sq_nonneg u)

lemma sine_ratio_lower (a : ℝ) (ha : 0 < a) (hcap : a ≤ Real.pi / 2) :
    2 / Real.pi ≤ Real.sin a / a := by
  have hhalf : Real.pi / 2 ≤ Real.pi := by linarith [Real.pi_pos]
  have h := sine_ratio_antitone ⟨ha, hcap.trans hhalf⟩ ⟨by positivity, hhalf⟩ hcap
  have heq : Real.sin (Real.pi / 2) / (Real.pi / 2) = 2 / Real.pi := by
    rw [Real.sin_pi_div_two]
    field_simp [ne_of_gt Real.pi_pos]
  change Real.sin (Real.pi / 2) / (Real.pi / 2) ≤ Real.sin a / a at h
  rw [heq] at h
  exact h

lemma sine_ratio_upper_after (a x : ℝ) (ha : 0 < a) (hcap : a ≤ Real.pi / 2) (hax : a ≤ x) :
    Real.sin x / x ≤ Real.sin a / a := by
  have hx : 0 < x := lt_of_lt_of_le ha hax
  have hhalf : Real.pi / 2 ≤ Real.pi := by linarith [Real.pi_pos]
  by_cases hxπ : x ≤ Real.pi
  · exact sine_ratio_antitone ⟨ha, hcap.trans hhalf⟩ ⟨hx, hxπ⟩ hax
  · have hπx : Real.pi ≤ x := le_of_lt (lt_of_not_ge hxπ)
    calc
      _ ≤ 1 / x := div_le_div_of_nonneg_right (Real.sin_le_one x) hx.le
      _ ≤ 1 / Real.pi := div_le_div_of_nonneg_left (by norm_num) Real.pi_pos hπx
      _ ≤ 2 / Real.pi := div_le_div_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 2) Real.pi_pos.le
      _ ≤ _ := sine_ratio_lower a ha hcap

def cosGap (a x : ℝ) : ℝ := Real.cos x - Real.cos a + (Real.sin a / (2 * a)) * (x ^ 2 - a ^ 2)

lemma hasDerivAt_cosGap (a x : ℝ) :
    HasDerivAt (cosGap a) (-Real.sin x + 2 * (Real.sin a / (2 * a)) * x) x := by
  change HasDerivAt (fun u : ℝ => Real.cos u - Real.cos a + (Real.sin a / (2 * a)) * (u ^ 2 - a ^ 2)) _ x
  convert ((Real.hasDerivAt_cos x).sub_const (Real.cos a)).add
    ((((hasDerivAt_id' x).fun_pow 2).sub_const (a ^ 2)).const_mul (Real.sin a / (2 * a))) using 1
  ring

lemma cosGap_derivative_form (a x : ℝ) (ha : 0 < a) (hx : 0 < x) :
    -Real.sin x + 2 * (Real.sin a / (2 * a)) * x = x * (Real.sin a / a - Real.sin x / x) := by
  field_simp [ne_of_gt ha, ne_of_gt hx]
  ring

lemma cosGap_nonneg (a : ℝ) (ha : 0 < a) (hcap : a ≤ Real.pi / 2) (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ cosGap a x := by
  have hcont : Continuous (cosGap a) := by unfold cosGap; fun_prop
  have hhalf : Real.pi / 2 ≤ Real.pi := by linarith [Real.pi_pos]
  have hanti : AntitoneOn (cosGap a) (Icc 0 a) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos
      (f' := fun u => -Real.sin u + 2 * (Real.sin a / (2 * a)) * u) (convex_Icc _ _) hcont.continuousOn
    · exact fun u _ => (hasDerivAt_cosGap a u).hasDerivWithinAt
    · intro u hu
      have hu' : u ∈ Ioo (0 : ℝ) a := by simpa only [interior_Icc] using hu
      rw [cosGap_derivative_form a u ha hu'.1]
      have hr := sine_ratio_antitone ⟨hu'.1, hu'.2.le.trans (hcap.trans hhalf)⟩ ⟨ha, hcap.trans hhalf⟩ hu'.2.le
      exact mul_nonpos_of_nonneg_of_nonpos hu'.1.le (sub_nonpos.mpr hr)
  have hmono : MonotoneOn (cosGap a) (Ici a) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg
      (f' := fun u => -Real.sin u + 2 * (Real.sin a / (2 * a)) * u) (convex_Ici _) hcont.continuousOn
    · exact fun u _ => (hasDerivAt_cosGap a u).hasDerivWithinAt
    · intro u hu
      have hu' : a < u := by simpa only [interior_Ici, mem_Ioi] using hu
      have hu0 : 0 < u := ha.trans hu'
      rw [cosGap_derivative_form a u ha hu0]
      exact mul_nonneg hu0.le (sub_nonneg.mpr (sine_ratio_upper_after a u ha hcap hu'.le))
  rcases le_total x a with hxa | hax
  · have h := hanti ⟨hx, hxa⟩ ⟨ha.le, le_rfl⟩ hxa
    simpa only [cosGap, sub_self, mul_zero, zero_add] using h
  · have h := hmono (show a ∈ Ici a from le_rfl) hax hax
    simpa only [cosGap, sub_self, mul_zero, zero_add] using h

/-- The global quadratic cosine minorant has no support restriction on x. -/
theorem cosine_minorant (a x : ℝ) (ha : 0 < a) (hcap : a ≤ Real.pi / 2) :
    Real.cos a - (Real.sin a / (2 * a)) * (x ^ 2 - a ^ 2) ≤ Real.cos x := by
  have h := cosGap_nonneg a ha hcap |x| (abs_nonneg x)
  have hc : Real.cos |x| = Real.cos x := by
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]
    · rw [abs_of_nonpos hx, Real.cos_neg]
  unfold cosGap at h
  rw [hc, sq_abs] at h
  linarith

end BerryEsseen.CharacteristicDerivative
#print axioms BerryEsseen.CharacteristicDerivative.sine_ratio_antitone
#print axioms BerryEsseen.CharacteristicDerivative.cosine_minorant

namespace BerryEsseen.CharacteristicDerivative

def oscillation (t x : ℝ) : ℂ := Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I)
def weightedCF (μ : ProbabilityMeasure ℝ) (t : ℝ) : ℂ :=
  ∫ x : ℝ, (x : ℂ) * oscillation t x ∂(μ : Measure ℝ)

lemma norm_oscillation (t x : ℝ) : ‖oscillation t x‖ = 1 := by
  unfold oscillation
  rw [← Complex.ofReal_mul]
  exact Complex.norm_exp_ofReal_mul_I (t * x)

lemma oscillation_re (t x : ℝ) : (oscillation t x).re = Real.cos (t * x) := by
  unfold oscillation
  rw [← Complex.ofReal_mul, Complex.exp_ofReal_mul_I_re]

lemma integrable_oscillation (μ : ProbabilityMeasure ℝ) (t : ℝ) :
    Integrable (oscillation t) (μ : Measure ℝ) := by
  apply (integrable_const (1 : ℝ)).mono' (by unfold oscillation; fun_prop)
  exact Eventually.of_forall fun x => (norm_oscillation t x).le

lemma integral_oscillation (μ : ProbabilityMeasure ℝ) (t : ℝ) :
    (∫ x : ℝ, oscillation t x ∂(μ : Measure ℝ)) = charFun (μ : Measure ℝ) t := by
  rw [charFun_apply_real]
  rfl

lemma integrable_weighted (μ : ProbabilityMeasure ℝ) (h1 : Integrable (fun x : ℝ => x) (μ : Measure ℝ)) (t : ℝ) :
    Integrable (fun x : ℝ => (x : ℂ) * oscillation t x) (μ : Measure ℝ) := by
  apply h1.norm.mono' (by unfold oscillation; fun_prop)
  exact Eventually.of_forall fun x => by simp only [norm_mul, norm_oscillation, Complex.norm_real, mul_one, le_refl]

lemma integrable_first_of_second (μ : ProbabilityMeasure ℝ)
    (h2 : Integrable (fun x : ℝ => x ^ 2) (μ : Measure ℝ)) :
    Integrable (fun x : ℝ => x) (μ : Measure ℝ) := by
  have hid : AEStronglyMeasurable (fun x : ℝ => x) (μ : Measure ℝ) := measurable_id.aestronglyMeasurable
  have h2n : Integrable (fun x : ℝ => ‖x‖ ^ 2) (μ : Measure ℝ) := by simpa only [Real.norm_eq_abs, sq_abs] using h2
  have h1n := integrable_norm_pow_of_le hid (by decide : 1 ≤ 2) h2n
  exact (integrable_norm_iff hid).mp (by simpa only [pow_one] using h1n)

/-- The official actual-measure Taylor API yields the native derivative, in radians. -/
theorem deriv_charFun_eq (μ : ProbabilityMeasure ℝ)
    (h1 : Integrable (fun x : ℝ => x) (μ : Measure ℝ)) (t : ℝ) :
    deriv (charFun (μ : Measure ℝ)) t = Complex.I * weightedCF μ t := by
  have hlp : MemLp id ((1 : ℕ) : ENNReal) (μ : Measure ℝ) := by
    simpa only [Nat.cast_one] using (memLp_one_iff_integrable.mpr h1 : MemLp id 1 (μ : Measure ℝ))
  have h := iteratedDeriv_charFun (n := 1) (t := t) hlp
  simpa only [iteratedDeriv_one, pow_one, weightedCF, oscillation] using h

theorem hasDerivAt_charFun (μ : ProbabilityMeasure ℝ)
    (h1 : Integrable (fun x : ℝ => x) (μ : Measure ℝ)) (t : ℝ) :
    HasDerivAt (charFun (μ : Measure ℝ)) (Complex.I * weightedCF μ t) t := by
  have hlp : MemLp id ((1 : ℕ) : ENNReal) (μ : Measure ℝ) := by
    simpa only [Nat.cast_one] using (memLp_one_iff_integrable.mpr h1 : MemLp id 1 (μ : Measure ℝ))
  have hc := contDiff_charFun (n := 1) hlp
  exact ((hc.differentiable (by norm_num)) t).hasDerivAt.congr_deriv (deriv_charFun_eq μ h1 t)

lemma norm_deriv_charFun (μ : ProbabilityMeasure ℝ)
    (h1 : Integrable (fun x : ℝ => x) (μ : Measure ℝ)) (t : ℝ) :
    ‖deriv (charFun (μ : Measure ℝ)) t‖ = ‖weightedCF μ t‖ := by
  rw [deriv_charFun_eq μ h1 t, norm_mul, Complex.norm_I, one_mul]

/-- Real dot product of two genuine complex values. -/
def dot (u v : ℂ) : ℝ := v.re * u.re + v.im * u.im

lemma dot_self (u : ℂ) : dot u u = Complex.normSq u := by simp only [dot, Complex.normSq_apply]
lemma dot_zero (u : ℂ) : dot u 0 = 0 := by simp [dot]

lemma integrable_dot (μ : Measure ℝ) (f : ℝ → ℂ) (hf : Integrable f μ) (v : ℂ) :
    Integrable (fun x => dot (f x) v) μ := by
  exact (hf.re.const_mul v.re).add (hf.im.const_mul v.im)

lemma integral_dot (μ : Measure ℝ) (f : ℝ → ℂ) (hf : Integrable f μ) (v : ℂ) :
    (∫ x, dot (f x) v ∂μ) = dot (∫ x, f x ∂μ) v := by
  have hr : Integrable (fun x => (f x).re) μ := hf.re
  have hi : Integrable (fun x => (f x).im) μ := hf.im
  have hre : (∫ x, (f x).re ∂μ) = (∫ x, f x ∂μ).re := integral_re hf
  have him : (∫ x, (f x).im ∂μ) = (∫ x, f x ∂μ).im := integral_im hf
  unfold dot
  rw [integral_add (hr.const_mul v.re) (hi.const_mul v.im), integral_const_mul, integral_const_mul, hre, him]

def projection (μ : ProbabilityMeasure ℝ) (t : ℝ) (z : ℂ) (x : ℝ) : ℂ :=
  oscillation t x - charFun (μ : Measure ℝ) t - (x : ℂ) * z

def expanded (μ : ProbabilityMeasure ℝ) (t : ℝ) (z : ℂ) (x : ℝ) : ℝ :=
  (1 + Complex.normSq (charFun (μ : Measure ℝ) t)) + Complex.normSq z * x ^ 2 -
    2 * dot (oscillation t x) (charFun (μ : Measure ℝ) t) -
    2 * dot ((x : ℂ) * oscillation t x) z + (2 * dot (charFun (μ : Measure ℝ) t) z) * x

lemma projection_identity (u f z : ℂ) (x : ℝ) :
    Complex.normSq (u - f - (x : ℂ) * z) = Complex.normSq u + Complex.normSq f + Complex.normSq z * x ^ 2 -
      2 * dot u f - 2 * dot ((x : ℂ) * u) z + (2 * dot f z) * x := by
  simp only [dot, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero]
  ring

lemma projection_sq_eq (μ : ProbabilityMeasure ℝ) (t : ℝ) (z : ℂ) (x : ℝ) :
    Complex.normSq (projection μ t z x) = expanded μ t z x := by
  unfold projection expanded
  rw [projection_identity, Complex.normSq_eq_norm_sq, norm_oscillation]
  norm_num

lemma integrable_expanded (μ : ProbabilityMeasure ℝ)
    (h1 : Integrable (fun x : ℝ => x) (μ : Measure ℝ))
    (h2 : Integrable (fun x : ℝ => x ^ 2) (μ : Measure ℝ)) (t : ℝ) (z : ℂ) :
    Integrable (expanded μ t z) (μ : Measure ℝ) := by
  exact (((((integrable_const (1 + Complex.normSq (charFun (μ : Measure ℝ) t))).add
    (h2.const_mul (Complex.normSq z))).sub
    ((integrable_dot _ _ (integrable_oscillation μ t) _).const_mul 2)).sub
    ((integrable_dot _ _ (integrable_weighted μ h1 t) z).const_mul 2)).add
    (h1.const_mul (2 * dot (charFun (μ : Measure ℝ) t) z)))

lemma integrable_projection_sq (μ : ProbabilityMeasure ℝ)
    (h1 : Integrable (fun x : ℝ => x) (μ : Measure ℝ))
    (h2 : Integrable (fun x : ℝ => x ^ 2) (μ : Measure ℝ)) (t : ℝ) (z : ℂ) :
    Integrable (fun x => Complex.normSq (projection μ t z x)) (μ : Measure ℝ) :=
  (integrable_expanded μ h1 h2 t z).congr (Eventually.of_forall fun x => (projection_sq_eq μ t z x).symm)

lemma integral_projection_sq (μ : ProbabilityMeasure ℝ)
    (h1 : Integrable (fun x : ℝ => x) (μ : Measure ℝ))
    (h2 : Integrable (fun x : ℝ => x ^ 2) (μ : Measure ℝ))
    (hm : (∫ x : ℝ, x ∂(μ : Measure ℝ)) = 0) (hv : (∫ x : ℝ, x ^ 2 ∂(μ : Measure ℝ)) = 1)
    (t : ℝ) (z : ℂ) :
    (∫ x, Complex.normSq (projection μ t z x) ∂(μ : Measure ℝ)) =
      1 - Complex.normSq (charFun (μ : Measure ℝ) t) + Complex.normSq z - 2 * dot (weightedCF μ t) z := by
  have hA : Integrable (fun _ : ℝ => 1 + Complex.normSq (charFun (μ : Measure ℝ) t)) (μ : Measure ℝ) := integrable_const _
  have hB : Integrable (fun x : ℝ => Complex.normSq z * x ^ 2) (μ : Measure ℝ) := h2.const_mul _
  have hC : Integrable (fun x : ℝ => 2 * dot (oscillation t x) (charFun (μ : Measure ℝ) t)) (μ : Measure ℝ) :=
    (integrable_dot _ _ (integrable_oscillation μ t) _).const_mul 2
  have hD : Integrable (fun x : ℝ => 2 * dot ((x : ℂ) * oscillation t x) z) (μ : Measure ℝ) :=
    (integrable_dot _ _ (integrable_weighted μ h1 t) z).const_mul 2
  have hE : Integrable (fun x : ℝ => (2 * dot (charFun (μ : Measure ℝ) t) z) * x) (μ : Measure ℝ) := h1.const_mul _
  have hAB : Integrable (fun x : ℝ => (1 + Complex.normSq (charFun (μ : Measure ℝ) t)) + Complex.normSq z * x ^ 2)
      (μ : Measure ℝ) := hA.add hB
  have hABC : Integrable (fun x : ℝ => (1 + Complex.normSq (charFun (μ : Measure ℝ) t)) + Complex.normSq z * x ^ 2 -
      2 * dot (oscillation t x) (charFun (μ : Measure ℝ) t)) (μ : Measure ℝ) := hAB.sub hC
  have hABCD : Integrable (fun x : ℝ => (1 + Complex.normSq (charFun (μ : Measure ℝ) t)) + Complex.normSq z * x ^ 2 -
      2 * dot (oscillation t x) (charFun (μ : Measure ℝ) t) - 2 * dot ((x : ℂ) * oscillation t x) z) (μ : Measure ℝ) := hABC.sub hD
  have heq : (fun x => Complex.normSq (projection μ t z x)) = expanded μ t z := funext (projection_sq_eq μ t z)
  rw [heq]
  unfold expanded
  rw [integral_add hABCD hE, integral_sub hABC hD, integral_sub hAB hC, integral_add hA hB,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
    hv, hm, integral_dot _ _ (integrable_oscillation μ t), integral_dot _ _ (integrable_weighted μ h1 t),
    integral_oscillation]
  change _ = 1 - Complex.normSq (charFun (μ : Measure ℝ) t) + Complex.normSq z -
    2 * dot (∫ x : ℝ, (x : ℂ) * oscillation t x ∂(μ : Measure ℝ)) z
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, mul_zero, dot_self]
  ring

/-- Actual complex L² covariance, obtained by integrating the nonnegative projection square. -/
theorem weightedCF_covariance (μ : ProbabilityMeasure ℝ)
    (h1 : Integrable (fun x : ℝ => x) (μ : Measure ℝ))
    (h2 : Integrable (fun x : ℝ => x ^ 2) (μ : Measure ℝ))
    (hm : (∫ x : ℝ, x ∂(μ : Measure ℝ)) = 0) (hv : (∫ x : ℝ, x ^ 2 ∂(μ : Measure ℝ)) = 1) (t : ℝ) :
    ‖weightedCF μ t‖ ^ 2 ≤ 1 - ‖charFun (μ : Measure ℝ) t‖ ^ 2 := by
  have hnon : 0 ≤ ∫ x, Complex.normSq (projection μ t (weightedCF μ t) x) ∂(μ : Measure ℝ) :=
    integral_nonneg fun x => Complex.normSq_nonneg _
  rw [integral_projection_sq μ h1 h2 hm hv, dot_self, Complex.normSq_eq_norm_sq,
    Complex.normSq_eq_norm_sq] at hnon
  linarith

end BerryEsseen.CharacteristicDerivative
#print axioms BerryEsseen.CharacteristicDerivative.hasDerivAt_charFun
#print axioms BerryEsseen.CharacteristicDerivative.weightedCF_covariance

namespace BerryEsseen.CharacteristicDerivative

/-- The centered exponential is genuinely L² and has its actual variance identity. -/
theorem centered_second_moment (μ : ProbabilityMeasure ℝ)
    (h1 : Integrable (fun x : ℝ => x) (μ : Measure ℝ))
    (h2 : Integrable (fun x : ℝ => x ^ 2) (μ : Measure ℝ))
    (hm : (∫ x : ℝ, x ∂(μ : Measure ℝ)) = 0) (hv : (∫ x : ℝ, x ^ 2 ∂(μ : Measure ℝ)) = 1) (t : ℝ) :
    Integrable (fun x => ‖oscillation t x - charFun (μ : Measure ℝ) t‖ ^ 2) (μ : Measure ℝ) ∧
    (∫ x, ‖oscillation t x - charFun (μ : Measure ℝ) t‖ ^ 2 ∂(μ : Measure ℝ)) =
      1 - ‖charFun (μ : Measure ℝ) t‖ ^ 2 := by
  refine ⟨?_, ?_⟩
  · simpa only [projection, mul_zero, sub_zero, Complex.normSq_eq_norm_sq] using
      integrable_projection_sq μ h1 h2 t 0
  · simpa [projection, Complex.normSq_eq_norm_sq, dot_zero] using integral_projection_sq μ h1 h2 hm hv t 0

/-- Integrating the global minorant uses only the actual second moment. -/
theorem charFun_real_lower (μ : ProbabilityMeasure ℝ)
    (h2 : Integrable (fun x : ℝ => x ^ 2) (μ : Measure ℝ))
    (hv : (∫ x : ℝ, x ^ 2 ∂(μ : Measure ℝ)) = 1) (t : ℝ) (ht : |t| ≤ Real.pi / 2) :
    Real.cos |t| ≤ (charFun (μ : Measure ℝ) t).re := by
  by_cases ht0 : t = 0
  · subst t
    simp [charFun_zero]
  let a := |t|
  let d := Real.sin a / (2 * a)
  have ha : 0 < a := abs_pos.mpr ht0
  have ha2 : a ^ 2 = t ^ 2 := sq_abs t
  have heq : (fun x : ℝ => Real.cos a - d * ((t * x) ^ 2 - a ^ 2)) =
      (fun x => Real.cos a + d * a ^ 2 - (d * t ^ 2) * x ^ 2) := by funext x; ring
  have hconst : Integrable (fun _ : ℝ => Real.cos a + d * a ^ 2) (μ : Measure ℝ) := integrable_const _
  have hsq : Integrable (fun x : ℝ => (d * t ^ 2) * x ^ 2) (μ : Measure ℝ) := h2.const_mul _
  have hpoly : Integrable (fun x : ℝ => Real.cos a - d * ((t * x) ^ 2 - a ^ 2)) (μ : Measure ℝ) := by
    rw [heq]
    exact hconst.sub hsq
  have hcos : Integrable (fun x : ℝ => Real.cos (t * x)) (μ : Measure ℝ) := by
    have hr : Integrable (fun x : ℝ => (oscillation t x).re) (μ : Measure ℝ) := (integrable_oscillation μ t).re
    simpa only [oscillation_re] using hr
  have hminor : (∫ x : ℝ, Real.cos a - d * ((t * x) ^ 2 - a ^ 2) ∂(μ : Measure ℝ)) ≤
      ∫ x : ℝ, Real.cos (t * x) ∂(μ : Measure ℝ) := by
    apply integral_mono_ae hpoly hcos
    exact Eventually.of_forall fun x => cosine_minorant a (t * x) ha ht
  have hpolyEq : (∫ x : ℝ, Real.cos a - d * ((t * x) ^ 2 - a ^ 2) ∂(μ : Measure ℝ)) = Real.cos a := by
    rw [heq, integral_sub hconst hsq, integral_const_mul, hv]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, mul_one]
    rw [ha2]
    ring
  have hcosEq : (∫ x : ℝ, Real.cos (t * x) ∂(μ : Measure ℝ)) = (charFun (μ : Measure ℝ) t).re := by
    have h : (∫ x : ℝ, (oscillation t x).re ∂(μ : Measure ℝ)) =
        (∫ x : ℝ, oscillation t x ∂(μ : Measure ℝ)).re := integral_re (integrable_oscillation μ t)
    simpa only [oscillation_re, integral_oscillation] using h
  rw [hpolyEq, hcosEq] at hminor
  exact hminor

lemma weightedCF_small (μ : ProbabilityMeasure ℝ)
    (h1 : Integrable (fun x : ℝ => x) (μ : Measure ℝ))
    (h2 : Integrable (fun x : ℝ => x ^ 2) (μ : Measure ℝ))
    (hm : (∫ x : ℝ, x ∂(μ : Measure ℝ)) = 0) (hv : (∫ x : ℝ, x ^ 2 ∂(μ : Measure ℝ)) = 1)
    (t : ℝ) (ht : |t| ≤ Real.pi / 2) : ‖weightedCF μ t‖ ≤ Real.sin |t| := by
  have hcos : 0 ≤ Real.cos |t| := Real.cos_nonneg_of_mem_Icc ⟨by linarith [abs_nonneg t, Real.pi_pos], ht⟩
  have hnorm : Real.cos |t| ≤ ‖charFun (μ : Measure ℝ) t‖ :=
    (charFun_real_lower μ h2 hv t ht).trans (Complex.re_le_norm _)
  have hsquare := (sq_le_sq₀ hcos (norm_nonneg _)).mpr hnorm
  have hcov := weightedCF_covariance μ h1 h2 hm hv t
  have hsin : 0 ≤ Real.sin |t| := Real.sin_nonneg_of_nonneg_of_le_pi (abs_nonneg t)
    (ht.trans (by linarith [Real.pi_pos]))
  apply (sq_le_sq₀ (norm_nonneg _) hsin).mp
  nlinarith [Real.sin_sq_add_cos_sq |t|]

lemma weightedCF_le_one (μ : ProbabilityMeasure ℝ)
    (h1 : Integrable (fun x : ℝ => x) (μ : Measure ℝ))
    (h2 : Integrable (fun x : ℝ => x ^ 2) (μ : Measure ℝ))
    (hm : (∫ x : ℝ, x ∂(μ : Measure ℝ)) = 0) (hv : (∫ x : ℝ, x ^ 2 ∂(μ : Measure ℝ)) = 1) (t : ℝ) :
    ‖weightedCF μ t‖ ≤ 1 := by
  have hcov := weightedCF_covariance μ h1 h2 hm hv t
  apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).mp
  nlinarith [sq_nonneg ‖charFun (μ : Measure ℝ) t‖]

/-- Sharp classical derivative input for every actual law with mean 0 and
second moment 1. Finite second moment alone supplies the needed first moment. -/
theorem deriv_sine_bound_of_second (μ : ProbabilityMeasure ℝ)
    (h2 : Integrable (fun x : ℝ => x ^ 2) (μ : Measure ℝ))
    (hm : (∫ x : ℝ, x ∂(μ : Measure ℝ)) = 0) (hv : (∫ x : ℝ, x ^ 2 ∂(μ : Measure ℝ)) = 1) (t : ℝ) :
    ‖deriv (charFun (μ : Measure ℝ)) t‖ ≤ Real.sin (min |t| (Real.pi / 2)) := by
  have h1 := integrable_first_of_second μ h2
  rw [norm_deriv_charFun μ h1 t]
  by_cases ht : |t| ≤ Real.pi / 2
  · rw [min_eq_left ht]
    exact weightedCF_small μ h1 h2 hm hv t ht
  · have hlarge : Real.pi / 2 ≤ |t| := (lt_of_not_ge ht).le
    rw [min_eq_right hlarge, Real.sin_pi_div_two]
    exact weightedCF_le_one μ h1 h2 hm hv t

theorem hasDerivAt_charFun_of_second (μ : ProbabilityMeasure ℝ)
    (h2 : Integrable (fun x : ℝ => x ^ 2) (μ : Measure ℝ)) (t : ℝ) :
    HasDerivAt (charFun (μ : Measure ℝ)) (Complex.I * weightedCF μ t) t :=
  hasDerivAt_charFun μ (integrable_first_of_second μ h2) t

theorem standardized_deriv_sine (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (t : ℝ) :
    ‖deriv (charFun (μ : Measure ℝ)) t‖ ≤ Real.sin (min |t| (Real.pi / 2)) :=
  deriv_sine_bound_of_second μ h.integrable_square h.mean_zero h.second_moment_one t

end BerryEsseen.CharacteristicDerivative
#print axioms BerryEsseen.CharacteristicDerivative.centered_second_moment
#print axioms BerryEsseen.CharacteristicDerivative.charFun_real_lower
#print axioms BerryEsseen.CharacteristicDerivative.deriv_sine_bound_of_second
#print axioms BerryEsseen.CharacteristicDerivative.hasDerivAt_charFun_of_second
#print axioms BerryEsseen.CharacteristicDerivative.standardized_deriv_sine
