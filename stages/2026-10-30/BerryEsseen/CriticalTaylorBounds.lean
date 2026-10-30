module

public import BerryEsseen.SquareBiasFourier
public import BerryEsseen.ThirdMomentRegion
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section

/-! 2026-10-29: the global compensated Taylor inequalities at the critical
parameters 1/4, 1/3 and 3/8, and their actual-law characteristic-function
consequences. These are the existing Prawitz first-segment bounds recalled
in Shevtsova, arXiv:1301.2783v3, formula (2) and Theorem 1. The factorial
scales are retained explicitly; no novelty or completed Berry--Esseen
constant is claimed. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter

namespace BerryEsseen.CriticalTaylorBounds

open CharacteristicExpansion (pureExp)

lemma nonneg_from_derivative {f f' : ℝ → ℝ} (s : ℝ) (hs : 0 ≤ s)
    (h0 : f 0 = 0) (hd : ∀ u, HasDerivAt f (f' u) u)
    (hp : ∀ u, 0 ≤ u → u ≤ s → 0 ≤ f' u) : 0 ≤ f s := by
  have hc : Continuous f := continuous_iff_continuousAt.mpr fun u => (hd u).continuousAt
  have hm : MonotoneOn f (Icc 0 s) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (f' := f') (convex_Icc _ _) hc.continuousOn
    · exact fun u _ => (hd u).hasDerivWithinAt
    · intro u hu
      have hu' : u ∈ Ioo (0 : ℝ) s := by simpa only [interior_Icc] using hu
      exact hp u hu'.1.le hu'.2.le
  have hh := hm ⟨le_rfl, hs⟩ ⟨hs, le_rfl⟩ hs
  simpa only [h0] using hh

def H1 (s : ℝ) : ℝ := s ^ 2 + s * Real.sin s + 4 * Real.cos s - 4
def H1d (s : ℝ) : ℝ := 2 * s + s * Real.cos s - 3 * Real.sin s
def H1dd (s : ℝ) : ℝ := 2 - 2 * Real.cos s - s * Real.sin s
def H2 (s : ℝ) : ℝ :=
  s ^ 4 - 8 * s ^ 2 - 4 * s ^ 2 * Real.cos s + 24 * s * Real.sin s + 24 * Real.cos s - 24
def G (s : ℝ) : ℝ := s ^ 3 - 12 * s - 3 * s * Real.cos s + 15 * Real.sin s
def H3 (s : ℝ) : ℝ := s ^ 6 - 144 * s ^ 2 * Real.cos s - 18 * s ^ 4 +
  (288 * s - 18 * s ^ 3) * Real.sin s + 288 * Real.cos s - 288

lemma hasDerivAt_H1 (s : ℝ) : HasDerivAt H1 (H1d s) s := by
  convert ((((hasDerivAt_id' s).fun_pow 2).add
    ((hasDerivAt_id' s).fun_mul (Real.hasDerivAt_sin s))).add
    ((Real.hasDerivAt_cos s).const_mul 4)).sub_const 4 using 1
  · funext u
    simp only [H1, Pi.add_apply, Pi.sub_apply] <;> ring
  · dsimp [H1d]
    norm_num <;> ring

lemma hasDerivAt_H1d (s : ℝ) : HasDerivAt H1d (H1dd s) s := by
  convert (((hasDerivAt_id' s).const_mul 2).add
    ((hasDerivAt_id' s).fun_mul (Real.hasDerivAt_cos s))).sub
    ((Real.hasDerivAt_sin s).const_mul 3) using 1
  · funext u
    simp only [H1d, Pi.add_apply, Pi.sub_apply] <;> ring
  · dsimp [H1dd]
    norm_num <;> ring

lemma hasDerivAt_H1dd (s : ℝ) :
    HasDerivAt H1dd (Real.sin s - s * Real.cos s) s := by
  convert (((Real.hasDerivAt_cos s).const_mul 2).const_sub 2).sub
    ((hasDerivAt_id' s).fun_mul (Real.hasDerivAt_sin s)) using 1
  · funext u
    simp only [H1dd, Pi.sub_apply] <;> ring
  · norm_num <;> ring

lemma H1dd_nonneg (s : ℝ) (hs0 : 0 ≤ s) (hsπ : s ≤ Real.pi) : 0 ≤ H1dd s := by
  apply nonneg_from_derivative s hs0 (by simp [H1dd]) hasDerivAt_H1dd
  exact fun u hu0 hus => CharacteristicDerivative.sin_sub_mul_cos_nonneg u hu0 (hus.trans hsπ)

lemma H1d_nonneg (s : ℝ) (hs : 0 ≤ s) : 0 ≤ H1d s := by
  by_cases hsπ : s ≤ Real.pi
  · apply nonneg_from_derivative s hs (by simp [H1d]) hasDerivAt_H1d
    exact fun u hu0 hus => H1dd_nonneg u hu0 (hus.trans hsπ)
  · have hs3 : 3 ≤ s := by linarith [Real.pi_gt_three]
    have hw := mul_le_mul_of_nonneg_left (Real.neg_one_le_cos s) hs
    dsimp [H1d]
    nlinarith [Real.sin_le_one s]

lemma H1_nonneg_of_nonneg (s : ℝ) (hs : 0 ≤ s) : 0 ≤ H1 s := by
  apply nonneg_from_derivative s hs (by simp [H1]) hasDerivAt_H1
  exact fun u hu _ => H1d_nonneg u hu

lemma H1_neg (s : ℝ) : H1 (-s) = H1 s := by simp only [H1, Real.sin_neg, Real.cos_neg]; ring

theorem H1_nonneg (s : ℝ) : 0 ≤ H1 s := by
  rcases le_total 0 s with hs | hs
  · exact H1_nonneg_of_nonneg s hs
  · simpa only [H1_neg] using H1_nonneg_of_nonneg (-s) (neg_nonneg.mpr hs)

lemma hasDerivAt_H2 (s : ℝ) : HasDerivAt H2 (4 * s * H1 s) s := by
  convert ((((((hasDerivAt_id' s).fun_pow 4).sub
    (((hasDerivAt_id' s).fun_pow 2).const_mul 8)).sub
    ((((hasDerivAt_id' s).fun_pow 2).const_mul 4).fun_mul (Real.hasDerivAt_cos s))).add
    (((hasDerivAt_id' s).const_mul 24).fun_mul (Real.hasDerivAt_sin s))).add
    ((Real.hasDerivAt_cos s).const_mul 24)).sub_const 24 using 1
  · funext u
    simp only [H2, Pi.add_apply, Pi.sub_apply] <;> ring
  · dsimp [H1]
    norm_num <;> ring

lemma H2_nonneg_of_nonneg (s : ℝ) (hs : 0 ≤ s) : 0 ≤ H2 s := by
  apply nonneg_from_derivative s hs (by simp [H2]) hasDerivAt_H2
  exact fun u hu _ => mul_nonneg (mul_nonneg (by norm_num) hu) (H1_nonneg u)

lemma H2_neg (s : ℝ) : H2 (-s) = H2 s := by simp only [H2, Real.sin_neg, Real.cos_neg]; ring

theorem H2_nonneg (s : ℝ) : 0 ≤ H2 s := by
  rcases le_total 0 s with hs | hs
  · exact H2_nonneg_of_nonneg s hs
  · simpa only [H2_neg] using H2_nonneg_of_nonneg (-s) (neg_nonneg.mpr hs)

lemma hasDerivAt_G (s : ℝ) : HasDerivAt G (3 * H1 s) s := by
  convert (((((hasDerivAt_id' s).fun_pow 3).sub ((hasDerivAt_id' s).const_mul 12)).sub
    (((hasDerivAt_id' s).const_mul 3).fun_mul (Real.hasDerivAt_cos s))).add
    ((Real.hasDerivAt_sin s).const_mul 15)) using 1
  · funext u
    simp only [G, Pi.add_apply, Pi.sub_apply] <;> ring
  · dsimp [H1]
    norm_num <;> ring

lemma G_nonneg (s : ℝ) (hs : 0 ≤ s) : 0 ≤ G s := by
  apply nonneg_from_derivative s hs (by simp [G]) hasDerivAt_G
  exact fun u _ _ => mul_nonneg (by norm_num) (H1_nonneg u)

lemma hasDerivAt_H3 (s : ℝ) : HasDerivAt H3 (6 * s ^ 2 * G s) s := by
  convert ((((((hasDerivAt_id' s).fun_pow 6).sub
    ((((hasDerivAt_id' s).fun_pow 2).const_mul 144).fun_mul (Real.hasDerivAt_cos s))).sub
    (((hasDerivAt_id' s).fun_pow 4).const_mul 18)).add
    ((((hasDerivAt_id' s).const_mul 288).sub (((hasDerivAt_id' s).fun_pow 3).const_mul 18)).fun_mul
      (Real.hasDerivAt_sin s))).add ((Real.hasDerivAt_cos s).const_mul 288)).sub_const 288 using 1
  · funext u
    simp only [H3, Pi.add_apply, Pi.sub_apply] <;> ring
  · dsimp [G]
    norm_num <;> ring

lemma H3_nonneg_of_nonneg (s : ℝ) (hs : 0 ≤ s) : 0 ≤ H3 s := by
  apply nonneg_from_derivative s hs (by simp [H3]) hasDerivAt_H3
  exact fun u hu _ => mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg u)) (G_nonneg u hu)

lemma H3_neg (s : ℝ) : H3 (-s) = H3 s := by simp only [H3, Real.sin_neg, Real.cos_neg]; ring

theorem H3_nonneg (s : ℝ) : 0 ≤ H3 s := by
  rcases le_total 0 s with hs | hs
  · exact H3_nonneg_of_nonneg s hs
  · simpa only [H3_neg] using H3_nonneg_of_nonneg (-s) (neg_nonneg.mpr hs)

def firstCompensated (s : ℝ) : ℂ := pureExp s - 1 - Complex.I * ((s / 4 : ℝ) : ℂ)
def secondCompensated (s : ℝ) : ℂ :=
  pureExp s - 1 - Complex.I * (s : ℂ) + ((s ^ 2 / 6 : ℝ) : ℂ)
def thirdCompensated (s : ℝ) : ℂ :=
  pureExp s - 1 - Complex.I * (s : ℂ) + ((s ^ 2 / 2 : ℝ) : ℂ) +
    Complex.I * ((s ^ 3 / 16 : ℝ) : ℂ)

lemma pureExp_re (s : ℝ) : (pureExp s).re = Real.cos s := by
  unfold pureExp
  rw [mul_comm]
  exact Complex.exp_ofReal_mul_I_re s

lemma pureExp_im (s : ℝ) : (pureExp s).im = Real.sin s := by
  unfold pureExp
  rw [mul_comm]
  exact Complex.exp_ofReal_mul_I_im s

lemma first_deficit (s : ℝ) : (3 * |s| / 4) ^ 2 - ‖firstCompensated s‖ ^ 2 = H1 s / 2 := by
  rw [← Complex.normSq_eq_norm_sq]
  simp only [firstCompensated, Complex.normSq_apply, pureExp_re, pureExp_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, one_mul, mul_one,
    zero_add, add_zero, sub_zero, H1]
  nlinarith only [Real.sin_sq_add_cos_sq s, sq_abs s]

lemma second_deficit (s : ℝ) : (s ^ 2 / 3) ^ 2 - ‖secondCompensated s‖ ^ 2 = H2 s / 12 := by
  rw [← Complex.normSq_eq_norm_sq]
  simp only [secondCompensated, Complex.normSq_apply, pureExp_re, pureExp_im,
    Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, one_mul, mul_one,
    zero_add, add_zero, sub_zero, H2]
  nlinarith only [Real.sin_sq_add_cos_sq s]

lemma third_deficit (s : ℝ) : (5 * |s| ^ 3 / 48) ^ 2 - ‖thirdCompensated s‖ ^ 2 = H3 s / 144 := by
  rw [← Complex.normSq_eq_norm_sq]
  have ha : (|s| ^ 3) ^ 2 = s ^ 6 := by
    calc
      _ = (|s| ^ 2) ^ 3 := by ring
      _ = _ := by rw [sq_abs]; ring
  simp only [thirdCompensated, Complex.normSq_apply, pureExp_re, pureExp_im,
    Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, one_mul, mul_one,
    zero_add, add_zero, sub_zero, H3]
  nlinarith only [Real.sin_sq_add_cos_sq s, ha]

/-- Critical `λ₁=1/4`, with `q₁=3/4`. -/
theorem first_compensated_bound (s : ℝ) : ‖firstCompensated s‖ ≤ 3 * |s| / 4 := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ 3 * |s| / 4)).mp
  nlinarith only [first_deficit s, H1_nonneg s]

/-- Critical `λ₂=1/3`, with `q₂/2!=1/3`. -/
theorem second_compensated_bound (s : ℝ) : ‖secondCompensated s‖ ≤ s ^ 2 / 3 := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ s ^ 2 / 3)).mp
  nlinarith only [second_deficit s, H2_nonneg s]

/-- Critical `λ₃=3/8`, with `q₃/3!=5/48`. -/
theorem third_compensated_bound (s : ℝ) : ‖thirdCompensated s‖ ≤ 5 * |s| ^ 3 / 48 := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ 5 * |s| ^ 3 / 48)).mp
  nlinarith only [third_deficit s, H3_nonneg s]

lemma pureExp_mul (t x : ℝ) : pureExp (t * x) = CharacteristicDerivative.oscillation t x := by
  unfold pureExp CharacteristicDerivative.oscillation
  congr 1
  push_cast
  ring

/-- The actual integrands whose expectations are the compensated native
second derivative, first derivative, and characteristic function. -/
def secondDerivativeIntegrand (t x : ℝ) : ℂ :=
  -((x ^ 2 : ℝ) : ℂ) * firstCompensated (t * x)
def firstDerivativeIntegrand (t x : ℝ) : ℂ :=
  Complex.I * (x : ℂ) * secondCompensated (t * x)
def functionIntegrand (t x : ℝ) : ℂ := thirdCompensated (t * x)

lemma secondDerivativeIntegrand_bound (t x : ℝ) :
    ‖secondDerivativeIntegrand t x‖ ≤ (3 * |t| / 4) * |x| ^ 3 := by
  calc
    _ = x ^ 2 * ‖firstCompensated (t * x)‖ := by
      simp only [secondDerivativeIntegrand, norm_mul, norm_neg, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (sq_nonneg x)]
    _ ≤ x ^ 2 * (3 * |t * x| / 4) :=
      mul_le_mul_of_nonneg_left (first_compensated_bound (t * x)) (sq_nonneg x)
    _ = _ := by rw [abs_mul, ← sq_abs x]; ring

lemma firstDerivativeIntegrand_bound (t x : ℝ) :
    ‖firstDerivativeIntegrand t x‖ ≤ (t ^ 2 / 3) * |x| ^ 3 := by
  calc
    _ = |x| * ‖secondCompensated (t * x)‖ := by
      simp only [firstDerivativeIntegrand, norm_mul, Complex.norm_I, one_mul,
        Complex.norm_real, Real.norm_eq_abs]
    _ ≤ |x| * ((t * x) ^ 2 / 3) :=
      mul_le_mul_of_nonneg_left (second_compensated_bound (t * x)) (abs_nonneg x)
    _ = _ := by rw [mul_pow, ← sq_abs x]; ring

lemma functionIntegrand_bound (t x : ℝ) :
    ‖functionIntegrand t x‖ ≤ (5 * |t| ^ 3 / 48) * |x| ^ 3 := by
  calc
    _ ≤ 5 * |t * x| ^ 3 / 48 := third_compensated_bound (t * x)
    _ = _ := by rw [abs_mul, mul_pow]; ring

theorem integrable_secondDerivativeIntegrand (μ : ProbabilityMeasure ℝ)
    (h : StandardizedLaw μ) (t : ℝ) :
    Integrable (secondDerivativeIntegrand t) (μ : Measure ℝ) := by
  apply (h.integrable_cube.const_mul (3 * |t| / 4)).mono'
    (by unfold secondDerivativeIntegrand firstCompensated pureExp; fun_prop)
  exact Eventually.of_forall (secondDerivativeIntegrand_bound t)

theorem integrable_firstDerivativeIntegrand (μ : ProbabilityMeasure ℝ)
    (h : StandardizedLaw μ) (t : ℝ) :
    Integrable (firstDerivativeIntegrand t) (μ : Measure ℝ) := by
  apply (h.integrable_cube.const_mul (t ^ 2 / 3)).mono'
    (by unfold firstDerivativeIntegrand secondCompensated pureExp; fun_prop)
  exact Eventually.of_forall (firstDerivativeIntegrand_bound t)

theorem integrable_functionIntegrand (μ : ProbabilityMeasure ℝ)
    (h : StandardizedLaw μ) (t : ℝ) : Integrable (functionIntegrand t) (μ : Measure ℝ) := by
  apply (h.integrable_cube.const_mul (5 * |t| ^ 3 / 48)).mono'
    (by unfold functionIntegrand thirdCompensated pureExp; fun_prop)
  exact Eventually.of_forall (functionIntegrand_bound t)

lemma integrable_complex_mean (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    Integrable (fun x : ℝ => (x : ℂ)) (μ : Measure ℝ) := by
  simpa only [Function.comp_def, Complex.ofRealCLM_apply] using
    Complex.ofRealCLM.integrable_comp h.integrable_mean

lemma integrable_complex_square (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    Integrable (fun x : ℝ => ((x ^ 2 : ℝ) : ℂ)) (μ : Measure ℝ) := by
  simpa only [Function.comp_def, Complex.ofRealCLM_apply] using
    Complex.ofRealCLM.integrable_comp h.integrable_square

lemma integrable_complex_cube (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    Integrable (fun x : ℝ => ((x ^ 3 : ℝ) : ℂ)) (μ : Measure ℝ) := by
  simpa only [Function.comp_def, Complex.ofRealCLM_apply] using
    Complex.ofRealCLM.integrable_comp (ZeroBias.integrable_signed_cube μ h)

lemma integrable_square_oscillation (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (t : ℝ) :
    Integrable (fun x : ℝ => ((x ^ 2 : ℝ) : ℂ) * CharacteristicDerivative.oscillation t x)
      (μ : Measure ℝ) := by
  apply h.integrable_square.mono' (by unfold CharacteristicDerivative.oscillation; fun_prop)
  exact Eventually.of_forall fun x => by
    simp only [norm_mul, CharacteristicDerivative.norm_oscillation, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg x), le_refl]

lemma second_derivative_integral (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (t : ℝ) :
    deriv (deriv (charFun (μ : Measure ℝ))) t =
      -(∫ x : ℝ, ((x ^ 2 : ℝ) : ℂ) * CharacteristicDerivative.oscillation t x ∂(μ : Measure ℝ)) := by
  rw [SquareBiasFourier.second_deriv_cf μ h t, charFun_apply_real, SquareBias.integral_squareLaw]
  congr 1

lemma integral_secondDerivativeIntegrand (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (t : ℝ) :
    (∫ x : ℝ, secondDerivativeIntegrand t x ∂(μ : Measure ℝ)) =
      deriv (deriv (charFun (μ : Measure ℝ))) t + 1 +
        Complex.I * ((ZeroBias.gamma μ * t / 4 : ℝ) : ℂ) := by
  have hA : Integrable (fun x : ℝ =>
      -(((x ^ 2 : ℝ) : ℂ) * CharacteristicDerivative.oscillation t x)) (μ : Measure ℝ) :=
    (integrable_square_oscillation μ h t).neg
  have hB := integrable_complex_square μ h
  have hC : Integrable (fun x : ℝ =>
      (Complex.I * ((t / 4 : ℝ) : ℂ)) * ((x ^ 3 : ℝ) : ℂ)) (μ : Measure ℝ) :=
    (integrable_complex_cube μ h).const_mul _
  have hAB : Integrable (fun x : ℝ =>
      -(((x ^ 2 : ℝ) : ℂ) * CharacteristicDerivative.oscillation t x) + ((x ^ 2 : ℝ) : ℂ))
      (μ : Measure ℝ) := hA.add hB
  have heq : (fun x : ℝ => secondDerivativeIntegrand t x) = (fun x : ℝ =>
      -(((x ^ 2 : ℝ) : ℂ) * CharacteristicDerivative.oscillation t x) + ((x ^ 2 : ℝ) : ℂ) +
        (Complex.I * ((t / 4 : ℝ) : ℂ)) * ((x ^ 3 : ℝ) : ℂ)) := by
    funext x
    unfold secondDerivativeIntegrand firstCompensated
    rw [pureExp_mul]
    push_cast
    ring
  rw [heq, integral_add hAB hC, integral_add hA hB, integral_neg, integral_const_mul,
    integral_complex_ofReal, integral_complex_ofReal, h.second_moment_one,
    second_derivative_integral μ h t]
  change _ = -(∫ x : ℝ, ((x ^ 2 : ℝ) : ℂ) * CharacteristicDerivative.oscillation t x ∂(μ : Measure ℝ)) +
    1 + Complex.I * ((ZeroBias.gamma μ * t / 4 : ℝ) : ℂ)
  change _ + (1 : ℝ) + Complex.I * ((t / 4 : ℝ) : ℂ) * (ZeroBias.gamma μ : ℂ) = _
  push_cast
  ring

lemma integral_firstDerivativeIntegrand (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (t : ℝ) :
    (∫ x : ℝ, firstDerivativeIntegrand t x ∂(μ : Measure ℝ)) =
      deriv (charFun (μ : Measure ℝ)) t + (t : ℂ) +
        Complex.I * ((ZeroBias.gamma μ * t ^ 2 / 6 : ℝ) : ℂ) := by
  have hA : Integrable (fun x : ℝ =>
      Complex.I * ((x : ℂ) * CharacteristicDerivative.oscillation t x)) (μ : Measure ℝ) :=
    (CharacteristicDerivative.integrable_weighted μ h.integrable_mean t).const_mul _
  have hB : Integrable (fun x : ℝ => (-Complex.I) * (x : ℂ)) (μ : Measure ℝ) :=
    (integrable_complex_mean μ h).const_mul _
  have hC : Integrable (fun x : ℝ => (t : ℂ) * ((x ^ 2 : ℝ) : ℂ)) (μ : Measure ℝ) :=
    (integrable_complex_square μ h).const_mul _
  have hD : Integrable (fun x : ℝ =>
      (Complex.I * ((t ^ 2 / 6 : ℝ) : ℂ)) * ((x ^ 3 : ℝ) : ℂ)) (μ : Measure ℝ) :=
    (integrable_complex_cube μ h).const_mul _
  have hAB : Integrable (fun x : ℝ => Complex.I * ((x : ℂ) * CharacteristicDerivative.oscillation t x) +
      (-Complex.I) * (x : ℂ)) (μ : Measure ℝ) := hA.add hB
  have hABC : Integrable (fun x : ℝ => Complex.I * ((x : ℂ) * CharacteristicDerivative.oscillation t x) +
      (-Complex.I) * (x : ℂ) + (t : ℂ) * ((x ^ 2 : ℝ) : ℂ)) (μ : Measure ℝ) := hAB.add hC
  have heq : (fun x : ℝ => firstDerivativeIntegrand t x) = (fun x : ℝ =>
      Complex.I * ((x : ℂ) * CharacteristicDerivative.oscillation t x) + (-Complex.I) * (x : ℂ) +
      (t : ℂ) * ((x ^ 2 : ℝ) : ℂ) +
      (Complex.I * ((t ^ 2 / 6 : ℝ) : ℂ)) * ((x ^ 3 : ℝ) : ℂ)) := by
    funext x
    unfold firstDerivativeIntegrand secondCompensated
    rw [pureExp_mul]
    push_cast
    have hi := Complex.I_sq
    linear_combination (-(t : ℂ) * (x : ℂ) ^ 2) * hi
  rw [heq, integral_add hABC hD, integral_add hAB hC, integral_add hA hB,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_complex_ofReal, integral_complex_ofReal, integral_complex_ofReal,
    h.mean_zero, h.second_moment_one, CharacteristicDerivative.deriv_charFun_eq μ h.integrable_mean t]
  change _ = Complex.I * (∫ x : ℝ, (x : ℂ) * CharacteristicDerivative.oscillation t x ∂(μ : Measure ℝ)) +
    (t : ℂ) + Complex.I * ((ZeroBias.gamma μ * t ^ 2 / 6 : ℝ) : ℂ)
  change _ + (-Complex.I) * (0 : ℝ) + (t : ℂ) * (1 : ℝ) +
    (Complex.I * ((t ^ 2 / 6 : ℝ) : ℂ)) * (ZeroBias.gamma μ : ℂ) = _
  push_cast
  ring

lemma integral_functionIntegrand (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (t : ℝ) :
    (∫ x : ℝ, functionIntegrand t x ∂(μ : Measure ℝ)) =
      charFun (μ : Measure ℝ) t - 1 + ((t ^ 2 / 2 : ℝ) : ℂ) +
        Complex.I * ((ZeroBias.gamma μ * t ^ 3 / 16 : ℝ) : ℂ) := by
  have hA := CharacteristicDerivative.integrable_oscillation μ t
  have hB : Integrable (fun _ : ℝ => (1 : ℂ)) (μ : Measure ℝ) := integrable_const _
  have hC : Integrable (fun x : ℝ => (Complex.I * (t : ℂ)) * (x : ℂ)) (μ : Measure ℝ) :=
    (integrable_complex_mean μ h).const_mul _
  have hD : Integrable (fun x : ℝ => ((t ^ 2 / 2 : ℝ) : ℂ) * ((x ^ 2 : ℝ) : ℂ))
      (μ : Measure ℝ) := (integrable_complex_square μ h).const_mul _
  have hE : Integrable (fun x : ℝ =>
      (Complex.I * ((t ^ 3 / 16 : ℝ) : ℂ)) * ((x ^ 3 : ℝ) : ℂ)) (μ : Measure ℝ) :=
    (integrable_complex_cube μ h).const_mul _
  have hAB : Integrable (fun x : ℝ => CharacteristicDerivative.oscillation t x - 1) (μ : Measure ℝ) :=
    hA.sub hB
  have hABC : Integrable (fun x : ℝ => CharacteristicDerivative.oscillation t x - 1 -
      (Complex.I * (t : ℂ)) * (x : ℂ)) (μ : Measure ℝ) := hAB.sub hC
  have hABCD : Integrable (fun x : ℝ => CharacteristicDerivative.oscillation t x - 1 -
      (Complex.I * (t : ℂ)) * (x : ℂ) + ((t ^ 2 / 2 : ℝ) : ℂ) * ((x ^ 2 : ℝ) : ℂ))
      (μ : Measure ℝ) := hABC.add hD
  have heq : (fun x : ℝ => functionIntegrand t x) = (fun x : ℝ =>
      CharacteristicDerivative.oscillation t x - 1 - (Complex.I * (t : ℂ)) * (x : ℂ) +
      ((t ^ 2 / 2 : ℝ) : ℂ) * ((x ^ 2 : ℝ) : ℂ) +
      (Complex.I * ((t ^ 3 / 16 : ℝ) : ℂ)) * ((x ^ 3 : ℝ) : ℂ)) := by
    funext x
    unfold functionIntegrand thirdCompensated
    rw [pureExp_mul]
    push_cast
    ring
  rw [heq, integral_add hABCD hE, integral_add hABC hD, integral_sub hAB hC, integral_sub hA hB,
    integral_const_mul, integral_const_mul, integral_const_mul,
    integral_complex_ofReal, integral_complex_ofReal, integral_complex_ofReal,
    h.mean_zero, h.second_moment_one, CharacteristicDerivative.integral_oscillation]
  change _ - (∫ _ : ℝ, (1 : ℂ) ∂(μ : Measure ℝ)) - Complex.I * (t : ℂ) * (0 : ℝ) +
    ((t ^ 2 / 2 : ℝ) : ℂ) * (1 : ℝ) + (Complex.I * ((t ^ 3 / 16 : ℝ) : ℂ)) *
      (ZeroBias.gamma μ : ℂ) = _
  simp only [integral_const, probReal_univ, one_smul]
  push_cast
  ring

lemma norm_integral_le_cubic_price (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (F : ℝ → ℂ) (hF : Integrable F (μ : Measure ℝ)) (C : ℝ)
    (hbound : ∀ x, ‖F x‖ ≤ C * |x| ^ 3) :
    ‖∫ x : ℝ, F x ∂(μ : Measure ℝ)‖ ≤ C * thirdAbsoluteMoment μ := by
  calc
    _ ≤ ∫ x : ℝ, ‖F x‖ ∂(μ : Measure ℝ) := norm_integral_le_integral_norm _
    _ ≤ ∫ x : ℝ, C * |x| ^ 3 ∂(μ : Measure ℝ) :=
      integral_mono_ae hF.norm (h.integrable_cube.const_mul C) (Eventually.of_forall hbound)
    _ = _ := by rw [integral_const_mul]; rfl

theorem second_derivative_compensated (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (t : ℝ) :
    ‖deriv (deriv (charFun (μ : Measure ℝ))) t + 1 +
      Complex.I * ((ZeroBias.gamma μ * t / 4 : ℝ) : ℂ)‖ ≤
        (3 * thirdAbsoluteMoment μ / 4) * |t| := by
  rw [← integral_secondDerivativeIntegrand μ h t]
  have hb := norm_integral_le_cubic_price μ h _ (integrable_secondDerivativeIntegrand μ h t)
    (3 * |t| / 4) (secondDerivativeIntegrand_bound t)
  nlinarith only [hb]

theorem first_derivative_compensated (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (t : ℝ) :
    ‖deriv (charFun (μ : Measure ℝ)) t + (t : ℂ) +
      Complex.I * ((ZeroBias.gamma μ * t ^ 2 / 6 : ℝ) : ℂ)‖ ≤
        thirdAbsoluteMoment μ * t ^ 2 / 3 := by
  rw [← integral_firstDerivativeIntegrand μ h t]
  have hb := norm_integral_le_cubic_price μ h _ (integrable_firstDerivativeIntegrand μ h t)
    (t ^ 2 / 3) (firstDerivativeIntegrand_bound t)
  nlinarith only [hb]

theorem function_compensated (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (t : ℝ) :
    ‖charFun (μ : Measure ℝ) t - 1 + ((t ^ 2 / 2 : ℝ) : ℂ) +
      Complex.I * ((ZeroBias.gamma μ * t ^ 3 / 16 : ℝ) : ℂ)‖ ≤
        (5 * thirdAbsoluteMoment μ / 48) * |t| ^ 3 := by
  rw [← integral_functionIntegrand μ h t]
  have hb := norm_integral_le_cubic_price μ h _ (integrable_functionIntegrand μ h t)
    (5 * |t| ^ 3 / 48) (functionIntegrand_bound t)
  nlinarith only [hb]

lemma remove_compensation (z : ℂ) (c B : ℝ)
    (h : ‖z + Complex.I * (c : ℂ)‖ ≤ B) : ‖z‖ ≤ B + |c| := by
  calc
    _ = ‖(z + Complex.I * (c : ℂ)) - Complex.I * (c : ℂ)‖ := by congr 1; ring
    _ ≤ ‖z + Complex.I * (c : ℂ)‖ + ‖Complex.I * (c : ℂ)‖ := norm_sub_le _ _
    _ = ‖z + Complex.I * (c : ℂ)‖ + |c| := by
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ _ := add_le_add h (le_refl |c|)

theorem second_derivative_triangle (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (t : ℝ) :
    ‖deriv (deriv (charFun (μ : Measure ℝ))) t + 1‖ ≤
      ((3 * thirdAbsoluteMoment μ + |ZeroBias.gamma μ|) / 4) * |t| := by
  have hb := remove_compensation _ _ _ (second_derivative_compensated μ h t)
  simp only [abs_div, abs_mul] at hb
  norm_num at hb
  nlinarith only [hb]

theorem first_derivative_triangle (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (t : ℝ) :
    ‖deriv (charFun (μ : Measure ℝ)) t + (t : ℂ)‖ ≤
      ((2 * thirdAbsoluteMoment μ + |ZeroBias.gamma μ|) / 6) * t ^ 2 := by
  have hb := remove_compensation _ _ _ (first_derivative_compensated μ h t)
  simp only [abs_div, abs_mul, abs_pow, sq_abs] at hb
  norm_num at hb
  nlinarith only [hb]

theorem function_triangle (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (t : ℝ) :
    ‖charFun (μ : Measure ℝ) t - 1 + ((t ^ 2 / 2 : ℝ) : ℂ)‖ ≤
      ((5 * thirdAbsoluteMoment μ + 3 * |ZeroBias.gamma μ|) / 48) * |t| ^ 3 := by
  have hb := remove_compensation _ _ _ (function_compensated μ h t)
  simp only [abs_div, abs_mul, abs_pow] at hb
  norm_num at hb
  push_cast
  nlinarith only [hb]

/-- The actual signed-third cap obtained from the sharp moment region. -/
def signedThirdPrice (μ : ProbabilityMeasure ℝ) : ℝ :=
  Real.sqrt ((thirdAbsoluteMoment μ ^ 2 - 4 + thirdAbsoluteMoment μ *
    Real.sqrt (thirdAbsoluteMoment μ ^ 2 + 8)) / 2)

lemma abs_gamma_le_price (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    |ZeroBias.gamma μ| ≤ signedThirdPrice μ := ThirdMomentRegion.abs_gamma_le_root μ h

theorem second_derivative_root_price (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (t : ℝ) :
    ‖deriv (deriv (charFun (μ : Measure ℝ))) t + 1‖ ≤
      ((3 * thirdAbsoluteMoment μ + signedThirdPrice μ) / 4) * |t| := by
  calc
    _ ≤ ((3 * thirdAbsoluteMoment μ + |ZeroBias.gamma μ|) / 4) * |t| :=
      second_derivative_triangle μ h t
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith [abs_gamma_le_price μ h]) (abs_nonneg t)

theorem first_derivative_root_price (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (t : ℝ) :
    ‖deriv (charFun (μ : Measure ℝ)) t + (t : ℂ)‖ ≤
      ((2 * thirdAbsoluteMoment μ + signedThirdPrice μ) / 6) * t ^ 2 := by
  calc
    _ ≤ ((2 * thirdAbsoluteMoment μ + |ZeroBias.gamma μ|) / 6) * t ^ 2 :=
      first_derivative_triangle μ h t
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith [abs_gamma_le_price μ h]) (sq_nonneg t)

theorem function_root_price (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (t : ℝ) :
    ‖charFun (μ : Measure ℝ) t - 1 + ((t ^ 2 / 2 : ℝ) : ℂ)‖ ≤
      ((5 * thirdAbsoluteMoment μ + 3 * signedThirdPrice μ) / 48) * |t| ^ 3 := by
  calc
    _ ≤ ((5 * thirdAbsoluteMoment μ + 3 * |ZeroBias.gamma μ|) / 48) * |t| ^ 3 :=
      function_triangle μ h t
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith [abs_gamma_le_price μ h])
      (pow_nonneg (abs_nonneg t) 3)

end BerryEsseen.CriticalTaylorBounds

#print axioms BerryEsseen.CriticalTaylorBounds.H1_nonneg
#print axioms BerryEsseen.CriticalTaylorBounds.first_compensated_bound
#print axioms BerryEsseen.CriticalTaylorBounds.second_compensated_bound
#print axioms BerryEsseen.CriticalTaylorBounds.third_compensated_bound
#print axioms BerryEsseen.CriticalTaylorBounds.integrable_secondDerivativeIntegrand
#print axioms BerryEsseen.CriticalTaylorBounds.integrable_firstDerivativeIntegrand
#print axioms BerryEsseen.CriticalTaylorBounds.integrable_functionIntegrand
#print axioms BerryEsseen.CriticalTaylorBounds.second_derivative_compensated
#print axioms BerryEsseen.CriticalTaylorBounds.first_derivative_compensated
#print axioms BerryEsseen.CriticalTaylorBounds.function_compensated
#print axioms BerryEsseen.CriticalTaylorBounds.second_derivative_triangle
#print axioms BerryEsseen.CriticalTaylorBounds.first_derivative_triangle
#print axioms BerryEsseen.CriticalTaylorBounds.function_triangle
#print axioms BerryEsseen.CriticalTaylorBounds.second_derivative_root_price
#print axioms BerryEsseen.CriticalTaylorBounds.first_derivative_root_price
#print axioms BerryEsseen.CriticalTaylorBounds.function_root_price
