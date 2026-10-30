module

public import BerryEsseen.Target
public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

@[expose] public section

/-! 2026-10-28: actual-law low-frequency characteristic expansion and damping.
Sixth/fourth moment finiteness is explicit; bounded support is only a sufficient
condition for those moments, never an implicit restriction on StandardizedLaw. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators Interval MeasureTheory

namespace BerryEsseen.CharacteristicExpansion

/-- Pure imaginary exponential along a real parameter. -/
def pureExp (s : ℝ) : ℂ := Complex.exp (Complex.I * (s : ℂ))

def expPolynomial (n : ℕ) (s : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), (Complex.I * (s : ℂ)) ^ k / (k.factorial : ℂ)

lemma contDiff_pureExp (n : ℕ) : ContDiff ℝ n pureExp := by
  have hOf : ContDiff ℝ n ((↑) : ℝ → ℂ) := Complex.ofRealCLM.contDiff
  exact (contDiff_const.mul hOf).cexp

lemma hasDerivAt_pureExp (s : ℝ) : HasDerivAt pureExp (Complex.I * pureExp s) s := by
  have h : HasDerivAt (fun z : ℂ => Complex.exp (Complex.I * z))
      (Complex.I * Complex.exp (Complex.I * (s : ℂ))) (s : ℂ) := by
    convert ((hasDerivAt_id' (s : ℂ)).const_mul Complex.I).cexp using 1
    ring
  exact h.comp_ofReal

lemma iteratedDeriv_pureExp (n : ℕ) :
    iteratedDeriv n pureExp = (fun s : ℝ => Complex.I ^ n * pureExp s) := by
  induction n with
  | zero => simp [iteratedDeriv_zero]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    ext s
    convert ((hasDerivAt_pureExp s).const_mul (Complex.I ^ n)).deriv using 1
    rw [pow_succ']
    ring

lemma norm_pureExp (s : ℝ) : ‖pureExp s‖ = 1 := by
  simpa only [pureExp, mul_comm] using Complex.norm_exp_ofReal_mul_I s

lemma norm_iteratedDeriv_pureExp (n : ℕ) (s : ℝ) : ‖iteratedDeriv n pureExp s‖ = 1 := by
  rw [iteratedDeriv_pureExp]
  simp only [norm_mul, norm_pow, Complex.norm_I, one_pow, norm_pureExp, one_mul]

lemma expPolynomial_zero (n : ℕ) : expPolynomial n 0 = 1 := by
  classical
  unfold expPolynomial
  rw [Finset.sum_eq_single 0]
  · simp
  · intro k hk hk0
    simp [hk0]
  · simp

lemma taylorEval_pureExp (n : ℕ) (s : ℝ) (hs : s ≠ 0) :
    taylorWithinEval pureExp n (uIcc 0 s) 0 s = expPolynomial n s := by
  classical
  have hu : UniqueDiffOn ℝ (uIcc 0 s) := uniqueDiffOn_uIcc (Ne.symm hs)
  rw [taylor_within_apply, expPolynomial]
  apply Finset.sum_congr rfl
  intro k hk
  rw [iteratedDerivWithin_eq_iteratedDeriv hu (contDiff_pureExp k).contDiffAt left_mem_uIcc]
  simp only [iteratedDeriv_pureExp, pureExp, Complex.ofReal_zero, mul_zero, Complex.exp_zero,
    mul_one, sub_zero, Complex.real_smul]
  push_cast
  rw [mul_pow]
  ring

/-- Global pure-imaginary Taylor remainder. This does not assume the argument is small. -/
theorem pureExp_taylor_bound (n : ℕ) (s : ℝ) :
    ‖pureExp s - expPolynomial n s‖ ≤ |s| ^ (n + 1) / ((n + 1).factorial : ℝ) := by
  by_cases hs : s = 0
  · subst s
    simp [pureExp, expPolynomial_zero]
  have hu : UniqueDiffOn ℝ (uIcc 0 s) := uniqueDiffOn_uIcc (Ne.symm hs)
  have hfac : (0 : ℝ) ≤ (n.factorial : ℝ) := Nat.cast_nonneg _
  have ht := taylor_integral_remainder (f := pureExp) (n := n) (x₀ := (0 : ℝ)) (x := s)
    (contDiff_pureExp (n + 1)).contDiffOn
  rw [taylorEval_pureExp n s hs] at ht
  rw [ht]
  calc
    _ ≤ ∫ x in uIoc 0 s, ‖((s - x) ^ n / (n.factorial : ℝ)) •
        iteratedDerivWithin (n + 1) pureExp (uIcc 0 s) x‖ :=
      intervalIntegral.norm_integral_le_integral_norm_uIoc
    _ = ∫ x in uIoc 0 s, (1 / (n.factorial : ℝ)) * |x - s| ^ n := by
      apply setIntegral_congr_fun (show MeasurableSet (uIoc 0 s) from measurableSet_Ioc)
      intro x hx
      dsimp only
      rw [iteratedDerivWithin_eq_iteratedDeriv hu (contDiff_pureExp (n + 1)).contDiffAt ⟨hx.1.le, hx.2⟩,
        norm_smul, Real.norm_eq_abs, norm_iteratedDeriv_pureExp, mul_one, abs_div, abs_pow,
        abs_of_nonneg hfac, abs_sub_comm]
      ring
    _ = _ := by
      rw [integral_const_mul, uIoc_comm 0 s, integral_pow_abs_sub_uIoc]
      simp only [zero_sub, abs_neg, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
        div_eq_mul_inv, mul_inv_rev]
      ring

/-- Actual signed moments; the fifth moment below is deliberately signed. -/
def moment (μ : ProbabilityMeasure ℝ) (k : ℕ) : ℝ := ∫ x : ℝ, x ^ k ∂(μ : Measure ℝ)
def sixthMoment (μ : ProbabilityMeasure ℝ) : ℝ := ∫ x : ℝ, |x| ^ 6 ∂(μ : Measure ℝ)
def gamma (μ : ProbabilityMeasure ℝ) : ℝ := moment μ 3

lemma integrable_moment_of_sixth (μ : ProbabilityMeasure ℝ)
    (h6 : Integrable (fun x : ℝ => |x| ^ 6) (μ : Measure ℝ)) (k : ℕ) (hk : k ≤ 6) :
    Integrable (fun x : ℝ => x ^ k) (μ : Measure ℝ) := by
  have hid : AEStronglyMeasurable (fun x : ℝ => x) (μ : Measure ℝ) := measurable_id.aestronglyMeasurable
  have hn6 : Integrable (fun x : ℝ => ‖x‖ ^ 6) (μ : Measure ℝ) := by simpa only [Real.norm_eq_abs] using h6
  have hnk := integrable_norm_pow_of_le hid hk hn6
  have hm : AEStronglyMeasurable (fun x : ℝ => x ^ k) (μ : Measure ℝ) := (continuous_id.pow k).aestronglyMeasurable
  apply (integrable_norm_iff hm).mp
  simpa only [Real.norm_eq_abs, abs_pow] using hnk

/-- Real bounded support supplies, rather than assumes, finite sixth moment and its actual cap. -/
theorem bounded_support_sixth (μ : ProbabilityMeasure ℝ) (R : ℝ) (_hR : 0 ≤ R)
    (hbound : ∀ᵐ x ∂(μ : Measure ℝ), |x| ≤ R) :
    Integrable (fun x : ℝ => |x| ^ 6) (μ : Measure ℝ) ∧ sixthMoment μ ≤ R ^ 6 := by
  have hm : AEStronglyMeasurable (fun x : ℝ => |x| ^ 6) (μ : Measure ℝ) :=
    (continuous_abs.pow 6).aestronglyMeasurable
  have hb : (fun x : ℝ => |x| ^ 6) ≤ᵐ[(μ : Measure ℝ)] (fun _ => R ^ 6) :=
    hbound.mono fun x hx => pow_le_pow_left₀ (abs_nonneg x) hx 6
  have hi : Integrable (fun x : ℝ => |x| ^ 6) (μ : Measure ℝ) := by
    apply (integrable_const (R ^ 6)).mono' hm
    filter_upwards [hb] with x hx
    simpa only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg x) 6)] using hx
  refine ⟨hi, ?_⟩
  have he := integral_mono_ae hi (integrable_const (R ^ 6)) hb
  simpa only [sixthMoment, integral_const, probReal_univ, one_smul] using he

end BerryEsseen.CharacteristicExpansion

#print axioms BerryEsseen.CharacteristicExpansion.pureExp_taylor_bound
#print axioms BerryEsseen.CharacteristicExpansion.bounded_support_sixth

namespace BerryEsseen.CharacteristicExpansion

lemma moment_zero (μ : ProbabilityMeasure ℝ) : moment μ 0 = 1 := by simp [moment]
lemma moment_one (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) : moment μ 1 = 0 := by
  simpa only [moment, pow_one] using h.mean_zero
lemma moment_two (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) : moment μ 2 = 1 := h.second_moment_one
lemma moment_four_nonneg (μ : ProbabilityMeasure ℝ) : 0 ≤ moment μ 4 := integral_nonneg fun x => by positivity
lemma sixthMoment_nonneg (μ : ProbabilityMeasure ℝ) : 0 ≤ sixthMoment μ := integral_nonneg fun x => pow_nonneg (abs_nonneg x) 6

lemma pure_monomial_factor (t x : ℝ) (k : ℕ) :
    (Complex.I * ((t * x : ℝ) : ℂ)) ^ k / (k.factorial : ℂ) =
      ((Complex.I * (t : ℂ)) ^ k / (k.factorial : ℂ)) * ((x ^ k : ℝ) : ℂ) := by
  push_cast
  rw [← mul_assoc Complex.I (t : ℂ) (x : ℂ), mul_pow]
  ring

lemma integrable_complex_monomial (μ : ProbabilityMeasure ℝ)
    (h6 : Integrable (fun x : ℝ => |x| ^ 6) (μ : Measure ℝ)) (t : ℝ) (k : ℕ) (hk : k ≤ 6) :
    Integrable (fun x : ℝ => (Complex.I * ((t * x : ℝ) : ℂ)) ^ k / (k.factorial : ℂ)) (μ : Measure ℝ) := by
  have hx : Integrable (fun x : ℝ => ((x ^ k : ℝ) : ℂ)) (μ : Measure ℝ) := by
    simpa only [Function.comp_def, Complex.ofRealCLM_apply] using
      Complex.ofRealCLM.integrable_comp (integrable_moment_of_sixth μ h6 k hk)
  have heq : (fun x : ℝ => (Complex.I * ((t * x : ℝ) : ℂ)) ^ k / (k.factorial : ℂ)) =
      (fun x : ℝ => ((Complex.I * (t : ℂ)) ^ k / (k.factorial : ℂ)) * ((x ^ k : ℝ) : ℂ)) :=
    funext fun x => pure_monomial_factor t x k
  rw [heq]
  exact hx.const_mul _

lemma integral_complex_monomial (μ : ProbabilityMeasure ℝ) (t : ℝ) (k : ℕ) :
    (∫ x : ℝ, (Complex.I * ((t * x : ℝ) : ℂ)) ^ k / (k.factorial : ℂ) ∂(μ : Measure ℝ)) =
      ((Complex.I * (t : ℂ)) ^ k / (k.factorial : ℂ)) * (moment μ k : ℂ) := by
  have heq : (fun x : ℝ => (Complex.I * ((t * x : ℝ) : ℂ)) ^ k / (k.factorial : ℂ)) =
      (fun x : ℝ => ((Complex.I * (t : ℂ)) ^ k / (k.factorial : ℂ)) * ((x ^ k : ℝ) : ℂ)) :=
    funext fun x => pure_monomial_factor t x k
  rw [heq, integral_const_mul]
  have hreal : (∫ x : ℝ, ((x ^ k : ℝ) : ℂ) ∂(μ : Measure ℝ)) =
      (((∫ x : ℝ, x ^ k ∂(μ : Measure ℝ)) : ℝ) : ℂ) := integral_complex_ofReal
  rw [hreal]
  rfl

def characteristicPolynomial (μ : ProbabilityMeasure ℝ) (t : ℝ) : ℂ :=
  ∑ k ∈ Finset.range 6, ((Complex.I * (t : ℂ)) ^ k / (k.factorial : ℂ)) * (moment μ k : ℂ)

lemma integrable_expPolynomial_five (μ : ProbabilityMeasure ℝ)
    (h6 : Integrable (fun x : ℝ => |x| ^ 6) (μ : Measure ℝ)) (t : ℝ) :
    Integrable (fun x : ℝ => expPolynomial 5 (t * x)) (μ : Measure ℝ) := by
  simp only [expPolynomial]
  apply integrable_finsetSum
  intro k hk
  exact integrable_complex_monomial μ h6 t k (by have := Finset.mem_range.mp hk; omega)

lemma integral_expPolynomial_five (μ : ProbabilityMeasure ℝ)
    (h6 : Integrable (fun x : ℝ => |x| ^ 6) (μ : Measure ℝ)) (t : ℝ) :
    (∫ x : ℝ, expPolynomial 5 (t * x) ∂(μ : Measure ℝ)) = characteristicPolynomial μ t := by
  simp only [expPolynomial, characteristicPolynomial]
  rw [integral_finsetSum (Finset.range 6) (fun k hk =>
    integrable_complex_monomial μ h6 t k (by have := Finset.mem_range.mp hk; omega))]
  apply Finset.sum_congr rfl
  intro k hk
  exact integral_complex_monomial μ t k

lemma charFun_eq_integral_pureExp (μ : ProbabilityMeasure ℝ) (t : ℝ) :
    charFun (μ : Measure ℝ) t = ∫ x : ℝ, pureExp (t * x) ∂(μ : Measure ℝ) := by
  rw [charFun_apply_real]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    dsimp only
    unfold pureExp
    congr 1
    push_cast
    ring

lemma integrable_pureExp_product (μ : ProbabilityMeasure ℝ) (t : ℝ) :
    Integrable (fun x : ℝ => pureExp (t * x)) (μ : Measure ℝ) := by
  have hc : Continuous (fun x : ℝ => pureExp (t * x)) := by unfold pureExp; fun_prop
  apply (integrable_const (1 : ℝ)).mono' hc.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x => (norm_pureExp (t * x)).le

/-- The actual CF has its sixth-moment Taylor price at every real frequency, without a pointwise support bound. -/
theorem characteristic_taylor_six (μ : ProbabilityMeasure ℝ)
    (h6 : Integrable (fun x : ℝ => |x| ^ 6) (μ : Measure ℝ)) (t : ℝ) :
    ‖charFun (μ : Measure ℝ) t - characteristicPolynomial μ t‖ ≤ sixthMoment μ * t ^ 6 / 720 := by
  have hE := integrable_pureExp_product μ t
  have hP := integrable_expPolynomial_five μ h6 t
  have hR : Integrable (fun x : ℝ => pureExp (t * x) - expPolynomial 5 (t * x)) (μ : Measure ℝ) := hE.sub hP
  have hInt : charFun (μ : Measure ℝ) t - characteristicPolynomial μ t =
      ∫ x : ℝ, pureExp (t * x) - expPolynomial 5 (t * x) ∂(μ : Measure ℝ) := by
    rw [charFun_eq_integral_pureExp, ← integral_expPolynomial_five μ h6 t]
    exact (integral_sub hE hP).symm
  have hpoint : ∀ x : ℝ, ‖pureExp (t * x) - expPolynomial 5 (t * x)‖ ≤ (t ^ 6 / 720) * |x| ^ 6 := by
    intro x
    calc
      _ ≤ |t * x| ^ 6 / 720 := by
        simpa only [show ((5 + 1).factorial : ℝ) = 720 by norm_num] using pureExp_taylor_bound 5 (t * x)
      _ = _ := by
        rw [abs_mul, mul_pow, ← abs_pow, abs_of_nonneg (by positivity : (0 : ℝ) ≤ t ^ 6)]
        ring
  calc
    _ = ‖∫ x : ℝ, pureExp (t * x) - expPolynomial 5 (t * x) ∂(μ : Measure ℝ)‖ := by rw [hInt]
    _ ≤ ∫ x : ℝ, ‖pureExp (t * x) - expPolynomial 5 (t * x)‖ ∂(μ : Measure ℝ) := norm_integral_le_integral_norm _
    _ ≤ ∫ x : ℝ, (t ^ 6 / 720) * |x| ^ 6 ∂(μ : Measure ℝ) := by
      apply integral_mono hR.norm (h6.const_mul _)
      intro x
      exact hpoint x
    _ = _ := by
      rw [integral_const_mul]
      change (t ^ 6 / 720) * sixthMoment μ = sixthMoment μ * t ^ 6 / 720
      ring

lemma pureExp_real (x : ℝ) : (pureExp x).re = Real.cos x := by
  simpa only [pureExp, mul_comm] using Complex.exp_ofReal_mul_I_re x

lemma expPolynomial_three_real (x : ℝ) : (expPolynomial 3 x).re = 1 - x ^ 2 / 2 := by
  norm_num [expPolynomial, Finset.sum_range_succ, pow_succ, Complex.mul_re, Complex.mul_im,
    Complex.div_re, Complex.div_im, Complex.normSq_apply]; ring

/-- The global quartic cosine majorant, derived from the same actual exponential Taylor estimate. -/
theorem cos_le_quartic (x : ℝ) : Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
  have hRe := Complex.re_le_norm (pureExp x - expPolynomial 3 x)
  rw [Complex.sub_re, pureExp_real, expPolynomial_three_real] at hRe
  have hT := pureExp_taylor_bound 3 x
  have hx4 : |x| ^ 4 = x ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity : (0 : ℝ) ≤ x ^ 4)]
  rw [show (3 + 1 : ℕ) = 4 by rfl, hx4, show (4 : ℕ).factorial = 24 by norm_num] at hT
  norm_num at hT
  linarith

end BerryEsseen.CharacteristicExpansion

#print axioms BerryEsseen.CharacteristicExpansion.characteristic_taylor_six
#print axioms BerryEsseen.CharacteristicExpansion.cos_le_quartic

namespace BerryEsseen.CharacteristicExpansion

def quarticCoeff (μ : ProbabilityMeasure ℝ) : ℝ := (3 - moment μ 4) / 24
def fifthCoeff (μ : ProbabilityMeasure ℝ) : ℝ := (10 * gamma μ - moment μ 5) / 120

def exponent (μ : ProbabilityMeasure ℝ) (t : ℝ) : ℂ :=
  -((t ^ 2 / 2 : ℝ) : ℂ) - Complex.I * ((gamma μ * t ^ 3 / 6 : ℝ) : ℂ)
def comparator (μ : ProbabilityMeasure ℝ) (t : ℝ) : ℂ := Complex.exp (exponent μ t)
def sixthPrice (g M6bar : ℝ) : ℝ := M6bar / 720 + g ^ 2 / 72 + (1 / 2 + g ^ 2 / 144) ^ 3 / 5

lemma exponent_real (μ : ProbabilityMeasure ℝ) (t : ℝ) : (exponent μ t).re = -(t ^ 2) / 2 := by
  simp only [exponent, Complex.sub_re, Complex.neg_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_self, sub_zero]
  ring
lemma exponent_imag (μ : ProbabilityMeasure ℝ) (t : ℝ) : (exponent μ t).im = -(gamma μ * t ^ 3) / 6 := by
  simp only [exponent, Complex.sub_im, Complex.neg_im, Complex.ofReal_im, Complex.mul_im,
    Complex.ofReal_re, Complex.I_re, Complex.I_im, mul_zero, one_mul, neg_zero, zero_add, zero_sub]
  ring
lemma exponent_norm_sq (μ : ProbabilityMeasure ℝ) (t : ℝ) :
    ‖exponent μ t‖ ^ 2 = t ^ 4 / 4 + gamma μ ^ 2 * t ^ 6 / 36 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, exponent_real, exponent_imag]
  ring

lemma gamma_sq_le (μ : ProbabilityMeasure ℝ) (g : ℝ) (hg : |gamma μ| ≤ g) : gamma μ ^ 2 ≤ g ^ 2 := by
  have hg0 : 0 ≤ g := (abs_nonneg _).trans hg
  simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (gamma μ)) hg0).mpr hg

lemma exponent_norm_le (μ : ProbabilityMeasure ℝ) (t g : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2)
    (hg : |gamma μ| ≤ g) : ‖exponent μ t‖ ≤ t ^ 2 * (1 / 2 + g ^ 2 / 144) := by
  have ht2 : t ^ 2 ≤ (1 : ℝ) / 4 := by
    nlinarith [mul_nonneg ht0 (show 0 ≤ 1 / 2 - t by linarith)]
  have hgt : gamma μ ^ 2 * t ^ 2 ≤ g ^ 2 / 4 := by
    calc
      gamma μ ^ 2 * t ^ 2 ≤ g ^ 2 * t ^ 2 := mul_le_mul_of_nonneg_right (gamma_sq_le μ g hg) (sq_nonneg t)
      _ ≤ g ^ 2 * (1 / 4 : ℝ) := mul_le_mul_of_nonneg_left ht2 (sq_nonneg g)
      _ = _ := by ring
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (sq_nonneg t) (by positivity))).mp
  calc
    ‖exponent μ t‖ ^ 2 = t ^ 4 / 4 + (t ^ 4 / 36) * (gamma μ ^ 2 * t ^ 2) := by rw [exponent_norm_sq]; ring
    _ ≤ t ^ 4 / 4 + (t ^ 4 / 36) * (g ^ 2 / 4) := by
      exact add_le_add (le_refl (t ^ 4 / 4))
        (mul_le_mul_of_nonneg_left hgt (show (0 : ℝ) ≤ t ^ 4 / 36 by positivity))
    _ ≤ (t ^ 2 * (1 / 2 + g ^ 2 / 144)) ^ 2 := by
      nlinarith only [mul_nonneg (pow_nonneg ht0 4) (sq_nonneg (g ^ 2 / 144))]

/-- The small complex argument condition is proved from the paper's actual gamma and g caps. -/
theorem exponent_norm_lt_sixth (μ : ProbabilityMeasure ℝ) (t g : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2)
    (hg : |gamma μ| ≤ g) (hgcap : g ≤ 37 / 20) : ‖exponent μ t‖ < 1 / 6 := by
  have hg0 : 0 ≤ g := (abs_nonneg _).trans hg
  have hg2 : g ^ 2 ≤ ((37 : ℝ) / 20) ^ 2 := (sq_le_sq₀ hg0 (by norm_num)).mpr hgcap
  have ht2 : t ^ 2 ≤ (1 : ℝ) / 4 := by nlinarith [mul_nonneg ht0 (show 0 ≤ 1 / 2 - t by linarith)]
  calc
    ‖exponent μ t‖ ≤ t ^ 2 * (1 / 2 + g ^ 2 / 144) := exponent_norm_le μ t g ht0 ht1 hg
    _ ≤ (1 / 4 : ℝ) * (1 / 2 + g ^ 2 / 144) := mul_le_mul_of_nonneg_right ht2 (by positivity)
    _ ≤ (1 / 4 : ℝ) * (1 / 2 + ((37 : ℝ) / 20) ^ 2 / 144) := by nlinarith [hg2]
    _ < 1 / 6 := by norm_num

lemma exp_sum_four (u : ℂ) : (∑ k ∈ Finset.range 4, u ^ k / (k.factorial : ℂ)) =
    1 + u + u ^ 2 / 2 + u ^ 3 / 6 := by norm_num [Finset.sum_range_succ]

/-- The omitted exponential terms have the paper's 1/5 cubic price on the proved small ball. -/
theorem exp_quadratic_small (u : ℂ) (hu : ‖u‖ ≤ 1 / 6) :
    ‖Complex.exp u - (1 + u + u ^ 2 / 2)‖ ≤ ‖u‖ ^ 3 / 5 := by
  have h4 := Complex.exp_bound (show ‖u‖ ≤ 1 by linarith) (n := 4) (by decide)
  rw [exp_sum_four] at h4
  have hfour : ‖Complex.exp u - (1 + u + u ^ 2 / 2 + u ^ 3 / 6)‖ ≤ ‖u‖ ^ 4 * (5 / 96 : ℝ) := by
    convert h4 using 1
    norm_num
  have hterm : ‖u ^ 3 / (6 : ℂ)‖ = ‖u‖ ^ 3 / 6 := by rw [norm_div, norm_pow]; norm_num
  have hpow3 : 0 ≤ ‖u‖ ^ 3 := pow_nonneg (norm_nonneg _) 3
  have hpow4 : ‖u‖ ^ 4 ≤ ‖u‖ ^ 3 / 6 := by
    have h := mul_le_mul_of_nonneg_right hu hpow3
    nlinarith
  have heq : Complex.exp u - (1 + u + u ^ 2 / 2) =
      (Complex.exp u - (1 + u + u ^ 2 / 2 + u ^ 3 / 6)) + u ^ 3 / 6 := by ring
  rw [heq]
  calc
    _ ≤ ‖Complex.exp u - (1 + u + u ^ 2 / 2 + u ^ 3 / 6)‖ + ‖u ^ 3 / (6 : ℂ)‖ := norm_add_le _ _
    _ ≤ ‖u‖ ^ 4 * (5 / 96 : ℝ) + ‖u‖ ^ 3 / 6 := by
      rw [hterm]
      exact add_le_add hfour (le_refl (‖u‖ ^ 3 / 6))
    _ ≤ ‖u‖ ^ 3 / 5 := by nlinarith [hpow4, hpow3]

lemma principal_cancellation (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (t : ℝ) :
    characteristicPolynomial μ t - (1 + exponent μ t + exponent μ t ^ 2 / 2) +
      ((quarticCoeff μ * t ^ 4 : ℝ) : ℂ) + Complex.I * ((fifthCoeff μ * t ^ 5 : ℝ) : ℂ) =
      ((gamma μ ^ 2 * t ^ 6 / 72 : ℝ) : ℂ) := by
  apply Complex.ext
  all_goals norm_num [characteristicPolynomial, Finset.sum_range_succ, quarticCoeff, fifthCoeff,
    exponent, gamma, moment_zero, moment_one μ h, moment_two μ h, pow_succ,
    Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im, Complex.normSq_apply]
  all_goals ring

/-- The first ut:low pointwise estimate, for the original actual CF and actual moment coefficients. -/
theorem low_frequency_expansion (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (h6 : Integrable (fun x : ℝ => |x| ^ 6) (μ : Measure ℝ))
    (t g M6bar : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2)
    (hg : |gamma μ| ≤ g) (hgcap : g ≤ 37 / 20) (hcap : sixthMoment μ ≤ M6bar) :
    ‖charFun (μ : Measure ℝ) t - comparator μ t + ((quarticCoeff μ * t ^ 4 : ℝ) : ℂ) +
      Complex.I * ((fifthCoeff μ * t ^ 5 : ℝ) : ℂ)‖ ≤ sixthPrice g M6bar * t ^ 6 := by
  let Q : ℂ := 1 + exponent μ t + exponent μ t ^ 2 / 2
  have hc := principal_cancellation μ h t
  have heq : charFun (μ : Measure ℝ) t - comparator μ t + ((quarticCoeff μ * t ^ 4 : ℝ) : ℂ) +
      Complex.I * ((fifthCoeff μ * t ^ 5 : ℝ) : ℂ) =
      (charFun (μ : Measure ℝ) t - characteristicPolynomial μ t) - (comparator μ t - Q) +
        ((gamma μ ^ 2 * t ^ 6 / 72 : ℝ) : ℂ) := by
    calc
      _ = (charFun (μ : Measure ℝ) t - characteristicPolynomial μ t) - (comparator μ t - Q) +
          (characteristicPolynomial μ t - Q + ((quarticCoeff μ * t ^ 4 : ℝ) : ℂ) +
            Complex.I * ((fifthCoeff μ * t ^ 5 : ℝ) : ℂ)) := by ring
      _ = _ := by rw [hc]
  have hCF : ‖charFun (μ : Measure ℝ) t - characteristicPolynomial μ t‖ ≤ M6bar * t ^ 6 / 720 := by
    calc
      _ ≤ sixthMoment μ * t ^ 6 / 720 := characteristic_taylor_six μ h6 t
      _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcap (pow_nonneg ht0 6)) (by norm_num)
  have hH : ‖comparator μ t - Q‖ ≤ (1 / 2 + g ^ 2 / 144) ^ 3 * t ^ 6 / 5 := by
    calc
      _ ≤ ‖exponent μ t‖ ^ 3 / 5 := exp_quadratic_small _ (exponent_norm_lt_sixth μ t g ht0 ht1 hg hgcap).le
      _ ≤ (t ^ 2 * (1 / 2 + g ^ 2 / 144)) ^ 3 / 5 :=
        div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (exponent_norm_le μ t g ht0 ht1 hg) 3) (by norm_num)
      _ = _ := by ring
  have hG : ‖((gamma μ ^ 2 * t ^ 6 / 72 : ℝ) : ℂ)‖ ≤ g ^ 2 * t ^ 6 / 72 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ gamma μ ^ 2 * t ^ 6 / 72)]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (gamma_sq_le μ g hg) (pow_nonneg ht0 6)) (by norm_num)
  rw [heq]
  calc
    _ ≤ ‖(charFun (μ : Measure ℝ) t - characteristicPolynomial μ t) - (comparator μ t - Q)‖ +
        ‖((gamma μ ^ 2 * t ^ 6 / 72 : ℝ) : ℂ)‖ := norm_add_le _ _
    _ ≤ (‖charFun (μ : Measure ℝ) t - characteristicPolynomial μ t‖ + ‖comparator μ t - Q‖) +
        ‖((gamma μ ^ 2 * t ^ 6 / 72 : ℝ) : ℂ)‖ := add_le_add (norm_sub_le _ _) (le_refl _)
    _ ≤ (M6bar * t ^ 6 / 720 + (1 / 2 + g ^ 2 / 144) ^ 3 * t ^ 6 / 5) + g ^ 2 * t ^ 6 / 72 :=
      add_le_add (add_le_add hCF hH) hG
    _ = _ := by unfold sixthPrice; ring

end BerryEsseen.CharacteristicExpansion

#print axioms BerryEsseen.CharacteristicExpansion.exponent_norm_lt_sixth
#print axioms BerryEsseen.CharacteristicExpansion.exp_quadratic_small
#print axioms BerryEsseen.CharacteristicExpansion.low_frequency_expansion

namespace BerryEsseen.CharacteristicExpansion

lemma integrable_moment_of_fourth (μ : ProbabilityMeasure ℝ)
    (h4 : Integrable (fun x : ℝ => x ^ 4) (μ : Measure ℝ)) (k : ℕ) (hk : k ≤ 4) :
    Integrable (fun x : ℝ => x ^ k) (μ : Measure ℝ) := by
  have hid : AEStronglyMeasurable (fun x : ℝ => x) (μ : Measure ℝ) := measurable_id.aestronglyMeasurable
  have hn4 : Integrable (fun x : ℝ => ‖x‖ ^ 4) (μ : Measure ℝ) := by
    convert h4 using 1
    ext x
    rw [Real.norm_eq_abs, ← abs_pow, abs_of_nonneg (by positivity : (0 : ℝ) ≤ x ^ 4)]
  have hnk := integrable_norm_pow_of_le hid hk hn4
  have hm : AEStronglyMeasurable (fun x : ℝ => x ^ k) (μ : Measure ℝ) := (continuous_id.pow k).aestronglyMeasurable
  apply (integrable_norm_iff hm).mp
  simpa only [Real.norm_eq_abs, abs_pow] using hnk

lemma integrable_product_monomial (μ : ProbabilityMeasure ℝ)
    (h4 : Integrable (fun x : ℝ => x ^ 4) (μ : Measure ℝ)) (i j : ℕ) (hi : i ≤ 4) (hj : j ≤ 4) :
    Integrable (fun p : ℝ × ℝ => p.1 ^ i * p.2 ^ j) ((μ : Measure ℝ).prod (μ : Measure ℝ)) :=
  (integrable_moment_of_fourth μ h4 i hi).mul_prod (integrable_moment_of_fourth μ h4 j hj)

lemma integral_product_monomial (μ : ProbabilityMeasure ℝ) (i j : ℕ) :
    (∫ p : ℝ × ℝ, p.1 ^ i * p.2 ^ j ∂((μ : Measure ℝ).prod (μ : Measure ℝ))) = moment μ i * moment μ j :=
  integral_prod_mul _ _

lemma product_difference_second (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (h4 : Integrable (fun x : ℝ => x ^ 4) (μ : Measure ℝ)) :
    Integrable (fun p : ℝ × ℝ => (p.1 - p.2) ^ 2) ((μ : Measure ℝ).prod (μ : Measure ℝ)) ∧
      (∫ p : ℝ × ℝ, (p.1 - p.2) ^ 2 ∂((μ : Measure ℝ).prod (μ : Measure ℝ))) = 2 := by
  have hA := integrable_product_monomial μ h4 2 0 (by decide) (by decide)
  have hB := integrable_product_monomial μ h4 1 1 (by decide) (by decide)
  have hC := integrable_product_monomial μ h4 0 2 (by decide) (by decide)
  have hAB : Integrable (fun p : ℝ × ℝ => p.1 ^ 2 * p.2 ^ 0 - 2 * (p.1 ^ 1 * p.2 ^ 1))
      ((μ : Measure ℝ).prod (μ : Measure ℝ)) := hA.sub (hB.const_mul 2)
  have hP : Integrable (fun p : ℝ × ℝ => p.1 ^ 2 * p.2 ^ 0 - 2 * (p.1 ^ 1 * p.2 ^ 1) + p.1 ^ 0 * p.2 ^ 2)
      ((μ : Measure ℝ).prod (μ : Measure ℝ)) := hAB.add hC
  have heq : (fun p : ℝ × ℝ => (p.1 - p.2) ^ 2) =
      (fun p : ℝ × ℝ => p.1 ^ 2 * p.2 ^ 0 - 2 * (p.1 ^ 1 * p.2 ^ 1) + p.1 ^ 0 * p.2 ^ 2) := by ext p; ring
  constructor
  · rw [heq]; exact hP
  · rw [heq, integral_add hAB hC, integral_sub hA (hB.const_mul 2), integral_const_mul]
    simp only [integral_product_monomial, moment_zero, moment_one μ h, moment_two μ h]
    norm_num

lemma product_difference_fourth (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (h4 : Integrable (fun x : ℝ => x ^ 4) (μ : Measure ℝ)) :
    Integrable (fun p : ℝ × ℝ => (p.1 - p.2) ^ 4) ((μ : Measure ℝ).prod (μ : Measure ℝ)) ∧
      (∫ p : ℝ × ℝ, (p.1 - p.2) ^ 4 ∂((μ : Measure ℝ).prod (μ : Measure ℝ))) = 2 * moment μ 4 + 6 := by
  have hA := integrable_product_monomial μ h4 4 0 (by decide) (by decide)
  have hB := integrable_product_monomial μ h4 3 1 (by decide) (by decide)
  have hC := integrable_product_monomial μ h4 2 2 (by decide) (by decide)
  have hD := integrable_product_monomial μ h4 1 3 (by decide) (by decide)
  have hE := integrable_product_monomial μ h4 0 4 (by decide) (by decide)
  have hAB : Integrable (fun p : ℝ × ℝ => p.1 ^ 4 * p.2 ^ 0 - 4 * (p.1 ^ 3 * p.2 ^ 1))
      ((μ : Measure ℝ).prod (μ : Measure ℝ)) := hA.sub (hB.const_mul 4)
  have hABC : Integrable (fun p : ℝ × ℝ => p.1 ^ 4 * p.2 ^ 0 - 4 * (p.1 ^ 3 * p.2 ^ 1) + 6 * (p.1 ^ 2 * p.2 ^ 2))
      ((μ : Measure ℝ).prod (μ : Measure ℝ)) := hAB.add (hC.const_mul 6)
  have hABCD : Integrable (fun p : ℝ × ℝ => p.1 ^ 4 * p.2 ^ 0 - 4 * (p.1 ^ 3 * p.2 ^ 1) + 6 * (p.1 ^ 2 * p.2 ^ 2) -
      4 * (p.1 ^ 1 * p.2 ^ 3)) ((μ : Measure ℝ).prod (μ : Measure ℝ)) := hABC.sub (hD.const_mul 4)
  have hP : Integrable (fun p : ℝ × ℝ => p.1 ^ 4 * p.2 ^ 0 - 4 * (p.1 ^ 3 * p.2 ^ 1) + 6 * (p.1 ^ 2 * p.2 ^ 2) -
      4 * (p.1 ^ 1 * p.2 ^ 3) + p.1 ^ 0 * p.2 ^ 4) ((μ : Measure ℝ).prod (μ : Measure ℝ)) := hABCD.add hE
  have heq : (fun p : ℝ × ℝ => (p.1 - p.2) ^ 4) =
      (fun p : ℝ × ℝ => p.1 ^ 4 * p.2 ^ 0 - 4 * (p.1 ^ 3 * p.2 ^ 1) + 6 * (p.1 ^ 2 * p.2 ^ 2) -
        4 * (p.1 ^ 1 * p.2 ^ 3) + p.1 ^ 0 * p.2 ^ 4) := by ext p; ring
  constructor
  · rw [heq]; exact hP
  · rw [heq, integral_add hABCD hE, integral_sub hABC (hD.const_mul 4),
      integral_add hAB (hC.const_mul 6), integral_sub hA (hB.const_mul 4),
      integral_const_mul, integral_const_mul, integral_const_mul]
    simp only [integral_product_monomial, moment_zero, moment_one μ h, moment_two μ h]
    ring

/-- The actual difference of independent copies, represented as a convolution with the reflected law. -/
def differenceMeasure (μ : ProbabilityMeasure ℝ) : Measure ℝ :=
  (μ : Measure ℝ) ∗ (μ : Measure ℝ).map (fun x : ℝ => -x)

instance differenceMeasure_probability (μ : ProbabilityMeasure ℝ) : IsProbabilityMeasure (differenceMeasure μ) := by
  unfold differenceMeasure
  infer_instance

def differenceProbability (μ : ProbabilityMeasure ℝ) : ProbabilityMeasure ℝ := ⟨differenceMeasure μ, inferInstance⟩

lemma differenceMeasure_eq_map_product (μ : ProbabilityMeasure ℝ) :
    differenceMeasure μ = ((μ : Measure ℝ).prod (μ : Measure ℝ)).map (fun p : ℝ × ℝ => p.1 - p.2) := by
  have hp := Measure.map_prod_map (μ : Measure ℝ) (μ : Measure ℝ) measurable_id measurable_neg
  rw [Measure.map_id] at hp
  unfold differenceMeasure Measure.conv
  rw [hp, Measure.map_map measurable_add (measurable_id.prodMap measurable_neg)]
  congr 1

lemma difference_moments (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (h4 : Integrable (fun x : ℝ => x ^ 4) (μ : Measure ℝ)) :
    Integrable (fun x : ℝ => x ^ 2) (differenceMeasure μ) ∧
    Integrable (fun x : ℝ => x ^ 4) (differenceMeasure μ) ∧
      (∫ x : ℝ, x ^ 2 ∂differenceMeasure μ) = 2 ∧
      (∫ x : ℝ, x ^ 4 ∂differenceMeasure μ) = 2 * moment μ 4 + 6 := by
  have h2 := product_difference_second μ h h4
  have hfour := product_difference_fourth μ h h4
  have hm : Measurable (fun p : ℝ × ℝ => p.1 - p.2) := by fun_prop
  have hF2 : AEStronglyMeasurable (fun x : ℝ => x ^ 2)
      (((μ : Measure ℝ).prod (μ : Measure ℝ)).map (fun p : ℝ × ℝ => p.1 - p.2)) :=
    (continuous_id.pow 2).aestronglyMeasurable
  have hF4 : AEStronglyMeasurable (fun x : ℝ => x ^ 4)
      (((μ : Measure ℝ).prod (μ : Measure ℝ)).map (fun p : ℝ × ℝ => p.1 - p.2)) :=
    (continuous_id.pow 4).aestronglyMeasurable
  rw [differenceMeasure_eq_map_product]
  refine ⟨(integrable_map_measure hF2 hm.aemeasurable).mpr h2.1,
    (integrable_map_measure hF4 hm.aemeasurable).mpr hfour.1, ?_, ?_⟩
  · rw [integral_map hm.aemeasurable hF2]
    exact h2.2
  · rw [integral_map hm.aemeasurable hF4]
    exact hfour.2

lemma charFun_differenceMeasure (μ : ProbabilityMeasure ℝ) (t : ℝ) :
    charFun (differenceMeasure μ) t = charFun (μ : Measure ℝ) t * charFun (μ : Measure ℝ) (-t) := by
  have hn : (fun x : ℝ => -x) = (fun x : ℝ => (-1 : ℝ) * x) := by ext x; ring
  rw [differenceMeasure, charFun_conv, hn, charFun_map_mul]
  simp only [neg_one_mul]

lemma integral_cos_charFun (ν : ProbabilityMeasure ℝ) (t : ℝ) :
    (∫ x : ℝ, Real.cos (t * x) ∂(ν : Measure ℝ)) = (charFun (ν : Measure ℝ) t).re := by
  calc
    _ = ∫ x : ℝ, (pureExp (t * x)).re ∂(ν : Measure ℝ) := by simp only [pureExp_real]
    _ = (∫ x : ℝ, pureExp (t * x) ∂(ν : Measure ℝ)).re := integral_re (integrable_pureExp_product ν t)
    _ = _ := by rw [charFun_eq_integral_pureExp]

lemma integrable_cos_law (ν : ProbabilityMeasure ℝ) (t : ℝ) :
    Integrable (fun x : ℝ => Real.cos (t * x)) (ν : Measure ℝ) := by
  have h : Integrable (fun x : ℝ => (pureExp (t * x)).re) (ν : Measure ℝ) := (integrable_pureExp_product ν t).re
  simpa only [pureExp_real] using h

/-- The CF norm square is the cosine expectation of the actual independent difference. -/
lemma norm_charFun_sq_symmetrization (μ : ProbabilityMeasure ℝ) (t : ℝ) :
    ‖charFun (μ : Measure ℝ) t‖ ^ 2 = ∫ x : ℝ, Real.cos (t * x) ∂differenceMeasure μ := by
  have hc := charFun_differenceMeasure μ t
  rw [charFun_neg] at hc
  have hn : (charFun (differenceMeasure μ) t).re = ‖charFun (μ : Measure ℝ) t‖ ^ 2 := by
    rw [hc, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  rw [← hn]
  exact (integral_cos_charFun (differenceProbability μ) t).symm

lemma norm_charFun_sq_le_quartic (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (h4 : Integrable (fun x : ℝ => x ^ 4) (μ : Measure ℝ)) (t : ℝ) :
    ‖charFun (μ : Measure ℝ) t‖ ^ 2 ≤ 1 - t ^ 2 + (moment μ 4 + 3) * t ^ 4 / 12 := by
  have hd := difference_moments μ h h4
  have hA : Integrable (fun x : ℝ => 1 - (t ^ 2 / 2) * x ^ 2) (differenceMeasure μ) :=
    (integrable_const 1).sub (hd.1.const_mul _)
  have hP : Integrable (fun x : ℝ => 1 - (t ^ 2 / 2) * x ^ 2 + (t ^ 4 / 24) * x ^ 4) (differenceMeasure μ) :=
    hA.add (hd.2.1.const_mul _)
  rw [norm_charFun_sq_symmetrization]
  calc
    _ ≤ ∫ x : ℝ, 1 - (t ^ 2 / 2) * x ^ 2 + (t ^ 4 / 24) * x ^ 4 ∂differenceMeasure μ := by
      apply integral_mono (integrable_cos_law (differenceProbability μ) t) hP
      intro x
      convert cos_le_quartic (t * x) using 1
      ring
    _ = _ := by
      rw [integral_add hA (hd.2.1.const_mul _), integral_sub (integrable_const 1) (hd.1.const_mul _),
        integral_const_mul, integral_const_mul, hd.2.2.1, hd.2.2.2]
      simp only [integral_const, probReal_univ, one_smul]
      ring

/-- The actual-law CF damping estimate; finite fourth moment is explicit. -/
theorem characteristic_damping (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (h4 : Integrable (fun x : ℝ => x ^ 4) (μ : Measure ℝ)) (t M : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) (hcap : moment μ 4 ≤ M) :
    ‖charFun (μ : Measure ℝ) t‖ ≤ Real.exp (-((45 - M) / 96 * t ^ 2)) := by
  have hM : 0 ≤ M := (moment_four_nonneg μ).trans hcap
  have ht2 : t ^ 2 ≤ (1 : ℝ) / 4 := by nlinarith [mul_nonneg ht0 (show 0 ≤ 1 / 2 - t by linarith)]
  have ht4 : t ^ 4 ≤ t ^ 2 / 4 := by
    have h := mul_le_mul_of_nonneg_right ht2 (sq_nonneg t)
    nlinarith
  have hpoly : ‖charFun (μ : Measure ℝ) t‖ ^ 2 ≤ 1 - ((45 - M) / 48 * t ^ 2) := by
    have hb := norm_charFun_sq_le_quartic μ h h4 t
    have hcapT := mul_le_mul_of_nonneg_right hcap (pow_nonneg ht0 4)
    have hstep := mul_le_mul_of_nonneg_left ht4 (show 0 ≤ M + 3 by linarith)
    nlinarith [hb, hcapT, hstep]
  have hs : ‖charFun (μ : Measure ℝ) t‖ ^ 2 ≤ (Real.exp (-((45 - M) / 96 * t ^ 2))) ^ 2 := by
    calc
      _ ≤ 1 - ((45 - M) / 48 * t ^ 2) := hpoly
      _ ≤ Real.exp (-((45 - M) / 48 * t ^ 2)) := Real.one_sub_le_exp_neg _
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  exact (sq_le_sq₀ (norm_nonneg _) (Real.exp_pos _).le).mp hs

lemma norm_comparator (μ : ProbabilityMeasure ℝ) (t : ℝ) : ‖comparator μ t‖ = Real.exp (-(t ^ 2) / 2) := by
  rw [comparator, Complex.norm_exp, exponent_real]

lemma comparator_damping (μ : ProbabilityMeasure ℝ) (t M : ℝ) (hcap : moment μ 4 ≤ M) :
    ‖comparator μ t‖ ≤ Real.exp (-((45 - M) / 96 * t ^ 2)) := by
  have hM : 0 ≤ M := (moment_four_nonneg μ).trans hcap
  have hprod := mul_nonneg hM (sq_nonneg t)
  rw [norm_comparator]
  apply Real.exp_le_exp.mpr
  nlinarith [hprod, sq_nonneg t]

/-- Both original pointwise damping bounds in the paper's physical input range. -/
theorem low_frequency_damping (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (h4 : Integrable (fun x : ℝ => x ^ 4) (μ : Measure ℝ)) (t M : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) (hcap : moment μ 4 ≤ M) (_hMupper : M ≤ 111 / 10) :
    ‖charFun (μ : Measure ℝ) t‖ ≤ Real.exp (-((45 - M) / 96 * t ^ 2)) ∧
      ‖comparator μ t‖ ≤ Real.exp (-((45 - M) / 96 * t ^ 2)) :=
  ⟨characteristic_damping μ h h4 t M ht0 ht1 hcap, comparator_damping μ t M hcap⟩

end BerryEsseen.CharacteristicExpansion

#print axioms BerryEsseen.CharacteristicExpansion.difference_moments
#print axioms BerryEsseen.CharacteristicExpansion.norm_charFun_sq_symmetrization
#print axioms BerryEsseen.CharacteristicExpansion.low_frequency_damping

namespace BerryEsseen.CharacteristicExpansion

lemma moment_four_eq_abs (μ : ProbabilityMeasure ℝ) :
    moment μ 4 = ∫ x : ℝ, |x| ^ 4 ∂(μ : Measure ℝ) := by
  unfold moment
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    change (x ^ 4 : ℝ) = |x| ^ 4
    rw [← abs_pow, abs_of_nonneg (by positivity : (0 : ℝ) ≤ x ^ 4)]

end BerryEsseen.CharacteristicExpansion

#print axioms BerryEsseen.CharacteristicExpansion.moment_four_eq_abs
