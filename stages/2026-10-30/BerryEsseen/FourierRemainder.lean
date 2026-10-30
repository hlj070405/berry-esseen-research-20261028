module

public import BerryEsseen.CompensatedExpectation
public import BerryEsseen.Extremizer
public import BerryEsseen.GaussianPrices

@[expose] public section

/-! 2026-10-28: the original compensated Fourier remainder for an actual iid sum.
The integrability and payoff formula are derived from actual probability laws,
their official characteristic functions, and a real Gaussian cosine integral. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology MeasureTheory NNReal ENNReal
open BerryEsseen.GaussianTools BerryEsseen.CompensatedExpectation

namespace BerryEsseen.FourierRemainder

lemma charFun_convPower (μ : Measure ℝ) [IsFiniteMeasure μ] (n : ℕ) (t : ℝ) :
    charFun (MixtureSum.convPower μ n) t = charFun μ t ^ n := by
  induction n with
  | zero => simp [MixtureSum.convPower, charFun_dirac]
  | succ n ih => rw [MixtureSum.convPower, charFun_conv, ih, pow_succ']

theorem charFun_iidSumProbability (μ : ProbabilityMeasure ℝ) (n : ℕ) (t : ℝ) :
    charFun (Extremizer.iidSumProbability μ n : Measure ℝ) t = charFun (μ : Measure ℝ) t ^ n := by
  rw [Extremizer.coe_iidSumProbability, MixtureSum.iidSumLaw_eq_convPower, charFun_convPower]

def gaussianProbability (n : ℕ) : ProbabilityMeasure ℝ :=
  ⟨gaussianReal 0 (n : NNReal), inferInstance⟩

@[simp] lemma coe_gaussianProbability (n : ℕ) :
    (gaussianProbability n : Measure ℝ) = gaussianReal 0 (n : NNReal) := rfl

lemma gaussian_charFun_real (v : NNReal) (t : ℝ) :
    charFun (gaussianReal 0 v) t = (Real.exp (-((v : ℝ) * t ^ 2) / 2) : ℂ) := by
  rw [charFun_gaussianReal]
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring

def gaussianFactor (n : ℕ) (t : ℝ) : ℝ := Real.exp (-((n : ℝ) * t ^ 2) / 2)

lemma charFun_gaussianProbability (n : ℕ) (t : ℝ) :
    charFun (gaussianProbability n : Measure ℝ) t = (gaussianFactor n t : ℂ) := by
  rw [coe_gaussianProbability, gaussian_charFun_real]
  simp only [gaussianFactor, NNReal.coe_natCast]

lemma gaussian_mean (n : ℕ) :
    (∫ x : ℝ, x ∂(gaussianProbability n : Measure ℝ)) = 0 := integral_id_gaussianReal

lemma gaussian_second_integrable (n : ℕ) :
    Integrable (fun x : ℝ => x ^ 2) (gaussianProbability n : Measure ℝ) := by
  change Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 (n : NNReal))
  have hLp : MemLp id (2 : ℝ≥0∞) (gaussianReal 0 (n : NNReal)) :=
    memLp_id_gaussianReal' 2 (by norm_num)
  have h := hLp.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  simpa only [id_eq, Real.norm_eq_abs, sq_abs] using h

lemma integral_phi_cos (a : ℝ) : (∫ u : ℝ, phi u * Real.cos (a * u)) = Real.exp (-(a ^ 2) / 2) := by
  have hi : Integrable (fun u : ℝ => Complex.exp (((a * u : ℝ) : ℂ) * Complex.I)) (gaussianReal 0 1) := by
    simpa only [Measure.coe_toProbabilityMeasure, sub_zero] using
      (integrable_shift_character (gaussianReal 0 1).toProbabilityMeasure 0 a)
  calc
    (∫ u : ℝ, phi u * Real.cos (a * u)) = ∫ u : ℝ, Real.cos (a * u) ∂gaussianReal 0 1 := by
      simpa only [phi, smul_eq_mul] using
        (integral_gaussianReal_eq_integral_smul (μ := 0) (v := 1) (f := fun u : ℝ => Real.cos (a * u)) one_ne_zero).symm
    _ = ∫ u : ℝ, (Complex.exp (((a * u : ℝ) : ℂ) * Complex.I)).re ∂gaussianReal 0 1 := by
      simp only [Complex.exp_ofReal_mul_I_re]
    _ = (∫ u : ℝ, Complex.exp (((a * u : ℝ) : ℂ) * Complex.I) ∂gaussianReal 0 1).re := integral_re hi
    _ = (charFun (gaussianReal 0 1) a).re := by simp only [charFun_apply_real, Complex.ofReal_mul]
    _ = _ := by
      rw [gaussian_charFun_real]
      simp only [NNReal.coe_one, one_mul, Complex.ofReal_re]

lemma inv_phi_zero : (1 : ℝ) / phi 0 = (2 * Real.pi) * phi 0 := by
  have hp : phi 0 = (Real.sqrt (2 * Real.pi))⁻¹ := by simp [phi_formula]
  have hs : phi 0 ^ 2 * (2 * Real.pi) = 1 := by
    have hr : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
    rw [hp]
    calc
      (Real.sqrt (2 * Real.pi))⁻¹ ^ 2 * (2 * Real.pi) =
          (Real.sqrt (2 * Real.pi))⁻¹ ^ 2 * Real.sqrt (2 * Real.pi) ^ 2 := by
        rw [Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.pi)]
      _ = 1 := by field_simp [ne_of_gt hr]
  apply (div_eq_iff (ne_of_gt (phi_pos 0))).mpr
  nlinarith

def gaussianCosine (n : ℕ) (H t : ℝ) : ℝ := gaussianFactor n t * Real.cos (H * t)

lemma integrable_gaussianCosine (n : ℕ) (hn : 0 < n) (H : ℝ) : Integrable (gaussianCosine n H) := by
  have hN : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have he : Integrable (fun t : ℝ => gaussianFactor n t) := by
    convert (integrable_exp_neg_mul_sq (b := (n : ℝ) / 2) (by positivity)) using 1
    ext t
    unfold gaussianFactor
    congr 1
    ring
  have hc : Continuous (gaussianCosine n H) := by unfold gaussianCosine gaussianFactor; fun_prop
  apply he.mono' hc.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun t => by
    have hp : 0 < gaussianFactor n t := Real.exp_pos _
    rw [Real.norm_eq_abs, gaussianCosine, abs_mul, abs_of_pos hp]
    calc
      gaussianFactor n t * |Real.cos (H * t)| ≤ gaussianFactor n t * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) hp.le
      _ = _ := mul_one _

lemma integral_gaussianCosine_univ (n : ℕ) (hn : 0 < n) (H : ℝ) :
    (∫ t : ℝ, gaussianCosine n H t) = (2 * Real.pi / Real.sqrt n) * phi (H / Real.sqrt n) := by
  have hN : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hN
  have heq : gaussianCosine n H = (fun t : ℝ => (1 / phi 0) *
      (phi (Real.sqrt n * t) * Real.cos ((H / Real.sqrt n) * (Real.sqrt n * t)))) := by
    ext t
    have harg : (H / Real.sqrt n) * (Real.sqrt n * t) = H * t := by
      field_simp [ne_of_gt hs]
    rw [harg, GaussianPrices.phi_eq_phi_zero_mul_exp (Real.sqrt n * t), mul_pow, Real.sq_sqrt hN.le]
    unfold gaussianCosine gaussianFactor
    have hneg : -((n : ℝ) * t ^ 2) / 2 = -((n : ℝ) * t ^ 2 / 2) := by ring
    rw [hneg]
    field_simp [ne_of_gt (phi_pos 0)]
  rw [heq, integral_const_mul, Measure.integral_comp_mul_left
    (fun u : ℝ => phi u * Real.cos ((H / Real.sqrt n) * u)) (Real.sqrt n), integral_phi_cos]
  simp only [abs_of_pos (inv_pos.mpr hs), smul_eq_mul]
  rw [inv_phi_zero, GaussianPrices.phi_eq_phi_zero_mul_exp (H / Real.sqrt n)]
  have hneg : -((H / Real.sqrt n) ^ 2) / 2 = -((H / Real.sqrt n) ^ 2 / 2) := by ring
  rw [hneg]
  ring

/-- The genuine half-axis Gaussian cosine integral, obtained from CF, scaling, and evenness. -/
theorem integral_gaussianCosine_Ioi (n : ℕ) (hn : 0 < n) (H : ℝ) :
    (∫ t in Ioi 0, gaussianCosine n H t) = (Real.pi / Real.sqrt n) * phi (H / Real.sqrt n) := by
  have heq : (fun t : ℝ => gaussianCosine n H |t|) = gaussianCosine n H := by
    ext t
    by_cases ht : 0 ≤ t
    · rw [abs_of_nonneg ht]
    · rw [abs_of_neg (lt_of_not_ge ht)]
      simp only [gaussianCosine, gaussianFactor, neg_sq, mul_neg, Real.cos_neg]
  have h := integral_comp_abs (f := gaussianCosine n H)
  rw [heq, integral_gaussianCosine_univ n hn H] at h
  have htwo : (2 * Real.pi / Real.sqrt n) * phi (H / Real.sqrt n) =
      2 * ((Real.pi / Real.sqrt n) * phi (H / Real.sqrt n)) := by ring
  rw [htwo] at h
  linarith

end BerryEsseen.FourierRemainder

#print axioms BerryEsseen.FourierRemainder.charFun_iidSumProbability
#print axioms BerryEsseen.FourierRemainder.integral_gaussianCosine_Ioi

namespace BerryEsseen.FourierRemainder

/-- The signed third moment of the original actual law. -/
def thirdMoment (μ : ProbabilityMeasure ℝ) : ℝ := ∫ x : ℝ, x ^ 3 ∂(μ : Measure ℝ)

lemma integrable_signed_cube (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    Integrable (fun x : ℝ => x ^ 3) (μ : Measure ℝ) := by
  have hm : AEStronglyMeasurable (fun x : ℝ => x ^ 3) (μ : Measure ℝ) :=
    (continuous_id.pow 3).aestronglyMeasurable
  apply (integrable_norm_iff hm).mp
  simpa only [Real.norm_eq_abs, abs_pow] using h.integrable_cube

/-- The literal original compensated Edgeworth integrand. -/
def originalIntegrand (μ : ProbabilityMeasure ℝ) (n : ℕ) (H t : ℝ) : ℝ :=
  (Complex.exp (-Complex.I * (t : ℂ) * (H : ℂ)) *
    (charFun (μ : Measure ℝ) t ^ n - (gaussianFactor n t : ℂ) *
      (1 - Complex.I * (n : ℂ) * (thirdMoment μ : ℂ) * (t : ℂ) ^ 3 / 6))).im / t ^ 3

/-- The manuscript's E_n, with its original 2*sqrt(n)/pi coefficient. -/
def value (μ : ProbabilityMeasure ℝ) (n : ℕ) (H : ℝ) : ℝ :=
  (2 * Real.sqrt n / Real.pi) * (∫ t in Ioi 0, originalIntegrand μ n H t)

/-- This ordering gives CF_sum-CF_Gaussian, hence Gaussian payoff minus sum payoff. -/
def baseIntegrand (μ : ProbabilityMeasure ℝ) (n : ℕ) (H t : ℝ) : ℝ :=
  differenceTransform (gaussianProbability n) (Extremizer.iidSumProbability μ n) H t

lemma equal_sum_gaussian_means (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (n : ℕ) :
    (∫ x : ℝ, x ∂(gaussianProbability n : Measure ℝ)) =
      ∫ x : ℝ, x ∂(Extremizer.iidSumProbability μ n : Measure ℝ) := by
  rw [gaussian_mean, (Extremizer.iidSum_moments μ h n).2.2.1]

lemma integrable_baseIntegrand (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (n : ℕ) (H : ℝ) :
    IntegrableOn (baseIntegrand μ n H) (Ioi 0) :=
  integrable_differenceTransform (gaussianProbability n) (Extremizer.iidSumProbability μ n)
    (gaussian_second_integrable n) (Extremizer.iidSum_moments μ h n).2.1 H
    (equal_sum_gaussian_means μ h n)

lemma phase_real (H t : ℝ) :
    (Complex.exp (-Complex.I * (t : ℂ) * (H : ℂ))).re = Real.cos (H * t) := by
  have he : -Complex.I * (t : ℂ) * (H : ℂ) = (((-(H * t) : ℝ) : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [he, Complex.exp_ofReal_mul_I_re, Real.cos_neg]

/-- The i*Edgeworth term contributes a positive real Gaussian cosine correction. -/
lemma edgeworth_algebra (p f : ℂ) (g a t : ℝ) (ht : t ≠ 0) :
    (p * (f - (g : ℂ) * (1 - Complex.I * ((a * t ^ 3 : ℝ) : ℂ)))).im / t ^ 3 =
      (p * (f - (g : ℂ))).im / t ^ 3 + a * g * p.re := by
  simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im]
  field_simp [ht]
  ring

lemma originalIntegrand_decomposition (μ : ProbabilityMeasure ℝ) (n : ℕ) (H t : ℝ) (ht : t ≠ 0) :
    originalIntegrand μ n H t = baseIntegrand μ n H t +
      ((n : ℝ) * thirdMoment μ / 6) * gaussianCosine n H t := by
  have hedge : Complex.I * (n : ℂ) * (thirdMoment μ : ℂ) * (t : ℂ) ^ 3 / 6 =
      Complex.I * ((((n : ℝ) * thirdMoment μ / 6) * t ^ 3 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [originalIntegrand, hedge, edgeworth_algebra _ _ _ _ _ ht, phase_real]
  have hbase : (Complex.exp (-Complex.I * (t : ℂ) * (H : ℂ)) *
      (charFun (μ : Measure ℝ) t ^ n - (gaussianFactor n t : ℂ))).im / t ^ 3 = baseIntegrand μ n H t := by
    simp only [baseIntegrand, differenceTransform, charFun_iidSumProbability, charFun_gaussianProbability]
  rw [hbase]
  simp only [gaussianCosine]
  ring

/-- The original infinite-axis Fourier remainder is genuinely absolutely integrable. -/
theorem integrable_originalIntegrand (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (hn : 0 < n) (H : ℝ) : IntegrableOn (originalIntegrand μ n H) (Ioi 0) := by
  have hi : IntegrableOn (fun t : ℝ => baseIntegrand μ n H t +
      ((n : ℝ) * thirdMoment μ / 6) * gaussianCosine n H t) (Ioi 0) :=
    (integrable_baseIntegrand μ h n H).add
      ((integrable_gaussianCosine n hn H).integrableOn.const_mul _)
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact (originalIntegrand_decomposition μ n H t (ne_of_gt ht)).symm

lemma integral_originalIntegrand (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (hn : 0 < n) (H : ℝ) :
    (∫ t in Ioi 0, originalIntegrand μ n H t) = (∫ t in Ioi 0, baseIntegrand μ n H t) +
      ((n : ℝ) * thirdMoment μ / 6) * ((Real.pi / Real.sqrt n) * phi (H / Real.sqrt n)) := by
  calc
    (∫ t in Ioi 0, originalIntegrand μ n H t) = ∫ t in Ioi 0,
        baseIntegrand μ n H t + ((n : ℝ) * thirdMoment μ / 6) * gaussianCosine n H t := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact originalIntegrand_decomposition μ n H t (ne_of_gt ht)
    _ = _ := by
      rw [integral_add (integrable_baseIntegrand μ h n H)
        ((integrable_gaussianCosine n hn H).integrableOn.const_mul _),
        integral_const_mul, integral_gaussianCosine_Ioi n hn H]

lemma integral_baseIntegrand (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (n : ℕ) (H : ℝ) :
    (∫ t in Ioi 0, baseIntegrand μ n H t) = (Real.pi / 4) *
      ((∫ x : ℝ, (x - H) * |x - H| ∂(gaussianProbability n : Measure ℝ)) -
        (∫ x : ℝ, (x - H) * |x - H| ∂(Extremizer.iidSumProbability μ n : Measure ℝ))) := by
  have hpay := compensated_expectation_difference (gaussianProbability n) (Extremizer.iidSumProbability μ n)
    (gaussian_second_integrable n) (Extremizer.iidSum_moments μ h n).2.1 H
    (equal_sum_gaussian_means μ h n)
  change _ = (Real.pi / 4) * _
  rw [hpay]
  change (∫ t in Ioi 0, baseIntegrand μ n H t) =
    (Real.pi / 4) * ((4 / Real.pi) * (∫ t in Ioi 0, baseIntegrand μ n H t))
  field_simp [Real.pi_ne_zero]

/-- Exact payoff expression for the original E_n. The Gaussian Edgeworth correction has the plus sign. -/
theorem value_eq_payoff (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (hn : 0 < n) (H : ℝ) :
    value μ n H = -(Real.sqrt n / 2) *
      ((∫ x : ℝ, (x - H) * |x - H| ∂(Extremizer.iidSumProbability μ n : Measure ℝ)) -
        (∫ x : ℝ, (x - H) * |x - H| ∂(gaussianProbability n : Measure ℝ))) +
      ((n : ℝ) * thirdMoment μ / 3) * phi (H / Real.sqrt n) := by
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  rw [value, integral_originalIntegrand μ h n hn H, integral_baseIntegrand μ h n H]
  field_simp [Real.pi_ne_zero, ne_of_gt hs]
  ring

end BerryEsseen.FourierRemainder

#print axioms BerryEsseen.FourierRemainder.originalIntegrand_decomposition
#print axioms BerryEsseen.FourierRemainder.integrable_originalIntegrand
#print axioms BerryEsseen.FourierRemainder.value_eq_payoff
