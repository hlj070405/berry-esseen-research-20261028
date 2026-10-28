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
  simp only [mul_zero, zero_mul, zero_sub]
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
  have hLp : MemLp (fun x : ℝ => x) (2 : ℝ≥0∞) (gaussianReal 0 (n : NNReal)) := by
    simpa only [id_eq] using (memLp_id_gaussianReal (μ := 0) (v := (n : NNReal)) 2)
  have h := hLp.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  simpa only [Real.norm_eq_abs, sq_abs] using h

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
    _ = _ := by rw [gaussian_charFun_real]; simp

lemma inv_phi_zero : (1 : ℝ) / phi 0 = (2 * Real.pi) * phi 0 := by
  have hp : phi 0 = (Real.sqrt (2 * Real.pi))⁻¹ := by simp [phi_formula]
  have hs : phi 0 ^ 2 * (2 * Real.pi) = 1 := by
    rw [hp, ← inv_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.pi)]
    exact inv_mul_cancel₀ (by positivity)
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
    rw [Real.norm_eq_abs, gaussianCosine, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      gaussianFactor n t * |Real.cos (H * t)| ≤ gaussianFactor n t * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (Real.exp_pos _).le
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
  linarith

end BerryEsseen.FourierRemainder

#print axioms BerryEsseen.FourierRemainder.charFun_iidSumProbability
#print axioms BerryEsseen.FourierRemainder.integral_gaussianCosine_Ioi
