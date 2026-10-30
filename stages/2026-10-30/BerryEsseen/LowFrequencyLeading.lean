module

public import BerryEsseen.LowFrequencyError
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section

/-! 2026-10-28: the actual-law low-frequency triangle candidate from ut:low.
The original H, exact Gaussian comparator, and original L₂ cost are retained. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators Interval
open BerryEsseen.CharacteristicExpansion BerryEsseen.LowFrequencyError

namespace BerryEsseen.LowFrequencyLeading

/-- The half-Gaussian mass used in the paper's I_u price. -/
def gaussianMass : ℝ := Real.sqrt (Real.pi / 2)

lemma gaussianMass_nonneg : 0 ≤ gaussianMass := Real.sqrt_nonneg _

lemma gaussianMass_le : gaussianMass ≤ 251 / 200 := by
  have hp := Real.pi_lt_d4
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ Real.pi / 2 by positivity)
  have hn := Real.sqrt_nonneg (Real.pi / 2)
  unfold gaussianMass
  nlinarith

lemma rpow_neg_half_nat (b : ℝ) (hb : 0 < b) (k : ℕ) :
    b ^ (-((k : ℝ) / 2)) = (Real.sqrt b ^ k)⁻¹ := by
  rw [← neg_div]
  rw [Real.rpow_div_two_eq_sqrt _ hb.le, Real.rpow_neg (Real.sqrt_nonneg _), Real.rpow_natCast]

lemma sqrt_odd_power (b : ℝ) (hb : 0 ≤ b) (k : ℕ) :
    Real.sqrt b ^ (2 * k + 1) = b ^ k * Real.sqrt b := by
  rw [pow_succ, pow_mul, Real.sq_sqrt hb]

lemma integral_even_gaussian_two (c : ℝ) (hc : 0 < c) :
    (∫ t in Ioi (0 : ℝ), t ^ 2 * Real.exp (-(c / 2 * t ^ 2))) =
      gaussianMass / (c * Real.sqrt c) := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := (2 : ℝ)) (q := (2 : ℝ)) (b := c / 2)
    (by norm_num) (by norm_num) (by positivity)
  have hg := Real.Gamma_nat_add_half 1
  norm_num at hg
  norm_num only [show ((2 : ℝ) + 1) / 2 = 3 / 2 by norm_num,
    show -((2 : ℝ) + 1) / 2 = -(3 : ℝ) / 2 by norm_num, Real.rpow_two] at h
  have hr := rpow_neg_half_nat (c / 2) (by positivity) 3
  norm_num only [Nat.cast_ofNat] at hr
  rw [hg, hr] at h
  rw [show (3 : ℕ) = 2 * 1 + 1 by norm_num, sqrt_odd_power _ (by positivity)] at h
  simp only [pow_one] at h
  rw [Real.sqrt_div hc.le] at h
  unfold gaussianMass
  rw [Real.sqrt_div Real.pi_pos.le]
  convert h using 1
  · simp only [neg_mul]
  · have hc0 := ne_of_gt hc
    have hs0 := ne_of_gt (Real.sqrt_pos.mpr hc)
    have ht0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))
    field_simp [hc0, hs0, ht0]
    ring_nf
    norm_num [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

lemma integral_even_gaussian_four (c : ℝ) (hc : 0 < c) :
    (∫ t in Ioi (0 : ℝ), t ^ 4 * Real.exp (-(c / 2 * t ^ 2))) =
      3 * gaussianMass / (c ^ 2 * Real.sqrt c) := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := (2 : ℝ)) (q := (4 : ℝ)) (b := c / 2)
    (by norm_num) (by norm_num) (by positivity)
  have hg := Real.Gamma_nat_add_half 2
  norm_num at hg
  norm_num only [show ((4 : ℝ) + 1) / 2 = 5 / 2 by norm_num,
    show -((4 : ℝ) + 1) / 2 = -(5 : ℝ) / 2 by norm_num, Real.rpow_ofNat] at h
  have hr := rpow_neg_half_nat (c / 2) (by positivity) 5
  norm_num only [Nat.cast_ofNat] at hr
  rw [hg, hr] at h
  rw [show (5 : ℕ) = 2 * 2 + 1 by norm_num, sqrt_odd_power _ (by positivity)] at h
  rw [Real.sqrt_div hc.le] at h
  unfold gaussianMass
  rw [Real.sqrt_div Real.pi_pos.le]
  convert h using 1
  · simp only [neg_mul]
  · have hc0 := ne_of_gt hc
    have hs0 := ne_of_gt (Real.sqrt_pos.mpr hc)
    have ht0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))
    field_simp [hc0, hs0, ht0]
    ring_nf
    norm_num [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

lemma integral_even_gaussian_six (c : ℝ) (hc : 0 < c) :
    (∫ t in Ioi (0 : ℝ), t ^ 6 * Real.exp (-(c / 2 * t ^ 2))) =
      15 * gaussianMass / (c ^ 3 * Real.sqrt c) := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := (2 : ℝ)) (q := (6 : ℝ)) (b := c / 2)
    (by norm_num) (by norm_num) (by positivity)
  have hg := Real.Gamma_nat_add_half 3
  norm_num at hg
  norm_num only [show ((6 : ℝ) + 1) / 2 = 7 / 2 by norm_num,
    show -((6 : ℝ) + 1) / 2 = -(7 : ℝ) / 2 by norm_num, Real.rpow_ofNat] at h
  have hr := rpow_neg_half_nat (c / 2) (by positivity) 7
  norm_num only [Nat.cast_ofNat] at hr
  rw [hg, hr] at h
  rw [show (7 : ℕ) = 2 * 3 + 1 by norm_num, sqrt_odd_power _ (by positivity)] at h
  rw [Real.sqrt_div hc.le] at h
  unfold gaussianMass
  rw [Real.sqrt_div Real.pi_pos.le]
  convert h using 1
  · simp only [neg_mul]
  · have hc0 := ne_of_gt hc
    have hs0 := ne_of_gt (Real.sqrt_pos.mpr hc)
    have ht0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))
    field_simp [hc0, hs0, ht0]
    ring_nf
    norm_num [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

lemma abs_cos_sub_one (u : ℝ) : |Real.cos u - 1| ≤ u ^ 2 / 2 := by
  rw [abs_of_nonpos (sub_nonpos.mpr (Real.cos_le_one _))]
  linarith [Real.one_sub_sq_div_two_le_cos (x := u)]

/-- Rotation uses separate real and imaginary Taylor errors, preserving the sharp prices. -/
lemma rotation_bound (v u : ℝ) :
    |(pureExp (-v) * (pureExp (-u) - (1 - Complex.I * (u : ℂ)))).im| ≤
      |u| ^ 3 / 6 + |v| * u ^ 2 / 2 := by
  have heq : (pureExp (-v) * (pureExp (-u) - (1 - Complex.I * (u : ℂ)))).im =
      Real.cos v * (u - Real.sin u) - Real.sin v * (Real.cos u - 1) := by
    simp only [pureExp, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.exp_re,
      Complex.exp_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero,
      zero_add, one_mul, Complex.one_re, Complex.one_im, Real.exp_zero,
      Real.cos_neg, Real.sin_neg]
    ring
  rw [heq]
  calc
    _ ≤ |Real.cos v * (u - Real.sin u)| + |Real.sin v * (Real.cos u - 1)| := abs_sub _ _
    _ = |Real.cos v| * |u - Real.sin u| + |Real.sin v| * |Real.cos u - 1| := by rw [abs_mul, abs_mul]
    _ ≤ 1 * (|u| ^ 3 / 6) + |v| * (u ^ 2 / 2) :=
      add_le_add (mul_le_mul (Real.abs_cos_le_one _) (Real.abs_sub_sin_le u) (abs_nonneg _) (by norm_num))
        (mul_le_mul Real.abs_sin_le_abs (abs_cos_sub_one u) (abs_nonneg _) (abs_nonneg _))
    _ = _ := by ring

end BerryEsseen.LowFrequencyLeading

#print axioms BerryEsseen.LowFrequencyLeading.integral_even_gaussian_six
#print axioms BerryEsseen.LowFrequencyLeading.rotation_bound

namespace BerryEsseen.LowFrequencyLeading

/-- A reusable two-term Gaussian domination, including L¹ of the original function. -/
lemma two_gaussian_cost (f : ℝ → ℝ) (hf : Measurable f) (k l : ℕ) (C D c : ℝ)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hc : 0 < c)
    (hnonneg : ∀ t ∈ Ioc (0 : ℝ) (1 / 2), 0 ≤ f t)
    (hb : ∀ t ∈ Ioc (0 : ℝ) (1 / 2), f t ≤
      C * (t ^ k * Real.exp (-(c * t ^ 2))) + D * (t ^ l * Real.exp (-(c * t ^ 2)))) :
    IntegrableOn f (Ioc (0 : ℝ) (1 / 2)) ∧
    (∫ t in Ioc (0 : ℝ) (1 / 2), f t) ≤
      C * (∫ t in Ioi (0 : ℝ), t ^ k * Real.exp (-(c * t ^ 2))) +
      D * (∫ t in Ioi (0 : ℝ), t ^ l * Real.exp (-(c * t ^ 2))) := by
  have hk := (integrable_gaussian_power k c hc).const_mul C
  have hl := (integrable_gaussian_power l c hc).const_mul D
  have hi : IntegrableOn f (Ioc (0 : ℝ) (1 / 2)) := by
    apply (hk.add hl).integrableOn.mono' hf.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg t ht)]
    exact hb t ht
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ t in Ioc (0 : ℝ) (1 / 2),
        C * (t ^ k * Real.exp (-(c * t ^ 2))) + D * (t ^ l * Real.exp (-(c * t ^ 2))) := by
      apply integral_mono_ae hi (hk.add hl).integrableOn
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact hb t ht
    _ = C * (∫ t in Ioc (0 : ℝ) (1 / 2), t ^ k * Real.exp (-(c * t ^ 2))) +
        D * (∫ t in Ioc (0 : ℝ) (1 / 2), t ^ l * Real.exp (-(c * t ^ 2))) := by
      rw [integral_add hk.integrableOn hl.integrableOn, integral_const_mul, integral_const_mul]
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_left (integral_truncated_gaussian_le k c hc) hC)
      (mul_le_mul_of_nonneg_left (integral_truncated_gaussian_le l c hc) hD)

lemma comparator_pow_split (μ : ProbabilityMeasure ℝ) (k : ℕ) (t : ℝ) :
    comparator μ t ^ k =
      ((Real.exp (-((k : ℝ) / 2 * t ^ 2)) : ℝ) : ℂ) * pureExp (-((k : ℝ) * gamma μ * t ^ 3 / 6)) := by
  unfold comparator exponent pureExp
  rw [← Complex.exp_nat_mul, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Actual Gaussian comparator retained in V_n, with its linear cubic correction. -/
def gaussianComparator (μ : ProbabilityMeasure ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  ((Real.exp (-((n : ℝ) / 2 * t ^ 2)) : ℝ) : ℂ) *
    (1 - Complex.I * (((n : ℝ) * gamma μ * t ^ 3 / 6 : ℝ) : ℂ))

def gaussianDifference (μ : ProbabilityMeasure ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  comparator μ t ^ n - gaussianComparator μ n t

def rotatedGaussianIntegrand (μ : ProbabilityMeasure ℝ) (n : ℕ) (H t : ℝ) : ℝ :=
  |(pureExp (-(H * t)) * gaussianDifference μ n t).im| / t ^ 3

lemma measurable_rotatedGaussianIntegrand (μ : ProbabilityMeasure ℝ) (n : ℕ) (H : ℝ) :
    Measurable (rotatedGaussianIntegrand μ n H) := by
  have hh := measurable_comparator μ
  unfold rotatedGaussianIntegrand gaussianDifference gaussianComparator pureExp
  fun_prop

lemma rotatedGaussianIntegrand_nonneg (μ : ProbabilityMeasure ℝ) (n : ℕ) (H t : ℝ) (ht : 0 ≤ t) :
    0 ≤ rotatedGaussianIntegrand μ n H t := by unfold rotatedGaussianIntegrand; positivity

lemma rotatedGaussian_bound (μ : ProbabilityMeasure ℝ) (n : ℕ) (H t g : ℝ)
    (ht : 0 < t) (hg : |gamma μ| ≤ g) :
    rotatedGaussianIntegrand μ n H t ≤
      ((n : ℝ) ^ 3 * g ^ 3 / 1296) * (t ^ 6 * Real.exp (-((n : ℝ) / 2 * t ^ 2))) +
      (|H| * (n : ℝ) ^ 2 * g ^ 2 / 72) * (t ^ 4 * Real.exp (-((n : ℝ) / 2 * t ^ 2))) := by
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hg0 : 0 ≤ g := (abs_nonneg _).trans hg
  have hu : |(n : ℝ) * gamma μ * t ^ 3 / 6| ≤ (n : ℝ) * g * t ^ 3 / 6 := by
    rw [abs_div, abs_mul, abs_mul, abs_of_nonneg hn0, abs_of_nonneg (pow_nonneg ht.le 3)]
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 6)]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg hn0)
      (pow_nonneg ht.le 3)) (by norm_num)
  have hu3 := pow_le_pow_left₀ (abs_nonneg _) hu 3
  have hu2 := pow_le_pow_left₀ (abs_nonneg _) hu 2
  have hr := rotation_bound (H * t) ((n : ℝ) * gamma μ * t ^ 3 / 6)
  have heq : |(pureExp (-(H * t)) * gaussianDifference μ n t).im| =
      Real.exp (-((n : ℝ) / 2 * t ^ 2)) *
      |(pureExp (-(H * t)) * (pureExp (-((n : ℝ) * gamma μ * t ^ 3 / 6)) -
        (1 - Complex.I * (((n : ℝ) * gamma μ * t ^ 3 / 6 : ℝ) : ℂ)))).im| := by
    unfold gaussianDifference gaussianComparator
    rw [comparator_pow_split]
    have hid (c e d p : ℂ) : p * (c * e - c * d) = c * (p * (e - d)) := by ring
    rw [hid]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
      abs_mul, abs_of_pos (Real.exp_pos _)]
  have hb : |(pureExp (-(H * t)) * gaussianDifference μ n t).im| ≤
      Real.exp (-((n : ℝ) / 2 * t ^ 2)) *
      (((n : ℝ) * g * t ^ 3 / 6) ^ 3 / 6 + |H| * t * ((n : ℝ) * g * t ^ 3 / 6) ^ 2 / 2) := by
    rw [heq]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    calc
      _ ≤ |(n : ℝ) * gamma μ * t ^ 3 / 6| ^ 3 / 6 +
          |H * t| * (((n : ℝ) * gamma μ * t ^ 3 / 6) ^ 2) / 2 := hr
      _ ≤ _ := by
        rw [abs_mul, abs_of_nonneg ht.le, ← sq_abs]
        exact add_le_add (div_le_div_of_nonneg_right hu3 (by norm_num))
          (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hu2 (by positivity)) (by norm_num))
  have hdiv := div_le_div_of_nonneg_right hb (pow_nonneg ht.le 3)
  change |(pureExp (-(H * t)) * gaussianDifference μ n t).im| / t ^ 3 ≤ _
  convert hdiv using 1
  field_simp [ne_of_gt ht]
  ring

end BerryEsseen.LowFrequencyLeading

namespace BerryEsseen.LowFrequencyLeading

/-- The original Gaussian rotation price, with the actual threshold H. -/
theorem gaussian_rotation_cost (μ : ProbabilityMeasure ℝ) (n : ℕ) (hn : 0 < n) (H g : ℝ)
    (hg : |gamma μ| ≤ g) :
    IntegrableOn (rotatedGaussianIntegrand μ n H) (Ioc (0 : ℝ) (1 / 2)) ∧
    Real.sqrt n * (∫ t in Ioc (0 : ℝ) (1 / 2), rotatedGaussianIntegrand μ n H t) ≤
      251 * g ^ 3 / 17280 + 251 * g ^ 2 * |H| / 4800 := by
  have hn0 : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hg0 : 0 ≤ g := (abs_nonneg _).trans hg
  have hcost := two_gaussian_cost (rotatedGaussianIntegrand μ n H)
    (measurable_rotatedGaussianIntegrand μ n H) 6 4
    ((n : ℝ) ^ 3 * g ^ 3 / 1296) (|H| * (n : ℝ) ^ 2 * g ^ 2 / 72) ((n : ℝ) / 2)
    (by positivity) (by positivity) (by positivity)
    (fun t ht => rotatedGaussianIntegrand_nonneg μ n H t ht.1.le)
    (fun t ht => rotatedGaussian_bound μ n H t g ht.1 hg)
  refine ⟨hcost.1, ?_⟩
  rw [integral_even_gaussian_six _ hn0, integral_even_gaussian_four _ hn0] at hcost
  calc
    _ ≤ Real.sqrt n * (((n : ℝ) ^ 3 * g ^ 3 / 1296) *
        (15 * gaussianMass / ((n : ℝ) ^ 3 * Real.sqrt n)) +
        (|H| * (n : ℝ) ^ 2 * g ^ 2 / 72) * (3 * gaussianMass / ((n : ℝ) ^ 2 * Real.sqrt n))) :=
      mul_le_mul_of_nonneg_left hcost.2 (Real.sqrt_nonneg _)
    _ = gaussianMass * (5 * g ^ 3 / 432 + g ^ 2 * |H| / 24) := by
      field_simp [ne_of_gt hn0, ne_of_gt (Real.sqrt_pos.mpr hn0)]
      ring
    _ ≤ (251 / 200 : ℝ) * (5 * g ^ 3 / 432 + g ^ 2 * |H| / 24) :=
      mul_le_mul_of_nonneg_right gaussianMass_le (by positivity)
    _ = _ := by ring

lemma pureExp_mul (u v : ℝ) : pureExp u * pureExp v = pureExp (u + v) := by
  unfold pureExp
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The actual leading quartic/fifth term of the power expansion. -/
def leadingTerm (μ : ProbabilityMeasure ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  -(n : ℂ) * (((quarticCoeff μ * t ^ 4 : ℝ) : ℂ) +
    Complex.I * ((fifthCoeff μ * t ^ 5 : ℝ) : ℂ)) * comparator μ t ^ (n - 1)

def leadingIntegrand (μ : ProbabilityMeasure ℝ) (n : ℕ) (H t : ℝ) : ℝ :=
  |(pureExp (-(H * t)) * leadingTerm μ n t).im| / t ^ 3

lemma measurable_leadingIntegrand (μ : ProbabilityMeasure ℝ) (n : ℕ) (H : ℝ) :
    Measurable (leadingIntegrand μ n H) := by
  have hh := measurable_comparator μ
  unfold leadingIntegrand leadingTerm pureExp
  fun_prop

lemma leadingIntegrand_nonneg (μ : ProbabilityMeasure ℝ) (n : ℕ) (H t : ℝ) (ht : 0 ≤ t) :
    0 ≤ leadingIntegrand μ n H t := by unfold leadingIntegrand; positivity

lemma leading_rotation_im (μ : ProbabilityMeasure ℝ) (n : ℕ) (H t : ℝ) :
    (pureExp (-(H * t)) * leadingTerm μ n t).im =
      (n : ℝ) * Real.exp (-(((n - 1 : ℕ) : ℝ) / 2 * t ^ 2)) *
      (quarticCoeff μ * t ^ 4 * Real.sin (H * t + ((n - 1 : ℕ) : ℝ) * gamma μ * t ^ 3 / 6) -
        fifthCoeff μ * t ^ 5 * Real.cos (H * t + ((n - 1 : ℕ) : ℝ) * gamma μ * t ^ 3 / 6)) := by
  have heq : pureExp (-(H * t)) * leadingTerm μ n t =
      (((-(n : ℝ) * Real.exp (-(((n - 1 : ℕ) : ℝ) / 2 * t ^ 2)) : ℝ)) : ℂ) *
      ((((quarticCoeff μ * t ^ 4 : ℝ) : ℂ) + Complex.I * ((fifthCoeff μ * t ^ 5 : ℝ) : ℂ)) *
        pureExp (-(H * t + ((n - 1 : ℕ) : ℝ) * gamma μ * t ^ 3 / 6))) := by
    unfold leadingTerm
    rw [comparator_pow_split, neg_add, ← pureExp_mul]
    push_cast
    ring
  rw [heq]
  simp only [pureExp, Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_re, Complex.exp_im, Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im,
    mul_zero, zero_mul, add_zero, zero_add, one_mul, Real.cos_neg, Real.sin_neg]
  ring_nf
  simp only [Real.exp_zero, mul_one]

lemma sin_le_phase_price (μ : ProbabilityMeasure ℝ) (n : ℕ) (H t g : ℝ) (ht : 0 ≤ t)
    (hg : |gamma μ| ≤ g) :
    |Real.sin (H * t + ((n - 1 : ℕ) : ℝ) * gamma μ * t ^ 3 / 6)| ≤
      |H| * t + ((n - 1 : ℕ) : ℝ) * g * t ^ 3 / 6 := by
  have hb0 : (0 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  calc
    _ ≤ |H * t + ((n - 1 : ℕ) : ℝ) * gamma μ * t ^ 3 / 6| := Real.abs_sin_le_abs
    _ ≤ |H * t| + |((n - 1 : ℕ) : ℝ) * gamma μ * t ^ 3 / 6| := abs_add_le _ _
    _ = |H| * t + ((n - 1 : ℕ) : ℝ) * |gamma μ| * t ^ 3 / 6 := by
      rw [abs_div, abs_mul, abs_mul, abs_mul, abs_of_nonneg ht,
        abs_of_nonneg hb0, abs_of_nonneg (pow_nonneg ht 3)]
      norm_num
    _ ≤ _ := by
      exact add_le_add (le_refl _) (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg hb0) (pow_nonneg ht 3)) (by norm_num))

lemma leadingIntegrand_bound (μ : ProbabilityMeasure ℝ) (n : ℕ) (H t g aStar Z : ℝ)
    (ht : 0 < t) (hg : |gamma μ| ≤ g) (ha : |quarticCoeff μ| ≤ aStar) (hZ : |fifthCoeff μ| ≤ Z) :
    leadingIntegrand μ n H t ≤
      ((n : ℝ) * (Z + aStar * |H|)) *
        (t ^ 2 * Real.exp (-(((n - 1 : ℕ) : ℝ) / 2 * t ^ 2))) +
      ((n : ℝ) * aStar * ((n - 1 : ℕ) : ℝ) * g / 6) *
        (t ^ 4 * Real.exp (-(((n - 1 : ℕ) : ℝ) / 2 * t ^ 2))) := by
  have ha0 : 0 ≤ aStar := (abs_nonneg _).trans ha
  have hz0 : 0 ≤ Z := (abs_nonneg _).trans hZ
  have hg0 : 0 ≤ g := (abs_nonneg _).trans hg
  have hb0 : (0 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  have hphase := sin_le_phase_price μ n H t g ht.le hg
  have hap : |quarticCoeff μ * t ^ 4| ≤ aStar * t ^ 4 := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg ht.le 4)]
    exact mul_le_mul_of_nonneg_right ha (pow_nonneg ht.le 4)
  have hzp : |fifthCoeff μ * t ^ 5| ≤ Z * t ^ 5 := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg ht.le 5)]
    exact mul_le_mul_of_nonneg_right hZ (pow_nonneg ht.le 5)
  have htrig : |quarticCoeff μ * t ^ 4 * Real.sin (H * t + ((n - 1 : ℕ) : ℝ) * gamma μ * t ^ 3 / 6) -
      fifthCoeff μ * t ^ 5 * Real.cos (H * t + ((n - 1 : ℕ) : ℝ) * gamma μ * t ^ 3 / 6)| ≤
      aStar * t ^ 4 * (|H| * t + ((n - 1 : ℕ) : ℝ) * g * t ^ 3 / 6) + Z * t ^ 5 := by
    calc
      _ ≤ |quarticCoeff μ * t ^ 4 * Real.sin _| + |fifthCoeff μ * t ^ 5 * Real.cos _| := abs_sub _ _
      _ = |quarticCoeff μ * t ^ 4| *
          |Real.sin (H * t + ((n - 1 : ℕ) : ℝ) * gamma μ * t ^ 3 / 6)| +
          |fifthCoeff μ * t ^ 5| *
          |Real.cos (H * t + ((n - 1 : ℕ) : ℝ) * gamma μ * t ^ 3 / 6)| := by
        simp only [abs_mul]
      _ ≤ aStar * t ^ 4 * (|H| * t + ((n - 1 : ℕ) : ℝ) * g * t ^ 3 / 6) + (Z * t ^ 5) * 1 :=
        add_le_add (mul_le_mul hap hphase (abs_nonneg _) (by positivity))
          (mul_le_mul hzp (Real.abs_cos_le_one _) (abs_nonneg _) (by positivity))
      _ = _ := by ring
  have him := mul_le_mul_of_nonneg_left htrig
    (show 0 ≤ (n : ℝ) * Real.exp (-(((n - 1 : ℕ) : ℝ) / 2 * t ^ 2)) by positivity)
  unfold leadingIntegrand
  rw [leading_rotation_im, abs_mul, abs_of_nonneg (show 0 ≤ (n : ℝ) * Real.exp _ by positivity)]
  have hd := div_le_div_of_nonneg_right him (pow_nonneg ht.le 3)
  convert hd using 1
  field_simp [ne_of_gt ht]
  ring

end BerryEsseen.LowFrequencyLeading

#print axioms BerryEsseen.LowFrequencyLeading.gaussian_rotation_cost
#print axioms BerryEsseen.LowFrequencyLeading.leadingIntegrand_bound

namespace BerryEsseen.LowFrequencyLeading

/-- The paper's F_n=(n/(n-1))^(3/2). -/
def factorF (n : ℕ) : ℝ := ((n : ℝ) / ((n : ℝ) - 1)) ^ (3 / 2 : ℝ)

lemma factorF_nonneg (n : ℕ) (hn : 2 < n) : 0 ≤ factorF n := by
  have hn0 : 0 < (n : ℝ) := Nat.cast_pos.mpr (by omega : 0 < n)
  have hn2 : (2 : ℝ) < (n : ℝ) := Nat.cast_lt.mpr hn
  exact Real.rpow_nonneg (div_nonneg hn0.le (by linarith)) _

lemma factorF_eq (n : ℕ) (hn : 2 < n) :
    factorF n = (n : ℝ) * Real.sqrt n / (((n : ℝ) - 1) * Real.sqrt ((n : ℝ) - 1)) := by
  have hn0 : 0 < (n : ℝ) := Nat.cast_pos.mpr (by omega : 0 < n)
  have hn2 : (2 : ℝ) < (n : ℝ) := Nat.cast_lt.mpr hn
  have hb : 0 < (n : ℝ) - 1 := by linarith
  unfold factorF
  rw [Real.rpow_div_two_eq_sqrt _ (div_nonneg hn0.le hb.le), Real.sqrt_div hn0.le, Real.rpow_ofNat,
    div_pow]
  rw [show (3 : ℕ) = 2 * 1 + 1 by norm_num, sqrt_odd_power _ hn0.le, sqrt_odd_power _ hb.le]
  simp only [pow_one]

/-- The actual leading term gives exactly the paper's triangle coefficients. -/
theorem leading_triangle_cost (μ : ProbabilityMeasure ℝ) (n : ℕ) (hn : 2 < n) (H g aStar Z Iu : ℝ)
    (hg : |gamma μ| ≤ g) (ha : |quarticCoeff μ| ≤ aStar) (hZ : |fifthCoeff μ| ≤ Z)
    (hIu : gaussianMass ≤ Iu) :
    IntegrableOn (leadingIntegrand μ n H) (Ioc (0 : ℝ) (1 / 2)) ∧
    Real.sqrt n * (∫ t in Ioc (0 : ℝ) (1 / 2), leadingIntegrand μ n H t) ≤
      Iu * factorF n * (Z + aStar * g / 2) + Iu * factorF n * aStar * |H| := by
  have hn0 : 0 < (n : ℝ) := Nat.cast_pos.mpr (by omega : 0 < n)
  have hn2 : (2 : ℝ) < (n : ℝ) := Nat.cast_lt.mpr hn
  have hb : 0 < (n : ℝ) - 1 := by linarith
  have hpred : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub (by omega : 1 ≤ n)]; norm_num
  have ha0 : 0 ≤ aStar := (abs_nonneg _).trans ha
  have hz0 : 0 ≤ Z := (abs_nonneg _).trans hZ
  have hg0 : 0 ≤ g := (abs_nonneg _).trans hg
  have hcost := two_gaussian_cost (leadingIntegrand μ n H) (measurable_leadingIntegrand μ n H) 2 4
    ((n : ℝ) * (Z + aStar * |H|)) ((n : ℝ) * aStar * ((n : ℝ) - 1) * g / 6) (((n : ℝ) - 1) / 2)
    (by positivity) (by positivity) (by positivity)
    (fun t ht => leadingIntegrand_nonneg μ n H t ht.1.le)
    (fun t ht => by simpa only [hpred] using leadingIntegrand_bound μ n H t g aStar Z ht.1 hg ha hZ)
  refine ⟨hcost.1, ?_⟩
  rw [integral_even_gaussian_two _ hb, integral_even_gaussian_four _ hb] at hcost
  calc
    _ ≤ Real.sqrt n * (((n : ℝ) * (Z + aStar * |H|)) *
        (gaussianMass / (((n : ℝ) - 1) * Real.sqrt ((n : ℝ) - 1))) +
        ((n : ℝ) * aStar * ((n : ℝ) - 1) * g / 6) *
          (3 * gaussianMass / (((n : ℝ) - 1) ^ 2 * Real.sqrt ((n : ℝ) - 1)))) :=
      mul_le_mul_of_nonneg_left hcost.2 (Real.sqrt_nonneg _)
    _ = gaussianMass * factorF n * (Z + aStar * g / 2 + aStar * |H|) := by
      rw [factorF_eq n hn]
      field_simp [ne_of_gt hb, ne_of_gt (Real.sqrt_pos.mpr hb)]
      ring
    _ ≤ Iu * factorF n * (Z + aStar * g / 2 + aStar * |H|) := by
      have hh := mul_le_mul_of_nonneg_right hIu
        (show 0 ≤ factorF n * (Z + aStar * g / 2 + aStar * |H|) by
          exact mul_nonneg (factorF_nonneg n hn) (by positivity))
      convert hh using 1 <;> ring
    _ = _ := by ring

/-- V_n is the original actual-CF expression, with the exact Gaussian correction. -/
def actualV (μ : ProbabilityMeasure ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  charFun (μ : Measure ℝ) t ^ n - gaussianComparator μ n t

def lowIntegrand (μ : ProbabilityMeasure ℝ) (n : ℕ) (H t : ℝ) : ℝ :=
  |(pureExp (-(H * t)) * actualV μ n t).im| / t ^ 3

/-- I₀(n,H) from ut:low, for the original n and H. -/
def I0 (μ : ProbabilityMeasure ℝ) (n : ℕ) (H : ℝ) : ℝ :=
  ∫ t in Ioc (0 : ℝ) (1 / 2), lowIntegrand μ n H t

lemma measurable_lowIntegrand (μ : ProbabilityMeasure ℝ) (n : ℕ) (H : ℝ) :
    Measurable (lowIntegrand μ n H) := by
  have hf := measurable_actual_charFun μ
  unfold lowIntegrand actualV gaussianComparator pureExp
  fun_prop

lemma lowIntegrand_nonneg (μ : ProbabilityMeasure ℝ) (n : ℕ) (H t : ℝ) (ht : 0 ≤ t) :
    0 ≤ lowIntegrand μ n H t := by unfold lowIntegrand; positivity

lemma actualV_decomposition (μ : ProbabilityMeasure ℝ) (n : ℕ) (t : ℝ) :
    actualV μ n t = leadingTerm μ n t +
      (n : ℂ) * actualR6 μ t * comparator μ t ^ (n - 1) + actualR2 μ n t + gaussianDifference μ n t := by
  have hp := actual_power_decomposition μ n t
  unfold actualV gaussianDifference leadingTerm
  calc
    _ = (charFun (μ : Measure ℝ) t ^ n - comparator μ t ^ n) +
        (comparator μ t ^ n - gaussianComparator μ n t) := by ring
    _ = _ := by rw [hp]

lemma rotated_im_le_norm (v : ℝ) (z : ℂ) : |(pureExp v * z).im| ≤ ‖z‖ := by
  calc
    _ ≤ ‖pureExp v * z‖ := Complex.abs_im_le_norm _
    _ = _ := by rw [norm_mul, norm_pureExp, one_mul]

lemma lowIntegrand_bound (μ : ProbabilityMeasure ℝ) (n : ℕ) (H t : ℝ) (ht : 0 < t) :
    lowIntegrand μ n H t ≤ leadingIntegrand μ n H t + rotatedGaussianIntegrand μ n H t +
      firstIntegrand μ n t + secondIntegrand μ n t := by
  have hfirst := rotated_im_le_norm (-(H * t))
    ((n : ℂ) * actualR6 μ t * comparator μ t ^ (n - 1))
  have hsecond := rotated_im_le_norm (-(H * t)) (actualR2 μ n t)
  have hb : |(pureExp (-(H * t)) * actualV μ n t).im| ≤
      |(pureExp (-(H * t)) * leadingTerm μ n t).im| +
      |(pureExp (-(H * t)) * gaussianDifference μ n t).im| +
      (n : ℝ) * ‖actualR6 μ t * comparator μ t ^ (n - 1)‖ + ‖actualR2 μ n t‖ := by
    rw [actualV_decomposition]
    simp only [mul_add, Complex.add_im]
    have habs := abs_add_le
      ((pureExp (-(H * t)) * leadingTerm μ n t).im +
        (pureExp (-(H * t)) * ((n : ℂ) * actualR6 μ t * comparator μ t ^ (n - 1))).im +
        (pureExp (-(H * t)) * actualR2 μ n t).im)
      ((pureExp (-(H * t)) * gaussianDifference μ n t).im)
    have habs2 := abs_add_le
      ((pureExp (-(H * t)) * leadingTerm μ n t).im +
        (pureExp (-(H * t)) * ((n : ℂ) * actualR6 μ t * comparator μ t ^ (n - 1))).im)
      ((pureExp (-(H * t)) * actualR2 μ n t).im)
    have habs3 := abs_add_le ((pureExp (-(H * t)) * leadingTerm μ n t).im)
      ((pureExp (-(H * t)) * ((n : ℂ) * actualR6 μ t * comparator μ t ^ (n - 1))).im)
    have heq : ‖(n : ℂ) * actualR6 μ t * comparator μ t ^ (n - 1)‖ =
        (n : ℝ) * ‖actualR6 μ t * comparator μ t ^ (n - 1)‖ := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_natCast]
      ring
    rw [heq] at hfirst
    linarith
  have hd := div_le_div_of_nonneg_right hb (pow_nonneg ht.le 3)
  change |(pureExp (-(H * t)) * actualV μ n t).im| / t ^ 3 ≤ _
  convert hd using 1
  unfold leadingIntegrand rotatedGaussianIntegrand firstIntegrand secondIntegrand
  ring

end BerryEsseen.LowFrequencyLeading

#print axioms BerryEsseen.LowFrequencyLeading.leading_triangle_cost
#print axioms BerryEsseen.LowFrequencyLeading.lowIntegrand_bound

namespace BerryEsseen.LowFrequencyLeading

/-- The triangle candidate coefficients, with the manuscript's original constants. -/
def triangleL0 (n : ℕ) (g aStar Z Iu : ℝ) : ℝ :=
  Iu * factorF n * (Z + aStar * g / 2) + 251 * g ^ 3 / 17280

def triangleLH (n : ℕ) (g aStar Iu : ℝ) : ℝ :=
  Iu * factorF n * aStar + 251 * g ^ 2 / 4800

/-- Full triangle alternative in ut:low for an actual standardized law, including L¹.
No restriction on the original threshold H or bounded-support restriction is introduced. -/
theorem low_frequency_triangle (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (h6 : Integrable (fun x : ℝ => |x| ^ 6) (μ : Measure ℝ)) (n : ℕ) (hn : 2 < n)
    (H g M M6bar aStar Z Iu : ℝ) (hg : |gamma μ| ≤ g) (hgcap : g ≤ 37 / 20)
    (hM4 : moment μ 4 ≤ M) (hMupper : M ≤ 111 / 10) (hM6 : sixthMoment μ ≤ M6bar)
    (ha : |quarticCoeff μ| ≤ aStar) (hZ : |fifthCoeff μ| ≤ Z) (hIu : gaussianMass ≤ Iu) :
    IntegrableOn (lowIntegrand μ n H) (Ioc (0 : ℝ) (1 / 2)) ∧
    Real.sqrt n * I0 μ n H ≤ triangleL0 n g aStar Z Iu + triangleLH n g aStar Iu * |H| +
      coefficientL2 n M g M6bar aStar Z / Real.sqrt n := by
  have hnNat : 0 < n := by omega
  have hn0 : 0 < (n : ℝ) := Nat.cast_pos.mpr hnNat
  have hs0 : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
  have hlead := leading_triangle_cost μ n hn H g aStar Z Iu hg ha hZ hIu
  have hrotation := gaussian_rotation_cost μ n hnNat H g hg
  have hfirst := first_error_cost μ h h6 n hn g M6bar hg hgcap hM6
  have hsecond := second_error_cost μ h h6 n hn g M M6bar aStar Z hg hgcap hM4 hMupper hM6 ha hZ
  have hmajor : IntegrableOn (fun t => leadingIntegrand μ n H t + rotatedGaussianIntegrand μ n H t +
      firstIntegrand μ n t + secondIntegrand μ n t) (Ioc (0 : ℝ) (1 / 2)) :=
    ((hlead.1.add hrotation.1).add hfirst.1).add hsecond.1
  have hi : IntegrableOn (lowIntegrand μ n H) (Ioc (0 : ℝ) (1 / 2)) := by
    apply hmajor.mono' (measurable_lowIntegrand μ n H).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (lowIntegrand_nonneg μ n H t ht.1.le)]
    exact lowIntegrand_bound μ n H t ht.1
  refine ⟨hi, ?_⟩
  have htotal : I0 μ n H ≤
      (∫ t in Ioc (0 : ℝ) (1 / 2), leadingIntegrand μ n H t) +
      (∫ t in Ioc (0 : ℝ) (1 / 2), rotatedGaussianIntegrand μ n H t) +
      (∫ t in Ioc (0 : ℝ) (1 / 2), firstIntegrand μ n t) +
      (∫ t in Ioc (0 : ℝ) (1 / 2), secondIntegrand μ n t) := by
    unfold I0
    calc
      _ ≤ ∫ t in Ioc (0 : ℝ) (1 / 2), leadingIntegrand μ n H t + rotatedGaussianIntegrand μ n H t +
          firstIntegrand μ n t + secondIntegrand μ n t := by
        apply integral_mono_ae hi hmajor
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        exact lowIntegrand_bound μ n H t ht.1
      _ = _ := by
        have hlr : IntegrableOn (fun t => leadingIntegrand μ n H t + rotatedGaussianIntegrand μ n H t)
            (Ioc (0 : ℝ) (1 / 2)) := hlead.1.add hrotation.1
        have hlrf : IntegrableOn (fun t => leadingIntegrand μ n H t + rotatedGaussianIntegrand μ n H t +
            firstIntegrand μ n t) (Ioc (0 : ℝ) (1 / 2)) := hlr.add hfirst.1
        rw [integral_add hlrf hsecond.1, integral_add hlr hfirst.1, integral_add hlead.1 hrotation.1]
  have herror : (∫ t in Ioc (0 : ℝ) (1 / 2), firstIntegrand μ n t) +
      (∫ t in Ioc (0 : ℝ) (1 / 2), secondIntegrand μ n t) ≤
        coefficientL2 n M g M6bar aStar Z / (n : ℝ) := by
    calc
      _ ≤ sixthPrice g M6bar / (2 * (n : ℝ) * rateA n ^ 2) +
          totalSixthPrice aStar Z (sixthPrice g M6bar) ^ 2 / (2 * (n : ℝ) * rateB n M ^ 3) :=
        add_le_add hfirst.2 hsecond.2
      _ = _ := by unfold coefficientL2; ring
  have heq : Real.sqrt n * (coefficientL2 n M g M6bar aStar Z / (n : ℝ)) =
      coefficientL2 n M g M6bar aStar Z / Real.sqrt n := by
    apply (eq_div_iff (ne_of_gt hs0)).mpr
    field_simp [ne_of_gt hn0]
    ring_nf
    rw [Real.sq_sqrt hn0.le]
    ring
  have herr := (mul_le_mul_of_nonneg_left herror hs0.le).trans_eq heq
  calc
    _ ≤ Real.sqrt n * (∫ t in Ioc (0 : ℝ) (1 / 2), leadingIntegrand μ n H t) +
        Real.sqrt n * (∫ t in Ioc (0 : ℝ) (1 / 2), rotatedGaussianIntegrand μ n H t) +
        Real.sqrt n * ((∫ t in Ioc (0 : ℝ) (1 / 2), firstIntegrand μ n t) +
          (∫ t in Ioc (0 : ℝ) (1 / 2), secondIntegrand μ n t)) := by
      convert mul_le_mul_of_nonneg_left htotal hs0.le using 1
      ring
    _ ≤ (Iu * factorF n * (Z + aStar * g / 2) + Iu * factorF n * aStar * |H|) +
        (251 * g ^ 3 / 17280 + 251 * g ^ 2 * |H| / 4800) +
        coefficientL2 n M g M6bar aStar Z / Real.sqrt n :=
      add_le_add (add_le_add hlead.2 hrotation.2) herr
    _ = _ := by unfold triangleL0 triangleLH; ring

lemma I0_eq_interval (μ : ProbabilityMeasure ℝ) (n : ℕ) (H : ℝ) :
    I0 μ n H = ∫ t in (0 : ℝ)..(1 / 2), lowIntegrand μ n H t := by
  exact (intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)).symm

/-- The original signed imaginary quotient is absolutely integrable as well. -/
theorem low_frequency_signed_integrable (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (h6 : Integrable (fun x : ℝ => |x| ^ 6) (μ : Measure ℝ)) (n : ℕ) (hn : 2 < n)
    (H g M M6bar aStar Z Iu : ℝ) (hg : |gamma μ| ≤ g) (hgcap : g ≤ 37 / 20)
    (hM4 : moment μ 4 ≤ M) (hMupper : M ≤ 111 / 10) (hM6 : sixthMoment μ ≤ M6bar)
    (ha : |quarticCoeff μ| ≤ aStar) (hZ : |fifthCoeff μ| ≤ Z) (hIu : gaussianMass ≤ Iu) :
    IntegrableOn (fun t => (pureExp (-(H * t)) * actualV μ n t).im / t ^ 3)
      (Ioc (0 : ℝ) (1 / 2)) := by
  have hi := (low_frequency_triangle μ h h6 n hn H g M M6bar aStar Z Iu hg hgcap hM4 hMupper hM6 ha hZ hIu).1
  have hm : Measurable (fun t => (pureExp (-(H * t)) * actualV μ n t).im / t ^ 3) := by
    have hf := measurable_actual_charFun μ
    unfold actualV gaussianComparator pureExp
    fun_prop
  apply hi.mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  simp only [Real.norm_eq_abs, abs_div, abs_of_nonneg (pow_nonneg ht.1.le 3), lowIntegrand]
  exact le_rfl

end BerryEsseen.LowFrequencyLeading

#print axioms BerryEsseen.LowFrequencyLeading.low_frequency_triangle
#print axioms BerryEsseen.LowFrequencyLeading.low_frequency_signed_integrable


namespace BerryEsseen.LowFrequencyLeading

/-- Identification with the manuscript's complex-exponential Gaussian correction. -/
lemma gaussianComparator_eq_original (μ : ProbabilityMeasure ℝ) (n : ℕ) (t : ℝ) :
    gaussianComparator μ n t = Complex.exp (-(((n : ℝ) * t ^ 2 / 2 : ℝ) : ℂ)) *
      (1 - Complex.I * (((n : ℝ) * gamma μ * t ^ 3 / 6 : ℝ) : ℂ)) := by
  unfold gaussianComparator
  rw [Complex.ofReal_exp]
  congr 2
  push_cast
  ring

lemma phase_eq_original (H t : ℝ) :
    pureExp (-(H * t)) = Complex.exp (-Complex.I * (t : ℂ) * (H : ℂ)) := by
  unfold pureExp
  congr 1
  push_cast
  ring

lemma actualV_eq_original (μ : ProbabilityMeasure ℝ) (n : ℕ) (t : ℝ) :
    actualV μ n t = charFun (μ : Measure ℝ) t ^ n -
      Complex.exp (-(((n : ℝ) * t ^ 2 / 2 : ℝ) : ℂ)) *
        (1 - Complex.I * (((n : ℝ) * gamma μ * t ^ 3 / 6 : ℝ) : ℂ)) := by
  unfold actualV
  rw [gaussianComparator_eq_original]

end BerryEsseen.LowFrequencyLeading
