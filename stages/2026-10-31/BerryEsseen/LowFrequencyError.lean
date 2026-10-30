module

public import BerryEsseen.CharacteristicExpansion
public import Mathlib.MeasureTheory.Integral.Gamma

@[expose] public section

/-! 2026-10-28: actual-law second-order power error and complete low-frequency
L2 costs. The pointwise CF inputs are proved in CharacteristicExpansion;
all improper Gaussian majorants and original quotients are genuinely integrable. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators Interval
open BerryEsseen.CharacteristicExpansion

namespace BerryEsseen.LowFrequencyError

/-- Index k represents the power n=k+2, avoiding truncated subtraction in the induction. -/
def powerErrorAux (z w : ℂ) (k : ℕ) : ℂ :=
  z ^ (k + 2) - w ^ (k + 2) - ((k + 2 : ℕ) : ℂ) * (z - w) * w ^ (k + 1)

lemma powerErrorAux_zero (z w : ℂ) : powerErrorAux z w 0 = (z - w) ^ 2 := by
  norm_num [powerErrorAux]; ring

lemma powerErrorAux_succ (z w : ℂ) (k : ℕ) :
    powerErrorAux z w (k + 1) = z * powerErrorAux z w k +
      ((k + 2 : ℕ) : ℂ) * (z - w) ^ 2 * w ^ (k + 1) := by
  simp only [powerErrorAux, pow_succ, Nat.cast_add, Nat.cast_ofNat]
  ring

/-- The sharp n(n-1)/2 power remainder, proved by its exact algebraic recurrence. -/
theorem norm_powerErrorAux (z w : ℂ) (r : ℝ) (hr : 0 ≤ r) (hz : ‖z‖ ≤ r) (hw : ‖w‖ ≤ r) (k : ℕ) :
    ‖powerErrorAux z w k‖ ≤ ((k + 2 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) / 2 * ‖z - w‖ ^ 2 * r ^ k := by
  induction k with
  | zero =>
    rw [powerErrorAux_zero, norm_pow]
    norm_num
  | succ k ih =>
    rw [powerErrorAux_succ]
    have hleft : ‖z‖ * ‖powerErrorAux z w k‖ ≤ r *
        (((k + 2 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) / 2 * ‖z - w‖ ^ 2 * r ^ k) := by
      calc
        _ ≤ r * ‖powerErrorAux z w k‖ := mul_le_mul_of_nonneg_right hz (norm_nonneg _)
        _ ≤ _ := mul_le_mul_of_nonneg_left ih hr
    have hright : ((k + 2 : ℕ) : ℝ) * ‖z - w‖ ^ 2 * ‖w‖ ^ (k + 1) ≤
        ((k + 2 : ℕ) : ℝ) * ‖z - w‖ ^ 2 * r ^ (k + 1) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hw (k + 1)) (by positivity)
    calc
      _ ≤ ‖z * powerErrorAux z w k‖ + ‖((k + 2 : ℕ) : ℂ) * (z - w) ^ 2 * w ^ (k + 1)‖ := norm_add_le _ _
      _ = ‖z‖ * ‖powerErrorAux z w k‖ + ((k + 2 : ℕ) : ℝ) * ‖z - w‖ ^ 2 * ‖w‖ ^ (k + 1) := by
        simp only [norm_mul, norm_pow, Complex.norm_natCast]
      _ ≤ _ := add_le_add hleft hright
      _ = _ := by
        simp only [pow_succ, Nat.cast_add, Nat.cast_ofNat]
        ring

def powerError (z w : ℂ) (n : ℕ) : ℂ := z ^ n - w ^ n - (n : ℂ) * (z - w) * w ^ (n - 1)

lemma norm_powerError_sharp (z w : ℂ) (r : ℝ) (hr : 0 ≤ r) (hz : ‖z‖ ≤ r) (hw : ‖w‖ ≤ r)
    (n : ℕ) (hn : 2 ≤ n) :
    ‖powerError z w n‖ ≤ (n : ℝ) * ((n - 1 : ℕ) : ℝ) / 2 * ‖z - w‖ ^ 2 * r ^ (n - 2) := by
  have h := norm_powerErrorAux z w r hr hz hw (n - 2)
  have hshape : n - 2 + 2 = n := Nat.sub_add_cancel hn
  have hpred : n - 2 + 1 = n - 1 := by omega
  simpa only [powerErrorAux, powerError, hshape, hpred] using h

lemma norm_powerError_nsq (z w : ℂ) (r : ℝ) (hr : 0 ≤ r) (hz : ‖z‖ ≤ r) (hw : ‖w‖ ≤ r)
    (n : ℕ) (hn : 2 ≤ n) :
    ‖powerError z w n‖ ≤ (n : ℝ) ^ 2 / 2 * ‖z - w‖ ^ 2 * r ^ (n - 2) := by
  have hc : (n : ℝ) * ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 := by
    have hp : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr (Nat.sub_le n 1)
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hm := mul_le_mul_of_nonneg_left hp hn0
    nlinarith [hm]
  have hweight : 0 ≤ ‖z - w‖ ^ 2 * r ^ (n - 2) := mul_nonneg (sq_nonneg _) (pow_nonneg hr _)
  calc
    _ ≤ (n : ℝ) * ((n - 1 : ℕ) : ℝ) / 2 * ‖z - w‖ ^ 2 * r ^ (n - 2) :=
      norm_powerError_sharp z w r hr hz hw n hn
    _ ≤ _ := by
      have hm := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hc (by norm_num : (0 : ℝ) ≤ 2)) hweight
      convert hm using 1 <;> ring

def rateA (n : ℕ) : ℝ := ((n : ℝ) - 1) / (2 * (n : ℝ))
def rateB (n : ℕ) (M : ℝ) : ℝ := ((45 - M) / 96) * (1 - 2 / (n : ℝ))
def totalSixthPrice (aStar Z E6 : ℝ) : ℝ := aStar + Z / 2 + E6 / 4

def actualR6 (μ : ProbabilityMeasure ℝ) (t : ℝ) : ℂ :=
  charFun (μ : Measure ℝ) t - comparator μ t + ((quarticCoeff μ * t ^ 4 : ℝ) : ℂ) +
    Complex.I * ((fifthCoeff μ * t ^ 5 : ℝ) : ℂ)

def actualR2 (μ : ProbabilityMeasure ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  powerError (charFun (μ : Measure ℝ) t) (comparator μ t) n

lemma sixthPrice_nonneg (g M6bar : ℝ) (hM6 : 0 ≤ M6bar) : 0 ≤ sixthPrice g M6bar := by
  unfold sixthPrice
  positivity

lemma totalSixthPrice_nonneg (aStar Z E6 : ℝ) (ha : 0 ≤ aStar) (hZ : 0 ≤ Z) (hE : 0 ≤ E6) :
    0 ≤ totalSixthPrice aStar Z E6 := by unfold totalSixthPrice; positivity

lemma rateA_pos (n : ℕ) (hn : 2 < n) : 0 < rateA n := by
  have hnr : (2 : ℝ) < (n : ℝ) := Nat.cast_lt.mpr hn
  unfold rateA
  exact div_pos (by linarith) (by linarith)

lemma rateB_pos (n : ℕ) (hn : 2 < n) (M : ℝ) (hM : M ≤ 111 / 10) : 0 < rateB n M := by
  have hnr : (2 : ℝ) < (n : ℝ) := Nat.cast_lt.mpr hn
  have hn0 : 0 < (n : ℝ) := by linarith
  have hfrac : 2 / (n : ℝ) < 1 := (div_lt_one hn0).mpr hnr
  unfold rateB
  apply mul_pos (by linarith) (by linarith)

end BerryEsseen.LowFrequencyError

#print axioms BerryEsseen.LowFrequencyError.norm_powerErrorAux
#print axioms BerryEsseen.LowFrequencyError.norm_powerError_nsq

namespace BerryEsseen.LowFrequencyError

lemma actualR6_bound (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (h6 : Integrable (fun x : ℝ => |x| ^ 6) (μ : Measure ℝ)) (t g M6bar : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) (hg : |gamma μ| ≤ g) (hgcap : g ≤ 37 / 20)
    (hcap : sixthMoment μ ≤ M6bar) : ‖actualR6 μ t‖ ≤ sixthPrice g M6bar * t ^ 6 :=
  low_frequency_expansion μ h h6 t g M6bar ht0 ht1 hg hgcap hcap

/-- The true CF-comparator gap, derived from the actual r6, a, and z5 coefficients. -/
theorem actual_gap_bound (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (h6 : Integrable (fun x : ℝ => |x| ^ 6) (μ : Measure ℝ)) (t g M6bar aStar Z : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) (hg : |gamma μ| ≤ g) (hgcap : g ≤ 37 / 20)
    (hcap : sixthMoment μ ≤ M6bar) (ha : |quarticCoeff μ| ≤ aStar) (hZ : |fifthCoeff μ| ≤ Z) :
    ‖charFun (μ : Measure ℝ) t - comparator μ t‖ ≤
      totalSixthPrice aStar Z (sixthPrice g M6bar) * t ^ 4 := by
  have ha0 : 0 ≤ aStar := (abs_nonneg _).trans ha
  have hZ0 : 0 ≤ Z := (abs_nonneg _).trans hZ
  have hE : 0 ≤ sixthPrice g M6bar := sixthPrice_nonneg g M6bar ((sixthMoment_nonneg μ).trans hcap)
  have ht2 : t ^ 2 ≤ (1 : ℝ) / 4 := by nlinarith [mul_nonneg ht0 (show 0 ≤ 1 / 2 - t by linarith)]
  have ht6 : t ^ 6 ≤ t ^ 4 / 4 := by
    have hm := mul_le_mul_of_nonneg_right ht2 (pow_nonneg ht0 4)
    nlinarith
  have ht5 : t ^ 5 ≤ t ^ 4 / 2 := by
    have hm := mul_le_mul_of_nonneg_right ht1 (pow_nonneg ht0 4)
    nlinarith
  have hA : ‖((quarticCoeff μ * t ^ 4 : ℝ) : ℂ)‖ ≤ aStar * t ^ 4 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg ht0]
    exact mul_le_mul_of_nonneg_right ha (pow_nonneg ht0 4)
  have hF : ‖Complex.I * ((fifthCoeff μ * t ^ 5 : ℝ) : ℂ)‖ ≤ Z * t ^ 5 := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg ht0]
    exact mul_le_mul_of_nonneg_right hZ (pow_nonneg ht0 5)
  have heq : charFun (μ : Measure ℝ) t - comparator μ t = actualR6 μ t -
      ((quarticCoeff μ * t ^ 4 : ℝ) : ℂ) - Complex.I * ((fifthCoeff μ * t ^ 5 : ℝ) : ℂ) := by
    unfold actualR6
    ring
  rw [heq]
  calc
    _ ≤ ‖actualR6 μ t - ((quarticCoeff μ * t ^ 4 : ℝ) : ℂ)‖ +
        ‖Complex.I * ((fifthCoeff μ * t ^ 5 : ℝ) : ℂ)‖ := norm_sub_le _ _
    _ ≤ (‖actualR6 μ t‖ + ‖((quarticCoeff μ * t ^ 4 : ℝ) : ℂ)‖) +
        ‖Complex.I * ((fifthCoeff μ * t ^ 5 : ℝ) : ℂ)‖ := add_le_add (norm_sub_le _ _) (le_refl _)
    _ ≤ (sixthPrice g M6bar * t ^ 6 + aStar * t ^ 4) + Z * t ^ 5 :=
      add_le_add (add_le_add (actualR6_bound μ h h6 t g M6bar ht0 ht1 hg hgcap hcap) hA) hF
    _ ≤ (sixthPrice g M6bar * (t ^ 4 / 4) + aStar * t ^ 4) + Z * (t ^ 4 / 2) :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left ht6 hE) (le_refl _)) (mul_le_mul_of_nonneg_left ht5 hZ0)
    _ = _ := by unfold totalSixthPrice; ring

lemma damping_power_eq (n : ℕ) (hn : 2 < n) (M t : ℝ) :
    Real.exp (-((45 - M) / 96 * t ^ 2)) ^ (n - 2) = Real.exp (-(n : ℝ) * rateB n M * t ^ 2) := by
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr (by omega : 0 < n))
  rw [← Real.exp_nat_mul]
  congr 1
  rw [Nat.cast_sub (by omega : 2 ≤ n)]
  unfold rateB
  field_simp [hn0]
  ring

/-- The original actual-law second-order power remainder, with the original B_n exponent. -/
theorem actualR2_bound (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (h6 : Integrable (fun x : ℝ => |x| ^ 6) (μ : Measure ℝ)) (n : ℕ) (hn : 2 < n)
    (t g M M6bar aStar Z : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2)
    (hg : |gamma μ| ≤ g) (hgcap : g ≤ 37 / 20) (hM4 : moment μ 4 ≤ M) (hMupper : M ≤ 111 / 10)
    (hM6 : sixthMoment μ ≤ M6bar) (ha : |quarticCoeff μ| ≤ aStar) (hZ : |fifthCoeff μ| ≤ Z) :
    ‖actualR2 μ n t‖ ≤ ((n : ℝ) ^ 2 / 2) * totalSixthPrice aStar Z (sixthPrice g M6bar) ^ 2 *
      t ^ 8 * Real.exp (-(n : ℝ) * rateB n M * t ^ 2) := by
  have hT : 0 ≤ totalSixthPrice aStar Z (sixthPrice g M6bar) :=
    totalSixthPrice_nonneg _ _ _ ((abs_nonneg _).trans ha) ((abs_nonneg _).trans hZ)
      (sixthPrice_nonneg _ _ ((sixthMoment_nonneg μ).trans hM6))
  have hd := low_frequency_damping μ h (integrable_moment_of_sixth μ h6 4 (by decide)) t M ht0 ht1 hM4 hMupper
  have hgap := actual_gap_bound μ h h6 t g M6bar aStar Z ht0 ht1 hg hgcap hM6 ha hZ
  have hgap2 := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hT (pow_nonneg ht0 4))).mpr hgap
  have hbase := norm_powerError_nsq (charFun (μ : Measure ℝ) t) (comparator μ t)
    (Real.exp (-((45 - M) / 96 * t ^ 2))) (Real.exp_pos _).le hd.1 hd.2 n (by omega)
  change ‖actualR2 μ n t‖ ≤ _ at hbase
  calc
    _ ≤ (n : ℝ) ^ 2 / 2 * ‖charFun (μ : Measure ℝ) t - comparator μ t‖ ^ 2 *
        Real.exp (-((45 - M) / 96 * t ^ 2)) ^ (n - 2) := hbase
    _ ≤ (n : ℝ) ^ 2 / 2 * (totalSixthPrice aStar Z (sixthPrice g M6bar) * t ^ 4) ^ 2 *
        Real.exp (-((45 - M) / 96 * t ^ 2)) ^ (n - 2) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hgap2 (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 2 / 2)) (by positivity)
    _ = _ := by rw [damping_power_eq n hn M t]; ring

end BerryEsseen.LowFrequencyError

#print axioms BerryEsseen.LowFrequencyError.actual_gap_bound
#print axioms BerryEsseen.LowFrequencyError.actualR2_bound

namespace BerryEsseen.LowFrequencyError

/-- Measurability of the true CF is obtained from its actual parameter integral. -/
lemma stronglyMeasurable_actual_charFun (μ : ProbabilityMeasure ℝ) : StronglyMeasurable (charFun (μ : Measure ℝ)) := by
  have hc : Continuous (fun p : ℝ × ℝ => Complex.exp (((p.1 * p.2 : ℝ) : ℂ) * Complex.I)) := by fun_prop
  have hi := hc.stronglyMeasurable.integral_prod_right' (ν := (μ : Measure ℝ))
  have heq : charFun (μ : Measure ℝ) = (fun t : ℝ =>
      ∫ x : ℝ, Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) ∂(μ : Measure ℝ)) := by
    ext t
    rw [charFun_apply_real]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by simp only [Complex.ofReal_mul]
  rw [heq]
  exact hi

lemma measurable_actual_charFun (μ : ProbabilityMeasure ℝ) : Measurable (charFun (μ : Measure ℝ)) :=
  (stronglyMeasurable_actual_charFun μ).measurable

lemma measurable_comparator (μ : ProbabilityMeasure ℝ) : Measurable (comparator μ) := by
  unfold comparator exponent
  fun_prop

def firstIntegrand (μ : ProbabilityMeasure ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  (n : ℝ) * ‖actualR6 μ t * comparator μ t ^ (n - 1)‖ / t ^ 3

def secondIntegrand (μ : ProbabilityMeasure ℝ) (n : ℕ) (t : ℝ) : ℝ := ‖actualR2 μ n t‖ / t ^ 3

lemma measurable_firstIntegrand (μ : ProbabilityMeasure ℝ) (n : ℕ) : Measurable (firstIntegrand μ n) := by
  have hf := measurable_actual_charFun μ
  have hh := measurable_comparator μ
  unfold firstIntegrand actualR6
  fun_prop

lemma measurable_secondIntegrand (μ : ProbabilityMeasure ℝ) (n : ℕ) : Measurable (secondIntegrand μ n) := by
  have hf := measurable_actual_charFun μ
  have hh := measurable_comparator μ
  unfold secondIntegrand actualR2 powerError
  fun_prop

lemma integrable_gaussian_power (k : ℕ) (c : ℝ) (hc : 0 < c) :
    Integrable (fun t : ℝ => t ^ k * Real.exp (-(c * t ^ 2))) := by
  have hk : (-1 : ℝ) < (k : ℝ) := lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg k)
  simpa only [Real.rpow_natCast, neg_mul] using
    (integrable_rpow_mul_exp_neg_mul_sq (b := c) (s := (k : ℝ)) hc hk)

lemma integral_gaussian_cubic (c : ℝ) (hc : 0 < c) :
    (∫ t in Ioi 0, t ^ 3 * Real.exp (-(c * t ^ 2))) = 1 / (2 * c ^ 2) := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := (2 : ℝ)) (q := (3 : ℝ)) (b := c)
    (by norm_num) (by norm_num) hc
  norm_num [Real.rpow_ofNat, Real.rpow_neg hc.le, neg_mul] at h
  convert h using 1
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

lemma integral_gaussian_quintic (c : ℝ) (hc : 0 < c) :
    (∫ t in Ioi 0, t ^ 5 * Real.exp (-(c * t ^ 2))) = 1 / c ^ 3 := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := (2 : ℝ)) (q := (5 : ℝ)) (b := c)
    (by norm_num) (by norm_num) hc
  norm_num [Real.rpow_ofNat, Real.rpow_neg hc.le, neg_mul] at h
  convert h using 1
  simp only [div_eq_mul_inv]
  ring

lemma comparator_power_norm (μ : ProbabilityMeasure ℝ) (n : ℕ) (hn : 2 < n) (t : ℝ) :
    ‖comparator μ t ^ (n - 1)‖ = Real.exp (-(n : ℝ) * rateA n * t ^ 2) := by
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr (by omega : 0 < n))
  rw [norm_pow, norm_comparator, ← Real.exp_nat_mul]
  congr 1
  rw [Nat.cast_sub (by omega : 1 ≤ n)]
  unfold rateA
  field_simp [hn0]
  ring

end BerryEsseen.LowFrequencyError

#print axioms BerryEsseen.LowFrequencyError.integral_gaussian_cubic
#print axioms BerryEsseen.LowFrequencyError.integral_gaussian_quintic

namespace BerryEsseen.LowFrequencyError

lemma firstIntegrand_nonneg (μ : ProbabilityMeasure ℝ) (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ firstIntegrand μ n t := by unfold firstIntegrand; positivity

lemma secondIntegrand_nonneg (μ : ProbabilityMeasure ℝ) (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ secondIntegrand μ n t := by unfold secondIntegrand; positivity

/-- Division by t³ is made only at positive t, so this is a bound on the actual quotient. -/
lemma firstIntegrand_bound (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (h6 : Integrable (fun x : ℝ => |x| ^ 6) (μ : Measure ℝ)) (n : ℕ) (hn : 2 < n)
    (t g M6bar : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1 / 2)
    (hg : |gamma μ| ≤ g) (hgcap : g ≤ 37 / 20) (hM6 : sixthMoment μ ≤ M6bar) :
    firstIntegrand μ n t ≤ (n : ℝ) * sixthPrice g M6bar *
      (t ^ 3 * Real.exp (-((n : ℝ) * rateA n * t ^ 2))) := by
  have hr := actualR6_bound μ h h6 t g M6bar ht0.le ht1 hg hgcap hM6
  rw [firstIntegrand, norm_mul, comparator_power_norm μ n hn t]
  have hh := mul_le_mul_of_nonneg_right hr
    (Real.exp_pos (-(n : ℝ) * rateA n * t ^ 2)).le
  have hh' := mul_le_mul_of_nonneg_left hh (show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n)
  have hdiv := div_le_div_of_nonneg_right hh' (pow_nonneg ht0.le 3)
  convert hdiv using 1
  field_simp [ne_of_gt ht0]

lemma secondIntegrand_bound (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (h6 : Integrable (fun x : ℝ => |x| ^ 6) (μ : Measure ℝ)) (n : ℕ) (hn : 2 < n)
    (t g M M6bar aStar Z : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1 / 2)
    (hg : |gamma μ| ≤ g) (hgcap : g ≤ 37 / 20) (hM4 : moment μ 4 ≤ M) (hMupper : M ≤ 111 / 10)
    (hM6 : sixthMoment μ ≤ M6bar) (ha : |quarticCoeff μ| ≤ aStar) (hZ : |fifthCoeff μ| ≤ Z) :
    secondIntegrand μ n t ≤ ((n : ℝ) ^ 2 / 2) * totalSixthPrice aStar Z (sixthPrice g M6bar) ^ 2 *
      (t ^ 5 * Real.exp (-((n : ℝ) * rateB n M * t ^ 2))) := by
  have hr := actualR2_bound μ h h6 n hn t g M M6bar aStar Z ht0.le ht1 hg hgcap hM4 hMupper hM6 ha hZ
  have hdiv := div_le_div_of_nonneg_right hr (pow_nonneg ht0.le 3)
  change ‖actualR2 μ n t‖ / t ^ 3 ≤ _
  convert hdiv using 1
  field_simp [ne_of_gt ht0]

/-- The entire positive half-axis Gaussian integral controls the closed finite interval. -/
lemma integral_truncated_gaussian_le (k : ℕ) (c : ℝ) (hc : 0 < c) :
    (∫ t in Ioc (0 : ℝ) (1 / 2), t ^ k * Real.exp (-(c * t ^ 2))) ≤
      ∫ t in Ioi (0 : ℝ), t ^ k * Real.exp (-(c * t ^ 2)) := by
  apply setIntegral_mono_set (integrable_gaussian_power k c hc).integrableOn
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (pow_nonneg ht.le k) (Real.exp_pos _).le
  · exact Eventually.of_forall fun t ht => ht.1

lemma integrableOn_of_gaussian_bound (f : ℝ → ℝ) (hf : Measurable f) (k : ℕ) (C c : ℝ)
    (hc : 0 < c)
    (hb : ∀ t ∈ Ioc (0 : ℝ) (1 / 2), ‖f t‖ ≤ C * (t ^ k * Real.exp (-(c * t ^ 2)))) :
    IntegrableOn f (Ioc (0 : ℝ) (1 / 2)) := by
  apply ((integrable_gaussian_power k c hc).const_mul C).integrableOn.mono' hf.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact hb t ht

lemma integral_le_gaussian_price (f : ℝ → ℝ) (hf : IntegrableOn f (Ioc (0 : ℝ) (1 / 2)))
    (k : ℕ) (C c : ℝ) (hC : 0 ≤ C) (hc : 0 < c)
    (hb : ∀ t ∈ Ioc (0 : ℝ) (1 / 2), f t ≤ C * (t ^ k * Real.exp (-(c * t ^ 2)))) :
    (∫ t in Ioc (0 : ℝ) (1 / 2), f t) ≤ C *
      ∫ t in Ioi (0 : ℝ), t ^ k * Real.exp (-(c * t ^ 2)) := by
  calc
    _ ≤ ∫ t in Ioc (0 : ℝ) (1 / 2), C * (t ^ k * Real.exp (-(c * t ^ 2))) := by
      apply integral_mono_ae hf ((integrable_gaussian_power k c hc).const_mul C).integrableOn
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact hb t ht
    _ = C * (∫ t in Ioc (0 : ℝ) (1 / 2), t ^ k * Real.exp (-(c * t ^ 2))) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (integral_truncated_gaussian_le k c hc) hC

/-- Actual first error integrand is L¹; its Gaussian majorant has the exact paper price. -/
theorem first_error_cost (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (h6 : Integrable (fun x : ℝ => |x| ^ 6) (μ : Measure ℝ)) (n : ℕ) (hn : 2 < n)
    (g M6bar : ℝ) (hg : |gamma μ| ≤ g) (hgcap : g ≤ 37 / 20) (hM6 : sixthMoment μ ≤ M6bar) :
    IntegrableOn (firstIntegrand μ n) (Ioc (0 : ℝ) (1 / 2)) ∧
    (∫ t in Ioc (0 : ℝ) (1 / 2), firstIntegrand μ n t) ≤
      sixthPrice g M6bar / (2 * (n : ℝ) * rateA n ^ 2) := by
  have hn0 : 0 < (n : ℝ) := Nat.cast_pos.mpr (by omega : 0 < n)
  have hA := rateA_pos n hn
  have hE := sixthPrice_nonneg g M6bar ((sixthMoment_nonneg μ).trans hM6)
  have hb := fun t (ht : t ∈ Ioc (0 : ℝ) (1 / 2)) =>
    firstIntegrand_bound μ h h6 n hn t g M6bar ht.1 ht.2 hg hgcap hM6
  have hi : IntegrableOn (firstIntegrand μ n) (Ioc (0 : ℝ) (1 / 2)) := by
    apply integrableOn_of_gaussian_bound _ (measurable_firstIntegrand μ n) 3
      ((n : ℝ) * sixthPrice g M6bar) ((n : ℝ) * rateA n) (mul_pos hn0 hA)
    intro t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (firstIntegrand_nonneg μ n t ht.1.le)]
    exact hb t ht
  refine ⟨hi, ?_⟩
  have hp := integral_le_gaussian_price _ hi 3 ((n : ℝ) * sixthPrice g M6bar)
    ((n : ℝ) * rateA n) (mul_nonneg hn0.le hE) (mul_pos hn0 hA) hb
  rw [integral_gaussian_cubic _ (mul_pos hn0 hA)] at hp
  convert hp using 1
  field_simp [ne_of_gt hn0, ne_of_gt hA]

/-- Actual second power error is L¹ and has the exact original B_n cubic-denominator price. -/
theorem second_error_cost (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (h6 : Integrable (fun x : ℝ => |x| ^ 6) (μ : Measure ℝ)) (n : ℕ) (hn : 2 < n)
    (g M M6bar aStar Z : ℝ) (hg : |gamma μ| ≤ g) (hgcap : g ≤ 37 / 20)
    (hM4 : moment μ 4 ≤ M) (hMupper : M ≤ 111 / 10) (hM6 : sixthMoment μ ≤ M6bar)
    (ha : |quarticCoeff μ| ≤ aStar) (hZ : |fifthCoeff μ| ≤ Z) :
    IntegrableOn (secondIntegrand μ n) (Ioc (0 : ℝ) (1 / 2)) ∧
    (∫ t in Ioc (0 : ℝ) (1 / 2), secondIntegrand μ n t) ≤
      totalSixthPrice aStar Z (sixthPrice g M6bar) ^ 2 / (2 * (n : ℝ) * rateB n M ^ 3) := by
  have hn0 : 0 < (n : ℝ) := Nat.cast_pos.mpr (by omega : 0 < n)
  have hB := rateB_pos n hn M hMupper
  have hC : 0 ≤ (n : ℝ) ^ 2 / 2 * totalSixthPrice aStar Z (sixthPrice g M6bar) ^ 2 := by positivity
  have hb := fun t (ht : t ∈ Ioc (0 : ℝ) (1 / 2)) =>
    secondIntegrand_bound μ h h6 n hn t g M M6bar aStar Z ht.1 ht.2 hg hgcap hM4 hMupper hM6 ha hZ
  have hi : IntegrableOn (secondIntegrand μ n) (Ioc (0 : ℝ) (1 / 2)) := by
    apply integrableOn_of_gaussian_bound _ (measurable_secondIntegrand μ n) 5
      ((n : ℝ) ^ 2 / 2 * totalSixthPrice aStar Z (sixthPrice g M6bar) ^ 2)
      ((n : ℝ) * rateB n M) (mul_pos hn0 hB)
    intro t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (secondIntegrand_nonneg μ n t ht.1.le)]
    exact hb t ht
  refine ⟨hi, ?_⟩
  have hp := integral_le_gaussian_price _ hi 5
    ((n : ℝ) ^ 2 / 2 * totalSixthPrice aStar Z (sixthPrice g M6bar) ^ 2)
    ((n : ℝ) * rateB n M) hC (mul_pos hn0 hB) hb
  rw [integral_gaussian_quintic _ (mul_pos hn0 hB)] at hp
  convert hp using 1
  field_simp [ne_of_gt hn0, ne_of_gt hB]

end BerryEsseen.LowFrequencyError

#print axioms BerryEsseen.LowFrequencyError.first_error_cost
#print axioms BerryEsseen.LowFrequencyError.second_error_cost

namespace BerryEsseen.LowFrequencyError

/-- Exactly the L₂ coefficient in ut:low, with physical input prices held fixed. -/
def coefficientL2 (n : ℕ) (M g M6bar aStar Z : ℝ) : ℝ :=
  sixthPrice g M6bar / (2 * rateA n ^ 2) +
  totalSixthPrice aStar Z (sixthPrice g M6bar) ^ 2 / (2 * rateB n M ^ 3)

/-- The actual complex Taylor error after division by t³. -/
def firstError (μ : ProbabilityMeasure ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  (n : ℂ) * actualR6 μ t * comparator μ t ^ (n - 1) / ((t ^ 3 : ℝ) : ℂ)

/-- The actual complex second-order power error after division by t³. -/
def secondError (μ : ProbabilityMeasure ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  actualR2 μ n t / ((t ^ 3 : ℝ) : ℂ)

lemma norm_firstError (μ : ProbabilityMeasure ℝ) (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    ‖firstError μ n t‖ = firstIntegrand μ n t := by
  simp only [firstError, firstIntegrand, norm_div, norm_mul, Complex.norm_natCast,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg ht 3)]
  ring

lemma norm_secondError (μ : ProbabilityMeasure ℝ) (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    ‖secondError μ n t‖ = secondIntegrand μ n t := by
  simp only [secondError, secondIntegrand, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg ht 3)]

lemma measurable_firstError (μ : ProbabilityMeasure ℝ) (n : ℕ) : Measurable (firstError μ n) := by
  have hf := measurable_actual_charFun μ
  have hh := measurable_comparator μ
  unfold firstError actualR6
  fun_prop

lemma measurable_secondError (μ : ProbabilityMeasure ℝ) (n : ℕ) : Measurable (secondError μ n) := by
  have hf := measurable_actual_charFun μ
  have hh := measurable_comparator μ
  unfold secondError actualR2 powerError
  fun_prop

/-- The complete two error costs of ut:low. Both original complex quotients are
L¹ and the sum of their norm integrals is at most the original L₂(n)/n.
The leading quartic/fifth terms and Gaussian phase error belong to later stages. -/
theorem low_frequency_error_cost (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (h6 : Integrable (fun x : ℝ => |x| ^ 6) (μ : Measure ℝ)) (n : ℕ) (hn : 2 < n)
    (g M M6bar aStar Z : ℝ) (hg : |gamma μ| ≤ g) (hgcap : g ≤ 37 / 20)
    (hM4 : moment μ 4 ≤ M) (hMupper : M ≤ 111 / 10) (hM6 : sixthMoment μ ≤ M6bar)
    (ha : |quarticCoeff μ| ≤ aStar) (hZ : |fifthCoeff μ| ≤ Z) :
    IntegrableOn (firstError μ n) (Ioc (0 : ℝ) (1 / 2)) ∧
    IntegrableOn (secondError μ n) (Ioc (0 : ℝ) (1 / 2)) ∧
    (∫ t in Ioc (0 : ℝ) (1 / 2), ‖firstError μ n t‖) +
      (∫ t in Ioc (0 : ℝ) (1 / 2), ‖secondError μ n t‖) ≤
      coefficientL2 n M g M6bar aStar Z / (n : ℝ) := by
  have hfirst := first_error_cost μ h h6 n hn g M6bar hg hgcap hM6
  have hsecond := second_error_cost μ h h6 n hn g M M6bar aStar Z hg hgcap hM4 hMupper hM6 ha hZ
  have heq1 : (fun t => ‖firstError μ n t‖) =ᵐ[volume.restrict (Ioc (0 : ℝ) (1 / 2))]
      firstIntegrand μ n := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact norm_firstError μ n t ht.1.le
  have heq2 : (fun t => ‖secondError μ n t‖) =ᵐ[volume.restrict (Ioc (0 : ℝ) (1 / 2))]
      secondIntegrand μ n := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact norm_secondError μ n t ht.1.le
  have hi1 : IntegrableOn (firstError μ n) (Ioc (0 : ℝ) (1 / 2)) :=
    hfirst.1.mono' (measurable_firstError μ n).aestronglyMeasurable (heq1.mono fun _ h => h.le)
  have hi2 : IntegrableOn (secondError μ n) (Ioc (0 : ℝ) (1 / 2)) :=
    hsecond.1.mono' (measurable_secondError μ n).aestronglyMeasurable (heq2.mono fun _ h => h.le)
  refine ⟨hi1, hi2, ?_⟩
  rw [integral_congr_ae heq1, integral_congr_ae heq2]
  calc
    _ ≤ sixthPrice g M6bar / (2 * (n : ℝ) * rateA n ^ 2) +
        totalSixthPrice aStar Z (sixthPrice g M6bar) ^ 2 / (2 * (n : ℝ) * rateB n M ^ 3) :=
      add_le_add hfirst.2 hsecond.2
    _ = _ := by unfold coefficientL2; ring

end BerryEsseen.LowFrequencyError

#print axioms BerryEsseen.LowFrequencyError.low_frequency_error_cost

namespace BerryEsseen.LowFrequencyError

/-- The algebraic split used in ut:low, for the same actual f, h, a and z₅. -/
lemma actual_power_decomposition (μ : ProbabilityMeasure ℝ) (n : ℕ) (t : ℝ) :
    charFun (μ : Measure ℝ) t ^ n - comparator μ t ^ n =
      -(n : ℂ) * (((quarticCoeff μ * t ^ 4 : ℝ) : ℂ) +
        Complex.I * ((fifthCoeff μ * t ^ 5 : ℝ) : ℂ)) * comparator μ t ^ (n - 1) +
      (n : ℂ) * actualR6 μ t * comparator μ t ^ (n - 1) + actualR2 μ n t := by
  unfold actualR6 actualR2 powerError
  ring

/-- The same complete cost in the manuscript's oriented interval notation. -/
theorem low_frequency_error_cost_interval (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (h6 : Integrable (fun x : ℝ => |x| ^ 6) (μ : Measure ℝ)) (n : ℕ) (hn : 2 < n)
    (g M M6bar aStar Z : ℝ) (hg : |gamma μ| ≤ g) (hgcap : g ≤ 37 / 20)
    (hM4 : moment μ 4 ≤ M) (hMupper : M ≤ 111 / 10) (hM6 : sixthMoment μ ≤ M6bar)
    (ha : |quarticCoeff μ| ≤ aStar) (hZ : |fifthCoeff μ| ≤ Z) :
    IntervalIntegrable (firstError μ n) volume 0 (1 / 2) ∧
    IntervalIntegrable (secondError μ n) volume 0 (1 / 2) ∧
    (∫ t in (0 : ℝ)..(1 / 2), ‖firstError μ n t‖) +
      (∫ t in (0 : ℝ)..(1 / 2), ‖secondError μ n t‖) ≤
      coefficientL2 n M g M6bar aStar Z / (n : ℝ) := by
  have hc := low_frequency_error_cost μ h h6 n hn g M M6bar aStar Z hg hgcap hM4 hMupper hM6 ha hZ
  have hab : (0 : ℝ) ≤ 1 / 2 := by norm_num
  exact ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr hc.1,
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr hc.2.1,
    by simpa only [intervalIntegral.integral_of_le hab] using hc.2.2⟩

end BerryEsseen.LowFrequencyError

#print axioms BerryEsseen.LowFrequencyError.actual_power_decomposition
#print axioms BerryEsseen.LowFrequencyError.low_frequency_error_cost_interval
