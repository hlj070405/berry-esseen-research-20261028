module

public import BerryEsseen.FourierRemainder
public import BerryEsseen.PearsonMoments
public import BerryEsseen.RationalGaussianTail

@[expose] public section

/-! 2026-10-28: the complete sixth high-frequency price, for the literal
Gaussian-cubic comparator in the original Fourier remainder. Both high-ray
quotients and all Gaussian majorants have genuine L¹ proofs. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace BerryEsseen.HighFrequencyComparator

open FourierRemainder CharacteristicExpansion RationalGaussianTail

/-- The exact Gaussian-cubic expression subtracted in originalIntegrand. -/
def actualComparator (μ : ProbabilityMeasure ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  (gaussianFactor n t : ℂ) *
    (1 - Complex.I * (n : ℂ) * (thirdMoment μ : ℂ) * (t : ℂ) ^ 3 / 6)

def comparatorQuotient (μ : ProbabilityMeasure ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  ‖actualComparator μ n t‖ / t ^ 3

lemma originalIntegrand_eq (μ : ProbabilityMeasure ℝ) (n : ℕ) (H t : ℝ) :
    originalIntegrand μ n H t =
      (Complex.exp (-Complex.I * (t : ℂ) * (H : ℂ)) *
        (charFun (μ : Measure ℝ) t ^ n - actualComparator μ n t)).im / t ^ 3 := rfl

lemma thirdMoment_eq_gamma (μ : ProbabilityMeasure ℝ) : thirdMoment μ = gamma μ := rfl

lemma gaussianFactor_eq_rate (n : ℕ) (t : ℝ) :
    gaussianFactor n t = Real.exp (-((n : ℝ) / 2) * t ^ 2) := by
  unfold gaussianFactor
  congr 1
  ring

/-- Identification with the original complex-exponential formula. -/
lemma actualComparator_eq_original (μ : ProbabilityMeasure ℝ) (n : ℕ) (t : ℝ) :
    actualComparator μ n t = Complex.exp (-(((n : ℝ) * t ^ 2 / 2 : ℝ) : ℂ)) *
      (1 - Complex.I * (n : ℂ) * (thirdMoment μ : ℂ) * (t : ℂ) ^ 3 / 6) := by
  unfold actualComparator gaussianFactor
  rw [Complex.ofReal_exp]
  congr 2
  push_cast
  ring

lemma tendsto_gaussian_atTop (c : ℝ) (hc : 0 < c) :
    Tendsto (fun t : ℝ => Real.exp (-c * t ^ 2)) atTop (𝓝 0) := by
  have htop : Tendsto (fun t : ℝ => c * t ^ 2) atTop atTop :=
    Tendsto.const_mul_atTop hc (tendsto_pow_atTop (by norm_num))
  have h := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp htop)
  simpa only [Function.comp_def, neg_mul] using h

/-- A real FTC evaluation, including the Gaussian tail's exact original rate. -/
lemma integral_mul_gaussian_Ioi (c b : ℝ) (hc : 0 < c) :
    (∫ t in Ioi b, t * Real.exp (-c * t ^ 2)) = Real.exp (-c * b ^ 2) / (2 * c) := by
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ => -Real.exp (-c * t ^ 2) / (2 * c))
      (t * Real.exp (-c * t ^ 2)) t := by
    have hi : HasDerivAt (fun t : ℝ => -c * t ^ 2) (-2 * c * t) t := by
      convert ((hasDerivAt_id' t).pow 2).const_mul (-c) using 1
      ring
    convert hi.exp.neg.div_const (2 * c) using 1
    field_simp [ne_of_gt hc]
  have hlim : Tendsto (fun t : ℝ => -Real.exp (-c * t ^ 2) / (2 * c)) atTop (𝓝 0) := by
    simpa only [neg_zero, zero_div] using ((tendsto_gaussian_atTop c hc).neg.div_const (2 * c))
  have hi : IntegrableOn (fun t : ℝ => t * Real.exp (-c * t ^ 2)) (Ioi b) :=
    (integrable_mul_exp_neg_mul_sq hc).integrableOn
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' (fun t _ => hd t) hi hlim
  simpa only [zero_sub, neg_div, neg_neg] using h

/-- The elementary Gaussian tail price, with its real integrals and full b-dependence. -/
theorem gaussian_tail_le (c b : ℝ) (hc : 0 < c) (hb : 0 < b) :
    (∫ t in Ioi b, Real.exp (-c * t ^ 2)) ≤ Real.exp (-c * b ^ 2) / (2 * c * b) := by
  have hi := (integrable_exp_neg_mul_sq hc).integrableOn (s := Ioi b)
  have hti := (integrable_mul_exp_neg_mul_sq hc).integrableOn (s := Ioi b)
  have hle : (∫ t in Ioi b, b * Real.exp (-c * t ^ 2)) ≤
      ∫ t in Ioi b, t * Real.exp (-c * t ^ 2) := by
    apply integral_mono_ae (hi.const_mul b) hti
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_le_mul_of_nonneg_right ht.le (Real.exp_pos _).le
  rw [integral_const_mul, integral_mul_gaussian_Ioi c b hc] at hle
  calc
    _ ≤ (Real.exp (-c * b ^ 2) / (2 * c)) / b :=
      (le_div_iff₀ hb).mpr (by simpa only [mul_comm] using hle)
    _ = _ := by rw [div_div]

lemma half_gaussian_tail_le (n : ℕ) (hn : 0 < n) :
    (∫ t in Ioi (1 / 2 : ℝ), Real.exp (-((n : ℝ) / 2) * t ^ 2)) ≤
      2 * Real.exp (-(n : ℝ) / 8) / n := by
  have hn0 : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have h := gaussian_tail_le ((n : ℝ) / 2) (1 / 2) (by positivity) (by norm_num)
  have he : -((n : ℝ) / 2) * (1 / 2) ^ 2 = -(n : ℝ) / 8 := by ring
  rw [he] at h
  convert h using 1
  field_simp [ne_of_gt hn0]

lemma norm_one_sub_I_mul_real (a : ℝ) :
    ‖(1 : ℂ) - Complex.I * (a : ℂ)‖ ≤ 1 + |a| := by
  simpa only [norm_one, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, one_mul]
    using norm_sub_le (1 : ℂ) (Complex.I * (a : ℂ))

/-- Triangle domination of the whole Gaussian-cubic comparator, using actual γ. -/
theorem norm_actualComparator_le (μ : ProbabilityMeasure ℝ) (n : ℕ) (t g : ℝ)
    (ht : 0 ≤ t) (hg : |gamma μ| ≤ g) :
    ‖actualComparator μ n t‖ ≤ Real.exp (-((n : ℝ) / 2) * t ^ 2) *
      (1 + (n : ℝ) * g * t ^ 3 / 6) := by
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have ha : |(n : ℝ) * gamma μ * t ^ 3 / 6| ≤ (n : ℝ) * g * t ^ 3 / 6 := by
    rw [abs_div, abs_mul, abs_mul, abs_of_nonneg hn0, abs_of_nonneg (pow_nonneg ht 3)]
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 6)]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hg hn0) (pow_nonneg ht 3)) (by norm_num)
  have hedge : Complex.I * (n : ℂ) * (thirdMoment μ : ℂ) * (t : ℂ) ^ 3 / 6 =
      Complex.I * ((((n : ℝ) * gamma μ * t ^ 3 / 6 : ℝ)) : ℂ) := by
    rw [thirdMoment_eq_gamma]
    push_cast
    ring
  rw [actualComparator, hedge, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    gaussianFactor_eq_rate, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left ((norm_one_sub_I_mul_real _).trans (add_le_add le_rfl ha))
    (Real.exp_pos _).le

lemma quotient_le_majorant (μ : ProbabilityMeasure ℝ) (n : ℕ) (t g : ℝ)
    (ht : 0 < t) (hg : |gamma μ| ≤ g) :
    comparatorQuotient μ n t ≤
      Real.exp (-((n : ℝ) / 2) * t ^ 2) / t ^ 3 +
        ((n : ℝ) * g / 6) * Real.exp (-((n : ℝ) / 2) * t ^ 2) := by
  have h := div_le_div_of_nonneg_right (norm_actualComparator_le μ n t g ht.le hg)
    (pow_nonneg ht.le 3)
  unfold comparatorQuotient
  convert h using 1
  field_simp [ne_of_gt ht]

lemma measurable_comparatorQuotient (μ : ProbabilityMeasure ℝ) (n : ℕ) :
    Measurable (comparatorQuotient μ n) := by
  have hc : Continuous (actualComparator μ n) := by unfold actualComparator gaussianFactor; fun_prop
  exact hc.norm.measurable.div (continuous_id.pow 3).measurable

/-- L¹ of the entire high-ray comparator quotient, including both Gaussian terms. -/
theorem integrableOn_comparatorQuotient (μ : ProbabilityMeasure ℝ) (n : ℕ) (hn : 0 < n) :
    IntegrableOn (comparatorQuotient μ n) (Ioi (1 / 2 : ℝ)) := by
  have hn0 : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hi3 := integrableOn_gaussian_inv_cube ((n : ℝ) / 2) (1 / 2) (by positivity) (by norm_num)
  have hi0 := (integrable_exp_neg_mul_sq (b := (n : ℝ) / 2) (by positivity)).integrableOn
    (s := Ioi (1 / 2 : ℝ))
  apply (hi3.add (hi0.const_mul ((n : ℝ) * |gamma μ| / 6))).mono'
    (measurable_comparatorQuotient μ n).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 < t := lt_trans (by norm_num) ht
  rw [Real.norm_eq_abs, abs_of_nonneg (by unfold comparatorQuotient; positivity)]
  exact quotient_le_majorant μ n t |gamma μ| ht0 le_rfl

/-- Absolute integrability of the actual complex quotient on the complete high ray. -/
theorem integrableOn_actualComparator_div_cube (μ : ProbabilityMeasure ℝ)
    (n : ℕ) (hn : 0 < n) :
    IntegrableOn (fun t : ℝ => actualComparator μ n t / (t : ℂ) ^ 3)
      (Ioi (1 / 2 : ℝ)) := by
  have hc : Continuous (actualComparator μ n) := by unfold actualComparator gaussianFactor; fun_prop
  have hd : Continuous (fun t : ℝ => (t : ℂ) ^ 3) := by fun_prop
  apply (integrable_norm_iff (hc.measurable.div hd.measurable).aestronglyMeasurable).mp
  apply (integrableOn_comparatorQuotient μ n hn).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 < t := lt_trans (by norm_num) ht
  simp only [comparatorQuotient, Pi.div_apply, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos ht0]

/-- The sixth high-frequency term with an explicit envelope on the actual γ. -/
theorem gaussian_comparator_price (μ : ProbabilityMeasure ℝ) (n : ℕ) (hn : 0 < n)
    (g : ℝ) (hg : |gamma μ| ≤ g) :
    Real.sqrt n * (∫ t in Ioi (1 / 2 : ℝ), comparatorQuotient μ n t) ≤
      Real.sqrt n * Real.exp (-(n : ℝ) / 8) * (2 * Lambda ((n : ℝ) / 8) + g / 3) := by
  have hn0 : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hg0 : 0 ≤ g := (abs_nonneg _).trans hg
  have hi3 := integrableOn_gaussian_inv_cube ((n : ℝ) / 2) (1 / 2) (by positivity) (by norm_num)
  have hi0 := (integrable_exp_neg_mul_sq (b := (n : ℝ) / 2) (by positivity)).integrableOn
    (s := Ioi (1 / 2 : ℝ))
  have hle : (∫ t in Ioi (1 / 2 : ℝ), comparatorQuotient μ n t) ≤
      (∫ t in Ioi (1 / 2 : ℝ), Real.exp (-((n : ℝ) / 2) * t ^ 2) / t ^ 3) +
        ((n : ℝ) * g / 6) * (∫ t in Ioi (1 / 2 : ℝ), Real.exp (-((n : ℝ) / 2) * t ^ 2)) := by
    calc
      _ ≤ ∫ t in Ioi (1 / 2 : ℝ), (Real.exp (-((n : ℝ) / 2) * t ^ 2) / t ^ 3 +
          ((n : ℝ) * g / 6) * Real.exp (-((n : ℝ) / 2) * t ^ 2)) := by
        apply integral_mono_ae (integrableOn_comparatorQuotient μ n hn) (hi3.add (hi0.const_mul _))
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact quotient_le_majorant μ n t g (lt_trans (by norm_num) ht) hg
      _ = _ := by rw [integral_add hi3 (hi0.const_mul _), integral_const_mul]
  have h3 := gaussian_inv_cube_tail ((n : ℝ) / 2) (1 / 2) (by positivity) (by norm_num)
  have hexp : -((n : ℝ) / 2) * (1 / 2) ^ 2 = -(n : ℝ) / 8 := by ring
  have hx : ((n : ℝ) / 2) * (1 / 2) ^ 2 = (n : ℝ) / 8 := by ring
  rw [hexp, hx] at h3
  norm_num only [show (2 : ℝ) * (1 / 2) ^ 2 = 1 / 2 by norm_num] at h3
  have h0 := half_gaussian_tail_le n hn
  calc
    _ ≤ Real.sqrt n * ((∫ t in Ioi (1 / 2 : ℝ), Real.exp (-((n : ℝ) / 2) * t ^ 2) / t ^ 3) +
        ((n : ℝ) * g / 6) * (∫ t in Ioi (1 / 2 : ℝ), Real.exp (-((n : ℝ) / 2) * t ^ 2))) :=
      mul_le_mul_of_nonneg_left hle (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt n * (2 * Real.exp (-(n : ℝ) / 8) * Lambda ((n : ℝ) / 8) +
        ((n : ℝ) * g / 6) * (2 * Real.exp (-(n : ℝ) / 8) / n)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
      exact add_le_add (by convert h3 using 1 <;> ring)
        (mul_le_mul_of_nonneg_left h0 (by positivity))
    _ = _ := by field_simp [ne_of_gt hn0]; ring

/-- Pearson's actual fourth-moment ceiling supplies the original sixth-term envelope. -/
theorem gaussian_comparator_price_of_moment_ceiling (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (h4 : Integrable (fun x : ℝ => |x| ^ 4) (μ : Measure ℝ))
    (n : ℕ) (hn : 0 < n) (M : ℝ) (hM : moment μ 4 ≤ M) :
    Real.sqrt n * (∫ t in Ioi (1 / 2 : ℝ), comparatorQuotient μ n t) ≤
      Real.sqrt n * Real.exp (-(n : ℝ) / 8) *
        (2 * Lambda ((n : ℝ) / 8) + Real.sqrt (M - 1) / 3) :=
  gaussian_comparator_price μ n hn _
    (PearsonMoments.gamma_abs_le_sqrt_of_moment_ceiling μ h h4 M hM)

end BerryEsseen.HighFrequencyComparator

#print axioms BerryEsseen.HighFrequencyComparator.integrableOn_comparatorQuotient
#print axioms BerryEsseen.HighFrequencyComparator.integrableOn_actualComparator_div_cube
#print axioms BerryEsseen.HighFrequencyComparator.gaussian_comparator_price
#print axioms BerryEsseen.HighFrequencyComparator.gaussian_comparator_price_of_moment_ceiling
