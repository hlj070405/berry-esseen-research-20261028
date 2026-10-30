module

public import BerryEsseen.N26CubicHighTail
public import BerryEsseen.LowFrequencyFloor
public import BerryEsseen.HighFrequencyFloor

@[expose] public section

/-! 2026-10-30: the first actual-n Fourier price for every natural n >= 26.
The numerical low-frequency floor does not change the original iid index.
The first high tail is deliberately proportional to sqrt(n); no periodic
event, incoming defect bound, or fixed raw price is assumed here. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open BerryEsseen.CharacteristicExpansion BerryEsseen.LowFrequencyError
open BerryEsseen.LowFrequencyLeading BerryEsseen.HighFrequencyComparator
open BerryEsseen.HighFrequencyFloor

namespace BerryEsseen.UniformLowMomentFourierInitial

theorem predecessor_bound (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (hn : 26 ≤ n) (C : ℝ)
    (hprev : Extremizer.fixedNSup (n - 1) ≤ esseenConstant)
    (hC : esseenConstant ≤ C) : ContactMajorant.PredecessorBound μ n C := by
  intro t
  have hp := GaussianRecurrence.predecessor_cdf_upper μ h (n - 1) (by omega) t
  have hρ := Extremizer.thirdAbsoluteMoment_pos μ h
  have hc := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hprev.trans hC) hρ.le)
    (Real.sqrt_nonneg ((n - 1 : ℕ) : ℝ))
  change (MixtureSum.iidSumLaw (μ : Measure ℝ) (n - 1)).real (Iic t) ≤
    GaussianTools.Phi (t / Real.sqrt (n - 1 : ℕ)) +
      C * thirdAbsoluteMoment μ / Real.sqrt (n - 1 : ℕ)
  change (MixtureSum.iidSumLaw (μ : Measure ℝ) (n - 1)).real (Iic t) ≤
    GaussianTools.Phi (t / Real.sqrt (n - 1 : ℕ)) +
      Extremizer.fixedNSup (n - 1) * thirdAbsoluteMoment μ /
        Real.sqrt (n - 1 : ℕ) at hp
  linarith only [hp, hc]

theorem original_support (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (hn : 26 ≤ n) (H C : ℝ)
    (hm : ContactVariation.PositiveClosedMaximum μ n H C)
    (hprev : Extremizer.fixedNSup (n - 1) ≤ esseenConstant)
    (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) :
    (μ : Measure ℝ).support ⊆ Icc (-(12 / 5 : ℝ)) (12 / 5) := by
  have hs := InitialSupport.low_moment_support μ h n (by omega) H C hm
    (predecessor_bound μ h n hn C hprev hC) hC hρ
  exact fun x hx => ⟨(hs hx).1.le, (hs hx).2.le⟩

/-- The floor acts only on deterministic coefficients. The actual I0 keeps n. -/
theorem low_frequency_of_support (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hs : (μ : Measure ℝ).support ⊆ Icc (-(12 / 5 : ℝ)) (12 / 5))
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10)
    (n : ℕ) (hn : 26 ≤ n) (H : ℝ) :
    IntegrableOn (lowIntegrand μ n H) (Ioc (0 : ℝ) (1 / 2)) ∧
      Real.sqrt n * I0 μ n H ≤ 191 / 1250 + (127 / 1000) * |H| := by
  have hM := (N26P39ResourceAcquisition.moment_caps_of_support μ h hs hρ).1
  rw [← moment_four_eq_abs] at hM
  have hc := LowFrequencyFloor.actual_triangle_floor μ h
    (N26InitialLowFrequency.sixth_integrable_of_support μ hs) 26 n (by decide) hn H
    (53 / 100) (1014 / 725) (94566 / 18125) (1 / 12) (63 / 1000) (63 / 50)
    (N26InitialLowFrequency.gamma_cap μ h hρ) (by norm_num) hM (by norm_num)
    (N26InitialLowFrequency.sixth_cap_of_support μ h hs hρ)
    (N26InitialLowFrequency.quartic_cap_of_support μ h hs hρ)
    (N26InitialLowFrequency.fifth_cap_of_support μ h hs hρ)
    N26InitialLowFrequency.gaussianMass_cap
  have hL2 := div_le_div_of_nonneg_right N26InitialLowFrequency.coefficientL2_cap
    (Real.sqrt_nonneg (26 : ℝ))
  have hLH := mul_le_mul_of_nonneg_right N26InitialLowFrequency.triangleLH_cap (abs_nonneg H)
  refine ⟨hc.1, ?_⟩
  linarith only [hc.2, N26InitialLowFrequency.triangleL0_cap, hLH, hL2,
    N26InitialFourierEnvelope.low_remainder_cap]

lemma inv_gaussian_floor (n : ℕ) (hn : 26 ≤ n) :
    Real.exp (-(n : ℝ) / 8) / Real.sqrt n ≤
      Real.exp (-(13 : ℝ) / 4) / Real.sqrt (26 : ℝ) := by
  have hh := invSqrtExp_antitone (1 / 8) (by norm_num)
    (show (0 : ℝ) < 26 by norm_num)
    (show (0 : ℝ) < n by exact_mod_cast (show 0 < n by omega))
    (Nat.cast_le.mpr hn)
  convert hh using 1 <;> unfold invSqrtExp <;> congr 2 <;> ring

lemma sqrt_gaussian_floor (n : ℕ) (hn : 26 ≤ n) :
    Real.sqrt n * Real.exp (-(n : ℝ) / 8) ≤
      Real.sqrt (26 : ℝ) * Real.exp (-(13 : ℝ) / 4) := by
  have hh := sqrtExp_antitone (1 / 8) 26 (by norm_num) (by norm_num)
    (show (26 : ℝ) ∈ Ici 26 from le_rfl) (Nat.cast_le.mpr hn) (Nat.cast_le.mpr hn)
  convert hh using 1 <;> unfold sqrtExp <;> congr 2 <;> ring

lemma sqrt_twenty_six_div :
    1 / Real.sqrt (26 : ℝ) = Real.sqrt (26 : ℝ) / 26 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 26)
  have hp : Real.sqrt (26 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  apply (div_eq_div_iff hp (by norm_num : (26 : ℝ) ≠ 0)).mpr
  nlinarith only [hs]

lemma first_gaussian_cost_cap (n : ℕ) (hn : 26 ≤ n) :
    16 * (Real.exp (-(n : ℝ) / 8) / Real.sqrt n) ≤ (204 : ℝ) / 1625 := by
  have hh := mul_le_mul_of_nonneg_left (inv_gaussian_floor n hn) (by norm_num : (0 : ℝ) ≤ 16)
  have he := mul_le_mul N26InitialFourierEnvelope.sqrt_twenty_six_upper
    LowMomentGaussianBand.exp_neg_thirteen_quarters_le (Real.exp_nonneg _)
    (by norm_num : (0 : ℝ) ≤ 51 / 10)
  have heq : 16 * (Real.exp (-(13 : ℝ) / 4) / Real.sqrt (26 : ℝ)) =
      (8 / 13 : ℝ) * (Real.sqrt (26 : ℝ) * Real.exp (-(13 : ℝ) / 4)) := by
    rw [div_eq_mul_inv, ← one_div, sqrt_twenty_six_div]
    ring
  rw [heq] at hh
  linarith only [hh, he]

lemma second_gaussian_cost_cap (n : ℕ) (hn : 26 ≤ n) :
    (53 / 300 : ℝ) * (Real.sqrt n * Real.exp (-(n : ℝ) / 8)) ≤
      (901 : ℝ) / 25000 := by
  have hh := mul_le_mul_of_nonneg_left (sqrt_gaussian_floor n hn)
    (by norm_num : (0 : ℝ) ≤ 53 / 300)
  have he := mul_le_mul N26InitialFourierEnvelope.sqrt_twenty_six_upper
    LowMomentGaussianBand.exp_neg_thirteen_quarters_le (Real.exp_nonneg _)
    (by norm_num : (0 : ℝ) ≤ 51 / 10)
  linarith only [hh, he]

lemma gaussian_inverse_cube_le (n : ℕ) (t : ℝ) (ht : 1 / 2 ≤ t) :
    Real.exp (-((n : ℝ) / 2) * t ^ 2) / t ^ 3 ≤
      16 * (t * Real.exp (-((n : ℝ) / 2) * t ^ 2)) := by
  have ht0 : 0 < t := by linarith only [ht]
  apply (div_le_iff₀ (pow_pos ht0 3)).mpr
  have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) ht 4
  have hp := mul_le_mul_of_nonneg_left hpow (Real.exp_nonneg (-((n : ℝ) / 2) * t ^ 2))
  norm_num at hp
  simp only [← neg_mul] at hp
  nlinarith only [hp]

theorem initial_segment_cost_le_of_support
    (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hs : (μ : Measure ℝ).support ⊆ Icc (-(12 / 5 : ℝ)) (12 / 5))
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10)
    (n : ℕ) (hn : 26 ≤ n) :
    Real.sqrt n * (∫ t in Icc (1 / 2 : ℝ) HighFrequencyDamping.cutoff,
      HighFrequencyDamping.initialIntegrand μ n t) ≤ (204 : ℝ) / 1625 := by
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hti := (integrable_mul_exp_neg_mul_sq (show (0 : ℝ) < (n : ℝ) / 2 by positivity)).integrableOn
    (s := Ioi (1 / 2 : ℝ))
  have hcf := (FourierSplit.integrableOn_cfQuotient_ray μ n (1 / 2) (by norm_num)).mono_set
    (show Ioc (1 / 2 : ℝ) HighFrequencyDamping.cutoff ⊆ Ioi (1 / 2) from fun _ ht => ht.1)
  have hsub : Ioc (1 / 2 : ℝ) HighFrequencyDamping.cutoff ⊆ Ioi (1 / 2) := fun _ ht => ht.1
  have hb : (∫ t in Ioc (1 / 2 : ℝ) HighFrequencyDamping.cutoff,
      HighFrequencyDamping.initialIntegrand μ n t) ≤
      16 * (∫ t in Ioi (1 / 2 : ℝ), t * Real.exp (-((n : ℝ) / 2) * t ^ 2)) := by
    calc
      _ ≤ ∫ t in Ioc (1 / 2 : ℝ) HighFrequencyDamping.cutoff,
          16 * (t * Real.exp (-((n : ℝ) / 2) * t ^ 2)) := by
        apply integral_mono_ae hcf ((hti.mono_set hsub).const_mul 16)
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        have ht0 : 0 < t := lt_trans (by norm_num) ht.1
        have hg := LowMomentGaussianBand.norm_charFun_pow_le_gaussian_of_support μ h hs hρ n t
          (by rw [abs_of_pos ht0]; simpa only [HighFrequencyDamping.cutoff] using ht.2)
        have hd := div_le_div_of_nonneg_right hg (pow_nonneg ht0.le 3)
        rw [show -(n : ℝ) * t ^ 2 / 2 = -((n : ℝ) / 2) * t ^ 2 by ring] at hd
        change ‖charFun (μ : Measure ℝ) t ^ n‖ / t ^ 3 ≤ _
        exact hd.trans (gaussian_inverse_cube_le n t ht.1.le)
      _ ≤ ∫ t in Ioi (1 / 2 : ℝ),
          16 * (t * Real.exp (-((n : ℝ) / 2) * t ^ 2)) := by
        apply setIntegral_mono_set (hti.const_mul 16)
        · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          have hthalf : (1 / 2 : ℝ) < t := ht
          have ht0 : 0 ≤ t := by linarith only [hthalf]
          positivity
        · exact Filter.Eventually.of_forall hsub
      _ = _ := integral_const_mul _ _
  rw [integral_mul_gaussian_Ioi ((n : ℝ) / 2) (1 / 2) (by positivity)] at hb
  have he : -((n : ℝ) / 2) * (1 / 2 : ℝ) ^ 2 = -(n : ℝ) / 8 := by ring
  rw [he] at hb
  rw [integral_Icc_eq_integral_Ioc]
  have hscaled := mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg (n : ℝ))
  have hp : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hn0)
  have heq : Real.sqrt n * (16 * (Real.exp (-(n : ℝ) / 8) / (2 * ((n : ℝ) / 2)))) =
      16 * (Real.exp (-(n : ℝ) / 8) / Real.sqrt n) := by
    field_simp [hn0.ne', hp]
    ring_nf
    rw [Real.sq_sqrt hn0.le]
  rw [heq] at hscaled
  exact hscaled.trans (first_gaussian_cost_cap n hn)

/-- Both Gaussian-cubic comparator terms are paid on the complete ray. -/
theorem comparator_cost_cap (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10)
    (n : ℕ) (hn : 26 ≤ n) :
    Real.sqrt n * (∫ t in Ioi (1 / 2 : ℝ), comparatorQuotient μ n t) ≤ (81 : ℝ) / 500 := by
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hg := N26InitialLowFrequency.gamma_cap μ h hρ
  have hti := (integrable_mul_exp_neg_mul_sq (show (0 : ℝ) < (n : ℝ) / 2 by positivity)).integrableOn
    (s := Ioi (1 / 2 : ℝ))
  have hi0 := (integrable_exp_neg_mul_sq (show (0 : ℝ) < (n : ℝ) / 2 by positivity)).integrableOn
    (s := Ioi (1 / 2 : ℝ))
  have hb : (∫ t in Ioi (1 / 2 : ℝ), comparatorQuotient μ n t) ≤
      16 * (∫ t in Ioi (1 / 2 : ℝ), t * Real.exp (-((n : ℝ) / 2) * t ^ 2)) +
        ((n : ℝ) * (53 / 100) / 6) *
          (∫ t in Ioi (1 / 2 : ℝ), Real.exp (-((n : ℝ) / 2) * t ^ 2)) := by
    calc
      _ ≤ ∫ t in Ioi (1 / 2 : ℝ),
          16 * (t * Real.exp (-((n : ℝ) / 2) * t ^ 2)) +
            ((n : ℝ) * (53 / 100) / 6) * Real.exp (-((n : ℝ) / 2) * t ^ 2) := by
        apply integral_mono_ae (integrableOn_comparatorQuotient μ n (by omega))
          ((hti.const_mul 16).add (hi0.const_mul _))
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have hp := quotient_le_majorant μ n t (53 / 100) (lt_trans (by norm_num) ht) hg
        exact hp.trans (add_le_add (gaussian_inverse_cube_le n t ht.le) le_rfl)
      _ = _ := by rw [integral_add (hti.const_mul 16) (hi0.const_mul _), integral_const_mul, integral_const_mul]
  rw [integral_mul_gaussian_Ioi ((n : ℝ) / 2) (1 / 2) (by positivity)] at hb
  have htail := half_gaussian_tail_le n (by omega)
  have he : -((n : ℝ) / 2) * (1 / 2 : ℝ) ^ 2 = -(n : ℝ) / 8 := by ring
  rw [he] at hb
  have hraw : (∫ t in Ioi (1 / 2 : ℝ), comparatorQuotient μ n t) ≤
      16 * (Real.exp (-(n : ℝ) / 8) / n) +
        (53 / 300 : ℝ) * Real.exp (-(n : ℝ) / 8) := by
    have hp := mul_le_mul_of_nonneg_left htail
      (show 0 ≤ (n : ℝ) * (53 / 100) / 6 by positivity)
    have heq : ((n : ℝ) * (53 / 100) / 6) * (2 * Real.exp (-(n : ℝ) / 8) / n) =
        (53 / 300 : ℝ) * Real.exp (-(n : ℝ) / 8) := by field_simp [hn0.ne']; ring
    rw [heq] at hp
    have hd : 2 * ((n : ℝ) / 2) = n := by ring
    rw [hd] at hb
    linarith only [hb, hp]
  have hscaled := mul_le_mul_of_nonneg_left hraw (Real.sqrt_nonneg (n : ℝ))
  have hp : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hn0)
  have heq : Real.sqrt n * (16 * (Real.exp (-(n : ℝ) / 8) / n) +
      (53 / 300 : ℝ) * Real.exp (-(n : ℝ) / 8)) =
      16 * (Real.exp (-(n : ℝ) / 8) / Real.sqrt n) +
        (53 / 300 : ℝ) * (Real.sqrt n * Real.exp (-(n : ℝ) / 8)) := by
    field_simp [hn0.ne', hp]
    ring_nf
    rw [Real.sq_sqrt hn0.le]
    ring
  rw [heq] at hscaled
  linarith only [hscaled, first_gaussian_cost_cap n hn, second_gaussian_cost_cap n hn]

lemma norm_charFun_pow_le_floor (μ : ProbabilityMeasure ℝ) (n : ℕ) (hn : 26 ≤ n) (t : ℝ) :
    ‖charFun (μ : Measure ℝ) t ^ n‖ ≤ ‖charFun (μ : Measure ℝ) t ^ 26‖ := by
  rw [norm_pow, norm_pow]
  have hp := pow_le_one₀ (norm_nonneg (charFun (μ : Measure ℝ) t))
    (norm_charFun_le_one (μ := (μ : Measure ℝ)) t) (n := n - 26)
  calc
    _ = ‖charFun (μ : Measure ℝ) t‖ ^ 26 * ‖charFun (μ : Measure ℝ) t‖ ^ (n - 26) := by
      rw [← pow_add, Nat.add_sub_of_le hn]
    _ ≤ ‖charFun (μ : Measure ℝ) t‖ ^ 26 * 1 :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := mul_one _

/-- This is the deliberately variable first tail; its sqrt(n) is retained. -/
theorem cf_tail_cost_le (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10)
    (n : ℕ) (hn : 26 ≤ n) :
    Real.sqrt n * (∫ t in Ioi HighFrequencyDamping.cutoff,
      HighFrequencyDamping.initialIntegrand μ n t) ≤ Real.sqrt n / 10 := by
  have hc : 0 < HighFrequencyDamping.cutoff := by norm_num [HighFrequencyDamping.cutoff]
  have hb : (∫ t in Ioi HighFrequencyDamping.cutoff,
      HighFrequencyDamping.initialIntegrand μ n t) ≤
      ∫ t in Ioi HighFrequencyDamping.cutoff, HighFrequencyDamping.initialIntegrand μ 26 t := by
    apply integral_mono_ae (FourierSplit.integrableOn_cfQuotient_ray μ n _ hc)
      (FourierSplit.integrableOn_cfQuotient_ray μ 26 _ hc)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact div_le_div_of_nonneg_right (norm_charFun_pow_le_floor μ n hn t)
      (pow_nonneg (hc.le.trans ht.le) 3)
  have h26 := N26CubicHighTail.cf_tail_le_price μ h hρ
  have hroot : (127 : ℝ) / 25 ≤ Real.sqrt (26 : ℝ) := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 26), Real.sqrt_nonneg (26 : ℝ)]
  have h26cap : (∫ t in Ioi HighFrequencyDamping.cutoff,
      HighFrequencyDamping.initialIntegrand μ 26 t) ≤ (1 : ℝ) / 10 := by
    apply (mul_le_mul_iff_right₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 26))).mp
    have hcubic := N26CubicHighTail.cubicTailPrice_lt.le
    nlinarith only [h26, hcubic, hroot]
  have hp := mul_le_mul_of_nonneg_left (hb.trans h26cap) (Real.sqrt_nonneg (n : ℝ))
  simpa only [div_eq_mul_inv, one_mul] using hp

theorem value_le_of_support_and_tail (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hs : (μ : Measure ℝ).support ⊆ Icc (-(12 / 5 : ℝ)) (12 / 5))
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10)
    (n : ℕ) (hn : 26 ≤ n) (H T : ℝ)
    (htail : Real.sqrt n * (∫ t in Ioi HighFrequencyDamping.cutoff,
      HighFrequencyDamping.initialIntegrand μ n t) ≤ T) :
    |FourierRemainder.value μ n H| ≤
      551 / 1875 + (2 / 3 : ℝ) * T + (127 / 1500) * |H| := by
  have hT : 0 ≤ T := by
    apply le_trans _ htail
    apply mul_nonneg (Real.sqrt_nonneg _)
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 ≤ t := (by norm_num [HighFrequencyDamping.cutoff] : (0 : ℝ) ≤ HighFrequencyDamping.cutoff).trans ht.le
    exact div_nonneg (norm_nonneg _) (pow_nonneg ht0 3)
  have hl := (low_frequency_of_support μ h hs hρ n hn H).2
  have hlow : Real.sqrt n * I0 μ n H ≤ 191 / 1250 + (127 / 1000) * |H| + 0 / Real.sqrt n := by
    simpa only [zero_div, add_zero] using hl
  have hm := (initial_segment_cost_le_of_support μ h hs hρ n hn).trans
    (by norm_num : (204 : ℝ) / 1625 ≤ 63 / 500)
  have hb := FourierSplit.value_le_affine_envelope μ h n (by omega) H
    (191 / 1250) (127 / 1000) 0 (63 / 500) T (81 / 500)
    hlow hm htail (comparator_cost_cap μ h hρ n hn)
  have hk : FourierSplit.KF n (191 / 1250) 0 (63 / 500) T (81 / 500) ≤
      551 / 1875 + (2 / 3 : ℝ) * T := by
    unfold FourierSplit.KF
    have hp := mul_le_mul_of_nonneg_right N26InitialFourierEnvelope.two_div_pi_cap
      (show 0 ≤ (191 / 1250 : ℝ) + 0 / Real.sqrt n + 63 / 500 + T + 81 / 500 by positivity)
    norm_num only [zero_div, add_zero] at hp ⊢
    nlinarith only [hp]
  exact hb.trans (add_le_add hk (mul_le_mul_of_nonneg_right
    N26InitialFourierEnvelope.affine_slope_cap (abs_nonneg H)))

theorem fourier_envelope_of_support (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hs : (μ : Measure ℝ).support ⊆ Icc (-(12 / 5 : ℝ)) (12 / 5))
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10)
    (n : ℕ) (hn : 26 ≤ n) (H : ℝ) :
    IntegrableOn (FourierRemainder.originalIntegrand μ n H) (Ioi 0) ∧
      |FourierRemainder.value μ n H| ≤
        3 / 10 + Real.sqrt n / 15 + (127 / 1500) * |H| := by
  refine ⟨FourierRemainder.integrable_originalIntegrand μ h n (by omega) H, ?_⟩
  have hb := value_le_of_support_and_tail μ h hs hρ n hn H (Real.sqrt n / 10)
    (cf_tail_cost_le μ h hρ n hn)
  linarith only [hb]

theorem original_fourier_envelope (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (hn : 26 ≤ n) (H C : ℝ)
    (hm : ContactVariation.PositiveClosedMaximum μ n H C)
    (hprev : Extremizer.fixedNSup (n - 1) ≤ esseenConstant)
    (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) :
    IntegrableOn (FourierRemainder.originalIntegrand μ n H) (Ioi 0) ∧
      |FourierRemainder.value μ n H| ≤
        3 / 10 + Real.sqrt n / 15 + (127 / 1500) * |H| :=
  fourier_envelope_of_support μ h (original_support μ h n hn H C hm hprev hC hρ) hρ n hn H

end BerryEsseen.UniformLowMomentFourierInitial

#print axioms BerryEsseen.UniformLowMomentFourierInitial.original_support
#print axioms BerryEsseen.UniformLowMomentFourierInitial.low_frequency_of_support
#print axioms BerryEsseen.UniformLowMomentFourierInitial.initial_segment_cost_le_of_support
#print axioms BerryEsseen.UniformLowMomentFourierInitial.comparator_cost_cap
#print axioms BerryEsseen.UniformLowMomentFourierInitial.cf_tail_cost_le
#print axioms BerryEsseen.UniformLowMomentFourierInitial.value_le_of_support_and_tail
#print axioms BerryEsseen.UniformLowMomentFourierInitial.fourier_envelope_of_support
#print axioms BerryEsseen.UniformLowMomentFourierInitial.original_fourier_envelope
