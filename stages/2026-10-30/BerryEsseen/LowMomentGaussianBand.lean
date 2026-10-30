module

public import BerryEsseen.CharacteristicExpansion
public import BerryEsseen.HighFrequencyDamping
public import BerryEsseen.N26P39ResourceAcquisition
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion

@[expose] public section

/-! 2026-10-30: Gaussian modulus domination of the actual characteristic
function on the whole physical band |t| ≤ 9/10, from a finite fourth moment
at most 8/5. The interval proof uses an exact polynomial certificate. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped Topology Interval

namespace BerryEsseen.LowMomentGaussianBand

open CharacteristicExpansion

def negExpPoly5 (z : ℝ) : ℝ :=
  1 - z + z ^ 2 / 2 - z ^ 3 / 6 + z ^ 4 / 24 - z ^ 5 / 120

lemma hasDerivAt_negExpPoly5 (z : ℝ) :
    HasDerivAt negExpPoly5 (-1 + z - z ^ 2 / 2 + z ^ 3 / 6 - z ^ 4 / 24) z := by
  convert (((((hasDerivAt_const z (1 : ℝ)).sub (hasDerivAt_id z)).add
    (((hasDerivAt_id z).pow 2).div_const 2)).sub
    (((hasDerivAt_id z).pow 3).div_const 6)).add
    (((hasDerivAt_id z).pow 4).div_const 24)).sub
    (((hasDerivAt_id z).pow 5).div_const 120) using 1 <;>
    try funext x
  all_goals dsimp [negExpPoly5] <;> ring

lemma hasDerivAt_exp_mul_negExpPoly5 (z : ℝ) :
    HasDerivAt (fun x : ℝ => Real.exp x * negExpPoly5 x)
      (-Real.exp z * z ^ 5 / 120) z := by
  convert (Real.hasDerivAt_exp z).mul (hasDerivAt_negExpPoly5 z) using 1
  dsimp [negExpPoly5]
  ring

/-- The odd Taylor polynomial lies below exp(-z) for every nonnegative z. -/
lemma negExpPoly5_le_exp_neg (z : ℝ) (hz : 0 ≤ z) :
    negExpPoly5 z ≤ Real.exp (-z) := by
  have hanti : AntitoneOn (fun x : ℝ => Real.exp x * negExpPoly5 x) (Ici 0) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
    · unfold negExpPoly5
      fun_prop
    · intro x hx
      exact (hasDerivAt_exp_mul_negExpPoly5 x).hasDerivWithinAt
    · intro x hx
      have hx0 : 0 ≤ x := (interior_subset hx : x ∈ Ici (0 : ℝ))
      have hp : 0 ≤ Real.exp x * x ^ 5 / 120 := by positivity
      linarith only [hp]
  have hprod : Real.exp z * negExpPoly5 z ≤ 1 := by
    simpa [negExpPoly5] using hanti (show (0 : ℝ) ∈ Ici 0 from le_rfl) hz hz
  apply (mul_le_mul_iff_right₀ (Real.exp_pos z)).mp
  calc
    Real.exp z * negExpPoly5 z ≤ 1 := hprod
    _ = Real.exp z * Real.exp (-z) := by rw [← Real.exp_add]; simp

/-- An exact certificate on [0,81/100]; no sampled interval values occur. -/
lemma quartic_le_negExpPoly5 (z : ℝ) (_hz0 : 0 ≤ z) (hz1 : z ≤ 81 / 100) :
    1 - z + (23 / 60 : ℝ) * z ^ 2 ≤ negExpPoly5 z := by
  have hfirst : 0 ≤ ((81 / 100 : ℝ) - z) * (10 - 2 * (z + 81 / 100)) / 60 := by
    apply div_nonneg
    · exact mul_nonneg (by linarith) (by linarith)
    · norm_num
  have hlast : 0 ≤ z ^ 2 * (1 - z) / 120 := by
    exact div_nonneg (mul_nonneg (sq_nonneg z) (by linarith)) (by norm_num)
  have hcoeff : 0 ≤ 7 / 60 - z / 6 + z ^ 2 / 24 - z ^ 3 / 120 := by
    have hid : 7 / 60 - z / 6 + z ^ 2 / 24 - z ^ 3 / 120 =
        (1061 / 300000 : ℝ) + ((81 / 100 : ℝ) - z) *
          (10 - 2 * (z + 81 / 100)) / 60 + z ^ 2 * (1 - z) / 120 := by ring
    rw [hid]
    positivity
  have hp := mul_nonneg (sq_nonneg z) hcoeff
  dsimp only [negExpPoly5]
  nlinarith only [hp]

/-- The actual CF squared, throughout the physical band. -/
theorem norm_charFun_sq_le_gaussian (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (h4 : Integrable (fun x : ℝ => x ^ 4) (μ : Measure ℝ))
    (hcap : moment μ 4 ≤ 8 / 5) (t : ℝ) (ht : |t| ≤ 9 / 10) :
    ‖charFun (μ : Measure ℝ) t‖ ^ 2 ≤ Real.exp (-(t ^ 2)) := by
  have ht2 : t ^ 2 ≤ (81 : ℝ) / 100 := by
    have habs := (sq_le_sq₀ (abs_nonneg t) (by norm_num : (0 : ℝ) ≤ 9 / 10)).mpr ht
    norm_num only [sq_abs] at habs
    norm_num at habs ⊢
    exact habs
  have hcoeff := mul_le_mul_of_nonneg_right hcap (show (0 : ℝ) ≤ t ^ 4 by positivity)
  calc
    ‖charFun (μ : Measure ℝ) t‖ ^ 2 ≤ 1 - t ^ 2 + (moment μ 4 + 3) * t ^ 4 / 12 :=
      norm_charFun_sq_le_quartic μ h h4 t
    _ ≤ 1 - t ^ 2 + (23 / 60 : ℝ) * (t ^ 2) ^ 2 := by nlinarith only [hcoeff]
    _ ≤ negExpPoly5 (t ^ 2) := quartic_le_negExpPoly5 _ (sq_nonneg t) ht2
    _ ≤ Real.exp (-(t ^ 2)) := negExpPoly5_le_exp_neg _ (sq_nonneg t)

theorem norm_charFun_le_gaussian (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (h4 : Integrable (fun x : ℝ => x ^ 4) (μ : Measure ℝ))
    (hcap : moment μ 4 ≤ 8 / 5) (t : ℝ) (ht : |t| ≤ 9 / 10) :
    ‖charFun (μ : Measure ℝ) t‖ ≤ Real.exp (-(t ^ 2) / 2) := by
  apply (sq_le_sq₀ (norm_nonneg _) (Real.exp_pos _).le).mp
  calc
    ‖charFun (μ : Measure ℝ) t‖ ^ 2 ≤ Real.exp (-(t ^ 2)) :=
      norm_charFun_sq_le_gaussian μ h h4 hcap t ht
    _ = (Real.exp (-(t ^ 2) / 2)) ^ 2 := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

/-- Natural powers include n=0 and use the original physical frequency t. -/
theorem norm_charFun_pow_le_gaussian (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (h4 : Integrable (fun x : ℝ => x ^ 4) (μ : Measure ℝ))
    (hcap : moment μ 4 ≤ 8 / 5) (n : ℕ) (t : ℝ) (ht : |t| ≤ 9 / 10) :
    ‖charFun (μ : Measure ℝ) t ^ n‖ ≤ Real.exp (-(n : ℝ) * t ^ 2 / 2) := by
  rw [norm_pow]
  calc
    ‖charFun (μ : Measure ℝ) t‖ ^ n ≤ (Real.exp (-(t ^ 2) / 2)) ^ n :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_charFun_le_gaussian μ h h4 hcap t ht) n
    _ = Real.exp (-(n : ℝ) * t ^ 2 / 2) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

/-- Same-law acquisition from the support and rho premises already available
in N26P39ResourceAcquisition, without a defect or phase premise. -/
theorem norm_charFun_pow_le_gaussian_of_support (μ : ProbabilityMeasure ℝ)
    (h : StandardizedLaw μ)
    (hs : (μ : Measure ℝ).support ⊆ Icc (-(12 / 5 : ℝ)) (12 / 5))
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10)
    (n : ℕ) (t : ℝ) (ht : |t| ≤ 9 / 10) :
    ‖charFun (μ : Measure ℝ) t ^ n‖ ≤ Real.exp (-(n : ℝ) * t ^ 2 / 2) := by
  have habs4 := ConservedResource.integrable_abs_pow_of_bounded_support μ (12 / 5) hs 4
  have h4 : Integrable (fun x : ℝ => x ^ 4) (μ : Measure ℝ) := by
    have heq : (fun x : ℝ => |x| ^ 4) = (fun x : ℝ => x ^ 4) := by
      funext x
      rw [← abs_pow, abs_of_nonneg (by positivity : (0 : ℝ) ≤ x ^ 4)]
    rw [heq] at habs4
    exact habs4
  have hcap := (N26P39ResourceAcquisition.moment_caps_of_support μ h hs hρ).1
  rw [← moment_four_eq_abs] at hcap
  exact norm_charFun_pow_le_gaussian μ h h4 (by linarith only [hcap]) n t ht

/-- The literal physical-frequency middle CF contribution. -/
def middleCF (μ : ProbabilityMeasure ℝ) : ℝ :=
  ∫ t in (1 / 2 : ℝ)..(9 / 10), ‖charFun (μ : Measure ℝ) t ^ 26‖ / t ^ 3

lemma middleCF_intervalIntegrable (μ : ProbabilityMeasure ℝ) :
    IntervalIntegrable (fun t : ℝ => ‖charFun (μ : Measure ℝ) t ^ 26‖ / t ^ 3)
      volume (1 / 2) (9 / 10) := by
  apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
  have hc : Continuous (charFun (μ : Measure ℝ)) := continuous_charFun
  exact (hc.pow 26).norm.continuousOn.div
    (continuous_id.pow 3).continuousOn (fun t ht => pow_ne_zero 3 (by linarith only [ht.1]))

/-- L1 on the actual middle set follows from CF continuity away from zero. -/
lemma middleCF_integrable (μ : ProbabilityMeasure ℝ) :
    IntegrableOn (fun t : ℝ => ‖charFun (μ : Measure ℝ) t ^ 26‖ / t ^ 3)
      (Ioc (1 / 2 : ℝ) (9 / 10)) :=
  (middleCF_intervalIntegrable μ).1

lemma middleCF_eq_setIntegral (μ : ProbabilityMeasure ℝ) :
    middleCF μ = ∫ t in Ioc (1 / 2 : ℝ) (9 / 10),
      ‖charFun (μ : Measure ℝ) t ^ 26‖ / t ^ 3 := by
  exact intervalIntegral.integral_of_le (by norm_num)

lemma middleCF_integrand_le (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (h4 : Integrable (fun x : ℝ => x ^ 4) (μ : Measure ℝ))
    (hcap : moment μ 4 ≤ 8 / 5) (t : ℝ) (ht : t ∈ Icc (1 / 2 : ℝ) (9 / 10)) :
    ‖charFun (μ : Measure ℝ) t ^ 26‖ / t ^ 3 ≤
      16 * t * Real.exp (-13 * t ^ 2) := by
  have ht0 : 0 < t := by linarith only [ht.1]
  have hb : ‖charFun (μ : Measure ℝ) t ^ 26‖ ≤ Real.exp (-13 * t ^ 2) := by
    convert norm_charFun_pow_le_gaussian μ h h4 hcap 26 t
      (by rw [abs_of_pos ht0]; exact ht.2) using 1 <;> congr 1 <;> ring
  calc
    ‖charFun (μ : Measure ℝ) t ^ 26‖ / t ^ 3 ≤ Real.exp (-13 * t ^ 2) / t ^ 3 :=
      div_le_div_of_nonneg_right hb (pow_nonneg ht0.le 3)
    _ ≤ 16 * t * Real.exp (-13 * t ^ 2) := by
      apply (div_le_iff₀ (pow_pos ht0 3)).mpr
      have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) ht.1 4
      have hp := mul_le_mul_of_nonneg_left hpow (Real.exp_nonneg (-13 * t ^ 2))
      rw [show ((1 / 2 : ℝ) ^ 4) = 1 / 16 by norm_num] at hp
      nlinarith only [hp]

lemma middle_gaussian_integral :
    (∫ t in (1 / 2 : ℝ)..(9 / 10), 16 * t * Real.exp (-13 * t ^ 2)) ≤
      (8 / 13 : ℝ) * Real.exp (-(13 : ℝ) / 4) := by
  have hd (t : ℝ) : HasDerivAt (fun x : ℝ => (-8 / 13) * Real.exp (-13 * x ^ 2))
      (16 * t * Real.exp (-13 * t ^ 2)) t := by
    convert (((hasDerivAt_id t).pow 2).const_mul (-13)).exp.const_mul (-8 / 13) using 1 <;>
      try funext x
    all_goals dsimp <;> ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    ((by fun_prop : Continuous (fun t : ℝ => 16 * t * Real.exp (-13 * t ^ 2))).intervalIntegrable _ _)]
  norm_num
  have hp := Real.exp_nonneg (-(1053 : ℝ) / 100)
  nlinarith only [hp]

/-- Entire middle-band control, by a Gaussian primitive rather than quadrature. -/
theorem middleCF_le_gaussian (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (h4 : Integrable (fun x : ℝ => x ^ 4) (μ : Measure ℝ))
    (hcap : moment μ 4 ≤ 8 / 5) :
    middleCF μ ≤ (8 / 13 : ℝ) * Real.exp (-(13 : ℝ) / 4) := by
  apply le_trans _ middle_gaussian_integral
  exact intervalIntegral.integral_mono_on (by norm_num) (middleCF_intervalIntegrable μ)
    ((by fun_prop : Continuous (fun t : ℝ => 16 * t * Real.exp (-13 * t ^ 2))).intervalIntegrable
      (1 / 2) (9 / 10)) (fun t ht => middleCF_integrand_le μ h h4 hcap t ht)

/-- A finite positive exponential series proves this rational constant. -/
lemma exp_neg_thirteen_quarters_le : Real.exp (-(13 : ℝ) / 4) ≤ 1 / 25 := by
  have hs := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 13 / 4) 10
  have h25 : (25 : ℝ) ≤ Real.exp (13 / 4) := by
    norm_num [Finset.sum_range_succ] at hs
    linarith only [hs]
  have hp : Real.exp (-(13 : ℝ) / 4) * Real.exp (13 / 4) = 1 := by
    rw [← Real.exp_add]
    norm_num
  have hm := mul_le_mul_of_nonneg_left h25 (Real.exp_nonneg (-(13 : ℝ) / 4))
  rw [hp] at hm
  linarith only [hm]

theorem sqrt_twenty_six_mul_middleCF_le (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (h4 : Integrable (fun x : ℝ => x ^ 4) (μ : Measure ℝ))
    (hcap : moment μ 4 ≤ 8 / 5) :
    Real.sqrt 26 * middleCF μ ≤ (204 : ℝ) / 1625 := by
  have hm : middleCF μ ≤ (8 : ℝ) / 325 := by
    calc
      middleCF μ ≤ (8 / 13 : ℝ) * Real.exp (-(13 : ℝ) / 4) := middleCF_le_gaussian μ h h4 hcap
      _ ≤ (8 / 13 : ℝ) * (1 / 25) :=
        mul_le_mul_of_nonneg_left exp_neg_thirteen_quarters_le (by norm_num)
      _ = _ := by norm_num
  have hs : Real.sqrt (26 : ℝ) ≤ (51 : ℝ) / 10 := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 26), Real.sqrt_nonneg (26 : ℝ)]
  calc
    Real.sqrt 26 * middleCF μ ≤ Real.sqrt 26 * ((8 : ℝ) / 325) :=
      mul_le_mul_of_nonneg_left hm (Real.sqrt_nonneg _)
    _ ≤ ((51 : ℝ) / 10) * (8 / 325) := mul_le_mul_of_nonneg_right hs (by norm_num)
    _ = _ := by norm_num

theorem sqrt_twenty_six_mul_middleCF_lt (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (h4 : Integrable (fun x : ℝ => x ^ 4) (μ : Measure ℝ))
    (hcap : moment μ 4 ≤ 8 / 5) :
    Real.sqrt 26 * middleCF μ < (63 : ℝ) / 500 :=
  (sqrt_twenty_six_mul_middleCF_le μ h h4 hcap).trans_lt (by norm_num)

lemma middleCF_eq_initial_integral (μ : ProbabilityMeasure ℝ) :
    middleCF μ = ∫ t in Icc (1 / 2 : ℝ) HighFrequencyDamping.cutoff,
      HighFrequencyDamping.initialIntegrand μ 26 t := by
  rw [integral_Icc_eq_integral_Ioc]
  exact middleCF_eq_setIntegral μ

/-- The existing FourierSplit middle-price input, with the same physical
frequency and the same law as in the characteristic-function theorem. -/
theorem initial_segment_cost_le (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (h4 : Integrable (fun x : ℝ => x ^ 4) (μ : Measure ℝ))
    (hcap : moment μ 4 ≤ 8 / 5) :
    Real.sqrt 26 * (∫ t in Icc (1 / 2 : ℝ) HighFrequencyDamping.cutoff,
      HighFrequencyDamping.initialIntegrand μ 26 t) ≤ (204 : ℝ) / 1625 := by
  rw [← middleCF_eq_initial_integral]
  exact sqrt_twenty_six_mul_middleCF_le μ h h4 hcap

theorem initial_segment_cost_le_of_support (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hs : (μ : Measure ℝ).support ⊆ Icc (-(12 / 5 : ℝ)) (12 / 5))
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) :
    Real.sqrt 26 * (∫ t in Icc (1 / 2 : ℝ) HighFrequencyDamping.cutoff,
      HighFrequencyDamping.initialIntegrand μ 26 t) ≤ (204 : ℝ) / 1625 := by
  have habs4 := ConservedResource.integrable_abs_pow_of_bounded_support μ (12 / 5) hs 4
  have h4 : Integrable (fun x : ℝ => x ^ 4) (μ : Measure ℝ) := by
    have heq : (fun x : ℝ => |x| ^ 4) = (fun x : ℝ => x ^ 4) := by
      funext x
      rw [← abs_pow, abs_of_nonneg (by positivity : (0 : ℝ) ≤ x ^ 4)]
    rw [heq] at habs4
    exact habs4
  have hcap := (N26P39ResourceAcquisition.moment_caps_of_support μ h hs hρ).1
  rw [← moment_four_eq_abs] at hcap
  exact initial_segment_cost_le μ h h4 (by linarith only [hcap])

/-- The original-law N26/rho≤1.1 endpoint acquires its own support and
fourth-moment cap; no raw price, defect ceiling or phase is a premise. -/
theorem original_initial_segment_cost_le (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (H C : ℝ) (hm : ContactVariation.PositiveClosedMaximum μ 26 H C)
    (hprev : Extremizer.fixedNSup 25 ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) :
    Real.sqrt 26 * (∫ t in Icc (1 / 2 : ℝ) HighFrequencyDamping.cutoff,
      HighFrequencyDamping.initialIntegrand μ 26 t) ≤ (204 : ℝ) / 1625 :=
  initial_segment_cost_le_of_support μ h
    (N26P39ResourceAcquisition.original_support μ h H C hm hprev hC hρ) hρ

end BerryEsseen.LowMomentGaussianBand

#print axioms BerryEsseen.LowMomentGaussianBand.negExpPoly5_le_exp_neg
#print axioms BerryEsseen.LowMomentGaussianBand.norm_charFun_le_gaussian
#print axioms BerryEsseen.LowMomentGaussianBand.norm_charFun_pow_le_gaussian
#print axioms BerryEsseen.LowMomentGaussianBand.norm_charFun_pow_le_gaussian_of_support
#print axioms BerryEsseen.LowMomentGaussianBand.middleCF_integrable
#print axioms BerryEsseen.LowMomentGaussianBand.middleCF_le_gaussian
#print axioms BerryEsseen.LowMomentGaussianBand.sqrt_twenty_six_mul_middleCF_le
#print axioms BerryEsseen.LowMomentGaussianBand.initial_segment_cost_le
#print axioms BerryEsseen.LowMomentGaussianBand.original_initial_segment_cost_le
