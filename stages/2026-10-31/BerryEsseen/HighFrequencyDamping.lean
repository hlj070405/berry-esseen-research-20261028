module

public import BerryEsseen.CharacteristicExpansion

@[expose] public section

/-! 2026-10-28: the original high-frequency initial segment, for the actual
characteristic function of an arbitrary standardized law with finite fourth
moment. The quartic input is the proved independent-difference integral. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators Interval
open BerryEsseen.CharacteristicExpansion

namespace BerryEsseen.HighFrequencyDamping

def cutoff : ℝ := 9 / 10
def quarticEnvelope (M u : ℝ) : ℝ := 1 - u + (M + 3) * u ^ 2 / 12
def dampingRate (M : ℝ) : ℝ :=
  (1 - max (quarticEnvelope M (1 / 4)) (quarticEnvelope M (81 / 100))) / 2
def chordBase (M : ℝ) : ℝ := 1 / 8 - (M + 3) / 384
def chordSlope (M : ℝ) : ℝ := (1 - (M + 3) * 53 / 600) / 2

lemma square_mem (t : ℝ) (ht : t ∈ Icc (1 / 2 : ℝ) cutoff) :
    t ^ 2 ∈ Icc (1 / 4 : ℝ) (81 / 100) := by
  dsimp only [cutoff] at ht
  constructor
  · nlinarith [mul_nonneg (show 0 ≤ t - 1 / 2 by linarith [ht.1])
      (show 0 ≤ t + 1 / 2 by linarith [ht.1])]
  · nlinarith [mul_nonneg (show 0 ≤ 9 / 10 - t by linarith [ht.2])
      (show 0 ≤ t + 9 / 10 by linarith [ht.1])]

/-- The convex quartic in t is bounded by the maximum at the two original endpoints. -/
lemma quarticEnvelope_le_max (M u : ℝ) (hM : 0 ≤ M)
    (hu : u ∈ Icc (1 / 4 : ℝ) (81 / 100)) :
    quarticEnvelope M u ≤
      max (quarticEnvelope M (1 / 4)) (quarticEnvelope M (81 / 100)) := by
  let Q := max (quarticEnvelope M (1 / 4)) (quarticEnvelope M (81 / 100))
  have hleft : quarticEnvelope M (1 / 4) ≤ Q := le_max_left _ _
  have hright : quarticEnvelope M (81 / 100) ≤ Q := le_max_right _ _
  have hL := mul_le_mul_of_nonneg_right hleft (sub_nonneg.mpr hu.2)
  have hR := mul_le_mul_of_nonneg_right hright (sub_nonneg.mpr hu.1)
  have hprod : 0 ≤ (M + 3) * (u - 1 / 4) * (81 / 100 - u) :=
    mul_nonneg (mul_nonneg (by linarith) (sub_nonneg.mpr hu.1)) (sub_nonneg.mpr hu.2)
  dsimp only [quarticEnvelope] at *
  change 1 - u + (M + 3) * u ^ 2 / 12 ≤ Q
  nlinarith

theorem dampingRate_pos (M : ℝ) (hM : M ≤ 111 / 10) : 0 < dampingRate M := by
  unfold dampingRate
  apply div_pos _ (by norm_num)
  apply sub_pos.mpr
  apply max_lt <;> dsimp only [quarticEnvelope] <;> nlinarith

/-- Exponentiation of the actual symmetrization bound, before taking an endpoint maximum. -/
theorem characteristic_quartic_damping (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (h4 : Integrable (fun x : ℝ => x ^ 4) (μ : Measure ℝ)) (t M : ℝ)
    (hcap : moment μ 4 ≤ M) :
    ‖charFun (μ : Measure ℝ) t‖ ≤ Real.exp (-(t ^ 2 / 2 - (M + 3) * t ^ 4 / 24)) := by
  have hb := norm_charFun_sq_le_quartic μ h h4 t
  have hcapT := mul_le_mul_of_nonneg_right hcap (show 0 ≤ t ^ 4 by positivity)
  have hs : ‖charFun (μ : Measure ℝ) t‖ ^ 2 ≤
      (Real.exp (-(t ^ 2 / 2 - (M + 3) * t ^ 4 / 24))) ^ 2 := by
    calc
      _ ≤ 1 - (t ^ 2 - (M + 3) * t ^ 4 / 12) := by nlinarith
      _ ≤ Real.exp (-(t ^ 2 - (M + 3) * t ^ 4 / 12)) := Real.one_sub_le_exp_neg _
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  exact (sq_le_sq₀ (norm_nonneg _) (Real.exp_pos _).le).mp hs

/-- The paper's original rate c, with no density or support assumption. -/
theorem characteristic_initial_damping (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (h4 : Integrable (fun x : ℝ => x ^ 4) (μ : Measure ℝ)) (t M : ℝ)
    (ht : t ∈ Icc (1 / 2 : ℝ) cutoff) (hcap : moment μ 4 ≤ M) :
    ‖charFun (μ : Measure ℝ) t‖ ≤ Real.exp (-dampingRate M) := by
  have hM : 0 ≤ M := (moment_four_nonneg μ).trans hcap
  have hp := quarticEnvelope_le_max M (t ^ 2) hM (square_mem t ht)
  have hd := characteristic_quartic_damping μ h h4 t M hcap
  apply hd.trans
  apply Real.exp_le_exp.mpr
  dsimp only [quarticEnvelope, dampingRate] at *
  nlinarith

theorem characteristic_power_initial_damping (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (h4 : Integrable (fun x : ℝ => x ^ 4) (μ : Measure ℝ)) (n : ℕ) (_hn : 0 < n) (t M : ℝ)
    (ht : t ∈ Icc (1 / 2 : ℝ) cutoff) (hcap : moment μ 4 ≤ M) :
    ‖charFun (μ : Measure ℝ) t‖ ^ n ≤ Real.exp (-(n : ℝ) * dampingRate M) := by
  calc
    _ ≤ (Real.exp (-dampingRate M)) ^ n :=
      pow_le_pow_left₀ (norm_nonneg _) (characteristic_initial_damping μ h h4 t M ht hcap) n
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

/-- The sharper chord retains its full t² dependence. -/
theorem quartic_chord (M t : ℝ) (hM : 0 ≤ M)
    (ht : t ∈ Icc (1 / 2 : ℝ) cutoff) :
    chordBase M + chordSlope M * (t ^ 2 - 1 / 4) ≤
      t ^ 2 / 2 - (M + 3) * t ^ 4 / 24 := by
  have ht2 := square_mem t ht
  have hprod : 0 ≤ (M + 3) * (t ^ 2 - 1 / 4) * (81 / 100 - t ^ 2) / 24 := by
    exact div_nonneg (mul_nonneg (mul_nonneg (by linarith) (sub_nonneg.mpr ht2.1))
      (sub_nonneg.mpr ht2.2)) (by norm_num)
  dsimp only [chordBase, chordSlope]
  nlinarith

theorem characteristic_power_chord_damping (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (h4 : Integrable (fun x : ℝ => x ^ 4) (μ : Measure ℝ)) (n : ℕ) (_hn : 0 < n) (t M : ℝ)
    (ht : t ∈ Icc (1 / 2 : ℝ) cutoff) (hcap : moment μ 4 ≤ M) :
    ‖charFun (μ : Measure ℝ) t‖ ^ n ≤
      Real.exp (-(n : ℝ) * (chordBase M + chordSlope M * (t ^ 2 - 1 / 4))) := by
  have hc := quartic_chord M t ((moment_four_nonneg μ).trans hcap) ht
  have hd := characteristic_quartic_damping μ h h4 t M hcap
  have hb : ‖charFun (μ : Measure ℝ) t‖ ≤
      Real.exp (-(chordBase M + chordSlope M * (t ^ 2 - 1 / 4))) :=
    hd.trans (Real.exp_le_exp.mpr (neg_le_neg hc))
  calc
    _ ≤ (Real.exp (-(chordBase M + chordSlope M * (t ^ 2 - 1 / 4)))) ^ n :=
      pow_le_pow_left₀ (norm_nonneg _) hb n
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

def initialIntegrand (μ : ProbabilityMeasure ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  ‖charFun (μ : Measure ℝ) t ^ n‖ / t ^ 3

lemma measurable_initialIntegrand (μ : ProbabilityMeasure ℝ) (n : ℕ) :
    Measurable (initialIntegrand μ n) := by
  have hc : Continuous (fun p : ℝ × ℝ => Complex.exp (((p.1 * p.2 : ℝ) : ℂ) * Complex.I)) := by fun_prop
  have hi := hc.stronglyMeasurable.integral_prod_right' (ν := (μ : Measure ℝ))
  have heq : charFun (μ : Measure ℝ) = (fun t : ℝ =>
      ∫ x : ℝ, Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) ∂(μ : Measure ℝ)) := by
    ext t
    rw [charFun_apply_real]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by simp only [Complex.ofReal_mul]
  have hf : Measurable (charFun (μ : Measure ℝ)) := by rw [heq]; exact hi.measurable
  unfold initialIntegrand
  fun_prop

lemma integrableOn_inverse_cube :
    IntegrableOn (fun t : ℝ => 1 / t ^ 3) (Icc (1 / 2 : ℝ) cutoff) := by
  apply ContinuousOn.integrableOn_Icc
  apply continuousOn_const.div (continuousOn_id.pow 3)
  intro t ht
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) ht.1
  change t ^ 3 ≠ 0
  exact pow_ne_zero 3 (ne_of_gt ht0)

lemma integral_inverse_cube :
    (∫ t in Icc (1 / 2 : ℝ) cutoff, 1 / t ^ 3) = 2 - 50 / 81 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num [cutoff] : (1 / 2 : ℝ) ≤ cutoff)]
  have heq : (fun t : ℝ => 1 / t ^ 3) = (fun t : ℝ => t ^ (-3 : ℤ)) := by
    ext t
    simp only [zpow_neg, one_div]
    rfl
  rw [heq, integral_zpow]
  · norm_num [cutoff]
  · right
    constructor
    · norm_num
    · rw [uIcc_of_le (by norm_num [cutoff] : (1 / 2 : ℝ) ≤ cutoff)]
      norm_num

/-- True L¹ of |f(t)^n|/t³ and precisely the original first high-frequency term. -/
theorem initial_segment_cost (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (h4 : Integrable (fun x : ℝ => x ^ 4) (μ : Measure ℝ)) (n : ℕ) (hn : 0 < n) (M : ℝ)
    (hcap : moment μ 4 ≤ M) (_hMupper : M ≤ 111 / 10) :
    IntegrableOn (initialIntegrand μ n) (Icc (1 / 2 : ℝ) cutoff) ∧
      Real.sqrt n * (∫ t in Icc (1 / 2 : ℝ) cutoff, initialIntegrand μ n t) ≤
        2 * Real.sqrt n * Real.exp (-(n : ℝ) * dampingRate M) := by
  let E := Real.exp (-(n : ℝ) * dampingRate M)
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hb : ∀ t ∈ Icc (1 / 2 : ℝ) cutoff,
      initialIntegrand μ n t ≤ E * (1 / t ^ 3) := by
    intro t ht
    have hd := characteristic_power_initial_damping μ h h4 n hn t M ht hcap
    rw [initialIntegrand, norm_pow]
    have ht0 : 0 ≤ t ^ 3 := pow_nonneg (by linarith [ht.1]) 3
    simpa only [mul_one_div] using div_le_div_of_nonneg_right hd ht0
  have hmajor : IntegrableOn (fun t : ℝ => E * (1 / t ^ 3)) (Icc (1 / 2 : ℝ) cutoff) :=
    integrableOn_inverse_cube.const_mul E
  have hi : IntegrableOn (initialIntegrand μ n) (Icc (1 / 2 : ℝ) cutoff) := by
    apply hmajor.mono' (measurable_initialIntegrand μ n).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have ht0 : 0 ≤ t := by linarith [ht.1]
    have hn0 : 0 ≤ initialIntegrand μ n t := div_nonneg (norm_nonneg _) (pow_nonneg ht0 3)
    rw [Real.norm_eq_abs, abs_of_nonneg hn0]
    exact hb t ht
  refine ⟨hi, ?_⟩
  have hp : (∫ t in Icc (1 / 2 : ℝ) cutoff, initialIntegrand μ n t) ≤ E * (2 - 50 / 81) := by
    calc
      _ ≤ ∫ t in Icc (1 / 2 : ℝ) cutoff, E * (1 / t ^ 3) :=
        setIntegral_mono_on hi hmajor measurableSet_Icc hb
      _ = _ := by rw [integral_const_mul, integral_inverse_cube]
  have hp2 : (∫ t in Icc (1 / 2 : ℝ) cutoff, initialIntegrand μ n t) ≤ 2 * E := by nlinarith
  have hfinal := mul_le_mul_of_nonneg_left hp2 (Real.sqrt_nonneg (n : ℝ))
  convert hfinal using 1 <;> dsimp only [E] <;> ring

end BerryEsseen.HighFrequencyDamping

#print axioms BerryEsseen.HighFrequencyDamping.characteristic_power_initial_damping
#print axioms BerryEsseen.HighFrequencyDamping.quartic_chord
#print axioms BerryEsseen.HighFrequencyDamping.characteristic_power_chord_damping
#print axioms BerryEsseen.HighFrequencyDamping.initial_segment_cost
