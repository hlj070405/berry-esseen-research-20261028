module

public import BerryEsseen.CharacteristicExpansion
public import Mathlib.Probability.ConditionalProbability

@[expose] public section

/-! 2026-10-28: the actual product-event conditioning step in the original
high-frequency proof. Events live on the two-coordinate space and need not
be functions of the difference. All oscillatory and exponential tests below
are bounded and genuinely integrable. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open BerryEsseen.CharacteristicExpansion

namespace BerryEsseen.HighFrequencyEvent

def productLaw (μ : ProbabilityMeasure ℝ) : Measure (ℝ × ℝ) :=
  (μ : Measure ℝ).prod (μ : Measure ℝ)

instance productLaw_isProbability (μ : ProbabilityMeasure ℝ) : IsProbabilityMeasure (productLaw μ) := by
  unfold productLaw
  infer_instance

def distance (p : ℝ × ℝ) : ℝ := |p.1 - p.2|
def eventProbability (μ : ProbabilityMeasure ℝ) (E : Set (ℝ × ℝ)) : ℝ := (productLaw μ).real E
def eventLaw (μ : ProbabilityMeasure ℝ) (E : Set (ℝ × ℝ)) : Measure (ℝ × ℝ) :=
  ProbabilityTheory.cond (productLaw μ) E

instance eventLaw_isZeroOrProbability (μ : ProbabilityMeasure ℝ) (E : Set (ℝ × ℝ)) :
    IsZeroOrProbabilityMeasure (eventLaw μ E) := by
  unfold eventLaw
  infer_instance

def oscillation (t : ℝ) (p : ℝ × ℝ) : ℝ := Real.sin (t * distance p / 2) ^ 2
def exponentialTest (n : ℕ) (a t : ℝ) (p : ℝ × ℝ) : ℝ :=
  Real.exp (-(n : ℝ) * a * oscillation t p)

/-- The actual conditional second distance moment; finiteness is supplied
explicitly by `integrable_distance_square_event` when this quantity is used. -/
def conditionalSecondMoment (μ : ProbabilityMeasure ℝ) (E : Set (ℝ × ℝ)) : ℝ :=
  ∫ p, distance p ^ 2 ∂eventLaw μ E

lemma event_measure_ne_zero (μ : ProbabilityMeasure ℝ) (E : Set (ℝ × ℝ))
    (hp : 0 < eventProbability μ E) : productLaw μ E ≠ 0 := by
  exact (measureReal_ne_zero_iff).mp (ne_of_gt hp)

theorem eventLaw_isProbability (μ : ProbabilityMeasure ℝ) (E : Set (ℝ × ℝ))
    (hp : 0 < eventProbability μ E) : IsProbabilityMeasure (eventLaw μ E) := by
  exact cond_isProbabilityMeasure (event_measure_ne_zero μ E hp)

/-- Conditional expectation is the actual restricted integral divided by its mass. -/
lemma integral_eventLaw (μ : ProbabilityMeasure ℝ) (E : Set (ℝ × ℝ)) (g : (ℝ × ℝ) → ℝ) :
    (∫ p, g p ∂eventLaw μ E) = (eventProbability μ E)⁻¹ * ∫ p in E, g p ∂productLaw μ := by
  unfold eventLaw ProbabilityTheory.cond
  rw [integral_smul_measure]
  simp only [ENNReal.toReal_inv, smul_eq_mul, eventProbability, measureReal_def]

lemma eventProbability_mul_integral (μ : ProbabilityMeasure ℝ) (E : Set (ℝ × ℝ))
    (hp : 0 < eventProbability μ E) (g : (ℝ × ℝ) → ℝ) :
    eventProbability μ E * (∫ p, g p ∂eventLaw μ E) = ∫ p in E, g p ∂productLaw μ := by
  rw [integral_eventLaw, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hp), one_mul]

lemma integrable_distance_square_event (μ : ProbabilityMeasure ℝ) (E : Set (ℝ × ℝ))
    (hp : 0 < eventProbability μ E)
    (h2 : Integrable (fun p : ℝ × ℝ => distance p ^ 2) (productLaw μ)) :
    Integrable (fun p : ℝ × ℝ => distance p ^ 2) (eventLaw μ E) := by
  unfold eventLaw ProbabilityTheory.cond
  exact h2.integrableOn.smul_measure (by simp [event_measure_ne_zero μ E hp])

lemma conditionalSecondMoment_normalization (μ : ProbabilityMeasure ℝ) (E : Set (ℝ × ℝ)) :
    conditionalSecondMoment μ E =
      (eventProbability μ E)⁻¹ * ∫ p in E, distance p ^ 2 ∂productLaw μ :=
  integral_eventLaw μ E _

lemma oscillation_nonneg (t : ℝ) (p : ℝ × ℝ) : 0 ≤ oscillation t p := sq_nonneg _
lemma oscillation_le_one (t : ℝ) (p : ℝ × ℝ) : oscillation t p ≤ 1 := Real.sin_sq_le_one _

lemma continuous_oscillation (t : ℝ) : Continuous (oscillation t) := by
  unfold oscillation distance
  fun_prop

lemma integrable_oscillation (ν : Measure (ℝ × ℝ)) [IsFiniteMeasure ν] (t : ℝ) :
    Integrable (oscillation t) ν := by
  apply (integrable_const (1 : ℝ)).mono' (continuous_oscillation t).aestronglyMeasurable
  exact Eventually.of_forall fun p => by
    rw [Real.norm_eq_abs, abs_of_nonneg (oscillation_nonneg t p)]
    exact oscillation_le_one t p

lemma integrable_exponentialTest (ν : Measure (ℝ × ℝ)) [IsFiniteMeasure ν]
    (n : ℕ) (a t : ℝ) (ha : 0 ≤ a) : Integrable (exponentialTest n a t) ν := by
  have hc : Continuous (exponentialTest n a t) := by
    unfold exponentialTest
    exact (continuous_const.mul (continuous_oscillation t)).rexp
  apply (integrable_const (1 : ℝ)).mono' hc.aestronglyMeasurable
  exact Eventually.of_forall fun p => by
    change ‖Real.exp (-(n : ℝ) * a * oscillation t p)‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_one_iff.mpr
    have hh := mul_nonneg (mul_nonneg (Nat.cast_nonneg n) ha) (oscillation_nonneg t p)
    nlinarith

lemma oscillation_eq_signed (t : ℝ) (p : ℝ × ℝ) :
    oscillation t p = Real.sin (t * (p.1 - p.2) / 2) ^ 2 := by
  unfold oscillation distance
  rcases le_or_gt 0 (p.1 - p.2) with hD | hD
  · rw [abs_of_nonneg hD]
  · rw [abs_of_neg hD]
    have heq : t * -(p.1 - p.2) / 2 = -(t * (p.1 - p.2) / 2) := by ring
    rw [heq, Real.sin_neg, neg_sq]

lemma norm_charFun_sq_product_cos (μ : ProbabilityMeasure ℝ) (t : ℝ) :
    ‖charFun (μ : Measure ℝ) t‖ ^ 2 =
      ∫ p : ℝ × ℝ, Real.cos (t * (p.1 - p.2)) ∂productLaw μ := by
  rw [norm_charFun_sq_symmetrization, differenceMeasure_eq_map_product]
  exact integral_map (by fun_prop) (by fun_prop)

/-- The exact identity for the true independent pair, without moment hypotheses. -/
theorem norm_charFun_sq_eq_one_sub_two_oscillation (μ : ProbabilityMeasure ℝ) (t : ℝ) :
    ‖charFun (μ : Measure ℝ) t‖ ^ 2 = 1 - 2 * ∫ p, oscillation t p ∂productLaw μ := by
  rw [norm_charFun_sq_product_cos]
  have heq : (fun p : ℝ × ℝ => Real.cos (t * (p.1 - p.2))) =
      (fun p => 1 - 2 * oscillation t p) := by
    ext p
    rw [oscillation_eq_signed]
    have hs := Real.sin_sq_eq_half_sub (t * (p.1 - p.2) / 2)
    rw [show 2 * (t * (p.1 - p.2) / 2) = t * (p.1 - p.2) by ring] at hs
    linarith
  rw [heq, integral_sub (integrable_const 1) ((integrable_oscillation (productLaw μ) t).const_mul 2),
    integral_const_mul]
  simp only [integral_const, probReal_univ, one_smul]

theorem characteristic_power_oscillation_damping (μ : ProbabilityMeasure ℝ) (n : ℕ)
    (_hn : 0 < n) (t : ℝ) :
    ‖charFun (μ : Measure ℝ) t‖ ^ n ≤
      Real.exp (-(n : ℝ) * ∫ p, oscillation t p ∂productLaw μ) := by
  let q := ∫ p, oscillation t p ∂productLaw μ
  have hsq := norm_charFun_sq_eq_one_sub_two_oscillation μ t
  have hs : ‖charFun (μ : Measure ℝ) t‖ ^ 2 ≤ (Real.exp (-q)) ^ 2 := by
    calc
      _ = 1 - 2 * q := hsq
      _ ≤ Real.exp (-(2 * q)) := Real.one_sub_le_exp_neg _
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hnorm := (sq_le_sq₀ (norm_nonneg _) (Real.exp_pos _).le).mp hs
  calc
    _ ≤ (Real.exp (-q)) ^ n := pow_le_pow_left₀ (norm_nonneg _) hnorm n
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

/-- The probability Jensen inequality for exp, proved by integrating its
supporting line. Both input and exponential integrability are explicit. -/
lemma exp_integral_le_integral_exp {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] (g : α → ℝ)
    (hg : Integrable g ν) (he : Integrable (fun x => Real.exp (g x)) ν) :
    Real.exp (∫ x, g x ∂ν) ≤ ∫ x, Real.exp (g x) ∂ν := by
  let m := ∫ x, g x ∂ν
  have ht : ∀ x, Real.exp m * (1 + (g x - m)) ≤ Real.exp (g x) := by
    intro x
    calc
      _ ≤ Real.exp m * Real.exp (g x - m) :=
        mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (g x - m)]) (Real.exp_pos m).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hi : Integrable (fun x => Real.exp m * (1 + (g x - m))) ν :=
    ((integrable_const 1).add (hg.sub (integrable_const m))).const_mul _
  have hiSub : Integrable (fun x => g x - m) ν := hg.sub (integrable_const m)
  have hiOne : Integrable (fun _ : α => (1 : ℝ)) ν := integrable_const 1
  have hmean : (∫ x, Real.exp m * (1 + (g x - m)) ∂ν) = Real.exp m := by
    rw [integral_const_mul, integral_add hiOne hiSub,
      integral_sub hg (integrable_const m)]
    simp only [integral_const, probReal_univ, one_smul]
    change Real.exp m * (1 + (m - m)) = Real.exp m
    ring
  calc
    _ = ∫ x, Real.exp m * (1 + (g x - m)) ∂ν := hmean.symm
    _ ≤ _ := integral_mono hi he ht

/-- Discarding the complement and replacing the actual event mass by its
lower bound has the direction needed before the decreasing exponential. -/
theorem oscillation_event_comparison (μ : ProbabilityMeasure ℝ) (E : Set (ℝ × ℝ))
    (a t : ℝ) (ha : 0 < a) (hpa : a ≤ eventProbability μ E) :
    a * (∫ p, oscillation t p ∂eventLaw μ E) ≤ ∫ p, oscillation t p ∂productLaw μ := by
  have hp : 0 < eventProbability μ E := ha.trans_le hpa
  have hnonneg : 0 ≤ ∫ p, oscillation t p ∂eventLaw μ E :=
    integral_nonneg (oscillation_nonneg t)
  calc
    _ ≤ eventProbability μ E * (∫ p, oscillation t p ∂eventLaw μ E) :=
      mul_le_mul_of_nonneg_right hpa hnonneg
    _ = ∫ p in E, oscillation t p ∂productLaw μ := eventProbability_mul_integral μ E hp _
    _ ≤ _ := setIntegral_le_integral (integrable_oscillation (productLaw μ) t)
      (Eventually.of_forall (oscillation_nonneg t))

/-- The original high-frequency event Jensen bound for arbitrary measurable
events in the actual independent product space, including coordinate-sign events. -/
theorem characteristic_event_damping (μ : ProbabilityMeasure ℝ) (E : Set (ℝ × ℝ))
    (_hE : MeasurableSet E) (a : ℝ) (ha : 0 < a) (hpa : a ≤ eventProbability μ E)
    (n : ℕ) (hn : 0 < n) (t : ℝ) :
    Integrable (exponentialTest n a t) (eventLaw μ E) ∧
      ‖charFun (μ : Measure ℝ) t‖ ^ n ≤ ∫ p, exponentialTest n a t p ∂eventLaw μ E := by
  letI : IsProbabilityMeasure (eventLaw μ E) := eventLaw_isProbability μ E (ha.trans_le hpa)
  have he := integrable_exponentialTest (eventLaw μ E) n a t ha.le
  refine ⟨he, ?_⟩
  have hcomp := oscillation_event_comparison μ E a t ha hpa
  have hmult := neg_le_neg (mul_le_mul_of_nonneg_left hcomp (Nat.cast_nonneg n))
  have hJ := exp_integral_le_integral_exp (eventLaw μ E)
    (fun p => -(n : ℝ) * a * oscillation t p)
    ((integrable_oscillation (eventLaw μ E) t).const_mul (-(n : ℝ) * a)) he
  rw [integral_const_mul] at hJ
  calc
    _ ≤ Real.exp (-(n : ℝ) * ∫ p, oscillation t p ∂productLaw μ) :=
      characteristic_power_oscillation_damping μ n hn t
    _ ≤ Real.exp (-(n : ℝ) * a * ∫ p, oscillation t p ∂eventLaw μ E) := by
      apply Real.exp_le_exp.mpr
      nlinarith only [hmult]
    _ ≤ _ := hJ

end BerryEsseen.HighFrequencyEvent

#print axioms BerryEsseen.HighFrequencyEvent.eventLaw_isProbability
#print axioms BerryEsseen.HighFrequencyEvent.norm_charFun_sq_eq_one_sub_two_oscillation
#print axioms BerryEsseen.HighFrequencyEvent.characteristic_power_oscillation_damping
#print axioms BerryEsseen.HighFrequencyEvent.characteristic_event_damping
