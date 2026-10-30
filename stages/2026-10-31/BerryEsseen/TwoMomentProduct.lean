module

public import BerryEsseen.TwoMoment
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Probability.Independence.Basic

@[expose] public section

/-!
The actual two-point reference measure and preservation of the squared
positive-part comparison under independent addition. The product
comparisons use nonnegative integrals, so the independent outer variable
needs no moment or integrability assumption.
-/

namespace BerryEsseen.TwoMoment

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- The centered two-point reference measure on the real line. -/
def referenceLaw (a z : ℝ) : Measure ℝ :=
  ENNReal.ofReal (z / (a ^ 2 + z)) • Measure.dirac a +
    ENNReal.ofReal (a ^ 2 / (a ^ 2 + z)) • Measure.dirac (-z / a)

theorem referenceLaw_isProbabilityMeasure (a z : ℝ) (ha : 0 < a) (hz : 0 ≤ z) :
    IsProbabilityMeasure (referenceLaw a z) := by
  have hd : 0 < a ^ 2 + z := add_pos_of_pos_of_nonneg (sq_pos_of_pos ha) hz
  have hw₁ : 0 ≤ z / (a ^ 2 + z) := div_nonneg hz hd.le
  have hw₂ : 0 ≤ a ^ 2 / (a ^ 2 + z) := div_nonneg (sq_nonneg _) hd.le
  have hsum : z / (a ^ 2 + z) + a ^ 2 / (a ^ 2 + z) = 1 := by
    field_simp [hd.ne'] ; ring
  constructor
  calc
    referenceLaw a z Set.univ = ENNReal.ofReal (z / (a ^ 2 + z)) +
        ENNReal.ofReal (a ^ 2 / (a ^ 2 + z)) := by simp [referenceLaw]
    _ = ENNReal.ofReal (z / (a ^ 2 + z) + a ^ 2 / (a ^ 2 + z)) :=
      (ENNReal.ofReal_add hw₁ hw₂).symm
    _ = 1 := by rw [hsum]; simp

theorem integrable_referenceLaw (a z : ℝ) (f : ℝ → ℝ) :
    Integrable f (referenceLaw a z) := by
  exact ((integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top).add_measure
    ((integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top)

/-- Exact integration against the reference measure, without a
measurability restriction on a test function on its two-point support. -/
theorem integral_referenceLaw (a z : ℝ) (ha : 0 < a) (hz : 0 ≤ z) (f : ℝ → ℝ) :
    (∫ x, f x ∂referenceLaw a z) =
      z / (a ^ 2 + z) * f a + a ^ 2 / (a ^ 2 + z) * f (-z / a) := by
  have hw₁ : 0 ≤ z / (a ^ 2 + z) := div_nonneg hz (by positivity)
  have hw₂ : 0 ≤ a ^ 2 / (a ^ 2 + z) := div_nonneg (sq_nonneg _) (by positivity)
  unfold referenceLaw
  rw [integral_add_measure
    ((integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top)
    ((integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top)]
  simp only [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal hw₁,
    ENNReal.toReal_ofReal hw₂, smul_eq_mul]

theorem integral_referenceLaw_id (a z : ℝ) (ha : 0 < a) (hz : 0 ≤ z) :
    (∫ x, x ∂referenceLaw a z) = 0 := by
  rw [integral_referenceLaw a z ha hz]
  have hd : 0 < a ^ 2 + z := add_pos_of_pos_of_nonneg (sq_pos_of_pos ha) hz
  field_simp [ha.ne', hd.ne'] ; ring

theorem integral_referenceLaw_sq (a z : ℝ) (ha : 0 < a) (hz : 0 ≤ z) :
    (∫ x, x ^ 2 ∂referenceLaw a z) = z := by
  rw [integral_referenceLaw a z ha hz]
  simpa using reference_full_square a z 0 ha hz

theorem integral_referenceLaw_squarePositivePart (a z c : ℝ)
    (ha : 0 < a) (hz : 0 ≤ z) :
    (∫ x, (max (x - c) 0) ^ 2 ∂referenceLaw a z) = referencePrice a z c :=
  integral_referenceLaw a z ha hz _

theorem referenceLaw_zero (a : ℝ) (ha : 0 < a) :
    referenceLaw a 0 = Measure.dirac 0 := by
  simp [referenceLaw, ha.ne']

theorem referenceLaw_upper (a z : ℝ) (ha : 0 < a) (hz : 0 ≤ z) :
    ∀ᵐ x ∂referenceLaw a z, x ≤ a := by
  rw [referenceLaw, ae_add_measure_iff]
  constructor
  · exact Measure.ae_smul_measure (by simp) _
  · apply Measure.ae_smul_measure _ _
    exact (ae_dirac_iff measurableSet_Iic).mpr ((lowerAtom_nonpos a z ha hz).trans ha.le)

/-- Nonnegative-integral form of the squared-positive-part order.
It remains meaningful when an independent summand has infinite moments. -/
def SquarePositiveOrder (μ ν : Measure ℝ) : Prop :=
  ∀ c : ℝ, (∫⁻ x, ENNReal.ofReal ((max (x - c) 0) ^ 2) ∂μ) ≤
    ∫⁻ x, ENNReal.ofReal ((max (x - c) 0) ^ 2) ∂ν

theorem squarePositiveOrder_refl (μ : Measure ℝ) : SquarePositiveOrder μ μ :=
  fun _ => le_rfl

variable {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]

lemma integrable_squarePositivePart (μ : Measure Ω) [IsFiniteMeasure μ]
    (U : Ω → ℝ) (c : ℝ) (hU : Measurable U)
    (hSq : Integrable (fun ω => U ω ^ 2) μ) :
    Integrable (fun ω => (max (U ω - c) 0) ^ 2) μ := by
  have hI := integrable_of_integrable_sq μ U hU hSq
  have hshift := integrable_shift_sq μ U c hI hSq
  apply hshift.mono'
    (((hU.sub measurable_const).max measurable_const).pow_const 2).aestronglyMeasurable
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact positivePart_sq_le_sq (U ω - c)

theorem squarePositiveOrder_map_referenceLaw (μ : Measure Ω) [IsProbabilityMeasure μ]
    (U : Ω → ℝ) (a z : ℝ) (ha : 0 < a) (hz : 0 ≤ z) (hU : Measurable U)
    (hSq : Integrable (fun ω => U ω ^ 2) μ) (hcenter : ∫ ω, U ω ∂μ = 0)
    (hvariance : (∫ ω, U ω ^ 2 ∂μ) ≤ z) (hupper : ∀ᵐ ω ∂μ, U ω ≤ a) :
    SquarePositiveOrder (μ.map U) (referenceLaw a z) := by
  intro c
  have hm : Measurable (fun x : ℝ => ENNReal.ofReal ((max (x - c) 0) ^ 2)) := by fun_prop
  rw [lintegral_map hm hU,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_squarePositivePart μ U c hU hSq)
      (Filter.Eventually.of_forall (fun ω => sq_nonneg _)),
    ← ofReal_integral_eq_lintegral_ofReal (integrable_referenceLaw a z _)
      (Filter.Eventually.of_forall (fun x => sq_nonneg _)),
    integral_referenceLaw_squarePositivePart a z c ha hz]
  exact ENNReal.ofReal_le_ofReal
    (integral_squarePositivePart_le_referencePrice μ U a z c ha hz hU hSq
      hcenter hvariance hupper)

/-- A real-law comparison is preserved after independent addition of an
arbitrary outer random variable. No moment is required of that variable. -/
theorem lintegral_prod_add_le (μ₁ μ₂ : Measure ℝ)
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (ν : Measure Ξ) [IsProbabilityMeasure ν] (V : Ξ → ℝ) (hV : Measurable V)
    (horder : SquarePositiveOrder μ₁ μ₂) (c : ℝ) :
    (∫⁻ p : ℝ × Ξ, ENNReal.ofReal ((max (p.1 + V p.2 - c) 0) ^ 2) ∂μ₁.prod ν) ≤
      ∫⁻ p : ℝ × Ξ, ENNReal.ofReal ((max (p.1 + V p.2 - c) 0) ^ 2) ∂μ₂.prod ν := by
  have hm : Measurable (fun p : ℝ × Ξ =>
      ENNReal.ofReal ((max (p.1 + V p.2 - c) 0) ^ 2)) := by fun_prop
  rw [lintegral_prod_symm _ hm.aemeasurable, lintegral_prod_symm _ hm.aemeasurable]
  apply lintegral_mono
  intro ξ
  have hshift (x : ℝ) : x + V ξ - c = x - (c - V ξ) := by ring
  simpa only [hshift] using horder (c - V ξ)

/-- Independent addition preserves the order in both operands. -/
theorem squarePositiveOrder_add (μ₁ μ₂ ν₁ ν₂ : Measure ℝ)
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂]
    (hμ : SquarePositiveOrder μ₁ μ₂) (hν : SquarePositiveOrder ν₁ ν₂) :
    SquarePositiveOrder ((μ₁.prod ν₁).map (fun p => p.1 + p.2))
      ((μ₂.prod ν₂).map (fun p => p.1 + p.2)) := by
  intro c
  have hm : Measurable (fun x : ℝ => ENNReal.ofReal ((max (x - c) 0) ^ 2)) := by fun_prop
  have hp : Measurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal ((max (p.1 + p.2 - c) 0) ^ 2)) := by fun_prop
  have hadd : Measurable (fun p : ℝ × ℝ => p.1 + p.2) := by fun_prop
  rw [lintegral_map hm hadd, lintegral_map hm hadd]
  calc
    _ ≤ ∫⁻ p : ℝ × ℝ, ENNReal.ofReal ((max (p.1 + p.2 - c) 0) ^ 2) ∂μ₂.prod ν₁ :=
      lintegral_prod_add_le μ₁ μ₂ ν₁ id measurable_id hμ c
    _ ≤ _ := by
      rw [lintegral_prod _ hp.aemeasurable, lintegral_prod _ hp.aemeasurable]
      apply lintegral_mono
      intro x
      have hshift (y : ℝ) : x + y - c = y - (c - x) := by ring
      simpa only [hshift] using hν (c - x)

/-- The same-space independence interface: the reference summand is
independent of the unchanged outer marginal on the right. -/
theorem lintegral_indep_add_le_referenceLaw (μ : Measure Ω) [IsProbabilityMeasure μ]
    (U V : Ω → ℝ) (a z c : ℝ) (ha : 0 < a) (hz : 0 ≤ z)
    (hU : Measurable U) (hV : Measurable V)
    (hindep : ProbabilityTheory.IndepFun U V μ)
    (hSq : Integrable (fun ω => U ω ^ 2) μ) (hcenter : ∫ ω, U ω ∂μ = 0)
    (hvariance : (∫ ω, U ω ^ 2 ∂μ) ≤ z) (hupper : ∀ᵐ ω ∂μ, U ω ≤ a) :
    (∫⁻ ω, ENNReal.ofReal ((max (U ω + V ω - c) 0) ^ 2) ∂μ) ≤
      ∫⁻ p : ℝ × ℝ, ENNReal.ofReal ((max (p.1 + p.2 - c) 0) ^ 2)
        ∂(referenceLaw a z).prod (μ.map V) := by
  have := referenceLaw_isProbabilityMeasure a z ha hz
  have horder := squarePositiveOrder_map_referenceLaw μ U a z ha hz hU hSq
    hcenter hvariance hupper
  have hm : Measurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal ((max (p.1 + p.2 - c) 0) ^ 2)) := by fun_prop
  have hprod := hindep.map_prod_eq_prod_map_map hU.aemeasurable hV.aemeasurable
  calc
    _ = ∫⁻ p : ℝ × ℝ, ENNReal.ofReal ((max (p.1 + p.2 - c) 0) ^ 2)
        ∂(μ.map U).prod (μ.map V) := by
      rw [← hprod, lintegral_map hm (hU.prodMk hV)]
    _ ≤ _ := lintegral_prod_add_le (μ.map U) (referenceLaw a z)
      (μ.map V) id measurable_id horder c

/-- Law of the first `n` independent real coordinates. At each step the
next marginal is combined with the preceding sum by a genuine product
measure and the measurable addition map. The marginals are arbitrary. -/
def finiteIndependentSumLaw (μ : ℕ → Measure ℝ) : ℕ → Measure ℝ
  | 0 => Measure.dirac 0
  | n + 1 => ((μ n).prod (finiteIndependentSumLaw μ n)).map (fun p => p.1 + p.2)

instance finiteIndependentSumLaw_isProbabilityMeasure (μ : ℕ → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (n : ℕ) :
    IsProbabilityMeasure (finiteIndependentSumLaw μ n) := by
  induction n with
  | zero => dsimp [finiteIndependentSumLaw]; infer_instance
  | succ n ih =>
    have := ih
    dsimp [finiteIndependentSumLaw]
    infer_instance

/-- Coordinatewise squared-positive-part order passes to any finite
independent sum. There is no support or moment assumption in this step. -/
theorem squarePositiveOrder_finiteIndependentSumLaw (μ ν : ℕ → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)]
    (horder : ∀ i, SquarePositiveOrder (μ i) (ν i)) (n : ℕ) :
    SquarePositiveOrder (finiteIndependentSumLaw μ n) (finiteIndependentSumLaw ν n) := by
  induction n with
  | zero => exact squarePositiveOrder_refl _
  | succ n ih =>
    exact squarePositiveOrder_add (μ n) (ν n)
      (finiteIndependentSumLaw μ n) (finiteIndependentSumLaw ν n) (horder n) ih

/-- A finite heterogeneous independent sum is dominated by the genuine
independent sum of its two-point reference marginals. The variance bounds
are kept coordinatewise; this theorem performs no variance equalization. -/
theorem squarePositiveOrder_finiteIndependentSumLaw_reference
    (μ : ℕ → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] (a z : ℕ → ℝ)
    (ha : ∀ i, 0 < a i) (hz : ∀ i, 0 ≤ z i)
    (hSq : ∀ i, Integrable (fun x : ℝ => x ^ 2) (μ i))
    (hcenter : ∀ i, (∫ x, x ∂μ i) = 0)
    (hvariance : ∀ i, (∫ x, x ^ 2 ∂μ i) ≤ z i)
    (hupper : ∀ i, ∀ᵐ x ∂μ i, x ≤ a i) (n : ℕ) :
    SquarePositiveOrder (finiteIndependentSumLaw μ n)
      (finiteIndependentSumLaw (fun i => referenceLaw (a i) (z i)) n) := by
  have : ∀ i, IsProbabilityMeasure (referenceLaw (a i) (z i)) :=
    fun i => referenceLaw_isProbabilityMeasure (a i) (z i) (ha i) (hz i)
  apply squarePositiveOrder_finiteIndependentSumLaw
  intro i
  have h := squarePositiveOrder_map_referenceLaw (μ i) id (a i) (z i) (ha i) (hz i)
    measurable_id (hSq i) (hcenter i) (hvariance i) (hupper i)
  simpa only [Measure.map_id] using h

end

end BerryEsseen.TwoMoment

#print axioms BerryEsseen.TwoMoment.referenceLaw_isProbabilityMeasure
#print axioms BerryEsseen.TwoMoment.integral_referenceLaw_id
#print axioms BerryEsseen.TwoMoment.integral_referenceLaw_sq
#print axioms BerryEsseen.TwoMoment.integral_referenceLaw_squarePositivePart
#print axioms BerryEsseen.TwoMoment.referenceLaw_upper
#print axioms BerryEsseen.TwoMoment.squarePositiveOrder_add
#print axioms BerryEsseen.TwoMoment.lintegral_indep_add_le_referenceLaw
#print axioms BerryEsseen.TwoMoment.squarePositiveOrder_finiteIndependentSumLaw_reference
