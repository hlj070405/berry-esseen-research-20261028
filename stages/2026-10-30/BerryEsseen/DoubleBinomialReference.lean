module

public import BerryEsseen.BinomialReferencePrice
public import BerryEsseen.CoupledReferenceOrder
public import BerryEsseen.FiniteAtomicLaw
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-! 2026-10-29: exact finite atomic realization of the actual two-group
reference convolution. The two caps and variances stay separate. Empty
groups and zero variances are included in the same measure identities.
The finite atomic constructor and integration API are reused directly. -/

namespace BerryEsseen.DoubleBinomialReference

open MeasureTheory
open scoped BigOperators NNReal ENNReal

noncomputable section

def upperProbability (b z : ℝ) : ℝ≥0 := Real.toNNReal (z / (b ^ 2 + z))
def lowerProbability (b z : ℝ) : ℝ≥0 := Real.toNNReal (b ^ 2 / (b ^ 2 + z))

theorem coe_upperProbability (b z : ℝ) (hb : 0 < b) (hz : 0 ≤ z) :
    (upperProbability b z : ℝ) = z / (b ^ 2 + z) :=
  Real.coe_toNNReal _ (div_nonneg hz (by positivity))

theorem coe_lowerProbability (b z : ℝ) (hb : 0 < b) (hz : 0 ≤ z) :
    (lowerProbability b z : ℝ) = b ^ 2 / (b ^ 2 + z) :=
  Real.coe_toNNReal _ (div_nonneg (sq_nonneg _) (by positivity))

theorem probabilities_sum (b z : ℝ) (hb : 0 < b) (hz : 0 ≤ z) :
    upperProbability b z + lowerProbability b z = 1 := by
  apply NNReal.coe_injective
  rw [NNReal.coe_add, coe_upperProbability b z hb hz, coe_lowerProbability b z hb hz, NNReal.coe_one]
  have hd : 0 < b ^ 2 + z := by positivity
  field_simp [hd.ne']
  ring

def countWeight (b z : ℝ) (n : ℕ) (j : Fin (n + 1)) : ℝ≥0 :=
  (n.choose (j : ℕ) : ℝ≥0) * upperProbability b z ^ (j : ℕ) *
    lowerProbability b z ^ (n - (j : ℕ))

def countAtom (b z : ℝ) (n : ℕ) (j : Fin (n + 1)) : ℝ :=
  (j : ℕ) * b - ((n - (j : ℕ) : ℕ) : ℝ) * z / b

theorem coe_countWeight (b z : ℝ) (n : ℕ) (j : Fin (n + 1)) (hb : 0 < b) (hz : 0 ≤ z) :
    (countWeight b z n j : ℝ) = (n.choose (j : ℕ) : ℝ) *
      (z / (b ^ 2 + z)) ^ (j : ℕ) * (b ^ 2 / (b ^ 2 + z)) ^ (n - (j : ℕ)) := by
  simp only [countWeight, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_pow,
    coe_upperProbability b z hb hz, coe_lowerProbability b z hb hz]

theorem countWeights_sum (b z : ℝ) (n : ℕ) (hb : 0 < b) (hz : 0 ≤ z) :
    ∑ j : Fin (n + 1), countWeight b z n j = 1 := by
  unfold countWeight
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => (n.choose j : ℝ≥0) *
    upperProbability b z ^ j * lowerProbability b z ^ (n - j))]
  calc
    _ = ∑ j ∈ Finset.range (n + 1), upperProbability b z ^ j *
        lowerProbability b z ^ (n - j) * (n.choose j : ℝ≥0) := by
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = (upperProbability b z + lowerProbability b z) ^ n :=
      (add_pow _ _ n).symm
    _ = 1 := by rw [probabilities_sum b z hb hz, one_pow]

/-- The single-group finite measure identity is proved from the existing
true two-Dirac convolution expansion, rather than from its price formula. -/
theorem convPower_eq_atomic_measure (b z : ℝ) (n : ℕ) (hb : 0 < b) (hz : 0 ≤ z) :
    MixtureSum.convPower (TwoMoment.referenceLaw b z) n =
      FiniteAtomicLaw.measure (countWeight b z n) (countAtom b z n) := by
  have hmix : TwoMoment.referenceLaw b z = lowerProbability b z • Measure.dirac (-z / b) +
      upperProbability b z • Measure.dirac b := by
    rw [TwoMoment.referenceLaw, ← coe_upperProbability b z hb hz, ← coe_lowerProbability b z hb hz]
    simp only [ENNReal.ofReal_coe_nnreal]
    exact add_comm _ _
  rw [hmix, TwoMoment.convPower_twoDirac_eq_binomial_measure]
  unfold FiniteAtomicLaw.measure
  rw [← Fin.sum_univ_eq_sum_range (fun j : ℕ =>
    ((n.choose j : ℝ≥0) * upperProbability b z ^ j * lowerProbability b z ^ (n - j)) •
      Measure.dirac ((j : ℝ) * b + ((n - j : ℕ) : ℝ) * (-z / b)))]
  apply Finset.sum_congr rfl
  intro j hj
  unfold countWeight countAtom
  congr 2
  ring

abbrev Index (n0 n1 : ℕ) := Fin (n0 + 1) × Fin (n1 + 1)

def weights (b0 z0 : ℝ) (n0 : ℕ) (b1 z1 : ℝ) (n1 : ℕ) (i : Index n0 n1) : ℝ≥0 :=
  countWeight b0 z0 n0 i.1 * countWeight b1 z1 n1 i.2

def atom (b0 z0 : ℝ) (n0 : ℕ) (b1 z1 : ℝ) (n1 : ℕ) (i : Index n0 n1) : ℝ :=
  countAtom b0 z0 n0 i.1 + countAtom b1 z1 n1 i.2

/-- The actual convolution of the two separately parameterized groups. -/
def law (b0 z0 : ℝ) (n0 : ℕ) (b1 z1 : ℝ) (n1 : ℕ) : Measure ℝ :=
  MixtureSum.convPower (TwoMoment.referenceLaw b0 z0) n0 ∗
    MixtureSum.convPower (TwoMoment.referenceLaw b1 z1) n1

theorem weights_sum (b0 z0 : ℝ) (n0 : ℕ) (b1 z1 : ℝ) (n1 : ℕ)
    (hb0 : 0 < b0) (hz0 : 0 ≤ z0) (hb1 : 0 < b1) (hz1 : 0 ≤ z1) :
    ∑ i, weights b0 z0 n0 b1 z1 n1 i = 1 := by
  unfold weights
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  rw [countWeights_sum b1 z1 n1 hb1 hz1]
  simp only [mul_one]
  exact countWeights_sum b0 z0 n0 hb0 hz0

private theorem conv_finsetSum {ι : Type*} (μ : Measure ℝ) [IsFiniteMeasure μ]
    (ν : ι → Measure ℝ) [∀ i, IsFiniteMeasure (ν i)] (s : Finset ι) :
    μ ∗ (∑ i ∈ s, ν i) = ∑ i ∈ s, μ ∗ ν i := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, Measure.conv_add, ih]

private theorem finsetSum_conv {ι : Type*} (μ : ι → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    (ν : Measure ℝ) [IsFiniteMeasure ν] (s : Finset ι) :
    (∑ i ∈ s, μ i) ∗ ν = ∑ i ∈ s, μ i ∗ ν := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, Measure.add_conv, ih]

private theorem atomic_measure_conv {ι κ : Type*} [Fintype ι] [Fintype κ]
    (w : ι → ℝ≥0) (v : κ → ℝ≥0) (z : ι → ℝ) (t : κ → ℝ) :
    FiniteAtomicLaw.measure w z ∗ FiniteAtomicLaw.measure v t =
      FiniteAtomicLaw.measure (fun i : ι × κ => w i.1 * v i.2) (fun i => z i.1 + t i.2) := by
  classical
  unfold FiniteAtomicLaw.measure
  rw [finsetSum_conv, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i hi
  rw [conv_finsetSum]
  apply Finset.sum_congr rfl
  intro j hj
  change ((w i : ℝ≥0∞) • Measure.dirac (z i)) ∗ ((v j : ℝ≥0∞) • Measure.dirac (t j)) =
    ((w i * v j : ℝ≥0) : ℝ≥0∞) • Measure.dirac (z i + t j)
  rw [Measure.conv_smul_left, Measure.conv_smul_right, smul_smul, ENNReal.coe_mul,
    Measure.dirac_conv_dirac]

theorem law_eq_atomic_measure (b0 z0 : ℝ) (n0 : ℕ) (b1 z1 : ℝ) (n1 : ℕ)
    (hb0 : 0 < b0) (hz0 : 0 ≤ z0) (hb1 : 0 < b1) (hz1 : 0 ≤ z1) :
    law b0 z0 n0 b1 z1 n1 =
      FiniteAtomicLaw.measure (weights b0 z0 n0 b1 z1 n1) (atom b0 z0 n0 b1 z1 n1) := by
  unfold law
  rw [convPower_eq_atomic_measure b0 z0 n0 hb0 hz0, convPower_eq_atomic_measure b1 z1 n1 hb1 hz1,
    atomic_measure_conv]
  rfl

/-- This is the shared finite-atomic constructor applied to the proved
binomial weights, not a new constructor for a substitute distribution. -/
def atomicLaw (b0 z0 : ℝ) (n0 : ℕ) (b1 z1 : ℝ) (n1 : ℕ)
    (hb0 : 0 < b0) (hz0 : 0 ≤ z0) (hb1 : 0 < b1) (hz1 : 0 ≤ z1) : ProbabilityMeasure ℝ :=
  FiniteAtomicLaw.atomicLaw (weights b0 z0 n0 b1 z1 n1)
    (weights_sum b0 z0 n0 b1 z1 n1 hb0 hz0 hb1 hz1) (atom b0 z0 n0 b1 z1 n1)

theorem law_eq_atomicLaw (b0 z0 : ℝ) (n0 : ℕ) (b1 z1 : ℝ) (n1 : ℕ)
    (hb0 : 0 < b0) (hz0 : 0 ≤ z0) (hb1 : 0 < b1) (hz1 : 0 ≤ z1) :
    law b0 z0 n0 b1 z1 n1 = (atomicLaw b0 z0 n0 b1 z1 n1 hb0 hz0 hb1 hz1 : Measure ℝ) :=
  law_eq_atomic_measure b0 z0 n0 b1 z1 n1 hb0 hz0 hb1 hz1

theorem integrable_law (b0 z0 : ℝ) (n0 : ℕ) (b1 z1 : ℝ) (n1 : ℕ)
    (hb0 : 0 < b0) (hz0 : 0 ≤ z0) (hb1 : 0 < b1) (hz1 : 0 ≤ z1) (f : ℝ → ℝ) :
    Integrable f (law b0 z0 n0 b1 z1 n1) := by
  rw [law_eq_atomic_measure b0 z0 n0 b1 z1 n1 hb0 hz0 hb1 hz1]
  exact FiniteAtomicLaw.integrable_measure _ _ f

theorem integral_law (b0 z0 : ℝ) (n0 : ℕ) (b1 z1 : ℝ) (n1 : ℕ)
    (hb0 : 0 < b0) (hz0 : 0 ≤ z0) (hb1 : 0 < b1) (hz1 : 0 ≤ z1) (f : ℝ → ℝ) :
    (∫ x, f x ∂law b0 z0 n0 b1 z1 n1) =
      ∑ i, (weights b0 z0 n0 b1 z1 n1 i : ℝ) * f (atom b0 z0 n0 b1 z1 n1 i) := by
  rw [law_eq_atomic_measure b0 z0 n0 b1 z1 n1 hb0 hz0 hb1 hz1]
  exact FiniteAtomicLaw.integral_measure _ _ f

/-- Explicit two-binomial formula for every real test function on the
same actual convolution measure. No measurability assumption is needed
for a real function on this finite support. -/
theorem integral_law_explicit (b0 z0 : ℝ) (n0 : ℕ) (b1 z1 : ℝ) (n1 : ℕ)
    (hb0 : 0 < b0) (hz0 : 0 ≤ z0) (hb1 : 0 < b1) (hz1 : 0 ≤ z1) (f : ℝ → ℝ) :
    let p0 := z0 / (b0 ^ 2 + z0)
    let q0 := b0 ^ 2 / (b0 ^ 2 + z0)
    let p1 := z1 / (b1 ^ 2 + z1)
    let q1 := b1 ^ 2 / (b1 ^ 2 + z1)
    (∫ x, f x ∂law b0 z0 n0 b1 z1 n1) =
      ∑ j : Fin (n0 + 1), ∑ l : Fin (n1 + 1),
        ((n0.choose (j : ℕ) : ℝ) * p0 ^ (j : ℕ) * q0 ^ (n0 - (j : ℕ))) *
        ((n1.choose (l : ℕ) : ℝ) * p1 ^ (l : ℕ) * q1 ^ (n1 - (l : ℕ))) *
        f (((j : ℕ) : ℝ) * b0 - ((n0 - (j : ℕ) : ℕ) : ℝ) * z0 / b0 +
          (((l : ℕ) : ℝ) * b1 - ((n1 - (l : ℕ) : ℕ) : ℝ) * z1 / b1)) := by
  dsimp only
  rw [integral_law b0 z0 n0 b1 z1 n1 hb0 hz0 hb1 hz1, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro l hl
  simp only [weights, NNReal.coe_mul, coe_countWeight b0 z0 n0 j hb0 hz0,
    coe_countWeight b1 z1 n1 l hb1 hz1, atom, countAtom]

theorem integral_hinge_square (b0 z0 : ℝ) (n0 : ℕ) (b1 z1 : ℝ) (n1 : ℕ)
    (hb0 : 0 < b0) (hz0 : 0 ≤ z0) (hb1 : 0 < b1) (hz1 : 0 ≤ z1) (A : ℝ) :
    (∫ x, (max (x - A) 0) ^ 2 ∂law b0 z0 n0 b1 z1 n1) =
      ∑ i, (weights b0 z0 n0 b1 z1 n1 i : ℝ) * (max (atom b0 z0 n0 b1 z1 n1 i - A) 0) ^ 2 :=
  integral_law b0 z0 n0 b1 z1 n1 hb0 hz0 hb1 hz1 _

theorem integral_hinge (b0 z0 : ℝ) (n0 : ℕ) (b1 z1 : ℝ) (n1 : ℕ)
    (hb0 : 0 < b0) (hz0 : 0 ≤ z0) (hb1 : 0 < b1) (hz1 : 0 ≤ z1) (A : ℝ) :
    (∫ x, max (x - A) 0 ∂law b0 z0 n0 b1 z1 n1) =
      ∑ i, (weights b0 z0 n0 b1 z1 n1 i : ℝ) * max (atom b0 z0 n0 b1 z1 n1 i - A) 0 :=
  integral_law b0 z0 n0 b1 z1 n1 hb0 hz0 hb1 hz1 _

theorem law_isProbabilityMeasure (b0 z0 : ℝ) (n0 : ℕ) (b1 z1 : ℝ) (n1 : ℕ)
    (hb0 : 0 < b0) (hz0 : 0 ≤ z0) (hb1 : 0 < b1) (hz1 : 0 ≤ z1) :
    IsProbabilityMeasure (law b0 z0 n0 b1 z1 n1) := by
  rw [law_eq_atomicLaw b0 z0 n0 b1 z1 n1 hb0 hz0 hb1 hz1]
  infer_instance

theorem law_memLp_two (b0 z0 : ℝ) (n0 : ℕ) (b1 z1 : ℝ) (n1 : ℕ)
    (hb0 : 0 < b0) (hz0 : 0 ≤ z0) (hb1 : 0 < b1) (hz1 : 0 ≤ z1) :
    MemLp (fun x : ℝ => x) 2 (law b0 z0 n0 b1 z1 n1) :=
  (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).mpr
    (integrable_law b0 z0 n0 b1 z1 n1 hb0 hz0 hb1 hz1 (fun x => x ^ 2))

/-- Centering and the actual second moment are attached to the same
convolution measure represented by the finite sum above. -/
theorem law_moments (b0 z0 : ℝ) (n0 : ℕ) (b1 z1 : ℝ) (n1 : ℕ)
    (hb0 : 0 < b0) (hz0 : 0 ≤ z0) (hb1 : 0 < b1) (hz1 : 0 ≤ z1) :
    Integrable (fun x : ℝ => x) (law b0 z0 n0 b1 z1 n1) ∧
      Integrable (fun x : ℝ => x ^ 2) (law b0 z0 n0 b1 z1 n1) ∧
      (∫ x, x ∂law b0 z0 n0 b1 z1 n1) = 0 ∧
      (∫ x, x ^ 2 ∂law b0 z0 n0 b1 z1 n1) = (n0 : ℝ) * z0 + (n1 : ℝ) * z1 := by
  haveI := TwoMoment.referenceLaw_isProbabilityMeasure b0 z0 hb0 hz0
  haveI := TwoMoment.referenceLaw_isProbabilityMeasure b1 z1 hb1 hz1
  obtain ⟨h01, h02, hm0, hv0⟩ := CommonProductMoments.convPower_moments
    (TwoMoment.referenceLaw b0 z0) (TwoMoment.integrable_referenceLaw b0 z0 _)
    (TwoMoment.integrable_referenceLaw b0 z0 _) (TwoMoment.integral_referenceLaw_id b0 z0 hb0 hz0) n0
  obtain ⟨h11, h12, hm1, hv1⟩ := CommonProductMoments.convPower_moments
    (TwoMoment.referenceLaw b1 z1) (TwoMoment.integrable_referenceLaw b1 z1 _)
    (TwoMoment.integrable_referenceLaw b1 z1 _) (TwoMoment.integral_referenceLaw_id b1 z1 hb1 hz1) n1
  refine ⟨integrable_law b0 z0 n0 b1 z1 n1 hb0 hz0 hb1 hz1 _,
    integrable_law b0 z0 n0 b1 z1 n1 hb0 hz0 hb1 hz1 _, ?_, ?_⟩
  · unfold law
    rw [CommonProductMoments.integral_conv_first _ _ h01 h11, hm0, hm1, add_zero]
  · unfold law
    rw [CommonProductMoments.integral_conv_square _ _ h01 h02 h11 h12 hm0 hm1, hv0, hv1,
      TwoMoment.integral_referenceLaw_sq b0 z0 hb0 hz0, TwoMoment.integral_referenceLaw_sq b1 z1 hb1 hz1]

theorem law_empty_left (b0 z0 b1 z1 : ℝ) (n1 : ℕ) :
    law b0 z0 0 b1 z1 n1 = MixtureSum.convPower (TwoMoment.referenceLaw b1 z1) n1 := by
  simp only [law, MixtureSum.convPower, Measure.dirac_zero_conv]

theorem law_empty_right (b0 z0 b1 z1 : ℝ) (n0 : ℕ) :
    law b0 z0 n0 b1 z1 0 = MixtureSum.convPower (TwoMoment.referenceLaw b0 z0) n0 := by
  simp only [law, MixtureSum.convPower, Measure.conv_dirac_zero]

theorem law_zero_variances (b0 b1 : ℝ) (n0 n1 : ℕ) (hb0 : 0 < b0) (hb1 : 0 < b1) :
    law b0 0 n0 b1 0 n1 = Measure.dirac 0 := by
  unfold law
  rw [TwoMoment.referenceLaw_zero b0 hb0, TwoMoment.referenceLaw_zero b1 hb1,
    PerturbationCDF.convPower_dirac, PerturbationCDF.convPower_dirac]
  simp

/-- The reference law already used by the common staircase is exactly
this double-binomial law, with each source's own actual second moment. -/
theorem coupledReferenceLaw_eq_law (ν0 ν1 : Measure ℝ) (b0 b1 : ℝ) (n k : ℕ)
    (hb0 : 0 < b0) (hb1 : 0 < b1) :
    TwoMoment.coupledReferenceLaw ν0 ν1 b0 b1 n k =
      law b0 (TwoMoment.lawSecondMoment ν0) (n - k) b1 (TwoMoment.lawSecondMoment ν1) k := by
  rw [TwoMoment.coupledReferenceLaw_of_pos ν0 ν1 b0 b1 hb0 hb1 n k]
  unfold law
  exact Measure.conv_comm _ _

theorem coupledReferenceLaw_eq_atomicLaw (ν0 ν1 : Measure ℝ) (b0 b1 : ℝ) (n k : ℕ)
    (hb0 : 0 < b0) (hb1 : 0 < b1) :
    TwoMoment.coupledReferenceLaw ν0 ν1 b0 b1 n k =
      (atomicLaw b0 (TwoMoment.lawSecondMoment ν0) (n - k) b1 (TwoMoment.lawSecondMoment ν1) k
        hb0 (TwoMoment.lawSecondMoment_nonneg ν0) hb1 (TwoMoment.lawSecondMoment_nonneg ν1) : Measure ℝ) := by
  rw [coupledReferenceLaw_eq_law ν0 ν1 b0 b1 n k hb0 hb1]
  exact law_eq_atomicLaw _ _ _ _ _ _ hb0 (TwoMoment.lawSecondMoment_nonneg ν0)
    hb1 (TwoMoment.lawSecondMoment_nonneg ν1)

theorem integral_coupledReferenceLaw (ν0 ν1 : Measure ℝ) (b0 b1 : ℝ) (n k : ℕ)
    (hb0 : 0 < b0) (hb1 : 0 < b1) (f : ℝ → ℝ) :
    (∫ x, f x ∂TwoMoment.coupledReferenceLaw ν0 ν1 b0 b1 n k) =
      ∑ i, (weights b0 (TwoMoment.lawSecondMoment ν0) (n - k) b1 (TwoMoment.lawSecondMoment ν1) k i : ℝ) *
        f (atom b0 (TwoMoment.lawSecondMoment ν0) (n - k) b1 (TwoMoment.lawSecondMoment ν1) k i) := by
  rw [coupledReferenceLaw_eq_law ν0 ν1 b0 b1 n k hb0 hb1]
  exact integral_law _ _ _ _ _ _ hb0 (TwoMoment.lawSecondMoment_nonneg ν0)
    hb1 (TwoMoment.lawSecondMoment_nonneg ν1) f

end

end BerryEsseen.DoubleBinomialReference

#print axioms BerryEsseen.DoubleBinomialReference.weights_sum
#print axioms BerryEsseen.DoubleBinomialReference.law_eq_atomicLaw
#print axioms BerryEsseen.DoubleBinomialReference.integral_law
#print axioms BerryEsseen.DoubleBinomialReference.integral_law_explicit
#print axioms BerryEsseen.DoubleBinomialReference.law_memLp_two
#print axioms BerryEsseen.DoubleBinomialReference.law_moments
#print axioms BerryEsseen.DoubleBinomialReference.coupledReferenceLaw_eq_atomicLaw
#print axioms BerryEsseen.DoubleBinomialReference.integral_coupledReferenceLaw
