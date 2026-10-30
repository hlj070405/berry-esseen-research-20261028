module

public import BerryEsseen.StopLossWidthDuality

@[expose] public section

/-! 2026-10-29: genuine finite atomic probability laws. The real integral
formula is derived from the finite sum of scaled Dirac measures, rather
than assumed or used as the definition of a price. -/

noncomputable section

namespace BerryEsseen.FiniteAtomicLaw

open MeasureTheory
open scoped BigOperators NNReal ENNReal

variable {ι : Type*} [Fintype ι]

def measure (w : ι → ℝ≥0) (z : ι → ℝ) : Measure ℝ :=
  ∑ i, w i • Measure.dirac (z i)

lemma measure_isProbability (w : ι → ℝ≥0) (hw : ∑ i, w i = 1) (z : ι → ℝ) :
    IsProbabilityMeasure (measure w z) := by
  have hs : (∑ i, (w i : ℝ≥0∞)) = 1 := by exact_mod_cast hw
  constructor
  simpa [measure, Measure.finsetSum_apply, NNReal.smul_def] using hs

def atomicLaw (w : ι → ℝ≥0) (hw : ∑ i, w i = 1) (z : ι → ℝ) : ProbabilityMeasure ℝ :=
  ⟨measure w z, measure_isProbability w hw z⟩

@[simp] lemma coe_atomicLaw (w : ι → ℝ≥0) (hw : ∑ i, w i = 1) (z : ι → ℝ) :
    (atomicLaw w hw z : Measure ℝ) = measure w z := rfl

theorem integrable_measure (w : ι → ℝ≥0) (z : ι → ℝ) (g : ℝ → ℝ) :
    Integrable g (measure w z) := by
  unfold measure
  apply integrable_finsetSum_measure.mpr
  intro i hi
  exact (integrable_dirac (by simp)).smul_measure_nnreal

theorem integral_measure (w : ι → ℝ≥0) (z : ι → ℝ) (g : ℝ → ℝ) :
    (∫ x, g x ∂measure w z) = ∑ i, (w i : ℝ) * g (z i) := by
  unfold measure
  rw [integral_finsetSum_measure (fun i hi =>
    (integrable_dirac (by simp)).smul_measure_nnreal)]
  apply Finset.sum_congr rfl
  intro i hi
  simp [NNReal.smul_def, smul_eq_mul]

theorem integrable (w : ι → ℝ≥0) (hw : ∑ i, w i = 1) (z : ι → ℝ) (g : ℝ → ℝ) :
    Integrable g (atomicLaw w hw z : Measure ℝ) := integrable_measure w z g

theorem integral (w : ι → ℝ≥0) (hw : ∑ i, w i = 1) (z : ι → ℝ) (g : ℝ → ℝ) :
    (∫ x, g x ∂(atomicLaw w hw z : Measure ℝ)) = ∑ i, (w i : ℝ) * g (z i) :=
  integral_measure w z g

theorem ae_of_atoms (w : ι → ℝ≥0) (hw : ∑ i, w i = 1) (z : ι → ℝ)
    (P : ℝ → Prop) (hP : ∀ i, P (z i)) : ∀ᵐ x ∂(atomicLaw w hw z : Measure ℝ), P x := by
  change ∀ᵐ x ∂(∑ i, w i • Measure.dirac (z i)), P x
  rw [ae_finsetSum_measure_iff]
  intro i hi
  change ∀ᵐ x ∂((w i : ℝ≥0∞) • Measure.dirac (z i)), P x
  exact Measure.ae_smul_measure (by simpa using hP i) _

lemma real_weights_sum (w : ι → ℝ≥0) (hw : ∑ i, w i = 1) :
    (∑ i, (w i : ℝ)) = 1 := by exact_mod_cast hw

end BerryEsseen.FiniteAtomicLaw

#print axioms BerryEsseen.FiniteAtomicLaw.measure_isProbability
#print axioms BerryEsseen.FiniteAtomicLaw.integrable
#print axioms BerryEsseen.FiniteAtomicLaw.integral
#print axioms BerryEsseen.FiniteAtomicLaw.ae_of_atoms
