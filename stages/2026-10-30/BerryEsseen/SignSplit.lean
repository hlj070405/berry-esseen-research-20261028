module

public import BerryEsseen.Target
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Tactic.Linarith

@[expose] public section

/-! 2026-10-28: the actual sign split of an arbitrary standardized real law.
The nonpositive group includes every possible atom at zero.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace BerryEsseen.SignSplit

theorem not_ae_zero (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    ¬ ((fun x : ℝ => x) =ᵐ[(μ : Measure ℝ)] 0) := by
  intro hz
  have hsq : (∫ x, x ^ 2 ∂(μ : Measure ℝ)) = 0 := by
    calc
      _ = ∫ _, (0 : ℝ) ∂(μ : Measure ℝ) := integral_congr_ae
        (hz.mono (fun x hx => by change x = 0 at hx; simp [hx]))
      _ = 0 := by simp
  have := h.second_moment_one
  linarith

theorem positive_mass_ne_zero (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    (μ : Measure ℝ) (Ioi 0) ≠ 0 := by
  intro hz
  change (μ : Measure ℝ) {x : ℝ | 0 < x} = 0 at hz
  have hnonpos : ∀ᵐ x ∂(μ : Measure ℝ), x ≤ 0 := by
    apply ae_iff.mpr
    simpa only [not_le] using hz
  have hneg : 0 ≤ᵐ[(μ : Measure ℝ)] (fun x : ℝ => -x) :=
    hnonpos.mono (fun x hx => by simpa using neg_nonneg.mpr hx)
  have hint : (∫ x, -x ∂(μ : Measure ℝ)) = 0 := by
    rw [integral_neg, h.mean_zero, neg_zero]
  have hzero := (integral_eq_zero_iff_of_nonneg_ae hneg h.integrable_mean.neg).mp hint
  exact not_ae_zero μ h (hzero.mono (fun x hx => by
    simpa only [Pi.zero_apply, neg_eq_zero] using hx))

theorem negative_mass_ne_zero (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    (μ : Measure ℝ) (Iio 0) ≠ 0 := by
  intro hz
  change (μ : Measure ℝ) {x : ℝ | x < 0} = 0 at hz
  have hnonneg : 0 ≤ᵐ[(μ : Measure ℝ)] (fun x : ℝ => x) := by
    apply ae_iff.mpr
    simpa only [Pi.zero_apply, not_le] using hz
  exact not_ae_zero μ h
    ((integral_eq_zero_iff_of_nonneg_ae hnonneg h.integrable_mean).mp h.mean_zero)

theorem nonpositive_mass_ne_zero (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    (μ : Measure ℝ) (Iic 0) ≠ 0 := by
  intro hz
  have hm : (μ : Measure ℝ) (Iio 0) ≤ (μ : Measure ℝ) (Iic 0) :=
    measure_mono Iio_subset_Iic_self
  rw [hz] at hm
  exact negative_mass_ne_zero μ h (le_zero_iff.mp hm)

def positiveWeight (μ : ProbabilityMeasure ℝ) : ℝ :=
  (μ : Measure ℝ).real (Ioi 0)

def nonpositiveWeight (μ : ProbabilityMeasure ℝ) : ℝ :=
  (μ : Measure ℝ).real (Iic 0)

theorem weights_add (μ : ProbabilityMeasure ℝ) :
    positiveWeight μ + nonpositiveWeight μ = 1 := by
  simpa only [positiveWeight, nonpositiveWeight, compl_Ioi] using
    (probReal_add_probReal_compl (μ := (μ : Measure ℝ))
      (s := Ioi 0) measurableSet_Ioi)

theorem weights_pos (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    0 < positiveWeight μ ∧ 0 < nonpositiveWeight μ := by
  constructor
  · exact ENNReal.toReal_pos (positive_mass_ne_zero μ h) (measure_ne_top _ _)
  · exact ENNReal.toReal_pos (nonpositive_mass_ne_zero μ h) (measure_ne_top _ _)

theorem positiveWeight_lt_one (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    positiveWeight μ < 1 := by
  have := weights_add μ
  have := (weights_pos μ h).2
  linarith

def positiveLaw (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) : ProbabilityMeasure ℝ :=
  ⟨cond (μ : Measure ℝ) (Ioi 0), cond_isProbabilityMeasure (positive_mass_ne_zero μ h)⟩

def nonpositiveLaw (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) : ProbabilityMeasure ℝ :=
  ⟨cond (μ : Measure ℝ) (Iic 0), cond_isProbabilityMeasure (nonpositive_mass_ne_zero μ h)⟩

theorem mass_smul_cond (ν : Measure ℝ) [IsFiniteMeasure ν] (s : Set ℝ)
    (h0 : ν s ≠ 0) : ν s • cond ν s = ν.restrict s := by
  rw [ProbabilityTheory.cond, smul_smul,
    ENNReal.mul_inv_cancel h0 (measure_ne_top _ _), one_smul]

theorem law_eq_sign_mixture (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    (μ : Measure ℝ) =
      ENNReal.ofReal (nonpositiveWeight μ) • (nonpositiveLaw μ h : Measure ℝ) +
      ENNReal.ofReal (positiveWeight μ) • (positiveLaw μ h : Measure ℝ) := by
  have hneg : ENNReal.ofReal (nonpositiveWeight μ) = (μ : Measure ℝ) (Iic 0) :=
    ENNReal.ofReal_toReal (measure_ne_top _ _)
  have hpos : ENNReal.ofReal (positiveWeight μ) = (μ : Measure ℝ) (Ioi 0) :=
    ENNReal.ofReal_toReal (measure_ne_top _ _)
  rw [hneg, hpos]
  change (μ : Measure ℝ) =
    (μ : Measure ℝ) (Iic 0) • cond (μ : Measure ℝ) (Iic 0) +
    (μ : Measure ℝ) (Ioi 0) • cond (μ : Measure ℝ) (Ioi 0)
  rw [mass_smul_cond _ _ (nonpositive_mass_ne_zero μ h),
      mass_smul_cond _ _ (positive_mass_ne_zero μ h)]
  simpa only [compl_Ioi] using
    ((μ : Measure ℝ).restrict_compl_add_restrict measurableSet_Ioi).symm

end BerryEsseen.SignSplit

#print axioms BerryEsseen.SignSplit.positive_mass_ne_zero
#print axioms BerryEsseen.SignSplit.law_eq_sign_mixture
