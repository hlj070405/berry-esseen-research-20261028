module

public import BerryEsseen.AffineSum
public import BerryEsseen.PerturbationMoment

@[expose] public section

noncomputable section

namespace BerryEsseen.Standardization

open MeasureTheory Filter Set
open scoped Topology

def mean (ν : ProbabilityMeasure ℝ) : ℝ := ∫ x : ℝ, x ∂(ν : Measure ℝ)

def variance (ν : ProbabilityMeasure ℝ) : ℝ :=
  ∫ x : ℝ, (x - mean ν) ^ 2 ∂(ν : Measure ℝ)

def centeredThird (ν : ProbabilityMeasure ℝ) : ℝ :=
  ∫ x : ℝ, |x - mean ν| ^ 3 ∂(ν : Measure ℝ)

def standardized (ν : ProbabilityMeasure ℝ) : ProbabilityMeasure ℝ :=
  ⟨(ν : Measure ℝ).map (fun x : ℝ => (x - mean ν) / Real.sqrt (variance ν)), inferInstance⟩

theorem lower_moments (ν : ProbabilityMeasure ℝ)
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) (ν : Measure ℝ)) :
    Integrable (fun x : ℝ => x) (ν : Measure ℝ) ∧
    Integrable (fun x : ℝ => x ^ 2) (ν : Measure ℝ) ∧
    Integrable (fun x : ℝ => x ^ 3) (ν : Measure ℝ) := by
  have hid : AEStronglyMeasurable (fun x : ℝ => x) (ν : Measure ℝ) :=
    measurable_id.aestronglyMeasurable
  have hn : Integrable (fun x : ℝ => ‖x‖ ^ 3) (ν : Measure ℝ) := by
    simpa only [Real.norm_eq_abs] using h3
  have h1 := integrable_norm_pow_of_le hid (by decide : 1 ≤ 3) hn
  have h2 := integrable_norm_pow_of_le hid (by decide : 2 ≤ 3) hn
  refine ⟨?_, ?_, ?_⟩
  · exact (integrable_norm_iff hid).mp (by simpa only [pow_one] using h1)
  · simpa only [Real.norm_eq_abs, sq_abs] using h2
  · apply (integrable_norm_iff (by fun_prop :
      AEStronglyMeasurable (fun x : ℝ => x ^ 3) (ν : Measure ℝ))).mp
    simpa only [Real.norm_eq_abs, abs_pow] using h3

theorem integrable_centered_square (ν : ProbabilityMeasure ℝ)
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) (ν : Measure ℝ)) :
    Integrable (fun x : ℝ => (x - mean ν) ^ 2) (ν : Measure ℝ) := by
  have hi := lower_moments ν h3
  simpa only [sub_eq_add_neg] using MomentBudget.integrable_square_add_const
    (ν : Measure ℝ) (fun x : ℝ => x) (-(mean ν)) hi.1 hi.2.1

theorem integrable_centered_cube (ν : ProbabilityMeasure ℝ)
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) (ν : Measure ℝ)) :
    Integrable (fun x : ℝ => |x - mean ν| ^ 3) (ν : Measure ℝ) := by
  have hi := lower_moments ν h3
  have hs := MomentBudget.integrable_cube_add_const (ν : Measure ℝ)
    (fun x : ℝ => x) (-(mean ν)) hi.1 hi.2.1 hi.2.2
  simpa only [Real.norm_eq_abs, abs_pow, sub_eq_add_neg] using hs.norm

theorem variance_nonneg (ν : ProbabilityMeasure ℝ) : 0 ≤ variance ν :=
  integral_nonneg (fun _ => sq_nonneg _)

/-- Any finite-absolute-third-moment law of positive variance is truly standardized. -/
theorem standardizedLaw (ν : ProbabilityMeasure ℝ)
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) (ν : Measure ℝ)) (hv : 0 < variance ν) :
    StandardizedLaw (standardized ν) := by
  have hc : 0 < Real.sqrt (variance ν) := Real.sqrt_pos.mpr hv
  have hi := lower_moments ν h3
  have hf : Measurable (fun x : ℝ => (x - mean ν) / Real.sqrt (variance ν)) := by fun_prop
  apply (standardizedLaw_iff _).mpr
  refine ⟨?_, ?_, ?_⟩
  · have habs : Integrable (fun x : ℝ => |(x - mean ν) / Real.sqrt (variance ν)| ^ 3)
        (ν : Measure ℝ) := by
      simpa only [abs_div, abs_of_pos hc, div_pow] using
        (integrable_centered_cube ν h3).div_const (Real.sqrt (variance ν) ^ 3)
    exact (integrable_map_measure (by fun_prop) hf.aemeasurable).mpr habs
  · change (∫ u : ℝ, u ∂(ν : Measure ℝ).map
      (fun x : ℝ => (x - mean ν) / Real.sqrt (variance ν))) = 0
    rw [integral_map (f := fun u : ℝ => u) hf.aemeasurable
      measurable_id.aestronglyMeasurable, integral_div,
      integral_sub hi.1 (integrable_const (mean ν))]
    simp only [integral_const, probReal_univ, one_smul, mean, sub_self, zero_div]
  · change (∫ u : ℝ, u ^ 2 ∂(ν : Measure ℝ).map
      (fun x : ℝ => (x - mean ν) / Real.sqrt (variance ν))) = 1
    rw [integral_map (f := fun u : ℝ => u ^ 2) hf.aemeasurable (by fun_prop)]
    simp only [div_pow]
    rw [integral_div]
    change variance ν / Real.sqrt (variance ν) ^ 2 = 1
    rw [Real.sq_sqrt (le_of_lt hv), div_self (ne_of_gt hv)]

/-- The third moment is that of this actual push-forward law. -/
theorem thirdAbsoluteMoment_standardized (ν : ProbabilityMeasure ℝ) (hv : 0 < variance ν) :
    thirdAbsoluteMoment (standardized ν) = centeredThird ν / Real.sqrt (variance ν) ^ 3 := by
  have hc : 0 < Real.sqrt (variance ν) := Real.sqrt_pos.mpr hv
  have hf : Measurable (fun x : ℝ => (x - mean ν) / Real.sqrt (variance ν)) := by fun_prop
  unfold thirdAbsoluteMoment
  change (∫ u : ℝ, |u| ^ 3 ∂(ν : Measure ℝ).map
    (fun x : ℝ => (x - mean ν) / Real.sqrt (variance ν))) = _
  rw [integral_map (f := fun u : ℝ => |u| ^ 3) hf.aemeasurable (by fun_prop)]
  simp only [abs_div, abs_of_pos hc, div_pow]
  rw [integral_div]
  rfl

/-- Closed CDF change of coordinates for the actual i.i.d. product law. -/
theorem iidSum_closedCDF (ν : ProbabilityMeasure ℝ) (hv : 0 < variance ν)
    (n : ℕ) (hn : 0 < n) (H : ℝ) :
    (MixtureSum.iidSumLaw (ν : Measure ℝ) n).real (Iic H) =
      (normalizedIidSumLaw (standardized ν) n).real
        (Iic ((H - (n : ℝ) * mean ν) / (Real.sqrt (variance ν) * Real.sqrt n))) := by
  have hc : 0 < Real.sqrt (variance ν) := Real.sqrt_pos.mpr hv
  have hd : Real.sqrt (variance ν) * Real.sqrt (n : ℝ) ≠ 0 :=
    ne_of_gt (mul_pos hc (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)))
  have hcdf := AffineSum.normalizedIidSumLaw_closedCDF (standardized ν) (ν : Measure ℝ)
    (mean ν) (Real.sqrt (variance ν)) hc rfl n hn
    ((H - (n : ℝ) * mean ν) / (Real.sqrt (variance ν) * Real.sqrt n))
  have heq : (n : ℝ) * mean ν + Real.sqrt (variance ν) * Real.sqrt n *
      ((H - (n : ℝ) * mean ν) / (Real.sqrt (variance ν) * Real.sqrt n)) = H := by
    field_simp [hd]
    ring
  rw [heq] at hcdf
  exact hcdf.symm

theorem mixture_abs_cube_integrable (μ : ProbabilityMeasure ℝ)
    (h3 : Integrable (fun u : ℝ => |u| ^ 3) (μ : Measure ℝ)) (x ε : ℝ) :
    Integrable (fun u : ℝ => |u| ^ 3) (PerturbationMoment.mixtureMeasure μ x ε) := by
  have hd : Integrable (fun u : ℝ => |u| ^ 3) (Measure.dirac x) :=
    integrable_dirac (a := x) (f := fun u : ℝ => |u| ^ 3) (by finiteness)
  exact (h3.smul_measure ENNReal.ofReal_ne_top).add_measure
    (hd.smul_measure ENNReal.ofReal_ne_top)

theorem mean_mixtureLaw (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (x ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    mean (PerturbationMoment.mixtureLaw μ x ε hε0 hε1) = ε * x := by
  change (∫ u : ℝ, u ∂PerturbationMoment.mixtureMeasure μ x ε) = ε * x
  exact PerturbationMoment.mixture_mean μ h x ε hε0

theorem variance_mixtureLaw (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (x ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    variance (PerturbationMoment.mixtureLaw μ x ε hε0 hε1) =
      PerturbationMoment.varianceFormula x ε := by
  change PerturbationMoment.actualCenteredSecondMoment μ x ε = _
  exact PerturbationMoment.actualCenteredSecondMoment_eq_formula μ h x ε hε0 hε1

theorem centeredThird_mixtureLaw (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (x ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    centeredThird (PerturbationMoment.mixtureLaw μ x ε hε0 hε1) =
      PerturbationMoment.centeredMomentFormula μ x ε := by
  change PerturbationMoment.actualCenteredThirdMoment μ x ε = _
  exact PerturbationMoment.actualCenteredThirdMoment_eq_formula μ h x ε hε0 hε1

theorem variance_mixtureLaw_pos (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (x ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    0 < variance (PerturbationMoment.mixtureLaw μ x ε hε0 (le_of_lt hε1)) := by
  rw [variance_mixtureLaw μ h x ε hε0 (le_of_lt hε1)]
  unfold PerturbationMoment.varianceFormula
  exact mul_pos (sub_pos.mpr hε1) (by nlinarith [mul_nonneg hε0 (sq_nonneg x)])

/-- Positive variance holds on a right neighborhood of the original law. -/
theorem eventually_perturbation_variance_pos (μ : ProbabilityMeasure ℝ)
    (h : StandardizedLaw μ) (x : ℝ) :
    ∀ᶠ ε in 𝓝[Set.Ici (0 : ℝ)] 0,
      0 < PerturbationMoment.actualCenteredSecondMoment μ x ε := by
  have hlt0 : ∀ᶠ ε : ℝ in 𝓝 (0 : ℝ), ε < 1 := Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)
  have hlt : ∀ᶠ ε : ℝ in 𝓝[Set.Ici (0 : ℝ)] 0, ε < 1 :=
    hlt0.filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hlt] with ε hε0 hε1
  have hp := variance_mixtureLaw_pos μ h x ε hε0 hε1
  exact hp

theorem perturbation_standardizedLaw (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (x ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    StandardizedLaw (standardized (PerturbationMoment.mixtureLaw μ x ε hε0 (le_of_lt hε1))) :=
  standardizedLaw _ (mixture_abs_cube_integrable μ h.integrable_cube x ε)
    (variance_mixtureLaw_pos μ h x ε hε0 hε1)

theorem perturbation_thirdAbsoluteMoment (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (x ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    thirdAbsoluteMoment
      (standardized (PerturbationMoment.mixtureLaw μ x ε hε0 (le_of_lt hε1))) =
    PerturbationMoment.centeredMomentFormula μ x ε /
      Real.sqrt (PerturbationMoment.varianceFormula x ε) ^ 3 := by
  rw [thirdAbsoluteMoment_standardized _ (variance_mixtureLaw_pos μ h x ε hε0 hε1),
    centeredThird_mixtureLaw μ h x ε hε0 (le_of_lt hε1),
    variance_mixtureLaw μ h x ε hε0 (le_of_lt hε1)]

theorem perturbation_iidSum_closedCDF (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (x ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1) (n : ℕ) (hn : 0 < n) (H : ℝ) :
    (MixtureSum.iidSumLaw (PerturbationMoment.mixtureMeasure μ x ε) n).real (Iic H) =
      (normalizedIidSumLaw
        (standardized (PerturbationMoment.mixtureLaw μ x ε hε0 (le_of_lt hε1))) n).real
        (Iic ((H - (n : ℝ) * (ε * x)) /
          (Real.sqrt (PerturbationMoment.varianceFormula x ε) * Real.sqrt n))) := by
  have hcdf := iidSum_closedCDF (PerturbationMoment.mixtureLaw μ x ε hε0 (le_of_lt hε1))
    (variance_mixtureLaw_pos μ h x ε hε0 hε1) n hn H
  rw [show (PerturbationMoment.mixtureLaw μ x ε hε0 (le_of_lt hε1) : Measure ℝ) =
    PerturbationMoment.mixtureMeasure μ x ε from rfl] at hcdf
  simpa only [mean_mixtureLaw μ h x ε hε0 (le_of_lt hε1),
    variance_mixtureLaw μ h x ε hε0 (le_of_lt hε1)] using hcdf

end BerryEsseen.Standardization

#print axioms BerryEsseen.Standardization.lower_moments
#print axioms BerryEsseen.Standardization.integrable_centered_cube
#print axioms BerryEsseen.Standardization.standardizedLaw
#print axioms BerryEsseen.Standardization.thirdAbsoluteMoment_standardized
#print axioms BerryEsseen.Standardization.iidSum_closedCDF
#print axioms BerryEsseen.Standardization.eventually_perturbation_variance_pos
#print axioms BerryEsseen.Standardization.perturbation_standardizedLaw
#print axioms BerryEsseen.Standardization.perturbation_thirdAbsoluteMoment
#print axioms BerryEsseen.Standardization.perturbation_iidSum_closedCDF
