module

public import BerryEsseen.AffineSum
public import BerryEsseen.GaussianMills

@[expose] public section

noncomputable section

namespace BerryEsseen.Reflection

open MeasureTheory Set

def reflectedProbabilityLaw (μ : ProbabilityMeasure ℝ) : ProbabilityMeasure ℝ :=
  ⟨(μ : Measure ℝ).map (fun x : ℝ => -x), inferInstance⟩

theorem standardized_reflected (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    StandardizedLaw (reflectedProbabilityLaw μ) := by
  have hf : Measurable (fun x : ℝ => -x) := by fun_prop
  apply (standardizedLaw_iff _).mpr
  refine ⟨?_, ?_, ?_⟩
  · apply (integrable_map_measure (by fun_prop) hf.aemeasurable).mpr
    simpa only [Function.comp_def, abs_neg] using h.integrable_cube
  · change (∫ u : ℝ, u ∂(μ : Measure ℝ).map (fun x : ℝ => -x)) = 0
    rw [integral_map (f := fun u : ℝ => u) hf.aemeasurable
      measurable_id.aestronglyMeasurable, integral_neg, h.mean_zero, neg_zero]
  · change (∫ u : ℝ, u ^ 2 ∂(μ : Measure ℝ).map (fun x : ℝ => -x)) = 1
    rw [integral_map (f := fun u : ℝ => u ^ 2) hf.aemeasurable (by fun_prop)]
    simpa only [neg_sq] using h.second_moment_one

theorem thirdAbsoluteMoment_reflected (μ : ProbabilityMeasure ℝ) :
    thirdAbsoluteMoment (reflectedProbabilityLaw μ) = thirdAbsoluteMoment μ := by
  have hf : Measurable (fun x : ℝ => -x) := by fun_prop
  unfold thirdAbsoluteMoment
  change (∫ u : ℝ, |u| ^ 3 ∂(μ : Measure ℝ).map (fun x : ℝ => -x)) = _
  rw [integral_map (f := fun u : ℝ => |u| ^ 3) hf.aemeasurable (by fun_prop)]
  simp only [abs_neg]

/-- Reflection commutes with the actual independent product sum,
including the empty-sum law at `n = 0`. -/
theorem normalizedIidSumLaw_reflected_eq (μ : ProbabilityMeasure ℝ) (n : ℕ) :
    normalizedIidSumLaw (reflectedProbabilityLaw μ) n =
      (normalizedIidSumLaw μ n).map (fun x : ℝ => -x) := by
  have href : (reflectedProbabilityLaw μ : Measure ℝ) =
      (μ : Measure ℝ).map (fun u : ℝ => (u - 0) / (-1)) := by
    change (μ : Measure ℝ).map (fun u : ℝ => -u) = _
    congr 1
    funext u
    simp [div_neg_eq_neg_div]
  have hid : (μ : Measure ℝ) = (μ : Measure ℝ).map (fun u : ℝ => (u - 0) / 1) := by
    simp only [sub_zero, div_one, Measure.map_id']
  have hneg : Measurable (fun x : ℝ => -x) := by fun_prop
  have hpos : Measurable (fun u : ℝ => (u - (n : ℝ) * 0) / (1 * Real.sqrt n)) := by fun_prop
  rw [AffineSum.normalizedIidSumLaw_eq_map (reflectedProbabilityLaw μ) (μ : Measure ℝ)
    0 (-1) href n,
    AffineSum.normalizedIidSumLaw_eq_map μ (μ : Measure ℝ) 0 1 hid n,
    Measure.map_map hneg hpos]
  congr 1
  funext u
  simp [div_neg_eq_neg_div]

/-- A reflected closed lower event is an original closed upper event. -/
theorem reflected_closedCDF (μ : ProbabilityMeasure ℝ) (n : ℕ) (x : ℝ) :
    (normalizedIidSumLaw (reflectedProbabilityLaw μ) n).real (Iic (-x)) =
      (normalizedIidSumLaw μ n).real (Ici x) := by
  rw [normalizedIidSumLaw_reflected_eq]
  have hf : Measurable (fun u : ℝ => -u) := by fun_prop
  rw [map_measureReal_apply hf measurableSet_Iic]
  have hs : (fun u : ℝ => -u) ⁻¹' Iic (-x) = Ici x := by ext u; simp
  rw [hs]

/-- The open complement is contained in the reflected closed event.
No equality of open and closed probabilities is asserted for the original law. -/
theorem negative_error_le_reflected_positive (μ : ProbabilityMeasure ℝ) (n : ℕ) (x : ℝ) :
    GaussianTools.Phi x - (normalizedIidSumLaw μ n).real (Iic x) ≤
      (normalizedIidSumLaw (reflectedProbabilityLaw μ) n).real (Iic (-x)) -
        GaussianTools.Phi (-x) := by
  have hc := probReal_add_probReal_compl (μ := normalizedIidSumLaw μ n)
    (s := Iic x) measurableSet_Iic
  simp only [compl_Iic] at hc
  have hmono : (normalizedIidSumLaw μ n).real (Ioi x) ≤
      (normalizedIidSumLaw μ n).real (Ici x) := measureReal_mono Ioi_subset_Ici_self
  rw [reflected_closedCDF, GaussianMills.Phi_neg, GaussianMills.tail]
  linarith

def PositiveClosedBound (n : ℕ) (C : ℝ) : Prop :=
  ∀ (μ : ProbabilityMeasure ℝ), StandardizedLaw μ → ∀ x : ℝ,
    (normalizedIidSumLaw μ n).real (Iic x) - GaussianTools.Phi x ≤
      C * thirdAbsoluteMoment μ / Real.sqrt n

def AbsoluteClosedBound (n : ℕ) (C : ℝ) : Prop :=
  ∀ (μ : ProbabilityMeasure ℝ), StandardizedLaw μ → ∀ x : ℝ,
    |(normalizedIidSumLaw μ n).real (Iic x) - GaussianTools.Phi x| ≤
      C * thirdAbsoluteMoment μ / Real.sqrt n

def PositiveRawClosedBound (n : ℕ) (C : ℝ) : Prop :=
  ∀ (μ : ProbabilityMeasure ℝ), StandardizedLaw μ → ∀ H : ℝ,
    (MixtureSum.iidSumLaw (μ : Measure ℝ) n).real (Iic H) -
      GaussianTools.Phi (H / Real.sqrt n) ≤ C * thirdAbsoluteMoment μ / Real.sqrt n

/-- A universal positive closed bound controls both signs for the same index. -/
theorem absoluteClosedBound_of_positive (n : ℕ) (C : ℝ)
    (hpos : PositiveClosedBound n C) : AbsoluteClosedBound n C := by
  intro μ h x
  apply abs_le.mpr
  constructor
  · have href := hpos (reflectedProbabilityLaw μ) (standardized_reflected μ h) (-x)
    rw [thirdAbsoluteMoment_reflected] at href
    have hneg := (negative_error_le_reflected_positive μ n x).trans href
    linarith
  · exact hpos μ h x

theorem positiveClosedBound_iff_absoluteClosedBound (n : ℕ) (C : ℝ) :
    PositiveClosedBound n C ↔ AbsoluteClosedBound n C := by
  refine ⟨absoluteClosedBound_of_positive n C, ?_⟩
  intro habs μ h x
  exact (le_abs_self _).trans (habs μ h x)

theorem normalized_closedCDF_eq_raw (μ : ProbabilityMeasure ℝ) (n : ℕ) (hn : 0 < n) (x : ℝ) :
    (normalizedIidSumLaw μ n).real (Iic x) =
      (MixtureSum.iidSumLaw (μ : Measure ℝ) n).real (Iic (Real.sqrt n * x)) := by
  have hid : (μ : Measure ℝ) = (μ : Measure ℝ).map (fun u : ℝ => (u - 0) / 1) := by
    simp only [sub_zero, div_one, Measure.map_id']
  simpa only [mul_zero, zero_add, one_mul] using
    AffineSum.normalizedIidSumLaw_closedCDF μ (μ : Measure ℝ) 0 1 (by norm_num) hid n hn x

theorem positiveClosedBound_of_raw (n : ℕ) (hn : 0 < n) (C : ℝ)
    (hraw : PositiveRawClosedBound n C) : PositiveClosedBound n C := by
  intro μ h x
  have hi := hraw μ h (Real.sqrt n * x)
  have hn0 : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn))
  rw [← normalized_closedCDF_eq_raw μ n hn x, mul_div_cancel_left₀ x hn0] at hi
  exact hi

theorem absoluteClosedBound_of_raw (n : ℕ) (hn : 0 < n) (C : ℝ)
    (hraw : PositiveRawClosedBound n C) : AbsoluteClosedBound n C :=
  absoluteClosedBound_of_positive n C (positiveClosedBound_of_raw n hn C hraw)

/-- This is a bridge to the complete original target, not an assertion
that its positive closed bound has already been proved. -/
theorem sharpIidBerryEsseen_of_positive
    (hpos : ∀ n : ℕ, 0 < n → PositiveClosedBound n esseenConstant) : SharpIidBerryEsseen := by
  intro μ h n hn x
  have hi := absoluteClosedBound_of_positive n esseenConstant (hpos n hn) μ h x
  simpa only [GaussianTools.Phi] using hi

theorem sharpIidBerryEsseen_of_raw
    (hraw : ∀ n : ℕ, 0 < n → PositiveRawClosedBound n esseenConstant) : SharpIidBerryEsseen :=
  sharpIidBerryEsseen_of_positive (fun n hn => positiveClosedBound_of_raw n hn _ (hraw n hn))

end BerryEsseen.Reflection

#print axioms BerryEsseen.Reflection.standardized_reflected
#print axioms BerryEsseen.Reflection.thirdAbsoluteMoment_reflected
#print axioms BerryEsseen.Reflection.normalizedIidSumLaw_reflected_eq
#print axioms BerryEsseen.Reflection.negative_error_le_reflected_positive
#print axioms BerryEsseen.Reflection.absoluteClosedBound_of_raw
#print axioms BerryEsseen.Reflection.sharpIidBerryEsseen_of_raw
