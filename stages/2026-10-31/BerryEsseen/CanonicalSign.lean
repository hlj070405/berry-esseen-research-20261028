module

public import BerryEsseen.SignSplit
public import BerryEsseen.MomentBudgetNormalized

@[expose] public section

noncomputable section

namespace BerryEsseen.CanonicalSign

open MeasureTheory ProbabilityTheory Set

def p (μ : ProbabilityMeasure ℝ) : ℝ := SignSplit.positiveWeight μ
def q (μ : ProbabilityMeasure ℝ) : ℝ := 1 - p μ

theorem q_eq_nonpositiveWeight (μ : ProbabilityMeasure ℝ) :
    q μ = SignSplit.nonpositiveWeight μ := by
  dsimp [q, p]
  linarith [SignSplit.weights_add μ]

theorem p_pos (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) : 0 < p μ :=
  (SignSplit.weights_pos μ h).1

theorem p_lt_one (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) : p μ < 1 :=
  SignSplit.positiveWeight_lt_one μ h

theorem q_pos (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) : 0 < q μ :=
  sub_pos.mpr (p_lt_one μ h)

private theorem integrable_cond (ν : Measure ℝ) (s : Set ℝ) (hs0 : ν s ≠ 0)
    (f : ℝ → ℝ) (hf : Integrable f ν) : Integrable f (cond ν s) := by
  unfold ProbabilityTheory.cond
  exact hf.restrict.smul_measure (by simp [hs0])

theorem integrable_nonpositive (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (f : ℝ → ℝ) (hf : Integrable f (μ : Measure ℝ)) :
    Integrable f (SignSplit.nonpositiveLaw μ h : Measure ℝ) :=
  integrable_cond (μ : Measure ℝ) (Iic 0)
    (SignSplit.nonpositive_mass_ne_zero μ h) f hf

theorem integrable_positive (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (f : ℝ → ℝ) (hf : Integrable f (μ : Measure ℝ)) :
    Integrable f (SignSplit.positiveLaw μ h : Measure ℝ) :=
  integrable_cond (μ : Measure ℝ) (Ioi 0)
    (SignSplit.positive_mass_ne_zero μ h) f hf

def mean0 (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) : ℝ :=
  ∫ x : ℝ, x ∂(SignSplit.nonpositiveLaw μ h : Measure ℝ)

def mean1 (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) : ℝ :=
  ∫ x : ℝ, x ∂(SignSplit.positiveLaw μ h : Measure ℝ)

theorem positive_ae (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    ∀ᵐ x ∂(SignSplit.positiveLaw μ h : Measure ℝ), 0 < x :=
  ae_cond_mem measurableSet_Ioi

theorem nonpositive_ae (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    ∀ᵐ x ∂(SignSplit.nonpositiveLaw μ h : Measure ℝ), x ≤ 0 :=
  ae_cond_mem measurableSet_Iic

theorem mean1_pos (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) : 0 < mean1 μ h := by
  have hi := integrable_positive μ h (fun x : ℝ => x) h.integrable_mean
  have hp := positive_ae μ h
  have hn : 0 ≤ᵐ[(SignSplit.positiveLaw μ h : Measure ℝ)] (fun x : ℝ => x) :=
    hp.mono (fun _ hx => le_of_lt hx)
  have hm : 0 ≤ mean1 μ h := integral_nonneg_of_ae hn
  by_contra hc
  have hz : mean1 μ h = 0 := le_antisymm (le_of_not_gt hc) hm
  have hzero := (integral_eq_zero_iff_of_nonneg_ae hn hi).mp hz
  obtain ⟨x, hx, hzx⟩ := (hp.and hzero).exists
  change x = 0 at hzx
  linarith

theorem mean_balance (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    q μ * mean0 μ h + p μ * mean1 μ h = 0 := by
  have hi0 := integrable_nonpositive μ h (fun x : ℝ => x) h.integrable_mean
  have hi1 := integrable_positive μ h (fun x : ℝ => x) h.integrable_mean
  have heq := congrArg (fun ν : Measure ℝ => ∫ x : ℝ, x ∂ν)
    (SignSplit.law_eq_sign_mixture μ h)
  rw [integral_add_measure (hi0.smul_measure ENNReal.ofReal_ne_top)
      (hi1.smul_measure ENNReal.ofReal_ne_top),
    integral_smul_measure, integral_smul_measure] at heq
  rw [ENNReal.toReal_ofReal (le_of_lt (SignSplit.weights_pos μ h).2),
    ENNReal.toReal_ofReal (le_of_lt (SignSplit.weights_pos μ h).1)] at heq
  rw [h.mean_zero] at heq
  simpa only [q_eq_nonpositiveWeight, p, mean0, mean1, smul_eq_mul] using heq.symm

theorem mean0_neg (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) : mean0 μ h < 0 := by
  have hb := mean_balance μ h
  have hp := mul_pos (p_pos μ h) (mean1_pos μ h)
  by_contra hc
  have hn := mul_nonneg (le_of_lt (q_pos μ h)) (le_of_not_gt hc)
  linarith

def scale (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) : ℝ :=
  (mean1 μ h - mean0 μ h)⁻¹

theorem scale_pos (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) : 0 < scale μ h :=
  inv_pos.mpr (sub_pos.mpr (lt_trans (mean0_neg μ h) (mean1_pos μ h)))

theorem scale_center0 (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    scale μ h * mean0 μ h + p μ = 0 := by
  have hg : mean1 μ h - mean0 μ h ≠ 0 :=
    ne_of_gt (sub_pos.mpr (lt_trans (mean0_neg μ h) (mean1_pos μ h)))
  have hb := mean_balance μ h
  dsimp [q] at hb
  unfold scale
  field_simp [hg]
  nlinarith

theorem scale_center1 (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    scale μ h * mean1 μ h - q μ = 0 := by
  have hg : mean1 μ h - mean0 μ h ≠ 0 :=
    ne_of_gt (sub_pos.mpr (lt_trans (mean0_neg μ h) (mean1_pos μ h)))
  have hb := mean_balance μ h
  unfold scale
  field_simp [hg]
  dsimp [q] at *
  nlinarith

def affineLaw (ν : ProbabilityMeasure ℝ) (c t : ℝ) : ProbabilityMeasure ℝ :=
  ⟨(ν : Measure ℝ).map (fun x : ℝ => c * x + t), inferInstance⟩

private theorem integrable_signed_cube (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    Integrable (fun x : ℝ => x ^ 3) (μ : Measure ℝ) := by
  apply (integrable_norm_iff (by fun_prop :
    AEStronglyMeasurable (fun x : ℝ => x ^ 3) (μ : Measure ℝ))).mp
  simpa only [Real.norm_eq_abs, abs_pow] using h.integrable_cube

theorem affineLaw_centered (ν : ProbabilityMeasure ℝ) (c t : ℝ)
    (h1 : Integrable (fun x : ℝ => x) (ν : Measure ℝ))
    (h2 : Integrable (fun x : ℝ => x ^ 2) (ν : Measure ℝ))
    (h3 : Integrable (fun x : ℝ => x ^ 3) (ν : Measure ℝ))
    (hm : c * (∫ x : ℝ, x ∂(ν : Measure ℝ)) + t = 0) :
    MomentBudget.CenteredResidualLaw (affineLaw ν c t) := by
  have hf : Measurable (fun x : ℝ => c * x + t) := by fun_prop
  have hfirst := (h1.const_mul c).add (integrable_const t)
  have hs : Integrable (fun x : ℝ => (c * x) ^ 2) (ν : Measure ℝ) := by
    simpa only [mul_pow] using h2.const_mul (c ^ 2)
  have ht : Integrable (fun x : ℝ => (c * x) ^ 3) (ν : Measure ℝ) := by
    simpa only [mul_pow] using h3.const_mul (c ^ 3)
  have hsecond := MomentBudget.integrable_square_add_const (ν : Measure ℝ)
    (fun x : ℝ => c * x) t (h1.const_mul c) hs
  have hthird := MomentBudget.integrable_cube_add_const (ν : Measure ℝ)
    (fun x : ℝ => c * x) t (h1.const_mul c) hs ht
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (integrable_map_measure measurable_id.aestronglyMeasurable hf.aemeasurable).mpr hfirst
  · exact (integrable_map_measure (by fun_prop) hf.aemeasurable).mpr hsecond
  · exact (integrable_map_measure (by fun_prop) hf.aemeasurable).mpr hthird
  · change (∫ u : ℝ, u ∂(ν : Measure ℝ).map (fun x : ℝ => c * x + t)) = 0
    rw [integral_map (f := fun u : ℝ => u) hf.aemeasurable
      measurable_id.aestronglyMeasurable,
      integral_add (h1.const_mul c) (integrable_const t), integral_const_mul]
    simpa only [integral_const, probReal_univ, one_smul] using hm

def residual0 (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) : ProbabilityMeasure ℝ :=
  affineLaw (SignSplit.nonpositiveLaw μ h) (scale μ h) (p μ)

def residual1 (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) : ProbabilityMeasure ℝ :=
  affineLaw (SignSplit.positiveLaw μ h) (scale μ h) (-(q μ))

theorem residual0_centered (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    MomentBudget.CenteredResidualLaw (residual0 μ h) :=
  affineLaw_centered (SignSplit.nonpositiveLaw μ h) (scale μ h) (p μ)
    (integrable_nonpositive μ h _ h.integrable_mean)
    (integrable_nonpositive μ h _ h.integrable_square)
    (integrable_nonpositive μ h _ (integrable_signed_cube μ h)) (scale_center0 μ h)

theorem residual1_centered (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    MomentBudget.CenteredResidualLaw (residual1 μ h) :=
  affineLaw_centered (SignSplit.positiveLaw μ h) (scale μ h) (-(q μ))
    (integrable_positive μ h _ h.integrable_mean)
    (integrable_positive μ h _ h.integrable_square)
    (integrable_positive μ h _ (integrable_signed_cube μ h))
    (by simpa only [mean1, sub_eq_add_neg] using scale_center1 μ h)

theorem residual0_sign (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    ∀ᵐ u ∂(residual0 μ h : Measure ℝ), u ≤ p μ := by
  have hf : Measurable (fun x : ℝ => scale μ h * x + p μ) := by fun_prop
  change ∀ᵐ u ∂(SignSplit.nonpositiveLaw μ h : Measure ℝ).map
    (fun x : ℝ => scale μ h * x + p μ), u ≤ p μ
  apply (ae_map_iff hf.aemeasurable measurableSet_Iic).mpr
  filter_upwards [nonpositive_ae μ h] with x hx
  have := mul_nonpos_of_nonneg_of_nonpos (le_of_lt (scale_pos μ h)) hx
  change scale μ h * x + p μ ≤ p μ
  linarith

theorem residual1_sign (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    ∀ᵐ u ∂(residual1 μ h : Measure ℝ), -(q μ) ≤ u := by
  have hf : Measurable (fun x : ℝ => scale μ h * x + -(q μ)) := by fun_prop
  change ∀ᵐ u ∂(SignSplit.positiveLaw μ h : Measure ℝ).map
    (fun x : ℝ => scale μ h * x + -(q μ)), -(q μ) ≤ u
  apply (ae_map_iff hf.aemeasurable measurableSet_Ici).mpr
  filter_upwards [positive_ae μ h] with x hx
  have := mul_nonneg (le_of_lt (scale_pos μ h)) (le_of_lt hx)
  change -(q μ) ≤ scale μ h * x + -(q μ)
  linarith

theorem map_affine_inverse (ν : ProbabilityMeasure ℝ) (c t : ℝ) (hc : c ≠ 0) :
    (affineLaw ν c t : Measure ℝ).map (fun u : ℝ => (u - t) / c) = (ν : Measure ℝ) := by
  have hf : Measurable (fun x : ℝ => c * x + t) := by fun_prop
  have hg : Measurable (fun u : ℝ => (u - t) / c) := by fun_prop
  change ((ν : Measure ℝ).map (fun x : ℝ => c * x + t)).map
    (fun u : ℝ => (u - t) / c) = _
  rw [Measure.map_map hg hf]
  have hinv : (fun u : ℝ => (u - t) / c) ∘ (fun x : ℝ => c * x + t) = id := by
    funext x
    dsimp
    field_simp [hc]
    ring
  rw [hinv, Measure.map_id]

theorem residual0_inverse (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    (residual0 μ h : Measure ℝ).map (fun u : ℝ => (u - p μ) / scale μ h) =
      (SignSplit.nonpositiveLaw μ h : Measure ℝ) :=
  map_affine_inverse _ _ _ (ne_of_gt (scale_pos μ h))

theorem residual1_inverse (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    (residual1 μ h : Measure ℝ).map (fun u : ℝ => (u + q μ) / scale μ h) =
      (SignSplit.positiveLaw μ h : Measure ℝ) := by
  simpa only [residual1, sub_neg_eq_add] using
    map_affine_inverse (SignSplit.positiveLaw μ h) (scale μ h) (-(q μ))
      (ne_of_gt (scale_pos μ h))

/-- Every target law is exactly the mixture of its canonical centered residuals. -/
theorem law_eq_residualMixture (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    μ = MomentBudget.residualMixtureLaw (residual0 μ h) (residual1 μ h)
      (p μ) (scale μ h) (le_of_lt (p_pos μ h)) (le_of_lt (p_lt_one μ h)) := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [MomentBudget.coe_residualMixtureLaw, MomentBudget.residualMixtureMeasure,
    residual0_inverse]
  change (μ : Measure ℝ) =
    ENNReal.ofReal (q μ) • (SignSplit.nonpositiveLaw μ h : Measure ℝ) +
      ENNReal.ofReal (p μ) • (residual1 μ h : Measure ℝ).map
        (fun u : ℝ => (u + q μ) / scale μ h)
  rw [residual1_inverse]
  simpa only [q_eq_nonpositiveWeight, p] using SignSplit.law_eq_sign_mixture μ h

def noiseVariance (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) : ℝ :=
  q μ * MomentBudget.residualSecondMoment (residual0 μ h) +
    p μ * MomentBudget.residualSecondMoment (residual1 μ h)

theorem noiseVariance_nonneg (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    0 ≤ noiseVariance μ h :=
  add_nonneg (mul_nonneg (le_of_lt (q_pos μ h))
      (MomentBudget.residualSecondMoment_nonneg _))
    (mul_nonneg (le_of_lt (p_pos μ h)) (MomentBudget.residualSecondMoment_nonneg _))

theorem scale_sq (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    scale μ h ^ 2 = p μ * q μ + noiseVariance μ h := by
  have hm := MomentBudget.actual_second_moment (residual0 μ h) (residual1 μ h)
    (residual0_centered μ h) (residual1_centered μ h) (p μ) (scale μ h)
    (le_of_lt (p_pos μ h)) (le_of_lt (p_lt_one μ h))
  rw [← law_eq_residualMixture μ h, h.second_moment_one] at hm
  have hc : scale μ h ^ 2 ≠ 0 := pow_ne_zero _ (ne_of_gt (scale_pos μ h))
  have heq := (div_eq_iff hc).mp hm.symm
  dsimp [q, noiseVariance] at *
  nlinarith

theorem scale_eq_sqrt (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    scale μ h = Real.sqrt (p μ * q μ + noiseVariance μ h) := by
  rw [← scale_sq μ h, Real.sqrt_sq (le_of_lt (scale_pos μ h))]

/-- The canonical representation at the exact scale used by the moment budget. -/
theorem law_eq_normalizedResidualMixture (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    μ = MomentBudget.residualMixtureLaw (residual0 μ h) (residual1 μ h)
      (p μ) (Real.sqrt (p μ * (1 - p μ) + noiseVariance μ h))
      (le_of_lt (p_pos μ h)) (le_of_lt (p_lt_one μ h)) := by
  simpa only [scale_eq_sqrt, q] using law_eq_residualMixture μ h

/-- The cubic budget concerns the original target law's actual third moment. -/
theorem thirdAbsoluteMoment_identity (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    thirdAbsoluteMoment μ * scale μ h ^ 3 =
      p μ * q μ * (1 - 2 * (p μ * q μ)) +
        3 * (p μ * q μ) *
          (MomentBudget.residualSecondMoment (residual0 μ h) +
            MomentBudget.residualSecondMoment (residual1 μ h)) -
        q μ * MomentBudget.residualCubicMoment (residual0 μ h) +
        p μ * MomentBudget.residualCubicMoment (residual1 μ h) := by
  have h0 := residual0_centered μ h
  have h1 := residual1_centered μ h
  have ht := MomentBudget.actual_thirdAbsoluteMoment_identity
    (residual0 μ h) (residual1 μ h) (p μ) (scale μ h)
    (le_of_lt (p_pos μ h)) (le_of_lt (p_lt_one μ h)) (scale_pos μ h)
    h0.integrable_first h0.integrable_second h0.integrable_third
    h1.integrable_first h1.integrable_second h1.integrable_third
    h0.mean_zero h1.mean_zero (residual0_sign μ h)
    (by simpa only [q] using residual1_sign μ h)
  rw [← law_eq_residualMixture μ h] at ht
  simpa only [q, MomentBudget.residualSecondMoment, MomentBudget.residualCubicMoment] using ht

end BerryEsseen.CanonicalSign

#print axioms BerryEsseen.CanonicalSign.mean1_pos
#print axioms BerryEsseen.CanonicalSign.residual0_centered
#print axioms BerryEsseen.CanonicalSign.residual1_centered
#print axioms BerryEsseen.CanonicalSign.law_eq_residualMixture
#print axioms BerryEsseen.CanonicalSign.scale_eq_sqrt
#print axioms BerryEsseen.CanonicalSign.law_eq_normalizedResidualMixture
#print axioms BerryEsseen.CanonicalSign.residual0_sign
#print axioms BerryEsseen.CanonicalSign.residual1_sign
#print axioms BerryEsseen.CanonicalSign.thirdAbsoluteMoment_identity
