module

public import BerryEsseen.CanonicalSign
public import BerryEsseen.SignedMoment
public import Mathlib.Tactic.FieldSimp

@[expose] public section

/-! 2026-10-28: physical conditional variances and canonical noise coordinates.
The physical theta variables are actual centered moments of the original
sign-conditional laws, rather than independent parameters.
-/

noncomputable section

open MeasureTheory

namespace BerryEsseen.NoiseCoordinates

open CanonicalSign

def conditionalVariance0 (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) : ℝ :=
  ∫ x : ℝ, (x - mean0 μ h) ^ 2 ∂(SignSplit.nonpositiveLaw μ h : Measure ℝ)

def conditionalVariance1 (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) : ℝ :=
  ∫ x : ℝ, (x - mean1 μ h) ^ 2 ∂(SignSplit.positiveLaw μ h : Measure ℝ)

def thetaMinus (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) : ℝ := q μ * conditionalVariance0 μ h
def thetaPlus (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) : ℝ := p μ * conditionalVariance1 μ h
def theta (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) : ℝ := thetaMinus μ h + thetaPlus μ h
def noiseLevel (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (n : ℕ) : ℝ :=
  (n : ℝ) * noiseVariance μ h
def allocation (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) : ℝ :=
  p μ * MomentBudget.residualSecondMoment (residual1 μ h) / noiseVariance μ h
def positiveFirstMoment (μ : ProbabilityMeasure ℝ) : ℝ := ∫ x : ℝ, max x 0 ∂(μ : Measure ℝ)

lemma integrable_conditionalVariance0 (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    Integrable (fun x : ℝ => (x - mean0 μ h) ^ 2) (SignSplit.nonpositiveLaw μ h : Measure ℝ) := by
  simpa only [sub_eq_add_neg] using MomentBudget.integrable_square_add_const
    (SignSplit.nonpositiveLaw μ h : Measure ℝ) (fun x : ℝ => x) (-(mean0 μ h))
    (integrable_nonpositive μ h _ h.integrable_mean)
    (integrable_nonpositive μ h _ h.integrable_square)

lemma integrable_conditionalVariance1 (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    Integrable (fun x : ℝ => (x - mean1 μ h) ^ 2) (SignSplit.positiveLaw μ h : Measure ℝ) := by
  simpa only [sub_eq_add_neg] using MomentBudget.integrable_square_add_const
    (SignSplit.positiveLaw μ h : Measure ℝ) (fun x : ℝ => x) (-(mean1 μ h))
    (integrable_positive μ h _ h.integrable_mean)
    (integrable_positive μ h _ h.integrable_square)

private lemma affine_centered_square (ν : ProbabilityMeasure ℝ) (c m t : ℝ)
    (hm : c * m + t = 0) :
    (∫ u : ℝ, u ^ 2 ∂(affineLaw ν c t : Measure ℝ)) =
      c ^ 2 * ∫ x : ℝ, (x - m) ^ 2 ∂(ν : Measure ℝ) := by
  change (∫ u : ℝ, u ^ 2 ∂(ν : Measure ℝ).map (fun x : ℝ => c * x + t)) = _
  rw [integral_map (by fun_prop) (by fun_prop)]
  have heq : (fun x : ℝ => (c * x + t) ^ 2) =
      (fun x : ℝ => c ^ 2 * (x - m) ^ 2) := by
    funext x
    have hc : c * x + t = c * (x - m) := by nlinarith
    rw [hc]
    ring
  rw [heq, integral_const_mul]

theorem residualSecondMoment0_eq (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    MomentBudget.residualSecondMoment (residual0 μ h) = scale μ h ^ 2 * conditionalVariance0 μ h :=
  affine_centered_square (SignSplit.nonpositiveLaw μ h) (scale μ h) (mean0 μ h) (p μ)
    (scale_center0 μ h)

theorem residualSecondMoment1_eq (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    MomentBudget.residualSecondMoment (residual1 μ h) = scale μ h ^ 2 * conditionalVariance1 μ h :=
  affine_centered_square (SignSplit.positiveLaw μ h) (scale μ h) (mean1 μ h) (-(q μ))
    (by simpa only [sub_eq_add_neg] using scale_center1 μ h)

theorem thetaMinus_nonneg (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) : 0 ≤ thetaMinus μ h :=
  mul_nonneg (q_pos μ h).le (integral_nonneg fun _ => sq_nonneg _)

theorem thetaPlus_nonneg (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) : 0 ≤ thetaPlus μ h :=
  mul_nonneg (p_pos μ h).le (integral_nonneg fun _ => sq_nonneg _)

theorem theta_nonneg (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) : 0 ≤ theta μ h :=
  add_nonneg (thetaMinus_nonneg μ h) (thetaPlus_nonneg μ h)

/-- The canonical noise is the scaled actual within-sign conditional variance. -/
theorem scale_sq_mul_theta (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    scale μ h ^ 2 * theta μ h = noiseVariance μ h := by
  unfold theta thetaMinus thetaPlus noiseVariance
  rw [residualSecondMoment0_eq, residualSecondMoment1_eq]
  ring

theorem scale_sq_mul_complement (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    scale μ h ^ 2 * (1 - theta μ h) = p μ * q μ := by
  have h1 := scale_sq μ h
  have h2 := scale_sq_mul_theta μ h
  nlinarith

theorem theta_lt_one (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) : theta μ h < 1 := by
  have hc : 0 < scale μ h ^ 2 := sq_pos_of_pos (scale_pos μ h)
  have hp : 0 < scale μ h ^ 2 * (1 - theta μ h) := by
    rw [scale_sq_mul_complement]
    exact mul_pos (p_pos μ h) (q_pos μ h)
  have hh := (mul_pos_iff_of_pos_left hc).mp hp
  linarith

theorem scale_sq_eq_physical (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    scale μ h ^ 2 = p μ * q μ / (1 - theta μ h) :=
  (eq_div_iff (ne_of_gt (sub_pos.mpr (theta_lt_one μ h)))).mpr (scale_sq_mul_complement μ h)

theorem noiseVariance_eq_physical (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    noiseVariance μ h = p μ * q μ * theta μ h / (1 - theta μ h) := by
  apply (eq_div_iff (ne_of_gt (sub_pos.mpr (theta_lt_one μ h)))).mpr
  rw [← scale_sq_mul_theta]
  calc
    (scale μ h ^ 2 * theta μ h) * (1 - theta μ h) =
        (scale μ h ^ 2 * (1 - theta μ h)) * theta μ h := by ring
    _ = _ := by rw [scale_sq_mul_complement]

/-- This identity includes zero noise and keeps the same actual law and sample size. -/
theorem noiseLevel_eq_physical (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (n : ℕ) :
    noiseLevel μ h n = (n : ℝ) * p μ * q μ * theta μ h / (1 - theta μ h) := by
  rw [noiseLevel, noiseVariance_eq_physical]
  ring

theorem theta_pos_of_noise_pos (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hs : 0 < noiseVariance μ h) : 0 < theta μ h := by
  rw [← scale_sq_mul_theta] at hs
  exact (mul_pos_iff_of_pos_left (sq_pos_of_pos (scale_pos μ h))).mp hs

/-- On the positive-noise domain, allocation is the physical positive-sign variance share. -/
theorem allocation_eq_physical (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hs : 0 < noiseVariance μ h) : allocation μ h = thetaPlus μ h / theta μ h := by
  have hc : scale μ h ≠ 0 := (scale_pos μ h).ne'
  have ht : theta μ h ≠ 0 := (theta_pos_of_noise_pos μ h hs).ne'
  unfold allocation thetaPlus
  rw [residualSecondMoment1_eq, ← scale_sq_mul_theta]
  field_simp [hc, ht]

private lemma integral_sign_groups (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (f : ℝ → ℝ) (hf : Integrable f (μ : Measure ℝ)) :
    (∫ x : ℝ, f x ∂(μ : Measure ℝ)) =
      q μ * (∫ x : ℝ, f x ∂(SignSplit.nonpositiveLaw μ h : Measure ℝ)) +
      p μ * (∫ x : ℝ, f x ∂(SignSplit.positiveLaw μ h : Measure ℝ)) := by
  have h0 := integrable_nonpositive μ h f hf
  have h1 := integrable_positive μ h f hf
  have heq := congrArg (fun ν : Measure ℝ => ∫ x : ℝ, f x ∂ν)
    (SignSplit.law_eq_sign_mixture μ h)
  rw [integral_add_measure (h0.smul_measure ENNReal.ofReal_ne_top)
      (h1.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
    ENNReal.toReal_ofReal (SignSplit.weights_pos μ h).2.le,
    ENNReal.toReal_ofReal (SignSplit.weights_pos μ h).1.le] at heq
  simpa only [q_eq_nonpositiveWeight, p, smul_eq_mul] using heq

private lemma integral_centered_sq (ν : ProbabilityMeasure ℝ) (m : ℝ)
    (h1 : Integrable (fun x : ℝ => x) (ν : Measure ℝ))
    (h2 : Integrable (fun x : ℝ => x ^ 2) (ν : Measure ℝ))
    (hm : (∫ x : ℝ, x ∂(ν : Measure ℝ)) = m) :
    (∫ x : ℝ, (x - m) ^ 2 ∂(ν : Measure ℝ)) =
      (∫ x : ℝ, x ^ 2 ∂(ν : Measure ℝ)) - m ^ 2 := by
  have hh := MomentBudget.integral_square_add_const (ν : Measure ℝ) (fun x : ℝ => x) (-m) h1 h2
  have heq : (fun x : ℝ => (x - m) ^ 2) = (fun x : ℝ => (x + -m) ^ 2) := by
    ext x
    rw [sub_eq_add_neg]
  rw [heq, hh, hm]
  ring

lemma conditionalVariance0_formula (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    conditionalVariance0 μ h =
      (∫ x : ℝ, x ^ 2 ∂(SignSplit.nonpositiveLaw μ h : Measure ℝ)) - mean0 μ h ^ 2 :=
  integral_centered_sq (SignSplit.nonpositiveLaw μ h) (mean0 μ h)
    (integrable_nonpositive μ h _ h.integrable_mean)
    (integrable_nonpositive μ h _ h.integrable_square) rfl

lemma conditionalVariance1_formula (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    conditionalVariance1 μ h =
      (∫ x : ℝ, x ^ 2 ∂(SignSplit.positiveLaw μ h : Measure ℝ)) - mean1 μ h ^ 2 :=
  integral_centered_sq (SignSplit.positiveLaw μ h) (mean1 μ h)
    (integrable_positive μ h _ h.integrable_mean)
    (integrable_positive μ h _ h.integrable_square) rfl

lemma signedSecondMoment_groups (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    SignedMoment.signedSecondMoment μ =
      p μ * (∫ x : ℝ, x ^ 2 ∂(SignSplit.positiveLaw μ h : Measure ℝ)) -
      q μ * (∫ x : ℝ, x ^ 2 ∂(SignSplit.nonpositiveLaw μ h : Measure ℝ)) := by
  have hi := integral_sign_groups μ h (fun x : ℝ => x * |x|)
    (SignedMoment.integrable_signedSecondMoment μ h)
  have h0 : (∫ x : ℝ, x * |x| ∂(SignSplit.nonpositiveLaw μ h : Measure ℝ)) =
      -(∫ x : ℝ, x ^ 2 ∂(SignSplit.nonpositiveLaw μ h : Measure ℝ)) := by
    calc
      _ = ∫ x : ℝ, -(x ^ 2) ∂(SignSplit.nonpositiveLaw μ h : Measure ℝ) :=
        integral_congr_ae ((nonpositive_ae μ h).mono fun x hx => by
          rw [abs_of_nonpos hx]
          ring)
      _ = _ := integral_neg _
  have h1 : (∫ x : ℝ, x * |x| ∂(SignSplit.positiveLaw μ h : Measure ℝ)) =
      (∫ x : ℝ, x ^ 2 ∂(SignSplit.positiveLaw μ h : Measure ℝ)) :=
    integral_congr_ae ((positive_ae μ h).mono fun x hx => by
      change x * |x| = x ^ 2
      rw [abs_of_nonneg hx.le]
      ring)
  rw [h0, h1] at hi
  change SignedMoment.signedSecondMoment μ = _ at hi
  nlinarith

/-- The signed second moment is tied to these same physical variance shares. -/
theorem signedSecondMoment_eq_physical (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    SignedMoment.signedSecondMoment μ =
      (1 - theta μ h) * (1 - 2 * p μ) + thetaPlus μ h - thetaMinus μ h := by
  have hc : scale μ h ≠ 0 := (scale_pos μ h).ne'
  have hm0 : mean0 μ h = -(p μ) / scale μ h := by
    apply (eq_div_iff hc).mpr
    nlinarith [scale_center0 μ h]
  have hm1 : mean1 μ h = q μ / scale μ h := by
    apply (eq_div_iff hc).mpr
    nlinarith [scale_center1 μ h]
  have hpq : p μ * q μ / scale μ h ^ 2 = 1 - theta μ h := by
    apply (div_eq_iff (pow_ne_zero _ hc)).mpr
    nlinarith [scale_sq_mul_complement μ h]
  have hb : SignedMoment.signedSecondMoment μ = thetaPlus μ h - thetaMinus μ h +
      p μ * mean1 μ h ^ 2 - q μ * mean0 μ h ^ 2 := by
    unfold thetaPlus thetaMinus
    rw [conditionalVariance0_formula μ h, conditionalVariance1_formula μ h,
      signedSecondMoment_groups μ h]
    ring
  calc
    _ = thetaPlus μ h - thetaMinus μ h +
        (p μ * q μ / scale μ h ^ 2) * (q μ - p μ) := by
      rw [hb, hm0, hm1]
      field_simp [hc]
      ring
    _ = _ := by rw [hpq]; unfold q; ring

theorem abs_signedSecondMoment_le_physical (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    |SignedMoment.signedSecondMoment μ| ≤
      (1 - theta μ h) * |1 - 2 * p μ| + theta μ h := by
  rw [signedSecondMoment_eq_physical]
  have htm := thetaMinus_nonneg μ h
  have htp := thetaPlus_nonneg μ h
  have hcomp : 0 ≤ 1 - theta μ h := (sub_pos.mpr (theta_lt_one μ h)).le
  calc
    _ ≤ |(1 - theta μ h) * (1 - 2 * p μ)| + |thetaPlus μ h - thetaMinus μ h| := by
      simpa only [sub_eq_add_neg, add_assoc] using
        abs_add_le ((1 - theta μ h) * (1 - 2 * p μ)) (thetaPlus μ h - thetaMinus μ h)
    _ ≤ (1 - theta μ h) * |1 - 2 * p μ| + theta μ h := by
      rw [abs_mul, abs_of_nonneg hcomp]
      have hdiff : |thetaPlus μ h - thetaMinus μ h| ≤ theta μ h := by
        unfold theta
        apply abs_le.mpr
        constructor <;> linarith
      exact add_le_add le_rfl hdiff

theorem positiveFirstMoment_eq_group (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    positiveFirstMoment μ = p μ * mean1 μ h := by
  have hi := integral_sign_groups μ h (fun x : ℝ => max x 0) h.integrable_mean.pos_part
  have h0 : (∫ x : ℝ, max x 0 ∂(SignSplit.nonpositiveLaw μ h : Measure ℝ)) = 0 := by
    calc
      _ = ∫ _ : ℝ, (0 : ℝ) ∂(SignSplit.nonpositiveLaw μ h : Measure ℝ) :=
        integral_congr_ae ((nonpositive_ae μ h).mono fun x hx => by
          change max x 0 = (0 : ℝ)
          exact max_eq_right hx)
      _ = 0 := integral_zero _ _
  have h1 : (∫ x : ℝ, max x 0 ∂(SignSplit.positiveLaw μ h : Measure ℝ)) = mean1 μ h :=
    integral_congr_ae ((positive_ae μ h).mono fun x hx => by
      change max x 0 = x
      exact max_eq_left hx.le)
  rw [h0, h1] at hi
  change positiveFirstMoment μ = q μ * 0 + p μ * mean1 μ h at hi
  simpa only [mul_zero, zero_add] using hi

theorem positiveFirstMoment_pos (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    0 < positiveFirstMoment μ := by
  rw [positiveFirstMoment_eq_group μ h]
  exact mul_pos (p_pos μ h) (mean1_pos μ h)

theorem positiveFirstMoment_mul_scale (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    positiveFirstMoment μ * scale μ h = p μ * q μ := by
  calc
    _ = p μ * (scale μ h * mean1 μ h) := by rw [positiveFirstMoment_eq_group μ h]; ring
    _ = _ := by congr 1; linarith [scale_center1 μ h]

theorem positiveFirstMoment_div_scale (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    positiveFirstMoment μ / scale μ h = 1 - theta μ h := by
  have hc := (scale_pos μ h).ne'
  have heq : positiveFirstMoment μ * scale μ h = ((1 - theta μ h) * scale μ h) * scale μ h := by
    calc
      _ = p μ * q μ := positiveFirstMoment_mul_scale μ h
      _ = scale μ h ^ 2 * (1 - theta μ h) := (scale_sq_mul_complement μ h).symm
      _ = _ := by ring
  apply (div_eq_iff hc).mpr
  exact mul_right_cancel₀ hc heq

theorem positiveFirstMoment_sq (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    positiveFirstMoment μ ^ 2 = p μ * q μ * (1 - theta μ h) := by
  have hc := (scale_pos μ h).ne'
  calc
    _ = (positiveFirstMoment μ * scale μ h) * (positiveFirstMoment μ / scale μ h) := by
      field_simp [hc]
    _ = _ := by rw [positiveFirstMoment_mul_scale μ h, positiveFirstMoment_div_scale μ h]

/-- A probability interval and an acquired bound on this law's actual
within-sign variance give an absolute signed-moment cap. -/
theorem abs_signedSecondMoment_le_interval (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (l u Θ : ℝ) (hl : 0 ≤ l) (hu : u ≤ 1) (hlp : l ≤ p μ) (hpu : p μ ≤ u)
    (hθ : theta μ h ≤ Θ) :
    |SignedMoment.signedSecondMoment μ| ≤
      max |1 - 2 * l| |1 - 2 * u| + (1 - max |1 - 2 * l| |1 - 2 * u|) * Θ := by
  let B := max |1 - 2 * l| |1 - 2 * u|
  have hl1 : l ≤ 1 := hlp.trans (p_lt_one μ h).le
  have hu0 : 0 ≤ u := (p_pos μ h).le.trans hpu
  have hB : B ≤ 1 := max_le
    (abs_le.mpr ⟨by linarith, by linarith⟩) (abs_le.mpr ⟨by linarith, by linarith⟩)
  have hleft : |1 - 2 * l| ≤ B := le_max_left _ _
  have hright : |1 - 2 * u| ≤ B := le_max_right _ _
  have hp : |1 - 2 * p μ| ≤ B := by
    apply abs_le.mpr
    constructor
    · linarith [neg_le_abs (1 - 2 * u)]
    · linarith [le_abs_self (1 - 2 * l)]
  have hcomp : 0 ≤ 1 - theta μ h := (sub_pos.mpr (theta_lt_one μ h)).le
  calc
    _ ≤ (1 - theta μ h) * |1 - 2 * p μ| + theta μ h :=
      abs_signedSecondMoment_le_physical μ h
    _ ≤ (1 - theta μ h) * B + theta μ h :=
      add_le_add (mul_le_mul_of_nonneg_left hp hcomp) le_rfl
    _ = B + (1 - B) * theta μ h := by ring
    _ ≤ B + (1 - B) * Θ := by
      have hm := mul_le_mul_of_nonneg_left hθ (show 0 ≤ 1 - B by linarith)
      linarith

end BerryEsseen.NoiseCoordinates

#print axioms BerryEsseen.NoiseCoordinates.scale_sq_mul_theta
#print axioms BerryEsseen.NoiseCoordinates.theta_lt_one
#print axioms BerryEsseen.NoiseCoordinates.noiseLevel_eq_physical
#print axioms BerryEsseen.NoiseCoordinates.allocation_eq_physical
#print axioms BerryEsseen.NoiseCoordinates.signedSecondMoment_eq_physical
#print axioms BerryEsseen.NoiseCoordinates.abs_signedSecondMoment_le_physical
#print axioms BerryEsseen.NoiseCoordinates.positiveFirstMoment_sq
#print axioms BerryEsseen.NoiseCoordinates.abs_signedSecondMoment_le_interval
