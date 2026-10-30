module

public import BerryEsseen.SignedMoment
public import BerryEsseen.MomentBudget
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.InnerProductSpace.NormPow

@[expose] public section

noncomputable section

namespace BerryEsseen.PerturbationMoment

open MeasureTheory Filter Set
open scoped Topology

def mixtureMeasure (μ : ProbabilityMeasure ℝ) (x ε : ℝ) : Measure ℝ :=
  ENNReal.ofReal (1 - ε) • (μ : Measure ℝ) + ENNReal.ofReal ε • Measure.dirac x

theorem mixtureMeasure_isProbability (μ : ProbabilityMeasure ℝ) (x ε : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) : IsProbabilityMeasure (mixtureMeasure μ x ε) := by
  constructor
  simp only [mixtureMeasure, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    measure_univ, mul_one]
  rw [← ENNReal.ofReal_add (sub_nonneg.mpr hε1) hε0]
  simp

def mixtureLaw (μ : ProbabilityMeasure ℝ) (x ε : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) : ProbabilityMeasure ℝ :=
  ⟨mixtureMeasure μ x ε, mixtureMeasure_isProbability μ x ε hε0 hε1⟩

theorem mixture_integrable_first (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (x ε : ℝ) : Integrable (fun u : ℝ => u) (mixtureMeasure μ x ε) := by
  have hd : Integrable (fun u : ℝ => u) (Measure.dirac x) :=
    integrable_dirac (a := x) (f := fun u : ℝ => u) (by finiteness)
  exact (h.integrable_mean.smul_measure ENNReal.ofReal_ne_top).add_measure
    (hd.smul_measure ENNReal.ofReal_ne_top)

theorem mixture_mean (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (x ε : ℝ) (hε0 : 0 ≤ ε) :
    (∫ u : ℝ, u ∂mixtureMeasure μ x ε) = ε * x := by
  have hd : Integrable (fun u : ℝ => u) (Measure.dirac x) :=
    integrable_dirac (a := x) (f := fun u : ℝ => u) (by finiteness)
  rw [mixtureMeasure, integral_add_measure
      (h.integrable_mean.smul_measure ENNReal.ofReal_ne_top)
      (hd.smul_measure ENNReal.ofReal_ne_top),
    integral_smul_measure, integral_smul_measure, h.mean_zero, integral_dirac]
  simp [ENNReal.toReal_ofReal hε0]

private theorem integrable_signed_cube (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    Integrable (fun u : ℝ => u ^ 3) (μ : Measure ℝ) := by
  apply (integrable_norm_iff (by fun_prop :
    AEStronglyMeasurable (fun u : ℝ => u ^ 3) (μ : Measure ℝ))).mp
  simpa only [Real.norm_eq_abs, abs_pow] using h.integrable_cube

theorem integrable_shift_abs_cube (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (t : ℝ) :
    Integrable (fun u : ℝ => |u - t| ^ 3) (μ : Measure ℝ) := by
  have hi := MomentBudget.integrable_cube_add_const (μ : Measure ℝ) (fun u : ℝ => u) (-t)
    h.integrable_mean h.integrable_square (integrable_signed_cube μ h)
  simpa only [Real.norm_eq_abs, abs_pow, sub_eq_add_neg] using hi.norm

def centeredMomentFormula (μ : ProbabilityMeasure ℝ) (x ε : ℝ) : ℝ :=
  (1 - ε) * (∫ u : ℝ, |u - ε * x| ^ 3 ∂(μ : Measure ℝ)) + ε * |(1 - ε) * x| ^ 3

def actualCenteredThirdMoment (μ : ProbabilityMeasure ℝ) (x ε : ℝ) : ℝ :=
  ∫ u : ℝ, |u - ∫ v : ℝ, v ∂mixtureMeasure μ x ε| ^ 3 ∂mixtureMeasure μ x ε

/-- The analytic formula is the actual central third moment of the probability mixture. -/
theorem actualCenteredThirdMoment_eq_formula (μ : ProbabilityMeasure ℝ)
    (h : StandardizedLaw μ) (x ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    actualCenteredThirdMoment μ x ε = centeredMomentFormula μ x ε := by
  have hi := integrable_shift_abs_cube μ h (ε * x)
  have hd : Integrable (fun u : ℝ => |u - ε * x| ^ 3) (Measure.dirac x) :=
    integrable_dirac (a := x) (f := fun u : ℝ => |u - ε * x| ^ 3) (by finiteness)
  unfold actualCenteredThirdMoment
  rw [mixture_mean μ h x ε hε0, mixtureMeasure,
    integral_add_measure (hi.smul_measure ENNReal.ofReal_ne_top)
      (hd.smul_measure ENNReal.ofReal_ne_top),
    integral_smul_measure, integral_smul_measure, integral_dirac]
  rw [ENNReal.toReal_ofReal hε0, ENNReal.toReal_ofReal (sub_nonneg.mpr hε1)]
  change (1 - ε) * _ + ε * |x - ε * x| ^ 3 = _
  have heq : x - ε * x = (1 - ε) * x := by ring
  rw [heq]
  rfl

/-- A single square-integrable bound controls the derivative for all parameters
in the fixed unit neighborhood. No fourth moment or bounded support is used. -/
theorem derivative_domination (u x ε : ℝ) (hε : ε ∈ Metric.ball (0 : ℝ) 1) :
    ‖-3 * x * (u - ε * x) * |u - ε * x|‖ ≤ 6 * |x| * (u ^ 2 + x ^ 2) := by
  have he : |ε| ≤ 1 := le_of_lt (by simpa [Metric.mem_ball, Real.dist_eq] using hε)
  have ha : |u - ε * x| ≤ |u| + |x| := by
    calc
      |u - ε * x| ≤ |u| + |ε * x| := by
        simpa using abs_sub_le u 0 (ε * x)
      _ = |u| + |ε| * |x| := by rw [abs_mul]
      _ ≤ |u| + |x| := by nlinarith [mul_le_mul_of_nonneg_right he (abs_nonneg x)]
  have hs := (sq_le_sq₀ (abs_nonneg (u - ε * x))
    (add_nonneg (abs_nonneg u) (abs_nonneg x))).mpr ha
  have hs2 : |u - ε * x| ^ 2 ≤ 2 * (u ^ 2 + x ^ 2) := by
    nlinarith [sq_nonneg (|u| - |x|), sq_abs u, sq_abs x]
  have hn : ‖-3 * x * (u - ε * x) * |u - ε * x|‖ =
      3 * |x| * |u - ε * x| ^ 2 := by
    simp only [Real.norm_eq_abs, abs_mul, abs_neg, abs_abs,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
    ring
  rw [hn]
  nlinarith [mul_le_mul_of_nonneg_left hs2 (by positivity : 0 ≤ 3 * |x|)]

theorem integrable_derivative_bound (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (x : ℝ) :
    Integrable (fun u : ℝ => 6 * |x| * (u ^ 2 + x ^ 2)) (μ : Measure ℝ) :=
  (h.integrable_square.add (integrable_const (x ^ 2))).const_mul (6 * |x|)

def varianceFormula (x ε : ℝ) : ℝ := (1 - ε) * (1 + ε * x ^ 2)

def actualCenteredSecondMoment (μ : ProbabilityMeasure ℝ) (x ε : ℝ) : ℝ :=
  ∫ u : ℝ, (u - ∫ v : ℝ, v ∂mixtureMeasure μ x ε) ^ 2 ∂mixtureMeasure μ x ε

theorem actualCenteredSecondMoment_eq_formula (μ : ProbabilityMeasure ℝ)
    (h : StandardizedLaw μ) (x ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    actualCenteredSecondMoment μ x ε = varianceFormula x ε := by
  have hi : Integrable (fun u : ℝ => (u - ε * x) ^ 2) (μ : Measure ℝ) := by
    simpa only [sub_eq_add_neg] using MomentBudget.integrable_square_add_const
      (μ : Measure ℝ) (fun u : ℝ => u) (-(ε * x)) h.integrable_mean h.integrable_square
  have hd : Integrable (fun u : ℝ => (u - ε * x) ^ 2) (Measure.dirac x) :=
    integrable_dirac (a := x) (f := fun u : ℝ => (u - ε * x) ^ 2) (by finiteness)
  have hmu : (∫ u : ℝ, (u - ε * x) ^ 2 ∂(μ : Measure ℝ)) = 1 + (ε * x) ^ 2 := by
    have heq := MomentBudget.integral_square_add_const (μ : Measure ℝ)
      (fun u : ℝ => u) (-(ε * x)) h.integrable_mean h.integrable_square
    simpa only [sub_eq_add_neg, h.mean_zero, h.second_moment_one, mul_zero, add_zero,
      neg_sq] using heq
  unfold actualCenteredSecondMoment
  rw [mixture_mean μ h x ε hε0, mixtureMeasure,
    integral_add_measure (hi.smul_measure ENNReal.ofReal_ne_top)
      (hd.smul_measure ENNReal.ofReal_ne_top),
    integral_smul_measure, integral_smul_measure, integral_dirac,
    ENNReal.toReal_ofReal hε0, ENNReal.toReal_ofReal (sub_nonneg.mpr hε1), hmu]
  change (1 - ε) * (1 + (ε * x) ^ 2) + ε * (x - ε * x) ^ 2 = _
  unfold varianceFormula
  ring

theorem hasDerivAt_varianceFormula (x : ℝ) :
    HasDerivAt (varianceFormula x) (x ^ 2 - 1) 0 := by
  have hd := ((hasDerivAt_const (0 : ℝ) 1).sub (hasDerivAt_id 0)).mul
    ((hasDerivAt_const (0 : ℝ) 1).add ((hasDerivAt_id 0).mul_const (x ^ 2)))
  convert hd using 1
  · funext ε
    rfl
  · simp; ring

private theorem eventually_valid_weight :
    ∀ᶠ ε in 𝓝[Set.Ici (0 : ℝ)] 0, ε ∈ Set.Icc (0 : ℝ) 1 := by
  have hlt0 : ∀ᶠ ε : ℝ in 𝓝 (0 : ℝ), ε < 1 :=
    Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)
  have hlt : ∀ᶠ ε : ℝ in 𝓝[Set.Ici (0 : ℝ)] 0, ε < 1 :=
    hlt0.filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hlt] with ε hε0 hε1
  exact ⟨hε0, le_of_lt hε1⟩

theorem actualCenteredSecondMoment_hasDerivWithinAt (μ : ProbabilityMeasure ℝ)
    (h : StandardizedLaw μ) (x : ℝ) :
    HasDerivWithinAt (actualCenteredSecondMoment μ x) (x ^ 2 - 1) (Set.Ici 0) 0 := by
  apply (hasDerivAt_varianceFormula x).hasDerivWithinAt.congr_of_eventuallyEq_of_mem
    ?_ (by simp)
  filter_upwards [eventually_valid_weight] with ε hε
  exact actualCenteredSecondMoment_eq_formula μ h x ε hε.1 hε.2

theorem hasDerivAt_abs_cube (u : ℝ) :
    HasDerivAt (fun z : ℝ => |z| ^ 3) (3 * |u| * u) u := by
  simpa only [show (3 : ℝ) - 2 = 1 by norm_num, Real.rpow_one, Real.rpow_ofNat] using
    hasDerivAt_abs_rpow u (p := (3 : ℝ)) (by norm_num)

theorem hasDerivAt_shift_abs_cube (u x ε : ℝ) :
    HasDerivAt (fun t : ℝ => |u - t * x| ^ 3)
      (-3 * x * (u - ε * x) * |u - ε * x|) ε := by
  have hi : HasDerivAt (fun t : ℝ => u - t * x) (-x) ε := by
    convert (hasDerivAt_const ε u).sub ((hasDerivAt_id ε).mul_const x) using 1
    · funext t
      rfl
    · simp
  have hd := (hasDerivAt_abs_cube (u - ε * x)).comp ε hi
  convert hd using 1
  · funext t
    rfl
  · ring

/-- Differentiation under the integral uses the one fixed integrable bound above. -/
theorem hasDerivAt_shift_integral (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (x : ℝ) :
    HasDerivAt (fun ε : ℝ => ∫ u : ℝ, |u - ε * x| ^ 3 ∂(μ : Measure ℝ))
      (-3 * x * SignedMoment.signedSecondMoment μ) 0 := by
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (μ : Measure ℝ))
    (F := fun ε u : ℝ => |u - ε * x| ^ 3)
    (F' := fun ε u : ℝ => -3 * x * (u - ε * x) * |u - ε * x|)
    (bound := fun u : ℝ => 6 * |x| * (u ^ 2 + x ^ 2))
    (s := Metric.ball (0 : ℝ) 1) (x₀ := (0 : ℝ))
    (Metric.ball_mem_nhds _ (by norm_num))
    (Filter.Eventually.of_forall fun ε => by fun_prop)
    (by simpa only [zero_mul, sub_zero] using h.integrable_cube)
    (by fun_prop)
    (Filter.Eventually.of_forall fun u ε hε => derivative_domination u x ε hε)
    (integrable_derivative_bound μ h x)
    (Filter.Eventually.of_forall fun u ε _ => hasDerivAt_shift_abs_cube u x ε)
  simpa only [zero_mul, sub_zero, mul_assoc, integral_const_mul,
    SignedMoment.signedSecondMoment] using hd.2

/-- The signed analytic extension has an ordinary derivative at zero. -/
theorem hasDerivAt_centeredMomentFormula (μ : ProbabilityMeasure ℝ)
    (h : StandardizedLaw μ) (x : ℝ) :
    HasDerivAt (centeredMomentFormula μ x)
      (|x| ^ 3 - thirdAbsoluteMoment μ - 3 * x * SignedMoment.signedSecondMoment μ) 0 := by
  have hfirst := ((hasDerivAt_const (0 : ℝ) 1).sub (hasDerivAt_id 0)).mul
    (hasDerivAt_shift_integral μ h x)
  have hlin := ((hasDerivAt_const (0 : ℝ) 1).sub (hasDerivAt_id 0)).mul_const x
  have hlast := (hasDerivAt_id (0 : ℝ)).mul
    ((hasDerivAt_abs_cube ((1 - (0 : ℝ)) * x)).comp 0 hlin)
  have hd := hfirst.add hlast
  convert hd using 1
  · funext ε
    rfl
  · simp [thirdAbsoluteMoment]
    ring

/-- The actual probability-mixture central moment has the required right derivative. -/
theorem actualCenteredThirdMoment_hasDerivWithinAt (μ : ProbabilityMeasure ℝ)
    (h : StandardizedLaw μ) (x : ℝ) :
    HasDerivWithinAt (actualCenteredThirdMoment μ x)
      (|x| ^ 3 - thirdAbsoluteMoment μ - 3 * x * SignedMoment.signedSecondMoment μ)
      (Set.Ici 0) 0 := by
  apply (hasDerivAt_centeredMomentFormula μ h x).hasDerivWithinAt.congr_of_eventuallyEq_of_mem
    ?_ (by simp)
  filter_upwards [eventually_valid_weight] with ε hε
  exact actualCenteredThirdMoment_eq_formula μ h x ε hε.1 hε.2

end BerryEsseen.PerturbationMoment

#print axioms BerryEsseen.PerturbationMoment.mixture_mean
#print axioms BerryEsseen.PerturbationMoment.actualCenteredThirdMoment_eq_formula
#print axioms BerryEsseen.PerturbationMoment.derivative_domination
#print axioms BerryEsseen.PerturbationMoment.actualCenteredSecondMoment_eq_formula
#print axioms BerryEsseen.PerturbationMoment.hasDerivAt_varianceFormula
#print axioms BerryEsseen.PerturbationMoment.actualCenteredSecondMoment_hasDerivWithinAt
#print axioms BerryEsseen.PerturbationMoment.hasDerivAt_shift_integral
#print axioms BerryEsseen.PerturbationMoment.hasDerivAt_centeredMomentFormula
#print axioms BerryEsseen.PerturbationMoment.actualCenteredThirdMoment_hasDerivWithinAt
