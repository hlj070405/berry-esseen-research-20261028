module

public import BerryEsseen.WeightedCDFTransport
public import Mathlib.Analysis.Complex.RealDeriv

@[expose] public section

/-! The cross-law CDF L1 and characteristic-function bounds for square
bias. Only the original standardized finite-third-moment law is assumed.
The CDF may jump; its single crossing is obtained by an infimum, and the
absolute-value primitive is justified by right derivatives at its corner. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology Interval

namespace BerryEsseen.SquareBiasDistance

open SquareBias WeightedCDFTransport

theorem cdfDifference_nonpos_left (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (s : ℝ) (hs : s ≤ -1) : cdfDifference μ h s ≤ 0 := by
  rw [cdfDifference_eq_integral]
  apply neg_nonpos.mpr
  apply setIntegral_nonneg measurableSet_Iic
  intro x hx
  unfold weight
  have hx1 : x ≤ -1 := le_trans hx hs
  nlinarith [sq_nonneg (x + 1)]

theorem cdfDifference_nonneg_right (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (s : ℝ) (hs : 1 ≤ s) : 0 ≤ cdfDifference μ h s := by
  have hsplit := integral_add_compl (s := Iic s) measurableSet_Iic (integrable_weight μ h)
  simp only [compl_Iic, integral_weight μ h] at hsplit
  rw [cdfDifference_eq_integral]
  have heq : -(∫ x in Iic s, weight x ∂(μ : Measure ℝ)) =
      ∫ x in Ioi s, weight x ∂(μ : Measure ℝ) := by linarith
  rw [heq]
  apply setIntegral_nonneg measurableSet_Ioi
  intro x hx
  unfold weight
  have hx1 : 1 < x := lt_of_le_of_lt hs hx
  nlinarith [sq_nonneg (x - 1)]

theorem cdfDifference_monotoneOn (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    MonotoneOn (cdfDifference μ h) (Icc (-1) 1) := by
  intro s hs t ht hst
  have hd := intervalIntegral.integral_Iic_sub_Iic
    ((integrable_weight μ h).integrableOn (s := Iic s))
    ((integrable_weight μ h).integrableOn (s := Iic t))
  rw [intervalIntegral.integral_of_le hst] at hd
  have hnon : (∫ x in Ioc s t, weight x ∂(μ : Measure ℝ)) ≤ 0 := by
    apply setIntegral_nonpos measurableSet_Ioc
    intro x hx
    unfold weight
    have hxl : -1 ≤ x := le_trans hs.1 hx.1.le
    have hxu : x ≤ 1 := le_trans hx.2 ht.2
    nlinarith [mul_nonneg (by linarith : 0 ≤ x + 1) (by linarith : 0 ≤ 1 - x)]
  rw [cdfDifference_eq_integral, cdfDifference_eq_integral]
  linarith

/-- No continuity of the CDF is needed, including at the crossing point. -/
theorem exists_single_crossing (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    ∃ a ∈ Icc (-1 : ℝ) 1,
      (∀ s < a, cdfDifference μ h s ≤ 0) ∧
      (∀ s > a, 0 ≤ cdfDifference μ h s) := by
  let S : Set ℝ := {s | s ∈ Icc (-1 : ℝ) 1 ∧ 0 ≤ cdfDifference μ h s}
  have hS : S.Nonempty := ⟨1, ⟨by norm_num, cdfDifference_nonneg_right μ h 1 le_rfl⟩⟩
  have hb : BddBelow S := ⟨-1, fun s hs => hs.1.1⟩
  let a := sInf S
  have haL : -1 ≤ a := le_csInf hS (fun s hs => hs.1.1)
  have haU : a ≤ 1 := csInf_le hb ⟨by norm_num, cdfDifference_nonneg_right μ h 1 le_rfl⟩
  refine ⟨a, ⟨haL, haU⟩, ?_, ?_⟩
  · intro s hsa
    by_cases hs : s ≤ -1
    · exact cdfDifference_nonpos_left μ h s hs
    · apply le_of_not_gt
      intro hpos
      have hsS : s ∈ S := ⟨⟨le_of_not_ge hs, hsa.le.trans haU⟩, hpos.le⟩
      exact (not_le_of_gt hsa) (csInf_le hb hsS)
  · intro s has
    by_cases hs : 1 ≤ s
    · exact cdfDifference_nonneg_right μ h s hs
    · obtain ⟨u, hu, hus⟩ := exists_lt_of_csInf_lt hS has
      exact hu.2.trans (cdfDifference_monotoneOn μ h hu.1
        ⟨haL.trans has.le, le_of_not_ge hs⟩ hus.le)

def step (a s : ℝ) : ℝ := if a ≤ s then 1 else -1

lemma measurable_step (a : ℝ) : Measurable (step a) := by
  unfold step
  exact measurable_const.piecewise (measurableSet_le measurable_const measurable_id) measurable_const

lemma norm_step (a s : ℝ) : ‖step a s‖ = 1 := by
  unfold step
  split_ifs <;> norm_num

lemma hasDerivWithinAt_abs_sub_right (a s : ℝ) :
    HasDerivWithinAt (fun y : ℝ => |y - a|) (step a s) (Ioi s) s := by
  rcases lt_trichotomy s a with hsa | heq | has
  · have hd : HasDerivAt (fun y : ℝ => |y - a|) (-1) s := by
      apply (((hasDerivAt_id s).sub_const a).neg).congr_of_eventuallyEq
      filter_upwards [eventually_lt_nhds hsa] with y hy
      exact abs_of_neg (sub_neg.mpr hy)
    simpa [step, not_le.mpr hsa] using hd.hasDerivWithinAt (s := Ioi s)
  · subst s
    have hd : HasDerivWithinAt (fun y : ℝ => y - a) 1 (Ioi a) a :=
      ((hasDerivAt_id a).sub_const a).hasDerivWithinAt
    have hh : HasDerivWithinAt (fun y : ℝ => |y - a|) 1 (Ioi a) a := by
      apply hd.congr
      · intro y hy
        exact abs_of_pos (sub_pos.mpr hy)
      · simp
    simpa [step] using hh
  · have hd : HasDerivAt (fun y : ℝ => |y - a|) 1 s := by
      apply ((hasDerivAt_id s).sub_const a).congr_of_eventuallyEq
      filter_upwards [eventually_gt_nhds has] with y hy
      exact abs_of_pos (sub_pos.mpr hy)
    simpa [step, has.le] using hd.hasDerivWithinAt (s := Ioi s)

lemma integral_step (a x : ℝ) : (∫ s in (0 : ℝ)..x, step a s) = |x - a| - |a| := by
  have hi : IntervalIntegrable (step a) volume 0 x :=
    intervalIntegrable_of_bounded (step a) (measurable_step a).stronglyMeasurable
      1 (fun s => (norm_step a s).le) 0 x
  have heq := intervalIntegral.integral_eq_sub_of_hasDeriv_right
    ((continuous_id.sub continuous_const).abs.continuousOn)
    (fun s _ => hasDerivWithinAt_abs_sub_right a s) hi
  change (∫ s in (0 : ℝ)..x, step a s) = |x - a| - |0 - a| at heq
  simpa only [zero_sub, abs_neg] using heq

lemma integrable_abs_shift (ν : ProbabilityMeasure ℝ)
    (hi : Integrable (fun x : ℝ => x) (ν : Measure ℝ)) (a : ℝ) :
    Integrable (fun x : ℝ => |x - a|) (ν : Measure ℝ) := by
  have hh := (hi.sub (integrable_const a)).norm
  change Integrable (fun x : ℝ => ‖x - a‖) (ν : Measure ℝ) at hh
  simpa only [Real.norm_eq_abs] using hh

lemma integrable_id_squareLaw (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    Integrable (fun x : ℝ => x) (squareLaw μ h : Measure ℝ) := by
  apply (integrable_norm_iff (f := fun x : ℝ => x) measurable_id.aestronglyMeasurable).mp
  simpa only [Real.norm_eq_abs] using integrable_abs_squareLaw μ h

lemma integrable_square_abs_shift (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (a : ℝ) :
    Integrable (fun x : ℝ => x ^ 2 * |x - a|) (μ : Measure ℝ) := by
  simpa only [smul_eq_mul] using (integrable_squareLaw_iff μ h (fun x : ℝ => |x - a|)).mp
    (integrable_abs_shift (squareLaw μ h) (integrable_id_squareLaw μ h) a)

/-- The CDF L1 distance is an actual difference of expectations about
the crossing point. Both expectations are finite. -/
theorem exists_cdfL1_identity (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    ∃ a ∈ Icc (-1 : ℝ) 1,
      (∫ s : ℝ, |cdfDifference μ h s|) =
        (∫ x : ℝ, |x - a| ∂(squareLaw μ h : Measure ℝ)) -
          ∫ x : ℝ, |x - a| ∂(μ : Measure ℝ) := by
  obtain ⟨a, ha, hleft, hright⟩ := exists_single_crossing μ h
  have ht := square_transport_of_bounded μ h (step a) (measurable_step a).stronglyMeasurable
    1 zero_le_one (fun s => (norm_step a s).le)
  have hsgn : (fun s : ℝ => cdfDifference μ h s * step a s) =ᵐ[volume]
      (fun s : ℝ => |cdfDifference μ h s|) := by
    filter_upwards [volume.ae_ne a] with s hs
    rcases lt_or_gt_of_ne hs with hsa | has
    · simp [step, not_le.mpr hsa, abs_of_nonpos (hleft s hsa)]
    · simp [step, has.le, abs_of_nonneg (hright s has)]
  have habs := integrable_abs_shift μ h.integrable_mean a
  have hsquare := integrable_square_abs_shift μ h a
  have hdiff : Integrable (fun x : ℝ => x ^ 2 * |x - a| - |x - a|) (μ : Measure ℝ) :=
    hsquare.sub habs
  have hw := (integrable_weight μ h).const_mul |a|
  have heq : (fun x : ℝ => weight x * (∫ s in (0 : ℝ)..x, step a s)) =
      fun x : ℝ => (x ^ 2 * |x - a| - |x - a|) - |a| * weight x := by
    funext x
    rw [integral_step]
    unfold weight
    ring
  refine ⟨a, ha, ?_⟩
  calc
    _ = ∫ s : ℝ, cdfDifference μ h s * step a s := (integral_congr_ae hsgn).symm
    _ = ∫ x : ℝ, weight x * (∫ s in (0 : ℝ)..x, step a s) ∂(μ : Measure ℝ) := by
      simpa only [smul_eq_mul] using ht.2.2.2
    _ = _ := by
      rw [heq, integral_sub hdiff hw, integral_sub hsquare habs,
        integral_const_mul, integral_weight μ h, mul_zero, sub_zero, integral_squareLaw]
      rfl

theorem integral_abs_shift_ge (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (a : ℝ) :
    |a| ≤ ∫ x : ℝ, |x - a| ∂(μ : Measure ℝ) := by
  have hb := norm_integral_le_integral_norm (μ := (μ : Measure ℝ)) (fun x : ℝ => x - a)
  rw [integral_sub h.integrable_mean (integrable_const a), h.mean_zero] at hb
  simpa only [integral_const, probReal_univ, one_smul, zero_sub, Real.norm_eq_abs, abs_neg] using hb

theorem integral_abs_shift_square_le (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (a : ℝ) :
    (∫ x : ℝ, |x - a| ∂(squareLaw μ h : Measure ℝ)) ≤ thirdAbsoluteMoment μ + |a| := by
  rw [integral_squareLaw]
  have hd : Integrable (fun x : ℝ => |x| ^ 3 + |a| * x ^ 2) (μ : Measure ℝ) :=
    h.integrable_cube.add (h.integrable_square.const_mul |a|)
  calc
    _ ≤ ∫ x : ℝ, (|x| ^ 3 + |a| * x ^ 2) ∂(μ : Measure ℝ) := by
      apply integral_mono (integrable_square_abs_shift μ h a) hd
      intro x
      change x ^ 2 * |x - a| ≤ |x| ^ 3 + |a| * x ^ 2
      have hh := mul_le_mul_of_nonneg_left (abs_sub x a) (sq_nonneg x)
      have hp : x ^ 2 * |x| = |x| ^ 3 := by rw [← sq_abs]; ring
      nlinarith
    _ = _ := by
      rw [integral_add h.integrable_cube (h.integrable_square.const_mul |a|),
        integral_const_mul, h.second_moment_one, mul_one]
      rfl

def cdfL1Distance (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) : ℝ :=
  ∫ s : ℝ, |cdfDifference μ h s|

theorem cdfL1Distance_le (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    cdfL1Distance μ h ≤ thirdAbsoluteMoment μ := by
  obtain ⟨a, _, heq⟩ := exists_cdfL1_identity μ h
  have hupper := integral_abs_shift_square_le μ h a
  have hlower := integral_abs_shift_ge μ h a
  unfold cdfL1Distance
  linarith

def phase (t x : ℝ) : ℂ := Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I)
def phaseSlope (t x : ℝ) : ℂ := ((t : ℂ) * Complex.I) * phase t x

lemma continuous_phase (t : ℝ) : Continuous (phase t) := by unfold phase; fun_prop
lemma continuous_phaseSlope (t : ℝ) : Continuous (phaseSlope t) := by
  unfold phaseSlope
  exact continuous_const.mul (continuous_phase t)

lemma norm_phase (t x : ℝ) : ‖phase t x‖ = 1 := by
  simpa only [phase, Complex.ofReal_mul] using Complex.norm_exp_ofReal_mul_I (t * x)

lemma norm_phaseSlope (t x : ℝ) : ‖phaseSlope t x‖ = |t| := by
  rw [phaseSlope, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, norm_phase]
  ring

lemma hasDerivAt_phase (t x : ℝ) : HasDerivAt (phase t) (phaseSlope t x) x := by
  have hd : HasDerivAt (fun z : ℂ => Complex.exp ((t : ℂ) * z * Complex.I))
      (phaseSlope t x) (x : ℂ) := by
    convert (((hasDerivAt_id' (x : ℂ)).const_mul (t : ℂ)).mul_const Complex.I).cexp using 1 <;>
      simp [phaseSlope, phase] <;> ring
  exact hd.comp_ofReal

lemma integral_phaseSlope (t x : ℝ) :
    (∫ s in (0 : ℝ)..x, phaseSlope t s) = phase t x - 1 := by
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => hasDerivAt_phase t s) ((continuous_phaseSlope t).intervalIntegrable 0 x)
  simpa [phase] using hi

lemma integrable_phase (ν : ProbabilityMeasure ℝ) (t : ℝ) :
    Integrable (phase t) (ν : Measure ℝ) := by
  apply (integrable_const (1 : ℝ)).mono' (continuous_phase t).aestronglyMeasurable
  exact Eventually.of_forall fun x => (norm_phase t x).le

lemma charFun_eq_integral_phase (ν : ProbabilityMeasure ℝ) (t : ℝ) :
    charFun (ν : Measure ℝ) t = ∫ x : ℝ, phase t x ∂(ν : Measure ℝ) := by
  rw [charFun_apply_real]
  rfl

/-- The actual difference of the two characteristic functions is a single
complex transport integral. All Fubini and primitive L1 conditions come
from the finite third moment, not a fourth moment. -/
theorem charFun_difference_transport (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (t : ℝ) :
    charFun (squareLaw μ h : Measure ℝ) t - charFun (μ : Measure ℝ) t =
      ∫ s : ℝ, cdfDifference μ h s • phaseSlope t s := by
  have ht := square_transport_of_bounded μ h (phaseSlope t)
    (continuous_phaseSlope t).stronglyMeasurable |t| (abs_nonneg t)
    (fun s => (norm_phaseSlope t s).le)
  have hi : Integrable (phase t) (μ : Measure ℝ) := integrable_phase μ t
  have hi2 : Integrable (fun x : ℝ => x ^ 2 • phase t x) (μ : Measure ℝ) :=
    (integrable_squareLaw_iff μ h (phase t)).mp (integrable_phase (squareLaw μ h) t)
  have hw : Integrable (fun x : ℝ => weight x • (1 : ℂ)) (μ : Measure ℝ) :=
    (integrable_weight μ h).smul_const (1 : ℂ)
  have hdiff : Integrable (fun x : ℝ => x ^ 2 • phase t x - phase t x) (μ : Measure ℝ) :=
    hi2.sub hi
  have heq : (fun x : ℝ => weight x • (∫ s in (0 : ℝ)..x, phaseSlope t s)) =
      fun x : ℝ => (x ^ 2 • phase t x - phase t x) - weight x • (1 : ℂ) := by
    funext x
    rw [integral_phaseSlope, smul_sub, weight, sub_smul, one_smul]
  rw [ht.2.2.2, heq, integral_sub hdiff hw, integral_sub hi2 hi,
    integral_smul_const, integral_weight μ h, zero_smul, sub_zero,
    charFun_eq_integral_phase, charFun_eq_integral_phase, integral_squareLaw]

/-- The sharp rho coefficient compares the square-biased and original
laws, uniformly in every real frequency, including negative frequencies. -/
theorem charFun_squareLaw_sub_le (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (t : ℝ) :
    ‖charFun (squareLaw μ h : Measure ℝ) t - charFun (μ : Measure ℝ) t‖ ≤
      thirdAbsoluteMoment μ * |t| := by
  rw [charFun_difference_transport]
  have hH : Integrable (fun s : ℝ => |cdfDifference μ h s|) := by
    simpa only [Real.norm_eq_abs] using (integrable_square_cdfDifference μ h).norm
  calc
    _ ≤ ∫ s : ℝ, |cdfDifference μ h s| * |t| := by
      apply norm_integral_le_of_norm_le (hH.mul_const |t|)
      exact Eventually.of_forall fun s => by
        rw [norm_smul, Real.norm_eq_abs, norm_phaseSlope]
    _ = cdfL1Distance μ h * |t| := by rw [integral_mul_const]; rfl
    _ ≤ thirdAbsoluteMoment μ * |t| :=
      mul_le_mul_of_nonneg_right (cdfL1Distance_le μ h) (abs_nonneg t)

end BerryEsseen.SquareBiasDistance

#print axioms BerryEsseen.SquareBiasDistance.exists_single_crossing
#print axioms BerryEsseen.SquareBiasDistance.integral_step
#print axioms BerryEsseen.SquareBiasDistance.exists_cdfL1_identity
#print axioms BerryEsseen.SquareBiasDistance.cdfL1Distance_le
#print axioms BerryEsseen.SquareBiasDistance.charFun_difference_transport
#print axioms BerryEsseen.SquareBiasDistance.charFun_squareLaw_sub_le
