module

public import BerryEsseen.SquareBias
public import BerryEsseen.ZeroBiasTransport

@[expose] public section

/-! Signed finite-first-moment transport for closed CDF differences.
The oriented segments use Ico, so every original atom retains its exact
closed-CDF endpoint. Product L1 is established before Fubini. -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology Interval

namespace BerryEsseen.WeightedCDFTransport

def segment (x s : ℝ) : ℝ := (if s < x then 1 else 0) - (if s < 0 then 1 else 0)

lemma measurable_segment : Measurable (fun p : ℝ × ℝ => segment p.1 p.2) := by
  unfold segment
  exact (measurable_const.piecewise (measurableSet_lt measurable_snd measurable_fst)
    measurable_const).sub (measurable_const.piecewise
      (measurableSet_lt measurable_snd measurable_const) measurable_const)

lemma segment_of_nonneg (x : ℝ) (hx : 0 ≤ x) :
    segment x = (Ico 0 x).indicator (fun _ => (1 : ℝ)) := by
  funext s
  simp only [segment, Set.indicator_apply, mem_Ico]
  split_ifs <;> simp_all <;> linarith

lemma segment_of_nonpos (x : ℝ) (hx : x ≤ 0) :
    segment x = fun s => -(Ico x 0).indicator (fun _ => (1 : ℝ)) s := by
  funext s
  simp only [segment, Set.indicator_apply, mem_Ico]
  split_ifs <;> simp_all <;> linarith

lemma integrable_segment (x : ℝ) : Integrable (segment x) := by
  rcases le_total 0 x with hx | hx
  · rw [segment_of_nonneg x hx]
    have hi : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ico 0 x) := integrable_const 1
    exact hi.integrable_indicator measurableSet_Ico
  · rw [segment_of_nonpos x hx]
    have hi : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ico x 0) := integrable_const 1
    exact (hi.integrable_indicator measurableSet_Ico).neg

lemma integral_norm_segment (x : ℝ) : (∫ s : ℝ, ‖segment x s‖) = |x| := by
  rcases le_total 0 x with hx | hx
  · rw [segment_of_nonneg x hx]
    simp only [norm_indicator_eq_indicator_norm, Real.norm_eq_abs, abs_one]
    rw [integral_indicator_const (1 : ℝ) measurableSet_Ico, smul_eq_mul, mul_one,
      Real.volume_real_Ico_of_le hx, sub_zero, abs_of_nonneg hx]
  · rw [segment_of_nonpos x hx]
    simp only [norm_neg, norm_indicator_eq_indicator_norm, Real.norm_eq_abs, abs_one]
    rw [integral_indicator_const (1 : ℝ) measurableSet_Ico, smul_eq_mul, mul_one,
      Real.volume_real_Ico_of_le hx, zero_sub, abs_of_nonpos hx]

lemma abs_segment_le_one (x s : ℝ) : |segment x s| ≤ 1 := by
  unfold segment
  split_ifs <;> norm_num

def weightedCDF (μ : ProbabilityMeasure ℝ) (w : ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ x : ℝ, w x * segment x s ∂(μ : Measure ℝ)

theorem integrable_kernel_prod (μ : ProbabilityMeasure ℝ) (w : ℝ → ℝ) (hw : Measurable w)
    (hfirst : Integrable (fun x : ℝ => |w x| * |x|) (μ : Measure ℝ)) :
    Integrable (fun p : ℝ × ℝ => w p.1 * segment p.1 p.2) ((μ : Measure ℝ).prod volume) := by
  have hm := (hw.comp measurable_fst).mul measurable_segment
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  refine ⟨Eventually.of_forall fun x => (integrable_segment x).const_mul (w x), ?_⟩
  have heq : (fun x : ℝ => ∫ s : ℝ, ‖w x * segment x s‖) =
      fun x : ℝ => |w x| * |x| := by
    funext x
    simp only [norm_mul]
    rw [integral_const_mul, integral_norm_segment, Real.norm_eq_abs]
  change Integrable (fun x : ℝ => ∫ s : ℝ, ‖w x * segment x s‖) (μ : Measure ℝ)
  rw [heq]
  exact hfirst

theorem integrable_weightedCDF (μ : ProbabilityMeasure ℝ) (w : ℝ → ℝ) (hw : Measurable w)
    (hfirst : Integrable (fun x : ℝ => |w x| * |x|) (μ : Measure ℝ)) :
    Integrable (weightedCDF μ w) :=
  (integrable_kernel_prod μ w hw hfirst).integral_prod_right

lemma integrable_kernel_x (μ : ProbabilityMeasure ℝ) (w : ℝ → ℝ)
    (hw : Measurable w) (hi : Integrable w (μ : Measure ℝ)) (s : ℝ) :
    Integrable (fun x : ℝ => w x * segment x s) (μ : Measure ℝ) := by
  apply hi.norm.mono' (((hw.mul
    (measurable_segment.comp (measurable_id.prodMk measurable_const)))).aestronglyMeasurable)
  exact Eventually.of_forall fun x => by
    change ‖w x * segment x s‖ ≤ ‖w x‖
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg _) (abs_segment_le_one x s)

lemma weightedCDF_eq_neg_setIntegral (μ : ProbabilityMeasure ℝ) (w : ℝ → ℝ)
    (hi : Integrable w (μ : Measure ℝ)) (hz : (∫ x, w x ∂(μ : Measure ℝ)) = 0) (s : ℝ) :
    weightedCDF μ w s = -∫ x in Iic s, w x ∂(μ : Measure ℝ) := by
  have heq : (fun x : ℝ => w x * segment x s) =
      fun x : ℝ => (Ioi s).indicator w x - (if s < 0 then w x else 0) := by
    funext x
    by_cases hs : s < 0 <;> by_cases hx : s < x <;> simp [segment, hs, hx]
  unfold weightedCDF
  rw [heq, integral_sub (hi.indicator measurableSet_Ioi)
    (by by_cases hs : s < 0 <;> simp [hs, hi]), integral_indicator measurableSet_Ioi]
  have hconst : (∫ x : ℝ, (if s < 0 then w x else 0) ∂(μ : Measure ℝ)) = 0 := by
    by_cases hs : s < 0 <;> simp [hs, hz]
  rw [hconst, sub_zero]
  have hsplit := integral_add_compl (s := Iic s) measurableSet_Iic hi
  simp only [compl_Iic, hz] at hsplit
  linarith

theorem square_cdfDifference_eq_weightedCDF (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    SquareBias.cdfDifference μ h = weightedCDF μ SquareBias.weight := by
  funext s
  rw [SquareBias.cdfDifference_eq_integral,
    weightedCDF_eq_neg_setIntegral μ SquareBias.weight (SquareBias.integrable_weight μ h)
      (SquareBias.integral_weight μ h)]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem intervalIntegrable_of_bounded (g : ℝ → E) (hg : StronglyMeasurable g)
    (B : ℝ) (hbound : ∀ s, ‖g s‖ ≤ B) (a b : ℝ) : IntervalIntegrable g volume a b := by
  apply intervalIntegrable_iff.mpr
  have hi : IntegrableOn (fun _ : ℝ => B) (uIoc a b) := continuous_const.integrableOn_Ioc
  apply MeasureTheory.Integrable.mono' (f := g) (g := fun _ : ℝ => B)
    (μ := volume.restrict (uIoc a b)) hi hg.aestronglyMeasurable
  exact Eventually.of_forall hbound

lemma integral_segment_smul (g : ℝ → E) (x : ℝ) :
    (∫ s : ℝ, segment x s • g s) = ∫ s in (0 : ℝ)..x, g s := by
  rcases le_total 0 x with hx | hx
  · rw [segment_of_nonneg x hx]
    have heq : (fun s : ℝ => (Ico 0 x).indicator (fun _ => (1 : ℝ)) s • g s) =
        (Ico 0 x).indicator g := by
      funext s
      by_cases hs : s ∈ Ico 0 x <;> simp [hs]
    rw [heq, integral_indicator measurableSet_Ico, integral_Ico_eq_integral_Ioc,
      intervalIntegral.integral_of_le hx]
  · rw [segment_of_nonpos x hx]
    have heq : (fun s : ℝ => -(Ico x 0).indicator (fun _ => (1 : ℝ)) s • g s) =
        fun s : ℝ => -((Ico x 0).indicator g s) := by
      funext s
      by_cases hs : s ∈ Ico x 0 <;> simp [hs]
    rw [heq, integral_neg, integral_indicator measurableSet_Ico,
      integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hx,
      intervalIntegral.integral_symm 0 x]
    simp only [neg_neg]

theorem integrable_test_kernel (μ : ProbabilityMeasure ℝ) (w : ℝ → ℝ) (hw : Measurable w)
    (hfirst : Integrable (fun x : ℝ => |w x| * |x|) (μ : Measure ℝ))
    (g : ℝ → E) (hg : StronglyMeasurable g) (B : ℝ) (_hB : 0 ≤ B)
    (hbound : ∀ s, ‖g s‖ ≤ B) :
    Integrable (fun p : ℝ × ℝ => (w p.1 * segment p.1 p.2) • g p.2)
      ((μ : Measure ℝ).prod volume) := by
  apply ((integrable_kernel_prod μ w hw hfirst).norm.const_mul B).mono'
    (((hw.comp measurable_fst).mul measurable_segment).stronglyMeasurable.smul
      (hg.comp_measurable measurable_snd)).aestronglyMeasurable
  exact Eventually.of_forall fun p => by
    change ‖(w p.1 * segment p.1 p.2) • g p.2‖ ≤ B * ‖w p.1 * segment p.1 p.2‖
    rw [norm_smul]
    nlinarith [mul_le_mul_of_nonneg_left (hbound p.2) (norm_nonneg (w p.1 * segment p.1 p.2))]

theorem integrable_weighted_primitive (μ : ProbabilityMeasure ℝ) (w : ℝ → ℝ) (hw : Measurable w)
    (hfirst : Integrable (fun x : ℝ => |w x| * |x|) (μ : Measure ℝ))
    (g : ℝ → E) (hg : StronglyMeasurable g) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ s, ‖g s‖ ≤ B) :
    Integrable (fun x : ℝ => w x • ∫ s in (0 : ℝ)..x, g s) (μ : Measure ℝ) := by
  have hi := (integrable_test_kernel μ w hw hfirst g hg B hB hbound).integral_prod_left
  have heq : (fun x : ℝ => ∫ s : ℝ, (w x * segment x s) • g s) =
      fun x : ℝ => w x • ∫ s in (0 : ℝ)..x, g s := by
    funext x
    simp_rw [mul_smul]
    rw [integral_smul, integral_segment_smul]
  rw [heq] at hi
  exact hi

variable [CompleteSpace E]

theorem integrable_weightedCDF_smul (μ : ProbabilityMeasure ℝ) (w : ℝ → ℝ) (hw : Measurable w)
    (hfirst : Integrable (fun x : ℝ => |w x| * |x|) (μ : Measure ℝ))
    (g : ℝ → E) (hg : StronglyMeasurable g) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ s, ‖g s‖ ≤ B) : Integrable (fun s : ℝ => weightedCDF μ w s • g s) := by
  have hi := (integrable_test_kernel μ w hw hfirst g hg B hB hbound).integral_prod_right
  simpa only [integral_smul_const, weightedCDF] using hi

/-- Bounded Borel tests, including complex tests, are transported with
no separation into real and imaginary estimates. -/
theorem transport_identity (μ : ProbabilityMeasure ℝ) (w : ℝ → ℝ) (hw : Measurable w)
    (hfirst : Integrable (fun x : ℝ => |w x| * |x|) (μ : Measure ℝ))
    (g : ℝ → E) (hg : StronglyMeasurable g) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ s, ‖g s‖ ≤ B) :
    (∫ s : ℝ, weightedCDF μ w s • g s) =
      ∫ x : ℝ, w x • (∫ s in (0 : ℝ)..x, g s) ∂(μ : Measure ℝ) := by
  calc
    _ = ∫ s : ℝ, ∫ x : ℝ, (w x * segment x s) • g s ∂(μ : Measure ℝ) := by
      simp only [integral_smul_const, weightedCDF]
    _ = ∫ x : ℝ, (∫ s : ℝ, (w x * segment x s) • g s) ∂(μ : Measure ℝ) :=
      (integral_integral_swap (integrable_test_kernel μ w hw hfirst g hg B hB hbound)).symm
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        simp_rw [mul_smul]
        rw [integral_smul, integral_segment_smul]

theorem integrable_square_cdfDifference (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    Integrable (SquareBias.cdfDifference μ h) := by
  rw [square_cdfDifference_eq_weightedCDF]
  exact integrable_weightedCDF μ SquareBias.weight SquareBias.measurable_weight
    (SquareBias.integrable_abs_weight_mul_abs μ h)

/-- The actual square-biased and original closed CDFs satisfy bounded-test
transport under the original finite-third-moment hypotheses alone. -/
theorem square_transport_of_bounded (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (g : ℝ → E) (hg : StronglyMeasurable g) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ s, ‖g s‖ ≤ B) :
    (∀ x : ℝ, IntervalIntegrable g volume 0 x) ∧
      Integrable (fun x : ℝ => SquareBias.weight x • (∫ s in (0 : ℝ)..x, g s)) (μ : Measure ℝ) ∧
      Integrable (fun s : ℝ => SquareBias.cdfDifference μ h s • g s) ∧
      (∫ s : ℝ, SquareBias.cdfDifference μ h s • g s) =
        ∫ x : ℝ, SquareBias.weight x • (∫ s in (0 : ℝ)..x, g s) ∂(μ : Measure ℝ) := by
  have hf := SquareBias.integrable_abs_weight_mul_abs μ h
  refine ⟨fun x => intervalIntegrable_of_bounded g hg B hbound 0 x,
    integrable_weighted_primitive μ SquareBias.weight SquareBias.measurable_weight hf g hg B hB hbound, ?_, ?_⟩
  · rw [square_cdfDifference_eq_weightedCDF]
    exact integrable_weightedCDF_smul μ SquareBias.weight SquareBias.measurable_weight hf g hg B hB hbound
  · rw [square_cdfDifference_eq_weightedCDF]
    exact transport_identity μ SquareBias.weight SquareBias.measurable_weight hf g hg B hB hbound

end BerryEsseen.WeightedCDFTransport

#print axioms BerryEsseen.WeightedCDFTransport.integrable_kernel_prod
#print axioms BerryEsseen.WeightedCDFTransport.square_cdfDifference_eq_weightedCDF
#print axioms BerryEsseen.WeightedCDFTransport.integrable_weighted_primitive
#print axioms BerryEsseen.WeightedCDFTransport.integrable_weightedCDF_smul
#print axioms BerryEsseen.WeightedCDFTransport.transport_identity
#print axioms BerryEsseen.WeightedCDFTransport.integrable_square_cdfDifference
#print axioms BerryEsseen.WeightedCDFTransport.square_transport_of_bounded
