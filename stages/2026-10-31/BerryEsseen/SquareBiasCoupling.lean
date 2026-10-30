module

public import BerryEsseen.SquareBiasDistance
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-! 2026-10-29: an explicit coupling of the original and square-biased laws.
The square-bias transport estimate ≤ρ is an existing result of Shevtsova,
arXiv:1212.6775, §3, Theorem 1. Here the common part and an independent
product of the remainders provide a direct construction; no novelty is claimed. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open BerryEsseen.SquareBias BerryEsseen.SquareBiasDistance

namespace BerryEsseen.SquareBiasCoupling

def commonWeight (x : ℝ) : ℝ := min 1 (x ^ 2)
def middleWeight (x : ℝ) : ℝ := 1 - commonWeight x
def outerWeight (x : ℝ) : ℝ := x ^ 2 - commonWeight x

def commonPart (μ : ProbabilityMeasure ℝ) : Measure ℝ :=
  (μ : Measure ℝ).withDensity (fun x => ENNReal.ofReal (commonWeight x))
def middlePart (μ : ProbabilityMeasure ℝ) : Measure ℝ :=
  (μ : Measure ℝ).withDensity (fun x => ENNReal.ofReal (middleWeight x))
def outerPart (μ : ProbabilityMeasure ℝ) : Measure ℝ :=
  (μ : Measure ℝ).withDensity (fun x => ENNReal.ofReal (outerWeight x))

lemma commonWeight_nonneg (x : ℝ) : 0 ≤ commonWeight x := le_min zero_le_one (sq_nonneg x)
lemma commonWeight_le_one (x : ℝ) : commonWeight x ≤ 1 := min_le_left _ _
lemma middleWeight_nonneg (x : ℝ) : 0 ≤ middleWeight x := sub_nonneg.mpr (commonWeight_le_one x)
lemma outerWeight_nonneg (x : ℝ) : 0 ≤ outerWeight x := sub_nonneg.mpr (min_le_right _ _)
lemma middleWeight_le_one (x : ℝ) : middleWeight x ≤ 1 := by unfold middleWeight; linarith [commonWeight_nonneg x]
lemma outerWeight_le_sq (x : ℝ) : outerWeight x ≤ x ^ 2 := by unfold outerWeight; linarith [commonWeight_nonneg x]

lemma common_add_middle (μ : ProbabilityMeasure ℝ) : commonPart μ + middlePart μ = (μ : Measure ℝ) := by
  have heq : (fun x : ℝ => ENNReal.ofReal (commonWeight x)) +
      (fun x => ENNReal.ofReal (middleWeight x)) = (1 : ℝ → ENNReal) := by
    funext x
    change ENNReal.ofReal (commonWeight x) + ENNReal.ofReal (middleWeight x) = 1
    rw [← ENNReal.ofReal_add (commonWeight_nonneg x) (middleWeight_nonneg x)]
    rw [show commonWeight x + middleWeight x = 1 by unfold middleWeight; ring, ENNReal.ofReal_one]
  unfold commonPart middlePart
  rw [← withDensity_add_left (by unfold commonWeight; fun_prop), heq, withDensity_one]

lemma common_add_outer (μ : ProbabilityMeasure ℝ) : commonPart μ + outerPart μ = squareMeasure μ := by
  have heq : (fun x : ℝ => ENNReal.ofReal (commonWeight x)) +
      (fun x => ENNReal.ofReal (outerWeight x)) = (fun x => ENNReal.ofReal (x ^ 2)) := by
    funext x
    change ENNReal.ofReal (commonWeight x) + ENNReal.ofReal (outerWeight x) = ENNReal.ofReal (x ^ 2)
    rw [← ENNReal.ofReal_add (commonWeight_nonneg x) (outerWeight_nonneg x)]
    rw [show commonWeight x + outerWeight x = x ^ 2 by unfold outerWeight; ring]
  unfold commonPart outerPart squareMeasure
  rw [← withDensity_add_left (by unfold commonWeight; fun_prop), heq]

lemma common_le (μ : ProbabilityMeasure ℝ) : commonPart μ ≤ (μ : Measure ℝ) := by
  unfold commonPart
  calc
    _ ≤ (μ : Measure ℝ).withDensity 1 := withDensity_mono (Eventually.of_forall fun x => by
      simpa only [ENNReal.ofReal_one, Pi.one_apply] using ENNReal.ofReal_le_ofReal (commonWeight_le_one x))
    _ = _ := withDensity_one

lemma middle_le (μ : ProbabilityMeasure ℝ) : middlePart μ ≤ (μ : Measure ℝ) := by
  unfold middlePart
  calc
    _ ≤ (μ : Measure ℝ).withDensity 1 := withDensity_mono (Eventually.of_forall fun x => by
      simpa only [ENNReal.ofReal_one, Pi.one_apply] using ENNReal.ofReal_le_ofReal (middleWeight_le_one x))
    _ = _ := withDensity_one

lemma outer_le_square (μ : ProbabilityMeasure ℝ) : outerPart μ ≤ squareMeasure μ := by
  unfold outerPart squareMeasure
  exact withDensity_mono (Eventually.of_forall fun x => ENNReal.ofReal_le_ofReal (outerWeight_le_sq x))

instance common_finite (μ : ProbabilityMeasure ℝ) : IsFiniteMeasure (commonPart μ) := by
  constructor
  exact lt_of_le_of_lt ((common_le μ) univ) (measure_lt_top (μ : Measure ℝ) univ)

instance middle_finite (μ : ProbabilityMeasure ℝ) : IsFiniteMeasure (middlePart μ) := by
  constructor
  exact lt_of_le_of_lt ((middle_le μ) univ) (measure_lt_top (μ : Measure ℝ) univ)

lemma outer_finite (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) : IsFiniteMeasure (outerPart μ) := by
  letI : IsProbabilityMeasure (squareMeasure μ) := squareMeasure_isProbability μ h
  constructor
  exact lt_of_le_of_lt ((outer_le_square μ) univ) (measure_lt_top (squareMeasure μ) univ)

def leftoverMass (μ : ProbabilityMeasure ℝ) : ℝ := (middlePart μ).real univ
def normalizer (μ : ProbabilityMeasure ℝ) : ENNReal := ENNReal.ofReal (1 / leftoverMass μ)

def coupling (μ : ProbabilityMeasure ℝ) : Measure (ℝ × ℝ) :=
  Measure.map (fun x : ℝ => (x, x)) (commonPart μ) + normalizer μ • (middlePart μ).prod (outerPart μ)

lemma leftoverMass_nonneg (μ : ProbabilityMeasure ℝ) : 0 ≤ leftoverMass μ := ENNReal.toReal_nonneg

lemma real_add_univ (ν η : Measure ℝ) [IsFiniteMeasure ν] [IsFiniteMeasure η] :
    (ν + η).real univ = ν.real univ + η.real univ := by
  unfold Measure.real
  rw [Measure.add_apply, ENNReal.toReal_add (measure_ne_top ν univ) (measure_ne_top η univ)]

lemma outer_real_mass (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    (outerPart μ).real univ = leftoverMass μ := by
  letI := outer_finite μ h
  have hcm : (commonPart μ).real univ + (middlePart μ).real univ = 1 := by
    rw [← real_add_univ, common_add_middle]
    simp
  have hco : (commonPart μ).real univ + (outerPart μ).real univ = 1 := by
    rw [← real_add_univ, common_add_outer]
    change (squareLaw μ h : Measure ℝ).real univ = 1
    simp
  unfold leftoverMass
  linarith

lemma middle_mass (μ : ProbabilityMeasure ℝ) : (middlePart μ) univ = ENNReal.ofReal (leftoverMass μ) := by
  exact (ENNReal.ofReal_toReal (measure_ne_top (middlePart μ) univ)).symm

lemma outer_mass (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    (outerPart μ) univ = ENNReal.ofReal (leftoverMass μ) := by
  letI := outer_finite μ h
  calc
    _ = ENNReal.ofReal ((outerPart μ).real univ) := (ENNReal.ofReal_toReal (measure_ne_top (outerPart μ) univ)).symm
    _ = _ := by rw [outer_real_mass μ h]

lemma normalizer_mul_middle (μ : ProbabilityMeasure ℝ) (hM : 0 < leftoverMass μ) :
    normalizer μ * (middlePart μ) univ = 1 := by
  rw [normalizer, middle_mass, ← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / leftoverMass μ),
    div_mul_cancel₀ 1 (ne_of_gt hM), ENNReal.ofReal_one]

lemma normalizer_mul_outer (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (hM : 0 < leftoverMass μ) :
    normalizer μ * (outerPart μ) univ = 1 := by
  rw [normalizer, outer_mass μ h, ← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / leftoverMass μ),
    div_mul_cancel₀ 1 (ne_of_gt hM), ENNReal.ofReal_one]

lemma middle_zero (μ : ProbabilityMeasure ℝ) (hM : leftoverMass μ = 0) : middlePart μ = 0 := by
  apply Measure.measure_univ_eq_zero.mp
  rw [middle_mass, hM, ENNReal.ofReal_zero]

lemma outer_zero (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (hM : leftoverMass μ = 0) : outerPart μ = 0 := by
  apply Measure.measure_univ_eq_zero.mp
  rw [outer_mass μ h, hM, ENNReal.ofReal_zero]

lemma common_eq_original_zero (μ : ProbabilityMeasure ℝ) (hM : leftoverMass μ = 0) : commonPart μ = (μ : Measure ℝ) := by
  simpa only [middle_zero μ hM, add_zero] using common_add_middle μ

lemma square_eq_original_zero (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (hM : leftoverMass μ = 0) :
    (squareLaw μ h : Measure ℝ) = (μ : Measure ℝ) := by
  have hc := common_add_outer μ
  rw [outer_zero μ h hM, add_zero, common_eq_original_zero μ hM] at hc
  exact hc.symm

lemma coupling_zero (μ : ProbabilityMeasure ℝ) (hM : leftoverMass μ = 0) :
    coupling μ = Measure.map (fun x : ℝ => (x, x)) (μ : Measure ℝ) := by
  unfold coupling normalizer
  rw [hM, common_eq_original_zero μ hM]
  simp

lemma map_fst_diag (ν : Measure ℝ) :
    Measure.map Prod.fst (Measure.map (fun x : ℝ => (x, x)) ν) = ν := by
  rw [Measure.map_map measurable_fst (by fun_prop)]
  exact Measure.map_id

lemma map_snd_diag (ν : Measure ℝ) :
    Measure.map Prod.snd (Measure.map (fun x : ℝ => (x, x)) ν) = ν := by
  rw [Measure.map_map measurable_snd (by fun_prop)]
  exact Measure.map_id

/-- The first marginal is the actual original law, including the zero-mass case. -/
theorem coupling_fst (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    Measure.map Prod.fst (coupling μ) = (μ : Measure ℝ) := by
  letI := outer_finite μ h
  by_cases hM : leftoverMass μ = 0
  · rw [coupling_zero μ hM, map_fst_diag]
  · have hp : 0 < leftoverMass μ := lt_of_le_of_ne (leftoverMass_nonneg μ) (Ne.symm hM)
    rw [coupling, Measure.map_add _ _ measurable_fst, map_fst_diag,
      Measure.map_smul _ measurable_fst.aemeasurable, Measure.map_fst_prod, smul_smul,
      normalizer_mul_outer μ h hp, one_smul, common_add_middle]

/-- The second marginal is the actual square-biased law. -/
theorem coupling_snd (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    Measure.map Prod.snd (coupling μ) = (squareLaw μ h : Measure ℝ) := by
  letI := outer_finite μ h
  by_cases hM : leftoverMass μ = 0
  · rw [coupling_zero μ hM, map_snd_diag, square_eq_original_zero μ h hM]
  · have hp : 0 < leftoverMass μ := lt_of_le_of_ne (leftoverMass_nonneg μ) (Ne.symm hM)
    change Measure.map Prod.snd (coupling μ) = squareMeasure μ
    rw [coupling, Measure.map_add _ _ measurable_snd, map_snd_diag,
      Measure.map_smul _ measurable_snd.aemeasurable, Measure.map_snd_prod, smul_smul,
      normalizer_mul_middle μ hp, one_smul, common_add_outer]

theorem coupling_isProbability (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) : IsProbabilityMeasure (coupling μ) := by
  constructor
  have hm := congrArg (fun ν : Measure ℝ => ν univ) (coupling_fst μ h)
  simpa only [Measure.map_apply measurable_fst MeasurableSet.univ, preimage_univ, measure_univ] using hm

def couplingLaw (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) : ProbabilityMeasure (ℝ × ℝ) :=
  ⟨coupling μ, coupling_isProbability μ h⟩

end BerryEsseen.SquareBiasCoupling
#print axioms BerryEsseen.SquareBiasCoupling.coupling_fst
#print axioms BerryEsseen.SquareBiasCoupling.coupling_snd
#print axioms BerryEsseen.SquareBiasCoupling.coupling_isProbability

namespace BerryEsseen.SquareBiasCoupling

lemma middle_support (μ : ProbabilityMeasure ℝ) : ∀ᵐ x ∂middlePart μ, |x| ≤ 1 := by
  unfold middlePart
  apply (ae_withDensity_iff (by unfold middleWeight commonWeight; fun_prop)).mpr
  exact Eventually.of_forall fun x hx => by
    by_cases hs : x ^ 2 ≤ 1
    · apply (sq_le_sq₀ (abs_nonneg x) (by norm_num : (0 : ℝ) ≤ 1)).mp
      simpa only [sq_abs, one_pow] using hs
    · have hw : middleWeight x = 0 := by
        unfold middleWeight commonWeight
        rw [min_eq_left (lt_of_not_ge hs).le]
        ring
      exact False.elim (hx (by rw [hw, ENNReal.ofReal_zero]))

lemma outer_support (μ : ProbabilityMeasure ℝ) : ∀ᵐ x ∂outerPart μ, 1 ≤ |x| := by
  unfold outerPart
  apply (ae_withDensity_iff (by unfold outerWeight commonWeight; fun_prop)).mpr
  exact Eventually.of_forall fun x hx => by
    by_cases hs : 1 ≤ x ^ 2
    · apply (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1) (abs_nonneg x)).mp
      simpa only [sq_abs, one_pow] using hs
    · have hw : outerWeight x = 0 := by
        unfold outerWeight commonWeight
        rw [min_eq_right (lt_of_not_ge hs).le]
        ring
      exact False.elim (hx (by rw [hw, ENNReal.ofReal_zero]))

/-- Its value at zero is immaterial: the outer measure gives zero mass there. -/
def direction (y : ℝ) : ℝ := if 0 ≤ y then 1 else -1

lemma measurable_direction : Measurable direction := by
  unfold direction
  exact measurable_const.piecewise (measurableSet_le measurable_const measurable_id) measurable_const

lemma abs_direction (y : ℝ) : |direction y| = 1 := by unfold direction; split_ifs <;> norm_num

def cost (p : ℝ × ℝ) : ℝ := |p.1 - p.2|

lemma cost_identity (x y : ℝ) (hx : |x| ≤ 1) (hy : 1 ≤ |y|) :
    |x - y| = |y| - x * direction y := by
  by_cases hy0 : 0 ≤ y
  · have hy1 : 1 ≤ y := by simpa only [abs_of_nonneg hy0] using hy
    have hx1 : x ≤ 1 := (abs_le.mp hx).2
    simp only [direction, ite_eq_left hy0, abs_of_nonpos (sub_nonpos.mpr (hx1.trans hy1)), abs_of_nonneg hy0]
    ring
  · have hyneg : y ≤ 0 := le_of_not_ge hy0
    have hy1 : y ≤ -1 := by rw [abs_of_nonpos hyneg] at hy; linarith
    have hx1 : -1 ≤ x := (abs_le.mp hx).1
    simp only [direction, ite_eq_right hy0, abs_of_nonneg (sub_nonneg.mpr (hy1.trans hx1)), abs_of_nonpos hyneg]
    ring

lemma integrable_id_common (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    Integrable (fun x : ℝ => x) (commonPart μ) := h.integrable_mean.mono_measure (common_le μ)
lemma integrable_id_middle (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    Integrable (fun x : ℝ => x) (middlePart μ) := h.integrable_mean.mono_measure (middle_le μ)
lemma integrable_id_outer (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    Integrable (fun x : ℝ => x) (outerPart μ) :=
  (integrable_id_squareLaw μ h).mono_measure (outer_le_square μ)

lemma integrable_abs_common (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    Integrable (fun x : ℝ => |x|) (commonPart μ) := by simpa only [Real.norm_eq_abs] using (integrable_id_common μ h).norm
lemma integrable_abs_middle (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    Integrable (fun x : ℝ => |x|) (middlePart μ) := by simpa only [Real.norm_eq_abs] using (integrable_id_middle μ h).norm
lemma integrable_abs_outer (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    Integrable (fun x : ℝ => |x|) (outerPart μ) := by simpa only [Real.norm_eq_abs] using (integrable_id_outer μ h).norm

lemma integrable_direction_outer (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    Integrable direction (outerPart μ) := by
  letI := outer_finite μ h
  apply (integrable_const (1 : ℝ)).mono' measurable_direction.aestronglyMeasurable
  exact Eventually.of_forall fun y => by simp only [Real.norm_eq_abs, abs_direction, le_refl]

lemma integrable_product_cost (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    Integrable cost ((middlePart μ).prod (outerPart μ)) := by
  letI := outer_finite μ h
  have hX : Integrable (fun p : ℝ × ℝ => |p.1|) ((middlePart μ).prod (outerPart μ)) := by
    simpa only [mul_one] using (integrable_abs_middle μ h).mul_prod
      (integrable_const (1 : ℝ) : Integrable (fun _ : ℝ => (1 : ℝ)) (outerPart μ))
  have hY : Integrable (fun p : ℝ × ℝ => |p.2|) ((middlePart μ).prod (outerPart μ)) := by
    simpa only [one_mul] using (integrable_const (1 : ℝ) : Integrable (fun _ : ℝ => (1 : ℝ)) (middlePart μ)).mul_prod
      (integrable_abs_outer μ h)
  apply (hX.add hY).mono' (by unfold cost; fun_prop)
  exact Eventually.of_forall fun p => by
    change ‖|p.1 - p.2|‖ ≤ |p.1| + |p.2|
    rw [Real.norm_eq_abs, abs_abs]
    exact abs_sub p.1 p.2

lemma integrable_diag_cost (μ : ProbabilityMeasure ℝ) :
    Integrable cost (Measure.map (fun x : ℝ => (x, x)) (commonPart μ)) := by
  apply (integrable_map_measure (by unfold cost; fun_prop) (by fun_prop)).mpr
  change Integrable (fun x : ℝ => |x - x|) (commonPart μ)
  simpa only [sub_self, abs_zero] using
    (integrable_const (0 : ℝ) : Integrable (fun _ : ℝ => (0 : ℝ)) (commonPart μ))

theorem integrable_cost (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    Integrable (fun p : ℝ × ℝ => |p.1 - p.2|) (coupling μ) := by
  change Integrable cost (coupling μ)
  unfold coupling
  exact (integrable_diag_cost μ).add_measure ((integrable_product_cost μ h).smul_measure (by
    unfold normalizer; exact ENNReal.ofReal_ne_top))

lemma integral_product_cost (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    (∫ p, cost p ∂(middlePart μ).prod (outerPart μ)) =
      leftoverMass μ * (∫ y : ℝ, |y| ∂outerPart μ) -
      (∫ x : ℝ, x ∂middlePart μ) * (∫ y : ℝ, direction y ∂outerPart μ) := by
  letI := outer_finite μ h
  have heq : cost =ᵐ[(middlePart μ).prod (outerPart μ)]
      (fun p : ℝ × ℝ => |p.2| - p.1 * direction p.2) := by
    apply (Measure.ae_prod_iff_ae_ae (show MeasurableSet {p : ℝ × ℝ | cost p = |p.2| - p.1 * direction p.2} from
      measurableSet_eq_fun (by unfold cost; fun_prop)
        (by have hd := measurable_direction; fun_prop))).mpr
    filter_upwards [middle_support μ] with x hx
    filter_upwards [outer_support μ] with y hy
    exact cost_identity x y hx hy
  have hY : Integrable (fun p : ℝ × ℝ => |p.2|) ((middlePart μ).prod (outerPart μ)) := by
    simpa only [one_mul] using (integrable_const (1 : ℝ) : Integrable (fun _ : ℝ => (1 : ℝ)) (middlePart μ)).mul_prod
      (integrable_abs_outer μ h)
  have hXY : Integrable (fun p : ℝ × ℝ => p.1 * direction p.2) ((middlePart μ).prod (outerPart μ)) :=
    (integrable_id_middle μ h).mul_prod (integrable_direction_outer μ h)
  rw [integral_congr_ae heq, integral_sub hY hXY, integral_fun_snd,
    integral_prod_mul (fun x : ℝ => x) direction, smul_eq_mul]
  rfl

lemma integral_diag_cost (μ : ProbabilityMeasure ℝ) :
    (∫ p, cost p ∂Measure.map (fun x : ℝ => (x, x)) (commonPart μ)) = 0 := by
  rw [integral_map (by fun_prop) (by unfold cost; fun_prop)]
  simp [cost]

lemma integral_cost_formula (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    (∫ p, cost p ∂coupling μ) = (1 / leftoverMass μ) *
      (leftoverMass μ * (∫ y : ℝ, |y| ∂outerPart μ) -
        (∫ x : ℝ, x ∂middlePart μ) * (∫ y : ℝ, direction y ∂outerPart μ)) := by
  have hd := integrable_diag_cost μ
  have hp := (integrable_product_cost μ h).smul_measure (show normalizer μ ≠ ⊤ from ENNReal.ofReal_ne_top)
  rw [coupling, integral_add_measure hd hp, integral_diag_cost, zero_add, integral_smul_measure,
    normalizer, ENNReal.toReal_ofReal (one_div_nonneg.mpr (leftoverMass_nonneg μ)), smul_eq_mul,
    integral_product_cost μ h]

lemma direction_mass_bound (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    |∫ y : ℝ, direction y ∂outerPart μ| ≤ leftoverMass μ := by
  have hn := norm_integral_le_integral_norm (μ := outerPart μ) direction
  have heq : (fun y : ℝ => ‖direction y‖) = (fun _ => (1 : ℝ)) := by
    funext y; rw [Real.norm_eq_abs, abs_direction]
  rw [Real.norm_eq_abs, heq, integral_const] at hn
  simpa only [smul_eq_mul, mul_one, outer_real_mass μ h] using hn

lemma middle_mean_bound (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    |∫ x : ℝ, x ∂middlePart μ| ≤ ∫ x : ℝ, |x| ∂commonPart μ := by
  have hm : (∫ x : ℝ, x ∂commonPart μ) + (∫ x : ℝ, x ∂middlePart μ) = 0 := by
    rw [← integral_add_measure (integrable_id_common μ h) (integrable_id_middle μ h), common_add_middle, h.mean_zero]
  have hb : (∫ x : ℝ, x ∂middlePart μ) = -(∫ x : ℝ, x ∂commonPart μ) := by linarith
  rw [hb, abs_neg]
  simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := commonPart μ) (fun x : ℝ => x)

lemma absolute_parts_sum (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    (∫ x : ℝ, |x| ∂commonPart μ) + (∫ x : ℝ, |x| ∂outerPart μ) = thirdAbsoluteMoment μ := by
  rw [← integral_add_measure (integrable_abs_common μ h) (integrable_abs_outer μ h), common_add_outer]
  exact integral_abs_squareLaw μ h

/-- The cost bound of the explicit independent-remainder coupling is the
classical square-bias ≤ρ bound, with all moments and marginals actual. -/
theorem cost_le_third (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    (∫ p : ℝ × ℝ, |p.1 - p.2| ∂coupling μ) ≤ thirdAbsoluteMoment μ := by
  change (∫ p, cost p ∂coupling μ) ≤ _
  rw [integral_cost_formula μ h]
  by_cases hM : leftoverMass μ = 0
  · rw [hM, div_zero, zero_mul]
    exact integral_nonneg fun x => pow_nonneg (abs_nonneg x) 3
  · have hp : 0 < leftoverMass μ := lt_of_le_of_ne (leftoverMass_nonneg μ) (Ne.symm hM)
    rw [one_div_mul_eq_div]
    apply (div_le_iff₀ hp).mpr
    have hS := direction_mass_bound μ h
    have hb := middle_mean_bound μ h
    have habs : |(∫ x : ℝ, x ∂middlePart μ) * (∫ y : ℝ, direction y ∂outerPart μ)| ≤
        |∫ x : ℝ, x ∂middlePart μ| * leftoverMass μ := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hS (abs_nonneg _)
    have hneg : -(∫ x : ℝ, x ∂middlePart μ) * (∫ y : ℝ, direction y ∂outerPart μ) ≤
        (∫ x : ℝ, |x| ∂commonPart μ) * leftoverMass μ := by
      have hstart := neg_le_abs ((∫ x : ℝ, x ∂middlePart μ) * (∫ y : ℝ, direction y ∂outerPart μ))
      rw [← neg_mul] at hstart
      exact (hstart.trans habs).trans (mul_le_mul_of_nonneg_right hb hp.le)
    have hsum : leftoverMass μ * (∫ y : ℝ, |y| ∂outerPart μ) +
        (∫ x : ℝ, |x| ∂commonPart μ) * leftoverMass μ = thirdAbsoluteMoment μ * leftoverMass μ := by
      calc
        _ = ((∫ x : ℝ, |x| ∂commonPart μ) + (∫ y : ℝ, |y| ∂outerPart μ)) * leftoverMass μ := by ring
        _ = _ := by rw [absolute_parts_sum μ h]
    linarith

end BerryEsseen.SquareBiasCoupling
#print axioms BerryEsseen.SquareBiasCoupling.integrable_cost
#print axioms BerryEsseen.SquareBiasCoupling.integral_cost_formula
#print axioms BerryEsseen.SquareBiasCoupling.cost_le_third
