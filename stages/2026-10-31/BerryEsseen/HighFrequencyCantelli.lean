module

public import BerryEsseen.HighFrequencyEvent
public import BerryEsseen.PearsonMoments
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import Mathlib.Probability.Moments.Variance

@[expose] public section

/-! 2026-10-28: Actual closed product-event acquisition for (ut:event-input).
The mass and conditional second-moment prices use only the original law's
finite fourth moment. Boundary atoms belong to the event. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal InnerProductSpace

namespace BerryEsseen.HighFrequencyCantelli

private lemma inner_toLp_eq_integral_mul {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} {f g : Ω → ℝ} (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x, f x * g x ∂ν := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp hf, MemLp.coeFn_toLp hg] with x hx hy
  rw [hx, hy]
  exact Real.inner_apply _ _

private lemma covariance_cauchy {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} {f g : Ω → ℝ} (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) :
    (∫ x, f x * g x ∂ν) ^ 2 ≤ (∫ x, f x ^ 2 ∂ν) * ∫ x, g x ^ 2 ∂ν := by
  have h := real_inner_mul_inner_self_le (hf.toLp f) (hg.toLp g)
  rw [inner_toLp_eq_integral_mul hf hg, inner_toLp_eq_integral_mul hf hf,
    inner_toLp_eq_integral_mul hg hg] at h
  simpa only [pow_two] using h

/-- A genuine centered indicator covariance gives both Cantelli's mass
price and its matching conditional-mean price. -/
theorem centered_event_bounds {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (Z : Ω → ℝ) (E : Set Ω) (h V : ℝ)
    (hE : MeasurableSet E) (hZ : Integrable Z ν)
    (hZ2 : Integrable (fun x => Z x ^ 2) ν) (hmean : (∫ x, Z x ∂ν) = 0)
    (hV : (∫ x, Z x ^ 2 ∂ν) ≤ V) (hh : 0 < h)
    (hcomp : ∀ x ∈ Eᶜ, Z x ≤ -h) :
    0 < h ^ 2 / (V + h ^ 2) ∧
      h ^ 2 / (V + h ^ 2) ≤ ν.real E ∧
      h * (∫ x in E, Z x ∂ν) ≤ V * ν.real E := by
  let p := ν.real E
  let q := ν.real Eᶜ
  let I := ∫ x in E, Z x ∂ν
  let W : Ω → ℝ := fun x => E.indicator (fun _ => (1 : ℝ)) x - p
  have hp0 : 0 ≤ p := measureReal_nonneg
  have hq0 : 0 ≤ q := measureReal_nonneg
  have hpq : p + q = 1 := by
    simpa only [p, q, probReal_univ] using
      (measureReal_add_measureReal_compl (μ := ν) (s := E) hE)
  have hqeq : q = 1 - p := by linarith only [hpq]
  have hV0 : 0 ≤ V := (integral_nonneg (fun x => sq_nonneg (Z x))).trans hV
  have hsplit := integral_add_compl hE hZ
  change I + (∫ x in Eᶜ, Z x ∂ν) = _ at hsplit
  rw [hmean] at hsplit
  have hcompl : (∫ x in Eᶜ, Z x ∂ν) ≤ -h * q := by
    calc
      _ ≤ ∫ _x in Eᶜ, -h ∂ν := setIntegral_mono_on hZ.integrableOn
        (integrable_const (-h)).integrableOn hE.compl hcomp
      _ = _ := by rw [setIntegral_const]; change q * (-h) = -h * q; ring
  have hIlower : h * q ≤ I := by linarith only [hsplit, hcompl]
  have hI0 : 0 ≤ I := (mul_nonneg hh.le hq0).trans hIlower
  have hInd : MemLp (E.indicator (fun _ : Ω => (1 : ℝ))) 2 ν :=
    (memLp_const 1).indicator hE.nullMeasurableSet
  have hW : MemLp W 2 ν := by
    have hm : Measurable W := (measurable_const.indicator hE).sub_const p
    apply MemLp.of_bound hm.aestronglyMeasurable (1 + |p|)
    filter_upwards [] with x
    rw [Real.norm_eq_abs]
    by_cases hx : x ∈ E
    · simpa only [W, Set.indicator_of_mem hx, abs_one] using abs_sub (1 : ℝ) p
    · simp only [W, Set.indicator_of_notMem hx, zero_sub, abs_neg]
      linarith
  have hZLp : MemLp Z 2 ν :=
    (memLp_two_iff_integrable_sq hZ.aestronglyMeasurable).mpr hZ2
  have hCovFun : (fun x => Z x * W x) =
      (fun x => E.indicator Z x - p * Z x) := by
    funext x
    by_cases hx : x ∈ E <;> simp [W, hx] <;> ring
  have hCovInt : Integrable (fun x => Z x * W x) ν := by
    rw [hCovFun]
    exact (hZ.indicator hE).sub (hZ.const_mul p)
  have hCov : (∫ x, Z x * W x ∂ν) = I := by
    rw [hCovFun, integral_sub (hZ.indicator hE) (hZ.const_mul p),
      integral_indicator hE, integral_const_mul, hmean, mul_zero, sub_zero]
  have hWFun : (fun x => W x ^ 2) =
      (fun x => (1 - 2 * p) * E.indicator (fun _ => (1 : ℝ)) x + p ^ 2) := by
    funext x
    by_cases hx : x ∈ E <;> simp [W, hx] <;> ring
  have hWsq : (∫ x, W x ^ 2 ∂ν) = p * q := by
    rw [hWFun, integral_add ((hInd.integrable (by norm_num)).const_mul (1 - 2 * p))
      (integrable_const (p ^ 2)), integral_const_mul,
      integral_indicator_const (μ := ν) (1 : ℝ) hE,
      integral_const, probReal_univ, one_smul, smul_eq_mul, mul_one]
    change (1 - 2 * p) * p + p ^ 2 = p * q
    rw [hqeq]
    ring
  have hCS := covariance_cauchy hZLp hW
  rw [hCov, hWsq] at hCS
  have hcov : I ^ 2 ≤ V * p * q := by
    calc
      _ ≤ (∫ x, Z x ^ 2 ∂ν) * (p * q) := hCS
      _ ≤ V * (p * q) := mul_le_mul_of_nonneg_right hV (mul_nonneg hp0 hq0)
      _ = _ := by ring
  have hcontrols : h ^ 2 * q ≤ V * p ∧ h * I ≤ V * p := by
    by_cases hq : q = 0
    · have hIsq : I ^ 2 = 0 := le_antisymm (by simpa only [hq, mul_zero] using hcov) (sq_nonneg I)
      have hI : I = 0 := sq_eq_zero_iff.mp hIsq
      simpa only [hq, hI, mul_zero] using
        (And.intro (mul_nonneg hV0 hp0) (mul_nonneg hV0 hp0))
    · have hqpos : 0 < q := lt_of_le_of_ne hq0 (Ne.symm hq)
      have hsq := pow_le_pow_left₀ (mul_nonneg hh.le hq0) hIlower 2
      have hprob : q * (h ^ 2 * q) ≤ q * (V * p) := by nlinarith only [hsq, hcov]
      have hmult := mul_le_mul_of_nonneg_right hIlower hI0
      have hmoment : q * (h * I) ≤ q * (V * p) := by nlinarith only [hmult, hcov]
      exact ⟨le_of_mul_le_mul_left hprob hqpos, le_of_mul_le_mul_left hmoment hqpos⟩
  have hden : 0 < V + h ^ 2 := add_pos_of_nonneg_of_pos hV0 (pow_pos hh 2)
  have hsum : h ^ 2 = h ^ 2 * p + h ^ 2 * q := by rw [hqeq]; ring
  refine ⟨div_pos (pow_pos hh 2) hden, ?_, hcontrols.2⟩
  apply (div_le_iff₀ hden).mpr
  nlinarith only [hcontrols.1, hsum]

def squaredDistance (z : ℝ × ℝ) : ℝ := HighFrequencyEvent.distance z ^ 2
def centeredSquare (z : ℝ × ℝ) : ℝ := squaredDistance z - 2
def event (d : ℝ) : Set (ℝ × ℝ) := {z | d ^ 2 ≤ squaredDistance z}
def gap (d : ℝ) : ℝ := 2 - d ^ 2
def variancePrice (M : ℝ) : ℝ := 2 * M + 2
def probabilityPrice (d M : ℝ) : ℝ := gap d ^ 2 / (variancePrice M + gap d ^ 2)
def secondMomentPrice (d M : ℝ) : ℝ := 2 + variancePrice M / gap d

lemma squaredDistance_measurable : Measurable squaredDistance := by
  unfold squaredDistance HighFrequencyEvent.distance
  fun_prop

lemma event_measurable (d : ℝ) : MeasurableSet (event d) :=
  measurableSet_le measurable_const squaredDistance_measurable

theorem squaredDistance_moments (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (h4 : Integrable (fun x : ℝ => x ^ 4) (μ : Measure ℝ)) :
    Integrable squaredDistance (HighFrequencyEvent.productLaw μ) ∧
    Integrable (fun z => squaredDistance z ^ 2) (HighFrequencyEvent.productLaw μ) ∧
    (∫ z, squaredDistance z ∂HighFrequencyEvent.productLaw μ) = 2 ∧
    (∫ z, squaredDistance z ^ 2 ∂HighFrequencyEvent.productLaw μ) =
      2 * CharacteristicExpansion.moment μ 4 + 6 := by
  have h2 := CharacteristicExpansion.product_difference_second μ hμ h4
  have hf := CharacteristicExpansion.product_difference_fourth μ hμ h4
  have hY : squaredDistance = (fun z : ℝ × ℝ => (z.1 - z.2) ^ 2) := by
    funext z
    simp only [squaredDistance, HighFrequencyEvent.distance, sq_abs]
  have hY2 : (fun z => squaredDistance z ^ 2) = (fun z : ℝ × ℝ => (z.1 - z.2) ^ 4) := by
    rw [hY]
    funext z
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hY, HighFrequencyEvent.productLaw]
    exact h2.1
  · rw [hY2, HighFrequencyEvent.productLaw]
    exact hf.1
  · rw [hY, HighFrequencyEvent.productLaw]
    exact h2.2
  · rw [hY2, HighFrequencyEvent.productLaw]
    exact hf.2

theorem centeredSquare_moments (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (h4 : Integrable (fun x : ℝ => x ^ 4) (μ : Measure ℝ)) :
    Integrable centeredSquare (HighFrequencyEvent.productLaw μ) ∧
    Integrable (fun z => centeredSquare z ^ 2) (HighFrequencyEvent.productLaw μ) ∧
    (∫ z, centeredSquare z ∂HighFrequencyEvent.productLaw μ) = 0 ∧
    (∫ z, centeredSquare z ^ 2 ∂HighFrequencyEvent.productLaw μ) =
      2 * CharacteristicExpansion.moment μ 4 + 2 := by
  obtain ⟨hY, hY2, hEY, hEY2⟩ := squaredDistance_moments μ hμ h4
  have hZ : Integrable centeredSquare (HighFrequencyEvent.productLaw μ) := hY.sub' (integrable_const 2)
  have hfun : (fun z => centeredSquare z ^ 2) =
      (fun z => squaredDistance z ^ 2 - 4 * squaredDistance z + 4) := by
    funext z
    unfold centeredSquare
    ring
  have hYY : Integrable (fun z => squaredDistance z ^ 2 - 4 * squaredDistance z)
      (HighFrequencyEvent.productLaw μ) := hY2.sub' (hY.const_mul 4)
  have hZ2 : Integrable (fun z => centeredSquare z ^ 2) (HighFrequencyEvent.productLaw μ) := by
    rw [hfun]
    exact hYY.fun_add (integrable_const 4)
  refine ⟨hZ, hZ2, ?_, ?_⟩
  · change (∫ z, squaredDistance z - 2 ∂HighFrequencyEvent.productLaw μ) = 0
    rw [integral_sub hY (integrable_const 2), hEY]
    simp only [integral_const, probReal_univ, one_smul, sub_self]
  · rw [hfun, integral_add hYY (integrable_const 4),
      integral_sub hY2 (hY.const_mul 4), integral_const_mul, hEY2, hEY]
    simp only [integral_const, probReal_univ, one_smul]
    ring

theorem one_le_moment_ceiling (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (h4 : Integrable (fun x : ℝ => x ^ 4) (μ : Measure ℝ)) (M : ℝ)
    (hM : CharacteristicExpansion.moment μ 4 ≤ M) : 1 ≤ M := by
  have h4abs : Integrable (fun x : ℝ => |x| ^ 4) (μ : Measure ℝ) := by
    convert h4 using 1
    funext x
    exact (by decide : Even (4 : ℕ)).pow_abs x
  have hP := PearsonMoments.pearson_bound μ hμ h4abs
  nlinarith only [hP, hM, sq_nonneg (CharacteristicExpansion.gamma μ)]

theorem variance_squaredDistance_le (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (h4 : Integrable (fun x : ℝ => x ^ 4) (μ : Measure ℝ)) (M : ℝ)
    (hM : CharacteristicExpansion.moment μ 4 ≤ M) :
    Var[squaredDistance; HighFrequencyEvent.productLaw μ] ≤ variancePrice M := by
  have hEY := (squaredDistance_moments μ hμ h4).2.2.1
  have hEZ2 := (centeredSquare_moments μ hμ h4).2.2.2
  rw [variance_eq_integral squaredDistance_measurable.aemeasurable, hEY]
  change (∫ z, centeredSquare z ^ 2 ∂HighFrequencyEvent.productLaw μ) ≤ variancePrice M
  rw [hEZ2]
  unfold variancePrice
  linarith only [hM]

structure EventInput (μ : ProbabilityMeasure ℝ) (d M : ℝ) : Prop where
  price_pos : 0 < probabilityPrice d M
  mass_lower : probabilityPrice d M ≤ HighFrequencyEvent.eventProbability μ (event d)
  conditional_probability : IsProbabilityMeasure (HighFrequencyEvent.eventLaw μ (event d))
  square_integrable : Integrable (fun z => HighFrequencyEvent.distance z ^ 2)
    (HighFrequencyEvent.eventLaw μ (event d))
  distance_lower : ∀ᵐ z ∂HighFrequencyEvent.eventLaw μ (event d), d ≤ HighFrequencyEvent.distance z
  second_moment_upper : HighFrequencyEvent.conditionalSecondMoment μ (event d) ≤ secondMomentPrice d M

/-- Actual acquisition: no free event mass, conditional moment, or substitute law. -/
theorem acquire (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (h4 : Integrable (fun x : ℝ => x ^ 4) (μ : Measure ℝ)) (M : ℝ)
    (hM : CharacteristicExpansion.moment μ 4 ≤ M) (d : ℝ) (hd : 0 < d) (hd2 : d ^ 2 < 2) :
    EventInput μ d M := by
  have hE := event_measurable d
  obtain ⟨hY, hY2, hEY, hEY2⟩ := squaredDistance_moments μ hμ h4
  obtain ⟨hZ, hZ2, hEZ, hEZ2⟩ := centeredSquare_moments μ hμ h4
  have hh : 0 < gap d := by unfold gap; linarith only [hd2]
  have hvar : (∫ z, centeredSquare z ^ 2 ∂HighFrequencyEvent.productLaw μ) ≤ variancePrice M := by
    rw [hEZ2]
    unfold variancePrice
    linarith only [hM]
  have hcomp : ∀ z ∈ (event d)ᶜ, centeredSquare z ≤ -gap d := by
    intro z hz
    change ¬d ^ 2 ≤ squaredDistance z at hz
    have hzlt := lt_of_not_ge hz
    unfold centeredSquare gap
    linarith only [hzlt]
  obtain ⟨ha, hpa, hI⟩ := centered_event_bounds (HighFrequencyEvent.productLaw μ)
    centeredSquare (event d) (gap d) (variancePrice M) hE hZ hZ2 hEZ hvar hh hcomp
  change 0 < probabilityPrice d M at ha
  change probabilityPrice d M ≤ HighFrequencyEvent.eventProbability μ (event d) at hpa
  have hp : 0 < HighFrequencyEvent.eventProbability μ (event d) := ha.trans_le hpa
  have hLaw := HighFrequencyEvent.eventLaw_isProbability μ (event d) hp
  have hYcond := HighFrequencyEvent.integrable_distance_square_event μ (event d) hp hY
  refine ⟨ha, hpa, hLaw, hYcond, ?_, ?_⟩
  · apply ProbabilityTheory.ae_cond_of_forall_mem hE
    intro z hz
    apply (sq_le_sq₀ hd.le (abs_nonneg (z.1 - z.2))).mp
    exact hz
  · have hsum : (∫ z in event d, squaredDistance z ∂HighFrequencyEvent.productLaw μ) =
        (∫ z in event d, centeredSquare z ∂HighFrequencyEvent.productLaw μ) +
          2 * HighFrequencyEvent.eventProbability μ (event d) := by
      have hfun : squaredDistance = (fun z => centeredSquare z + 2) := by
        funext z
        unfold centeredSquare
        ring
      rw [hfun, integral_add hZ.integrableOn (integrable_const 2), setIntegral_const]
      simp only [HighFrequencyEvent.eventProbability, smul_eq_mul]
      ring
    have hIupper : (∫ z in event d, centeredSquare z ∂HighFrequencyEvent.productLaw μ) ≤
        variancePrice M * HighFrequencyEvent.eventProbability μ (event d) / gap d := by
      apply (le_div_iff₀ hh).mpr
      simpa only [HighFrequencyEvent.eventProbability, mul_comm] using hI
    have hnormal := HighFrequencyEvent.eventProbability_mul_integral μ (event d) hp squaredDistance
    change HighFrequencyEvent.eventProbability μ (event d) *
      HighFrequencyEvent.conditionalSecondMoment μ (event d) = _ at hnormal
    apply le_of_mul_le_mul_left (a := HighFrequencyEvent.eventProbability μ (event d))
    · calc
        _ = _ := hnormal
        _ = _ := hsum
        _ ≤ variancePrice M * HighFrequencyEvent.eventProbability μ (event d) / gap d +
            2 * HighFrequencyEvent.eventProbability μ (event d) := by linarith only [hIupper]
        _ = HighFrequencyEvent.eventProbability μ (event d) * secondMomentPrice d M := by
          unfold secondMomentPrice
          ring
    · exact hp

end BerryEsseen.HighFrequencyCantelli

#print axioms BerryEsseen.HighFrequencyCantelli.centered_event_bounds
#print axioms BerryEsseen.HighFrequencyCantelli.squaredDistance_moments
#print axioms BerryEsseen.HighFrequencyCantelli.centeredSquare_moments
#print axioms BerryEsseen.HighFrequencyCantelli.one_le_moment_ceiling
#print axioms BerryEsseen.HighFrequencyCantelli.variance_squaredDistance_le
#print axioms BerryEsseen.HighFrequencyCantelli.acquire
