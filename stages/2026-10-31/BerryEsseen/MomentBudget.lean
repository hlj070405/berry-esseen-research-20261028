module

public import BerryEsseen.Target
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

@[expose] public section

/-! 2026-10-28: actual third-moment identities and the common allocation budget,
for arbitrary real probability laws. The cubic endpoint argument uses a
pointwise polynomial majorant and Bochner integration, including zero caps. -/

noncomputable section

open MeasureTheory

namespace BerryEsseen.MomentBudget

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The cubic endpoint polynomial majorant; no lower support bound is needed. -/
theorem cubic_endpoint_majorant (u a b : ℝ) (hu : u ≤ a) :
    u ^ 3 ≤ (a - 2 * b) * u ^ 2 + (2 * a * b - b ^ 2) * u + a * b ^ 2 := by
  have h := mul_nonneg (sub_nonneg.mpr hu) (sq_nonneg (u + b))
  nlinarith

/-- A centered integrable variable with upper endpoint zero is zero almost surely. -/
theorem centered_nonpos_ae_zero (μ : Measure Ω) (U : Ω → ℝ)
    (hU : Integrable U μ) (hmean : ∫ ω, U ω ∂μ = 0)
    (hupper : ∀ᵐ ω ∂μ, U ω ≤ 0) : U =ᵐ[μ] 0 := by
  have hn : 0 ≤ᵐ[μ] (fun ω => -U ω) := hupper.mono fun ω h => neg_nonneg.mpr h
  have hi : ∫ ω, -U ω ∂μ = 0 := by rw [integral_neg, hmean, neg_zero]
  have hz := (integral_eq_zero_iff_of_nonneg_ae hn hU.neg).mp hi
  filter_upwards [hz] with ω hω
  simpa using hω

/-- The sharp cubic endpoint bound for a positive cap, valid for any distribution. -/
theorem integral_cube_le_endpoint_pos (μ : Measure Ω) [IsProbabilityMeasure μ]
    (U : Ω → ℝ) (a z : ℝ) (ha : 0 < a)
    (hU : Integrable U μ) (hU2 : Integrable (fun ω => U ω ^ 2) μ)
    (hU3 : Integrable (fun ω => U ω ^ 3) μ)
    (hmean : ∫ ω, U ω ∂μ = 0) (hsecond : ∫ ω, U ω ^ 2 ∂μ = z)
    (hupper : ∀ᵐ ω ∂μ, U ω ≤ a) :
    (∫ ω, U ω ^ 3 ∂μ) ≤ a * z - z ^ 2 / a := by
  let b := z / a
  have hA := hU2.const_mul (a - 2 * b)
  have hB := hU.const_mul (2 * a * b - b ^ 2)
  have hC : Integrable (fun _ : Ω => a * b ^ 2) μ := integrable_const _
  have hAB : Integrable (fun ω => (a - 2 * b) * U ω ^ 2 +
      (2 * a * b - b ^ 2) * U ω) μ := hA.add hB
  have hABC : Integrable (fun ω => (a - 2 * b) * U ω ^ 2 +
      (2 * a * b - b ^ 2) * U ω + a * b ^ 2) μ := hAB.add hC
  have hle := integral_mono_ae hU3 hABC
    (hupper.mono fun ω h => cubic_endpoint_majorant (U ω) a b h)
  have heq : (∫ ω, (a - 2 * b) * U ω ^ 2 +
      (2 * a * b - b ^ 2) * U ω + a * b ^ 2 ∂μ) =
      (a - 2 * b) * z + a * b ^ 2 := by
    rw [integral_add hAB hC, integral_add hA hB,
      integral_const_mul, integral_const_mul, hmean, hsecond]
    simp
  rw [heq] at hle
  convert hle using 1
  dsimp [b]
  field_simp [ne_of_gt ha]
  ring

/-- Zero caps are included: centering forces the whole residual to vanish. -/
theorem integral_cube_le_endpoint (μ : Measure Ω) [IsProbabilityMeasure μ]
    (U : Ω → ℝ) (a z : ℝ) (ha : 0 ≤ a)
    (hU : Integrable U μ) (hU2 : Integrable (fun ω => U ω ^ 2) μ)
    (hU3 : Integrable (fun ω => U ω ^ 3) μ)
    (hmean : ∫ ω, U ω ∂μ = 0) (hsecond : ∫ ω, U ω ^ 2 ∂μ = z)
    (hupper : ∀ᵐ ω ∂μ, U ω ≤ a) :
    (∫ ω, U ω ^ 3 ∂μ) ≤ a * z - z ^ 2 / a := by
  rcases eq_or_lt_of_le ha with hzero | hpos
  · subst a
    have hz := centered_nonpos_ae_zero μ U hU hmean hupper
    have hc : (∫ ω, U ω ^ 3 ∂μ) = 0 := by
      calc
        _ = ∫ _ : Ω, (0 : ℝ) ∂μ := integral_congr_ae (hz.mono fun ω h => by simp [h])
        _ = 0 := integral_zero _ _
    simp [hc]
  · exact integral_cube_le_endpoint_pos μ U a z hpos hU hU2 hU3 hmean hsecond hupper

end BerryEsseen.MomentBudget

#print axioms BerryEsseen.MomentBudget.cubic_endpoint_majorant
#print axioms BerryEsseen.MomentBudget.centered_nonpos_ae_zero
#print axioms BerryEsseen.MomentBudget.integral_cube_le_endpoint


namespace BerryEsseen.MomentBudget

/-- Actual mixture of the two standardized residual push-forward laws. -/
def residualMixtureMeasure (μ0 μ1 : ProbabilityMeasure ℝ) (p c : ℝ) : Measure ℝ :=
  ENNReal.ofReal (1 - p) • Measure.map (fun u : ℝ => (u - p) / c) (μ0 : Measure ℝ) +
    ENNReal.ofReal p • Measure.map (fun u : ℝ => (u + (1 - p)) / c) (μ1 : Measure ℝ)

theorem residualMixtureMeasure_isProbability (μ0 μ1 : ProbabilityMeasure ℝ) (p c : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsProbabilityMeasure (residualMixtureMeasure μ0 μ1 p c) := by
  constructor
  simp only [residualMixtureMeasure, Measure.add_apply, Measure.smul_apply,
    smul_eq_mul, measure_univ, mul_one]
  rw [← ENNReal.ofReal_add (sub_nonneg.mpr hp1) hp0]
  simp

/-- The standardized mixture, as the same `ProbabilityMeasure` used by the target. -/
def residualMixtureLaw (μ0 μ1 : ProbabilityMeasure ℝ) (p c : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : ProbabilityMeasure ℝ :=
  ⟨residualMixtureMeasure μ0 μ1 p c,
    residualMixtureMeasure_isProbability μ0 μ1 p c hp0 hp1⟩

@[simp] theorem coe_residualMixtureLaw (μ0 μ1 : ProbabilityMeasure ℝ) (p c : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (residualMixtureLaw μ0 μ1 p c hp0 hp1 : Measure ℝ) =
      residualMixtureMeasure μ0 μ1 p c := rfl

variable {Ω : Type*} [MeasurableSpace Ω]

lemma integrable_cube_add_const (μ : Measure Ω) [IsFiniteMeasure μ] (U : Ω → ℝ) (t : ℝ)
    (h1 : Integrable U μ) (h2 : Integrable (fun ω => U ω ^ 2) μ)
    (h3 : Integrable (fun ω => U ω ^ 3) μ) :
    Integrable (fun ω => (U ω + t) ^ 3) μ := by
  convert ((h3.add (h2.const_mul (3 * t))).add (h1.const_mul (3 * t ^ 2))).add
    (integrable_const (t ^ 3)) using 1
  ext ω
  simp only [Pi.add_apply]
  ring

lemma integral_cube_add_const (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → ℝ) (t : ℝ)
    (h1 : Integrable U μ) (h2 : Integrable (fun ω => U ω ^ 2) μ)
    (h3 : Integrable (fun ω => U ω ^ 3) μ) :
    (∫ ω, (U ω + t) ^ 3 ∂μ) = (∫ ω, U ω ^ 3 ∂μ) +
      3 * t * (∫ ω, U ω ^ 2 ∂μ) + 3 * t ^ 2 * (∫ ω, U ω ∂μ) + t ^ 3 := by
  have heq : (fun ω => (U ω + t) ^ 3) = (fun ω => U ω ^ 3 +
      3 * t * U ω ^ 2 + 3 * t ^ 2 * U ω + t ^ 3) := by ext ω; ring
  have hA : Integrable (fun ω => U ω ^ 3 + 3 * t * U ω ^ 2) μ :=
    h3.add (h2.const_mul _)
  have hB : Integrable (fun ω => U ω ^ 3 + 3 * t * U ω ^ 2 + 3 * t ^ 2 * U ω) μ :=
    hA.add (h1.const_mul _)
  rw [heq, integral_add hB (integrable_const _), integral_add hA (h1.const_mul _),
    integral_add h3 (h2.const_mul _), integral_const_mul, integral_const_mul]
  simp

end BerryEsseen.MomentBudget

namespace BerryEsseen.MomentBudget

lemma integral_residualMixture (μ0 μ1 : ProbabilityMeasure ℝ) (p c : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (f : ℝ → ℝ) (hf : StronglyMeasurable f)
    (h0 : Integrable (fun u => f ((u - p) / c)) (μ0 : Measure ℝ))
    (h1 : Integrable (fun u => f ((u + (1 - p)) / c)) (μ1 : Measure ℝ)) :
    (∫ x, f x ∂residualMixtureMeasure μ0 μ1 p c) =
      (1 - p) * (∫ u, f ((u - p) / c) ∂(μ0 : Measure ℝ)) +
        p * (∫ u, f ((u + (1 - p)) / c) ∂(μ1 : Measure ℝ)) := by
  have hm0 : Measurable (fun u : ℝ => (u - p) / c) := by fun_prop
  have hm1 : Measurable (fun u : ℝ => (u + (1 - p)) / c) := by fun_prop
  have hi0 := (integrable_map_measure hf.aestronglyMeasurable hm0.aemeasurable).mpr h0
  have hi1 := (integrable_map_measure hf.aestronglyMeasurable hm1.aemeasurable).mpr h1
  rw [residualMixtureMeasure, integral_add_measure
      (hi0.smul_measure ENNReal.ofReal_ne_top) (hi1.smul_measure ENNReal.ofReal_ne_top),
    integral_smul_measure, integral_smul_measure,
    integral_map hm0.aemeasurable hf.aestronglyMeasurable,
    integral_map hm1.aemeasurable hf.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofReal hp0, ENNReal.toReal_ofReal (sub_nonneg.mpr hp1),
    smul_eq_mul]

variable {Ω : Type*} [MeasurableSpace Ω]

lemma abs_cube_div_of_nonpos (u c : ℝ) (hu : u ≤ 0) (hc : 0 < c) :
    |u / c| ^ 3 = -(u ^ 3) / c ^ 3 := by
  rw [abs_div, abs_of_nonpos hu, abs_of_pos hc, div_pow]
  ring

lemma abs_cube_div_of_nonneg (u c : ℝ) (hu : 0 ≤ u) (hc : 0 < c) :
    |u / c| ^ 3 = u ^ 3 / c ^ 3 := by
  rw [abs_div, abs_of_nonneg hu, abs_of_pos hc, div_pow]

/-- The manuscript's `ρ` identity for the actual standardized mixture measure.
Only the moments needed to expand and integrate the cubic are assumed finite. -/
theorem actual_thirdAbsoluteMoment_identity
    (μ0 μ1 : ProbabilityMeasure ℝ) (p c : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hc : 0 < c)
    (h01 : Integrable (fun u : ℝ => u) (μ0 : Measure ℝ))
    (h02 : Integrable (fun u : ℝ => u ^ 2) (μ0 : Measure ℝ))
    (h03 : Integrable (fun u : ℝ => u ^ 3) (μ0 : Measure ℝ))
    (h11 : Integrable (fun u : ℝ => u) (μ1 : Measure ℝ))
    (h12 : Integrable (fun u : ℝ => u ^ 2) (μ1 : Measure ℝ))
    (h13 : Integrable (fun u : ℝ => u ^ 3) (μ1 : Measure ℝ))
    (hm0 : ∫ u : ℝ, u ∂(μ0 : Measure ℝ) = 0)
    (hm1 : ∫ u : ℝ, u ∂(μ1 : Measure ℝ) = 0)
    (hsign0 : ∀ᵐ u ∂(μ0 : Measure ℝ), u ≤ p)
    (hsign1 : ∀ᵐ u ∂(μ1 : Measure ℝ), -(1 - p) ≤ u) :
    thirdAbsoluteMoment (residualMixtureLaw μ0 μ1 p c hp0 hp1) * c ^ 3 =
      p * (1 - p) * (1 - 2 * (p * (1 - p))) +
        3 * (p * (1 - p)) * ((∫ u, u ^ 2 ∂(μ0 : Measure ℝ)) +
          (∫ u, u ^ 2 ∂(μ1 : Measure ℝ))) -
        (1 - p) * (∫ u, u ^ 3 ∂(μ0 : Measure ℝ)) +
        p * (∫ u, u ^ 3 ∂(μ1 : Measure ℝ)) := by
  have hshift0 : Integrable (fun u : ℝ => (u - p) ^ 3) (μ0 : Measure ℝ) := by
    simpa only [sub_eq_add_neg] using integrable_cube_add_const
      (μ0 : Measure ℝ) (fun u => u) (-p) h01 h02 h03
  have hshift1 := integrable_cube_add_const
    (μ1 : Measure ℝ) (fun u : ℝ => u) (1 - p) h11 h12 h13
  have hae0 : (fun u : ℝ => |(u - p) / c| ^ 3) =ᵐ[(μ0 : Measure ℝ)]
      (fun u => -((u - p) ^ 3) / c ^ 3) := hsign0.mono fun u h =>
    abs_cube_div_of_nonpos (u - p) c (sub_nonpos.mpr h) hc
  have hae1 : (fun u : ℝ => |(u + (1 - p)) / c| ^ 3) =ᵐ[(μ1 : Measure ℝ)]
      (fun u => (u + (1 - p)) ^ 3 / c ^ 3) := hsign1.mono fun u h =>
    abs_cube_div_of_nonneg (u + (1 - p)) c (by linarith) hc
  have hint0 : Integrable (fun u : ℝ => |(u - p) / c| ^ 3) (μ0 : Measure ℝ) :=
    (hshift0.neg.div_const (c ^ 3)).congr hae0.symm
  have hint1 : Integrable (fun u : ℝ => |(u + (1 - p)) / c| ^ 3) (μ1 : Measure ℝ) :=
    (hshift1.div_const (c ^ 3)).congr hae1.symm
  have hsm : StronglyMeasurable (fun x : ℝ => |x| ^ 3) :=
    (continuous_abs.pow 3).stronglyMeasurable
  unfold thirdAbsoluteMoment
  rw [coe_residualMixtureLaw,
    integral_residualMixture μ0 μ1 p c hp0 hp1 _ hsm hint0 hint1,
    integral_congr_ae hae0, integral_congr_ae hae1,
    integral_div, integral_neg, integral_div]
  have hex0 := integral_cube_add_const (μ0 : Measure ℝ) (fun u : ℝ => u) (-p)
    h01 h02 h03
  have hex1 := integral_cube_add_const (μ1 : Measure ℝ) (fun u : ℝ => u) (1 - p)
    h11 h12 h13
  simp only [hm0, hm1, mul_zero, add_zero] at hex0 hex1
  simp only [sub_eq_add_neg] at *
  rw [hex0, hex1]
  field_simp [ne_of_gt hc]
  ring

end BerryEsseen.MomentBudget

#print axioms BerryEsseen.MomentBudget.actual_thirdAbsoluteMoment_identity

namespace BerryEsseen.MomentBudget

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Reflection of the upper endpoint bound, for the second residual group. -/
theorem neg_integral_cube_le_endpoint (μ : Measure Ω) [IsProbabilityMeasure μ]
    (U : Ω → ℝ) (a z : ℝ) (ha : 0 ≤ a)
    (hU : Integrable U μ) (hU2 : Integrable (fun ω => U ω ^ 2) μ)
    (hU3 : Integrable (fun ω => U ω ^ 3) μ)
    (hmean : ∫ ω, U ω ∂μ = 0) (hsecond : ∫ ω, U ω ^ 2 ∂μ = z)
    (hlower : ∀ᵐ ω ∂μ, -a ≤ U ω) :
    -(∫ ω, U ω ^ 3 ∂μ) ≤ a * z - z ^ 2 / a := by
  have h2 : Integrable (fun ω => (-U ω) ^ 2) μ := by simpa using hU2
  have h3 : Integrable (fun ω => (-U ω) ^ 3) μ := by
    convert hU3.neg using 1
    ext ω
    simp only [Pi.neg_apply]
    ring
  have hm : (∫ ω, -U ω ∂μ) = 0 := by rw [integral_neg, hmean, neg_zero]
  have hz : (∫ ω, (-U ω) ^ 2 ∂μ) = z := by simpa using hsecond
  have hu : ∀ᵐ ω ∂μ, -U ω ≤ a := hlower.mono fun ω h => by linarith
  have h := integral_cube_le_endpoint μ (fun ω => -U ω) a z ha hU.neg h2 h3 hm hz hu
  have heq : (fun ω => (-U ω) ^ 3) = (fun ω => -(U ω ^ 3)) := by ext ω; ring
  rw [heq, integral_neg] at h
  exact h

/-- Two-term Cauchy--Schwarz, including vanishing caps with their zero moment. -/
theorem two_cap_cauchy (a b x y : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hax : a = 0 → x = 0) (hby : b = 0 → y = 0) :
    (x + y) ^ 2 ≤ (a + b) * (x ^ 2 / a + y ^ 2 / b) := by
  by_cases ha0 : a = 0
  · have hx := hax ha0
    subst a
    subst x
    by_cases hb0 : b = 0
    · simp [hb0, hby hb0]
    · simp [← mul_div_assoc, hb0]
  by_cases hb0 : b = 0
  · have hy := hby hb0
    subst b
    subst y
    simp [← mul_div_assoc, ha0]
  have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hbp : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  have hid : (a + b) * (x ^ 2 / a + y ^ 2 / b) * (a * b) -
      (x + y) ^ 2 * (a * b) = (b * x - a * y) ^ 2 := by
    field_simp [ha0, hb0]
    <;> ring
  apply (mul_le_mul_iff_of_pos_right (mul_pos hap hbp)).mp
  nlinarith [sq_nonneg (b * x - a * y)]

/-- The common positive cap may be larger than the sum of the actual caps. -/
theorem two_cap_cauchy_delta (a b x y δ : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hδ : 0 < δ) (hcap : a + b ≤ δ)
    (hax : a = 0 → x = 0) (hby : b = 0 → y = 0) :
    (x + y) ^ 2 / δ ≤ x ^ 2 / a + y ^ 2 / b := by
  have hnon : 0 ≤ x ^ 2 / a + y ^ 2 / b :=
    add_nonneg (div_nonneg (sq_nonneg x) ha) (div_nonneg (sq_nonneg y) hb)
  apply (div_le_iff₀ hδ).mpr
  calc
    (x + y) ^ 2 ≤ (a + b) * (x ^ 2 / a + y ^ 2 / b) :=
      two_cap_cauchy a b x y ha hb hax hby
    _ ≤ δ * (x ^ 2 / a + y ^ 2 / b) := mul_le_mul_of_nonneg_right hcap hnon
    _ = (x ^ 2 / a + y ^ 2 / b) * δ := mul_comm _ _

/-- The shared cap budget before changing coordinates to the allocation `α`. -/
theorem shared_cubic_budget (p z0 z1 m0 m1 a0 a1 δ : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hz0 : 0 ≤ z0) (hz1 : 0 ≤ z1)
    (ha0 : 0 ≤ a0) (ha1 : 0 ≤ a1) (hδ : 0 < δ) (hcap : a0 + a1 ≤ δ)
    (ha0z : a0 = 0 → z0 = 0) (ha1z : a1 = 0 → z1 = 0)
    (hm0 : m0 ≤ a0 * z0 - z0 ^ 2 / a0)
    (hm1 : -m1 ≤ a1 * z1 - z1 ^ 2 / a1) :
    -((1 - p) * m0) + p * m1 ≥
      -δ * ((1 - p) * z0 + p * z1) +
        (Real.sqrt (1 - p) * z0 + Real.sqrt p * z1) ^ 2 / δ := by
  have hq : 0 ≤ 1 - p := sub_nonneg.mpr hp1
  have hcs := two_cap_cauchy_delta a0 a1 (Real.sqrt (1 - p) * z0)
    (Real.sqrt p * z1) δ ha0 ha1 hδ hcap
    (fun h => by rw [ha0z h, mul_zero]) (fun h => by rw [ha1z h, mul_zero])
  rw [mul_pow, mul_pow, Real.sq_sqrt hq, Real.sq_sqrt hp0] at hcs
  have hprice0 := mul_le_mul_of_nonneg_left hm0 hq
  have hprice1 := mul_le_mul_of_nonneg_left hm1 hp0
  have hbound0 : a0 ≤ δ := by linarith
  have hbound1 : a1 ≤ δ := by linarith
  have hcost0 := mul_le_mul_of_nonneg_left hbound0 (mul_nonneg hq hz0)
  have hcost1 := mul_le_mul_of_nonneg_left hbound1 (mul_nonneg hp0 hz1)
  simp only [mul_div_assoc] at hprice0 hprice1 hcs
  nlinarith

end BerryEsseen.MomentBudget

#print axioms BerryEsseen.MomentBudget.two_cap_cauchy_delta
#print axioms BerryEsseen.MomentBudget.shared_cubic_budget

namespace BerryEsseen.MomentBudget

/-- The three finite moments and centering of an arbitrary residual law. -/
structure CenteredResidualLaw (μ : ProbabilityMeasure ℝ) : Prop where
  integrable_first : Integrable (fun u : ℝ => u) (μ : Measure ℝ)
  integrable_second : Integrable (fun u : ℝ => u ^ 2) (μ : Measure ℝ)
  integrable_third : Integrable (fun u : ℝ => u ^ 3) (μ : Measure ℝ)
  mean_zero : (∫ u : ℝ, u ∂(μ : Measure ℝ)) = 0

def residualSecondMoment (μ : ProbabilityMeasure ℝ) : ℝ := ∫ u, u ^ 2 ∂(μ : Measure ℝ)
def residualCubicMoment (μ : ProbabilityMeasure ℝ) : ℝ := ∫ u, u ^ 3 ∂(μ : Measure ℝ)

lemma residualSecondMoment_nonneg (μ : ProbabilityMeasure ℝ) :
    0 ≤ residualSecondMoment μ := integral_nonneg fun _ => sq_nonneg _

/-- Finite absolute third moment supplies every integrability hypothesis used here. -/
theorem centeredResidualLaw_of_abs_cube (μ : ProbabilityMeasure ℝ)
    (h3 : Integrable (fun u : ℝ => |u| ^ 3) (μ : Measure ℝ))
    (hm : ∫ u : ℝ, u ∂(μ : Measure ℝ) = 0) : CenteredResidualLaw μ := by
  have hid : AEStronglyMeasurable (fun u : ℝ => u) (μ : Measure ℝ) :=
    measurable_id.aestronglyMeasurable
  have hn : Integrable (fun u : ℝ => ‖u‖ ^ 3) (μ : Measure ℝ) := by
    simpa only [Real.norm_eq_abs] using h3
  have h1 := integrable_norm_pow_of_le hid (by decide : 1 ≤ 3) hn
  have h2 := integrable_norm_pow_of_le hid (by decide : 2 ≤ 3) hn
  refine ⟨?_, ?_, ?_, hm⟩
  · exact (integrable_norm_iff hid).mp (by simpa only [pow_one] using h1)
  · simpa only [Real.norm_eq_abs, sq_abs] using h2
  · have hmeas : AEStronglyMeasurable (fun u : ℝ => u ^ 3) (μ : Measure ℝ) := by
      fun_prop
    apply (integrable_norm_iff hmeas).mp
    simpa only [Real.norm_eq_abs, abs_pow] using h3

/-- Coordinates for the same residual variances; no new allocation is introduced. -/
theorem allocation_coordinates (p z0 z1 s α : ℝ)
    (hp : 0 < p) (hp1 : p < 1) (hs : 0 < s)
    (hsecond : s = (1 - p) * z0 + p * z1) (hα : α = p * z1 / s) :
    p * (1 - p) * (z0 + z1) = s * (p + α * ((1 - p) - p)) ∧
    Real.sqrt (1 - p) * z0 + Real.sqrt p * z1 =
      s * ((1 - α) / Real.sqrt (1 - p) + α / Real.sqrt p) := by
  have hq : 0 < 1 - p := sub_pos.mpr hp1
  have hαs : α * s = p * z1 := by rw [hα]; exact div_mul_cancel₀ _ (ne_of_gt hs)
  have hβs : (1 - α) * s = (1 - p) * z0 := by nlinarith [hsecond]
  constructor
  · calc
      p * (1 - p) * (z0 + z1) =
          ((1 - p) * z0 + p * z1) * p + (p * z1) * ((1 - p) - p) := by ring
      _ = s * p + (α * s) * ((1 - p) - p) := by rw [hαs, hsecond]
      _ = s * (p + α * ((1 - p) - p)) := by ring
  · have hqdiv : ((1 - p) * z0) / Real.sqrt (1 - p) = Real.sqrt (1 - p) * z0 := by
      apply (div_eq_iff (ne_of_gt (Real.sqrt_pos.mpr hq))).mpr
      calc
        (1 - p) * z0 = Real.sqrt (1 - p) ^ 2 * z0 := by rw [Real.sq_sqrt (le_of_lt hq)]
        _ = (Real.sqrt (1 - p) * z0) * Real.sqrt (1 - p) := by ring
    have hpdiv : (p * z1) / Real.sqrt p = Real.sqrt p * z1 := by
      apply (div_eq_iff (ne_of_gt (Real.sqrt_pos.mpr hp))).mpr
      calc
        p * z1 = Real.sqrt p ^ 2 * z1 := by rw [Real.sq_sqrt (le_of_lt hp)]
        _ = (Real.sqrt p * z1) * Real.sqrt p := by ring
    calc
      Real.sqrt (1 - p) * z0 + Real.sqrt p * z1 =
          ((1 - α) * s) / Real.sqrt (1 - p) + (α * s) / Real.sqrt p := by
        rw [hαs, hβs, hqdiv, hpdiv]
      _ = s * ((1 - α) / Real.sqrt (1 - p) + α / Real.sqrt p) := by ring

/-- The manuscript's allocation floor, with `(v+s)^(3/2)` written as `sqrt(v+s)^3`. -/
def gDelta (p s δ α : ℝ) : ℝ :=
  (p * (1 - p) * (1 - 2 * (p * (1 - p))) +
    (3 * (p + α * ((1 - p) - p)) - δ) * s +
    ((1 - α) / Real.sqrt (1 - p) + α / Real.sqrt p) ^ 2 * s ^ 2 / δ) /
      (Real.sqrt (p * (1 - p) + s)) ^ 3

end BerryEsseen.MomentBudget

namespace BerryEsseen.MomentBudget

lemma residualSecondMoment_zero_of_upper_zero (μ : ProbabilityMeasure ℝ)
    (h : CenteredResidualLaw μ) (hu : ∀ᵐ u ∂(μ : Measure ℝ), u ≤ 0) :
    residualSecondMoment μ = 0 := by
  have hz := centered_nonpos_ae_zero (μ : Measure ℝ) (fun u : ℝ => u)
    h.integrable_first h.mean_zero hu
  calc
    residualSecondMoment μ = ∫ _ : ℝ, (0 : ℝ) ∂(μ : Measure ℝ) :=
      integral_congr_ae (hz.mono fun u heq => by simp [heq])
    _ = 0 := integral_zero _ _

lemma residualSecondMoment_zero_of_lower_zero (μ : ProbabilityMeasure ℝ)
    (h : CenteredResidualLaw μ) (hu : ∀ᵐ u ∂(μ : Measure ℝ), 0 ≤ u) :
    residualSecondMoment μ = 0 := by
  have hn : ∀ᵐ u ∂(μ : Measure ℝ), -u ≤ 0 := hu.mono fun u heq => by linarith
  have hm : (∫ u : ℝ, -u ∂(μ : Measure ℝ)) = 0 := by
    rw [integral_neg, h.mean_zero, neg_zero]
  have hz := centered_nonpos_ae_zero (μ : Measure ℝ) (fun u : ℝ => -u)
    h.integrable_first.neg hm hn
  calc
    residualSecondMoment μ = ∫ _ : ℝ, (0 : ℝ) ∂(μ : Measure ℝ) :=
      integral_congr_ae (hz.mono fun u heq => by
        have hu0 : u = 0 := by simpa using heq
        simp [hu0])
    _ = 0 := integral_zero _ _

/-- The actual-law allocation floor. Its `α` and `s` are constrained to be
exactly those of the same two residual variances, including zero-cap groups. -/
theorem actual_allocation_floor (μ0 μ1 : ProbabilityMeasure ℝ)
    (h0 : CenteredResidualLaw μ0) (h1 : CenteredResidualLaw μ1)
    (p s α a0 a1 δ : ℝ) (hp : 0 < p) (hp1 : p < 1) (hs : 0 < s)
    (hsecond : s = (1 - p) * residualSecondMoment μ0 + p * residualSecondMoment μ1)
    (hα : α = p * residualSecondMoment μ1 / s)
    (ha0 : 0 ≤ a0) (ha1 : 0 ≤ a1) (hδ : 0 < δ) (hcap : a0 + a1 ≤ δ)
    (hupper0 : ∀ᵐ u ∂(μ0 : Measure ℝ), u ≤ a0)
    (hlower1 : ∀ᵐ u ∂(μ1 : Measure ℝ), -a1 ≤ u)
    (hsign0 : ∀ᵐ u ∂(μ0 : Measure ℝ), u ≤ p)
    (hsign1 : ∀ᵐ u ∂(μ1 : Measure ℝ), -(1 - p) ≤ u) :
    gDelta p s δ α ≤ thirdAbsoluteMoment
      (residualMixtureLaw μ0 μ1 p (Real.sqrt (p * (1 - p) + s))
        (le_of_lt hp) (le_of_lt hp1)) := by
  have hq : 0 < 1 - p := sub_pos.mpr hp1
  have hc : 0 < Real.sqrt (p * (1 - p) + s) :=
    Real.sqrt_pos.mpr (add_pos (mul_pos hp hq) hs)
  have hzero0 : a0 = 0 → residualSecondMoment μ0 = 0 := by
    intro heq
    apply residualSecondMoment_zero_of_upper_zero μ0 h0
    simpa only [heq] using hupper0
  have hzero1 : a1 = 0 → residualSecondMoment μ1 = 0 := by
    intro heq
    apply residualSecondMoment_zero_of_lower_zero μ1 h1
    simpa only [heq, neg_zero] using hlower1
  have hprice0 := integral_cube_le_endpoint (μ0 : Measure ℝ) (fun u : ℝ => u)
    a0 (residualSecondMoment μ0) ha0 h0.integrable_first h0.integrable_second
    h0.integrable_third h0.mean_zero rfl hupper0
  have hprice1 := neg_integral_cube_le_endpoint (μ1 : Measure ℝ) (fun u : ℝ => u)
    a1 (residualSecondMoment μ1) ha1 h1.integrable_first h1.integrable_second
    h1.integrable_third h1.mean_zero rfl hlower1
  have hbudget := shared_cubic_budget p (residualSecondMoment μ0) (residualSecondMoment μ1)
    (residualCubicMoment μ0) (residualCubicMoment μ1) a0 a1 δ (le_of_lt hp)
    (le_of_lt hp1) (residualSecondMoment_nonneg μ0) (residualSecondMoment_nonneg μ1)
    ha0 ha1 hδ hcap hzero0 hzero1 hprice0 hprice1
  rw [← hsecond] at hbudget
  have hid := actual_thirdAbsoluteMoment_identity μ0 μ1 p
    (Real.sqrt (p * (1 - p) + s)) (le_of_lt hp) (le_of_lt hp1) hc
    h0.integrable_first h0.integrable_second h0.integrable_third
    h1.integrable_first h1.integrable_second h1.integrable_third
    h0.mean_zero h1.mean_zero hsign0 hsign1
  have hcoordinates := allocation_coordinates p (residualSecondMoment μ0)
    (residualSecondMoment μ1) s α hp hp1 hs hsecond hα
  unfold gDelta
  apply (div_le_iff₀ (pow_pos hc 3)).mpr
  calc
    p * (1 - p) * (1 - 2 * (p * (1 - p))) +
        (3 * (p + α * ((1 - p) - p)) - δ) * s +
        ((1 - α) / Real.sqrt (1 - p) + α / Real.sqrt p) ^ 2 * s ^ 2 / δ =
      p * (1 - p) * (1 - 2 * (p * (1 - p))) +
        3 * (p * (1 - p) * (residualSecondMoment μ0 + residualSecondMoment μ1)) -
        δ * s + (Real.sqrt (1 - p) * residualSecondMoment μ0 +
          Real.sqrt p * residualSecondMoment μ1) ^ 2 / δ := by
      rw [hcoordinates.1, hcoordinates.2]
      ring
    _ ≤ thirdAbsoluteMoment
      (residualMixtureLaw μ0 μ1 p (Real.sqrt (p * (1 - p) + s))
        (le_of_lt hp) (le_of_lt hp1)) * Real.sqrt (p * (1 - p) + s) ^ 3 := by
      dsimp only [residualSecondMoment, residualCubicMoment] at hbudget ⊢
      linarith

/-- The count variance formula uses exactly the same allocation coordinates. -/
theorem allocation_count_variance (p z0 z1 s α N k : ℝ)
    (hp : 0 < p) (hp1 : p < 1) (hs : 0 < s)
    (hsecond : s = (1 - p) * z0 + p * z1) (hα : α = p * z1 / s) :
    N * z0 + k * z1 = s * (N * (1 - α) / (1 - p) + k * α / p) := by
  have hq : 0 < 1 - p := sub_pos.mpr hp1
  have hαs : α * s = p * z1 := by rw [hα]; exact div_mul_cancel₀ _ (ne_of_gt hs)
  have hβs : (1 - α) * s = (1 - p) * z0 := by nlinarith [hsecond]
  have hz0 : s * (1 - α) / (1 - p) = z0 := by
    apply (div_eq_iff (ne_of_gt hq)).mpr
    nlinarith
  have hz1 : s * α / p = z1 := by
    apply (div_eq_iff (ne_of_gt hp)).mpr
    nlinarith
  calc
    N * z0 + k * z1 = N * (s * (1 - α) / (1 - p)) + k * (s * α / p) := by rw [hz0, hz1]
    _ = s * (N * (1 - α) / (1 - p) + k * α / p) := by ring

end BerryEsseen.MomentBudget

#print axioms BerryEsseen.MomentBudget.actual_allocation_floor
#print axioms BerryEsseen.MomentBudget.allocation_count_variance

namespace BerryEsseen.MomentBudget

variable {Ω : Type*} [MeasurableSpace Ω]

lemma integrable_square_add_const (μ : Measure Ω) [IsFiniteMeasure μ] (U : Ω → ℝ) (t : ℝ)
    (h1 : Integrable U μ) (h2 : Integrable (fun ω => U ω ^ 2) μ) :
    Integrable (fun ω => (U ω + t) ^ 2) μ := by
  have hA : Integrable (fun ω => U ω ^ 2 + 2 * t * U ω) μ :=
    h2.add (h1.const_mul _)
  have hB : Integrable (fun ω => U ω ^ 2 + 2 * t * U ω + t ^ 2) μ :=
    hA.add (integrable_const _)
  exact hB.congr (Filter.Eventually.of_forall fun ω => by ring)

lemma integral_square_add_const (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → ℝ) (t : ℝ)
    (h1 : Integrable U μ) (h2 : Integrable (fun ω => U ω ^ 2) μ) :
    (∫ ω, (U ω + t) ^ 2 ∂μ) = (∫ ω, U ω ^ 2 ∂μ) +
      2 * t * (∫ ω, U ω ∂μ) + t ^ 2 := by
  have heq : (fun ω => (U ω + t) ^ 2) =
      (fun ω => U ω ^ 2 + 2 * t * U ω + t ^ 2) := by ext ω; ring
  have hA : Integrable (fun ω => U ω ^ 2 + 2 * t * U ω) μ :=
    h2.add (h1.const_mul _)
  rw [heq, integral_add hA (integrable_const _), integral_add h2 (h1.const_mul _),
    integral_const_mul]
  simp

/-- Centering of the actual standardized mixture. -/
theorem actual_first_moment (μ0 μ1 : ProbabilityMeasure ℝ)
    (h0 : CenteredResidualLaw μ0) (h1 : CenteredResidualLaw μ1)
    (p c : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (∫ x : ℝ, x ∂(residualMixtureLaw μ0 μ1 p c hp0 hp1 : Measure ℝ)) = 0 := by
  rw [coe_residualMixtureLaw, integral_residualMixture μ0 μ1 p c hp0 hp1
    (fun x : ℝ => x) stronglyMeasurable_id
    ((h0.integrable_first.sub (integrable_const p)).div_const c)
    ((h1.integrable_first.add (integrable_const (1 - p))).div_const c),
    integral_div, integral_div,
    integral_sub h0.integrable_first (integrable_const p),
    integral_add h1.integrable_first (integrable_const (1 - p))]
  simp only [h0.mean_zero, h1.mean_zero, integral_const, probReal_univ,
    one_smul, zero_sub, zero_add]
  ring

/-- The true second moment of the same mixture; this identifies the normalizing scale. -/
theorem actual_second_moment (μ0 μ1 : ProbabilityMeasure ℝ)
    (h0 : CenteredResidualLaw μ0) (h1 : CenteredResidualLaw μ1)
    (p c : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (∫ x : ℝ, x ^ 2 ∂(residualMixtureLaw μ0 μ1 p c hp0 hp1 : Measure ℝ)) =
      (p * (1 - p) + (1 - p) * residualSecondMoment μ0 +
        p * residualSecondMoment μ1) / c ^ 2 := by
  have hshift0 : Integrable (fun u : ℝ => (u - p) ^ 2) (μ0 : Measure ℝ) := by
    simpa only [sub_eq_add_neg] using integrable_square_add_const
      (μ0 : Measure ℝ) (fun u : ℝ => u) (-p) h0.integrable_first h0.integrable_second
  have hshift1 := integrable_square_add_const (μ1 : Measure ℝ)
    (fun u : ℝ => u) (1 - p) h1.integrable_first h1.integrable_second
  have hi0 : Integrable (fun u : ℝ => ((u - p) / c) ^ 2) (μ0 : Measure ℝ) := by
    simpa only [div_pow] using hshift0.div_const (c ^ 2)
  have hi1 : Integrable (fun u : ℝ => ((u + (1 - p)) / c) ^ 2) (μ1 : Measure ℝ) := by
    simpa only [div_pow] using hshift1.div_const (c ^ 2)
  have hsm : StronglyMeasurable (fun x : ℝ => x ^ 2) :=
    (continuous_id.pow 2).stronglyMeasurable
  rw [coe_residualMixtureLaw, integral_residualMixture μ0 μ1 p c hp0 hp1 _ hsm hi0 hi1]
  simp only [div_pow]
  rw [integral_div, integral_div]
  have hex0 := integral_square_add_const (μ0 : Measure ℝ) (fun u : ℝ => u) (-p)
    h0.integrable_first h0.integrable_second
  have hex1 := integral_square_add_const (μ1 : Measure ℝ) (fun u : ℝ => u) (1 - p)
    h1.integrable_first h1.integrable_second
  simp only [h0.mean_zero, h1.mean_zero, mul_zero, add_zero] at hex0 hex1
  simp only [sub_eq_add_neg] at *
  rw [hex0, hex1]
  dsimp only [residualSecondMoment]
  ring

end BerryEsseen.MomentBudget

#print axioms BerryEsseen.MomentBudget.actual_first_moment
#print axioms BerryEsseen.MomentBudget.actual_second_moment
