module

public import BerryEsseen.ContactVariation
public import Mathlib.Probability.CDF
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

noncomputable section

namespace BerryEsseen.SupportContact

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

instance iidSumLaw_isProbability (μ : Measure ℝ) [IsProbabilityMeasure μ] (n : ℕ) :
    IsProbabilityMeasure (MixtureSum.iidSumLaw μ n) := by
  unfold MixtureSum.iidSumLaw
  infer_instance

/-- Fubini on the actual closed sum event gives both integrability and the
convolution identity, without density or atomlessness assumptions. -/
theorem shiftedCDF_integrable_integral (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (H : ℝ) :
    Integrable (fun x : ℝ => ν.real (Iic (H - x))) μ ∧
    (∫ x : ℝ, ν.real (Iic (H - x)) ∂μ) = (μ ∗ ν).real (Iic H) := by
  let s : Set (ℝ × ℝ) := {p | p.1 + p.2 ≤ H}
  have hs : MeasurableSet s := measurableSet_le (measurable_fst.add measurable_snd) measurable_const
  have hi : Integrable (s.indicator (fun _ : ℝ × ℝ => (1 : ℝ))) (μ.prod ν) :=
    (integrable_const 1).indicator hs
  have hfiber (x : ℝ) : (fun y : ℝ => s.indicator (fun _ => (1 : ℝ)) (x, y)) =
      (Iic (H - x)).indicator (fun _ => (1 : ℝ)) := by
    funext y
    have hevent : (x, y) ∈ s ↔ y ∈ Iic (H - x) := by
      change x + y ≤ H ↔ y ≤ H - x
      constructor <;> intro h <;> linarith
    simp only [Set.indicator_apply, hevent]
  have hinner : (fun x : ℝ => ∫ y : ℝ, s.indicator (fun _ => (1 : ℝ)) (x, y) ∂ν) =
      (fun x : ℝ => ν.real (Iic (H - x))) := by
    funext x
    rw [hfiber x, integral_indicator_const (1 : ℝ) measurableSet_Iic]
    simp
  refine ⟨?_, ?_⟩
  · rw [← hinner]
    exact hi.integral_prod_left
  · rw [← hinner, ← integral_prod _ hi, integral_indicator_const (1 : ℝ) hs]
    simp only [smul_eq_mul, mul_one]
    unfold Measure.conv
    have hm : Measurable (fun p : ℝ × ℝ => p.1 + p.2) := by fun_prop
    rw [map_measureReal_apply hm measurableSet_Iic]
    rfl

theorem iidSumLaw_rec (μ : ProbabilityMeasure ℝ) (n : ℕ) (hn : 0 < n) :
    (μ : Measure ℝ) ∗ MixtureSum.iidSumLaw (μ : Measure ℝ) (n - 1) =
      MixtureSum.iidSumLaw (μ : Measure ℝ) n := by
  calc
    (μ : Measure ℝ) ∗ MixtureSum.iidSumLaw (μ : Measure ℝ) (n - 1) =
        (μ : Measure ℝ) ∗ MixtureSum.convPower (μ : Measure ℝ) (n - 1) := by
      rw [MixtureSum.iidSumLaw_eq_convPower]
    _ = MixtureSum.convPower (μ : Measure ℝ) ((n - 1) + 1) := rfl
    _ = MixtureSum.convPower (μ : Measure ℝ) n := by rw [Nat.sub_add_cancel (by omega : 1 ≤ n)]
    _ = _ := (MixtureSum.iidSumLaw_eq_convPower (μ : Measure ℝ) n).symm

theorem integral_iid_closedCDF (μ : ProbabilityMeasure ℝ) (n : ℕ) (hn : 0 < n) (H : ℝ) :
    (∫ x : ℝ, (MixtureSum.iidSumLaw (μ : Measure ℝ) (n - 1)).real (Iic (H - x))
      ∂(μ : Measure ℝ)) = (MixtureSum.iidSumLaw (μ : Measure ℝ) n).real (Iic H) := by
  have hi := (shiftedCDF_integrable_integral (μ : Measure ℝ)
    (MixtureSum.iidSumLaw (μ : Measure ℝ) (n - 1)) H).2
  rw [iidSumLaw_rec μ n hn] at hi
  exact hi

/-- The genuine closed CDF is upper semicontinuous even at its jumps. -/
theorem upperSemicontinuous_closedCDF (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    UpperSemicontinuous (fun t : ℝ => ν.real (Iic t)) := by
  have hf : UpperSemicontinuous (cdf ν : ℝ → ℝ) := by
    intro a b hb
    have hc : Tendsto (cdf ν) (𝓝[Ioi a] a) (𝓝 (cdf ν a)) :=
      ((cdf ν).right_continuous a).mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
    have he : ∀ᶠ t in 𝓝[Ioi a] a, cdf ν t < b := hc.eventually (Iio_mem_nhds hb)
    have hboth : ∀ᶠ t in 𝓝[Ioi a] a, a < t ∧ cdf ν t < b := by
      filter_upwards [self_mem_nhdsWithin, he] with t ht htb
      exact ⟨ht, htb⟩
    obtain ⟨t, hat, htb⟩ := hboth.exists
    filter_upwards [Iio_mem_nhds hat] with y hyt
    exact lt_of_le_of_lt ((cdf ν).mono (le_of_lt hyt)) htb
  have heq : (fun t : ℝ => ν.real (Iic t)) = (cdf ν : ℝ → ℝ) :=
    funext (fun t => (cdf_eq_real ν t).symm)
  rw [heq]
  exact hf

theorem upperSemicontinuous_shiftedCDF (ν : Measure ℝ) [IsProbabilityMeasure ν] (H : ℝ) :
    UpperSemicontinuous (fun x : ℝ => ν.real (Iic (H - x))) :=
  (upperSemicontinuous_closedCDF ν).comp (g := fun x : ℝ => H - x) (by fun_prop)

theorem integrable_momentSlope (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    Integrable (ContactVariation.momentSlope μ) (μ : Measure ℝ) := by
  unfold ContactVariation.momentSlope
  exact ((h.integrable_cube.sub
      (h.integrable_square.const_mul ((3 / 2 : ℝ) * thirdAbsoluteMoment μ))).sub
      (h.integrable_mean.const_mul (3 * SignedMoment.signedSecondMoment μ))).add
    (integrable_const (thirdAbsoluteMoment μ / 2))

theorem integral_momentSlope_zero (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    (∫ x : ℝ, ContactVariation.momentSlope μ x ∂(μ : Measure ℝ)) = 0 := by
  have h2 := h.integrable_square.const_mul ((3 / 2 : ℝ) * thirdAbsoluteMoment μ)
  have h1 := h.integrable_mean.const_mul (3 * SignedMoment.signedSecondMoment μ)
  have hA : Integrable (fun x : ℝ => |x| ^ 3 -
      (3 / 2 : ℝ) * thirdAbsoluteMoment μ * x ^ 2) (μ : Measure ℝ) := h.integrable_cube.sub h2
  have hAB : Integrable (fun x : ℝ => |x| ^ 3 -
      (3 / 2 : ℝ) * thirdAbsoluteMoment μ * x ^ 2 -
      3 * SignedMoment.signedSecondMoment μ * x) (μ : Measure ℝ) := hA.sub h1
  unfold ContactVariation.momentSlope
  rw [integral_add hAB (integrable_const (thirdAbsoluteMoment μ / 2)),
    integral_sub hA h1, integral_sub h.integrable_cube h2,
    integral_const_mul, integral_const_mul, h.second_moment_one, h.mean_zero]
  simp only [integral_const, probReal_univ, one_smul]
  change thirdAbsoluteMoment μ - (3 / 2 : ℝ) * thirdAbsoluteMoment μ * 1 -
    3 * SignedMoment.signedSecondMoment μ * 0 + thirdAbsoluteMoment μ / 2 = 0
  ring

private def gaussianPart (n : ℕ) (H x : ℝ) : ℝ :=
  GaussianTools.phi (H / Real.sqrt n) *
    (Real.sqrt n * x + (H / Real.sqrt n) / 2 * (x ^ 2 - 1))

private theorem integrable_gaussianPart (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (H : ℝ) : Integrable (gaussianPart n H) (μ : Measure ℝ) := by
  have hlin := h.integrable_mean.const_mul (Real.sqrt n)
  have hquad := (h.integrable_square.sub (integrable_const 1)).const_mul ((H / Real.sqrt n) / 2)
  exact (hlin.add hquad).const_mul (GaussianTools.phi (H / Real.sqrt n))

private theorem integral_gaussianPart_zero (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (H : ℝ) : (∫ x : ℝ, gaussianPart n H x ∂(μ : Measure ℝ)) = 0 := by
  have hlin := h.integrable_mean.const_mul (Real.sqrt n)
  have hquad : Integrable (fun x : ℝ => (H / Real.sqrt n) / 2 * (x ^ 2 - 1))
      (μ : Measure ℝ) :=
    (h.integrable_square.sub (integrable_const 1)).const_mul ((H / Real.sqrt n) / 2)
  unfold gaussianPart
  rw [integral_const_mul, integral_add hlin hquad,
    integral_const_mul, integral_const_mul,
    integral_sub h.integrable_square (integrable_const 1), h.mean_zero, h.second_moment_one]
  simp

theorem integrable_D (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (H C : ℝ) : Integrable (ContactVariation.D μ n H C) (μ : Measure ℝ) := by
  have hc := (shiftedCDF_integrable_integral (μ : Measure ℝ)
    (MixtureSum.iidSumLaw (μ : Measure ℝ) (n - 1)) H).1
  have hpart : Integrable (fun x : ℝ => (n : ℝ) *
      ((MixtureSum.iidSumLaw (μ : Measure ℝ) (n - 1)).real (Iic (H - x)) -
        (MixtureSum.iidSumLaw (μ : Measure ℝ) n).real (Iic H))) (μ : Measure ℝ) :=
    (hc.sub (integrable_const
      ((MixtureSum.iidSumLaw (μ : Measure ℝ) n).real (Iic H)))).const_mul (n : ℝ)
  change Integrable (fun x : ℝ => (n : ℝ) *
      ((MixtureSum.iidSumLaw (μ : Measure ℝ) (n - 1)).real (Iic (H - x)) -
        (MixtureSum.iidSumLaw (μ : Measure ℝ) n).real (Iic H)) + gaussianPart n H x -
      (C / Real.sqrt n) * ContactVariation.momentSlope μ x) (μ : Measure ℝ)
  exact (hpart.add (integrable_gaussianPart μ h n H)).sub
    ((integrable_momentSlope μ h).const_mul (C / Real.sqrt n))

/-- This is the integral of the actual variation function; its CDF term
vanishes by the genuine independent-sum convolution identity. -/
theorem integral_D_zero (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (hn : 0 < n) (H C : ℝ) :
    (∫ x : ℝ, ContactVariation.D μ n H C x ∂(μ : Measure ℝ)) = 0 := by
  have hc := (shiftedCDF_integrable_integral (μ : Measure ℝ)
    (MixtureSum.iidSumLaw (μ : Measure ℝ) (n - 1)) H).1
  have hpart : Integrable (fun x : ℝ => (n : ℝ) *
      ((MixtureSum.iidSumLaw (μ : Measure ℝ) (n - 1)).real (Iic (H - x)) -
        (MixtureSum.iidSumLaw (μ : Measure ℝ) n).real (Iic H))) (μ : Measure ℝ) :=
    (hc.sub (integrable_const
      ((MixtureSum.iidSumLaw (μ : Measure ℝ) n).real (Iic H)))).const_mul (n : ℝ)
  have hpart0 : (∫ x : ℝ, (n : ℝ) *
      ((MixtureSum.iidSumLaw (μ : Measure ℝ) (n - 1)).real (Iic (H - x)) -
        (MixtureSum.iidSumLaw (μ : Measure ℝ) n).real (Iic H)) ∂(μ : Measure ℝ)) = 0 := by
    rw [integral_const_mul, integral_sub hc (integrable_const _),
      integral_iid_closedCDF μ n hn H]
    simp
  change (∫ x : ℝ, (n : ℝ) *
      ((MixtureSum.iidSumLaw (μ : Measure ℝ) (n - 1)).real (Iic (H - x)) -
        (MixtureSum.iidSumLaw (μ : Measure ℝ) n).real (Iic H)) + gaussianPart n H x -
      (C / Real.sqrt n) * ContactVariation.momentSlope μ x ∂(μ : Measure ℝ)) = 0
  have hsum : Integrable (fun x : ℝ => (n : ℝ) *
      ((MixtureSum.iidSumLaw (μ : Measure ℝ) (n - 1)).real (Iic (H - x)) -
        (MixtureSum.iidSumLaw (μ : Measure ℝ) n).real (Iic H)) + gaussianPart n H x)
      (μ : Measure ℝ) := hpart.add (integrable_gaussianPart μ h n H)
  rw [integral_sub hsum
      ((integrable_momentSlope μ h).const_mul (C / Real.sqrt n)),
    integral_add hpart (integrable_gaussianPart μ h n H), hpart0,
    integral_gaussianPart_zero μ h n H, integral_const_mul, integral_momentSlope_zero μ h]
  ring

/-- The sole discontinuous term is a nonnegative multiple of a genuine
closed CDF; the remaining polynomial and absolute-cubic terms are continuous. -/
theorem upperSemicontinuous_D (μ : ProbabilityMeasure ℝ) (n : ℕ) (H C : ℝ) :
    UpperSemicontinuous (ContactVariation.D μ n H C) := by
  let f : ℝ → ℝ := fun x =>
    (MixtureSum.iidSumLaw (μ : Measure ℝ) (n - 1)).real (Iic (H - x))
  let g : ℝ → ℝ := fun t => (n : ℝ) * t
  let R : ℝ → ℝ := fun x =>
    -(n : ℝ) * (MixtureSum.iidSumLaw (μ : Measure ℝ) n).real (Iic H) +
      gaussianPart n H x - (C / Real.sqrt n) * ContactVariation.momentSlope μ x
  have hf : UpperSemicontinuous f := upperSemicontinuous_shiftedCDF _ H
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hmon : Monotone g := fun a b hab => mul_le_mul_of_nonneg_left hab (Nat.cast_nonneg n)
  have hscaled : UpperSemicontinuous (g ∘ f) := hg.comp_upperSemicontinuous hf hmon
  have hM : Continuous (ContactVariation.momentSlope μ) := by
    unfold ContactVariation.momentSlope
    fun_prop
  have hG : Continuous (gaussianPart n H) := by unfold gaussianPart; fun_prop
  have hR : Continuous R := by dsimp [R]; fun_prop
  have heq : ContactVariation.D μ n H C = (fun x : ℝ => (g ∘ f) x + R x) := by
    funext x
    dsimp [g, f, R, Function.comp_def]
    unfold ContactVariation.D gaussianPart
    ring
  rw [heq]
  exact hscaled.add hR.upperSemicontinuous

theorem D_ae_eq_zero (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (hn : 0 < n) (H C : ℝ)
    (hm : ContactVariation.PositiveClosedMaximum μ n H C) :
    ContactVariation.D μ n H C =ᵐ[(μ : Measure ℝ)] 0 := by
  have hnon : 0 ≤ᵐ[(μ : Measure ℝ)] (fun x : ℝ => -ContactVariation.D μ n H C x) :=
    Filter.Eventually.of_forall fun x => neg_nonneg.mpr (ContactVariation.D_nonpos μ h n hn H C hm x)
  have hint : (∫ x : ℝ, -ContactVariation.D μ n H C x ∂(μ : Measure ℝ)) = 0 := by
    rw [integral_neg, integral_D_zero μ h n hn H C, neg_zero]
  have hz := (integral_eq_zero_iff_of_nonneg_ae hnon (integrable_D μ h n H C).neg).mp hint
  exact hz.mono (fun x hx => by simpa only [Pi.zero_apply, neg_eq_zero] using hx)

/-- Every support point is a contact point, including atoms. Existence of
the faithful global maximizer remains a separate theorem. -/
theorem D_eq_zero_on_support (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (hn : 0 < n) (H C : ℝ)
    (hm : ContactVariation.PositiveClosedMaximum μ n H C) (x : ℝ)
    (hx : x ∈ (μ : Measure ℝ).support) : ContactVariation.D μ n H C x = 0 := by
  apply le_antisymm (ContactVariation.D_nonpos μ h n hn H C hm x)
  by_contra hnneg
  have hneg : ContactVariation.D μ n H C x < 0 := lt_of_not_ge hnneg
  have hnull : (μ : Measure ℝ) {y | ContactVariation.D μ n H C y ≠ 0} = 0 := by
    simpa only [Pi.zero_apply] using ae_iff.mp (D_ae_eq_zero μ h n hn H C hm)
  have hsub : {y | ContactVariation.D μ n H C y < 0} ⊆
      {y | ContactVariation.D μ n H C y ≠ 0} := fun y hy => ne_of_lt hy
  have hbad : (μ : Measure ℝ) {y | ContactVariation.D μ n H C y < 0} = 0 :=
    measure_mono_null hsub hnull
  have hnhds : {y | ContactVariation.D μ n H C y < 0} ∈ 𝓝 x :=
    (upperSemicontinuous_D μ n H C) x 0 hneg
  have hpos := (Measure.mem_support_iff_forall (μ := (μ : Measure ℝ)) x).mp hx _ hnhds
  exact (ne_of_gt hpos) hbad

end BerryEsseen.SupportContact

#print axioms BerryEsseen.SupportContact.shiftedCDF_integrable_integral
#print axioms BerryEsseen.SupportContact.integral_iid_closedCDF
#print axioms BerryEsseen.SupportContact.upperSemicontinuous_closedCDF
#print axioms BerryEsseen.SupportContact.integrable_D
#print axioms BerryEsseen.SupportContact.integral_D_zero
#print axioms BerryEsseen.SupportContact.upperSemicontinuous_D
#print axioms BerryEsseen.SupportContact.D_ae_eq_zero
#print axioms BerryEsseen.SupportContact.D_eq_zero_on_support
