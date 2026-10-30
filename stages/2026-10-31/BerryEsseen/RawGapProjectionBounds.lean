module

public import BerryEsseen.RawResourceEnvelope

@[expose] public section

/-! 2026-10-30: the actual gap terms are a positive right-endpoint
replacement of the same law's zero-bias integral. The estimates below
sum the genuine disjoint open gaps; no finite-support approximation,
central-gap deletion, or independent moment replacement is used. -/

noncomputable section

open MeasureTheory Set
open scoped BigOperators Interval

namespace BerryEsseen.RawGapProjectionBounds

open ZeroBias ZeroBiasHigherMoments GapDefect ContactGapResource ContactGapSum

/-- The signed derivative cost of replacing an open gap by its right endpoint. -/
def gapSlopeResource (μ : ProbabilityMeasure ℝ) (f : ℝ → ℝ) (g : Gap μ) : ℝ :=
  -tau μ g.val.2 * (∫ t in g.val.1..g.val.2, (t - g.val.1) * deriv f t)

theorem gapSlopeResource_le_integral (μ : ProbabilityMeasure ℝ)
    (h : StandardizedLaw μ) (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (g : Gap μ) (hb : 0 ≤ f g.val.2) :
    gapSlopeResource μ f g ≤ ∫ t in Ioo g.val.1 g.val.2, tau μ t * f t := by
  have hi := GapIntegration.local_C1_integral f univ isOpen_univ hf.contDiffOn
    g.val.1 g.val.2 g.property.2.2.1 (subset_univ _)
  have hm := congrArg (fun z : ℝ => tau μ g.val.2 * z) hi
  have hp : 0 ≤ tau μ g.val.2 * ((g.val.2 - g.val.1) * f g.val.2) :=
    mul_nonneg (tau_nonneg μ h _) (mul_nonneg (by linarith [g.property.2.2.1]) hb)
  rw [GapIntegration.integral_tau_mul_on_gap μ g.val.1 g.val.2 g.property]
  unfold gapSlopeResource
  nlinarith only [hm, hp]

/-- Positivity is needed only for the weighted function and for the actual
right endpoints. In particular a bounded-hull function may be negative
outside that hull, where the original zero-bias density vanishes. -/
theorem tsum_gapSlopeResource_le_integral (μ : ProbabilityMeasure ℝ)
    (h : StandardizedLaw μ) (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hfi : Integrable (fun t : ℝ => tau μ t * f t))
    (hf0 : ∀ t : ℝ, 0 ≤ tau μ t * f t)
    (hb : ∀ g : Gap μ, 0 ≤ f g.val.2)
    (hs : Summable (gapSlopeResource μ f)) :
    (∑' g : Gap μ, gapSlopeResource μ f g) ≤ ∫ t : ℝ, tau μ t * f t := by
  have hd : Pairwise (fun g k : Gap μ =>
      Disjoint (Ioo g.val.1 g.val.2) (Ioo k.val.1 k.val.2)) := by
    intro g k hne
    exact SupportGaps.gapSet_pairwiseDisjoint (μ : Measure ℝ).support
      g.property k.property (fun heq => hne (Subtype.ext heq))
  have hsum := hasSum_integral_iUnion (fun g : Gap μ => measurableSet_Ioo) hd
    hfi.integrableOn
  calc
    (∑' g : Gap μ, gapSlopeResource μ f g) ≤
        ∑' g : Gap μ, ∫ t in Ioo g.val.1 g.val.2, tau μ t * f t :=
      hs.tsum_le_tsum (fun g => gapSlopeResource_le_integral μ h f hf g (hb g))
        hsum.summable
    _ = ∫ t in gapUnion μ, tau μ t * f t := hsum.tsum_eq
    _ ≤ ∫ t : ℝ, tau μ t * f t :=
      setIntegral_le_integral hfi (Filter.Eventually.of_forall hf0)

theorem contDiff_momentSlope (μ : ProbabilityMeasure ℝ) :
    ContDiff ℝ 1 (ContactVariation.momentSlope μ) := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun x => (ContactPolynomial.hasDerivAt_momentSlope μ x).differentiableAt, ?_⟩
  have hd : deriv (ContactVariation.momentSlope μ) = fun x : ℝ =>
      3 * x * |x| - 3 * thirdAbsoluteMoment μ * x -
        3 * SignedMoment.signedSecondMoment μ :=
    funext fun x => (ContactPolynomial.hasDerivAt_momentSlope μ x).deriv
  rw [hd]
  fun_prop

theorem momentSlope_resource_eq (μ : ProbabilityMeasure ℝ) (B : ℝ) (g : Gap μ) :
    gapSlopeResource μ (fun t => ContactVariation.momentSlope μ t + B) g =
      (3 / 2 : ℝ) * SignedMoment.signedSecondMoment μ * Jg μ g +
        3 * thirdAbsoluteMoment μ * J1g μ g - 3 * J2g μ g := by
  have hd : deriv (fun t => ContactVariation.momentSlope μ t + B) = fun t : ℝ =>
      3 * t * |t| - 3 * thirdAbsoluteMoment μ * t -
        3 * SignedMoment.signedSecondMoment μ :=
    funext fun t => ((ContactPolynomial.hasDerivAt_momentSlope μ t).add_const B).deriv
  have hf : (fun t : ℝ => (t - g.val.1) *
      (3 * t * |t| - 3 * thirdAbsoluteMoment μ * t -
        3 * SignedMoment.signedSecondMoment μ)) =
      (fun t : ℝ => 3 * ((t - g.val.1) * t * |t|) -
        (3 * thirdAbsoluteMoment μ) * ((t - g.val.1) * t) -
        (3 * SignedMoment.signedSecondMoment μ) * (t - g.val.1)) := by
    funext t
    ring
  have h0 := (intervalIntegrable_gap0 g.val.1 g.val.2).const_mul
    (3 * SignedMoment.signedSecondMoment μ)
  have h1 := (intervalIntegrable_gap1 g.val.1 g.val.2).const_mul
    (3 * thirdAbsoluteMoment μ)
  have h2 := (intervalIntegrable_gap2 g.val.1 g.val.2).const_mul (3 : ℝ)
  unfold gapSlopeResource
  rw [hd, hf, intervalIntegral.integral_sub (h2.sub h1) h0,
    intervalIntegral.integral_sub h2 h1, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, integral_gap0]
  unfold Jg J1g J2g gapWeight
  ring

theorem hasSum_momentSlope_resource (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (R B : ℝ) (hR : 0 ≤ R)
    (hs : (μ : Measure ℝ).support ⊆ Icc (-R) R) :
    HasSum (gapSlopeResource μ (fun t => ContactVariation.momentSlope μ t + B))
      ((3 / 2 : ℝ) * SignedMoment.signedSecondMoment μ * actualJ μ +
        3 * thirdAbsoluteMoment μ * actualJ1 μ - 3 * actualJ2 μ) := by
  have hsum := (((gapWeight_summable μ h).hasSum.mul_left
    ((3 / 2 : ℝ) * SignedMoment.signedSecondMoment μ)).add
    ((summable_J1g μ h R hs).hasSum.mul_left (3 * thirdAbsoluteMoment μ))).sub
    ((summable_J2g μ h R hR hs).hasSum.mul_left (3 : ℝ))
  convert hsum using 1
  · funext g
    exact momentSlope_resource_eq μ B g
  · rfl

theorem integrable_tau_momentSlope_add (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (h4 : Integrable (fun x : ℝ => x ^ 4) (μ : Measure ℝ))
    (h5 : Integrable (fun x : ℝ => |x| ^ 5) (μ : Measure ℝ)) (B : ℝ) :
    Integrable (fun t : ℝ => tau μ t * (ContactVariation.momentSlope μ t + B)) := by
  have h3 := integrable_abs_pow_tau μ h 3 h5
  have hsub := (h3.sub ((integrable_square_tau μ h h4).const_mul
    ((3 / 2 : ℝ) * thirdAbsoluteMoment μ))).sub
    ((integrable_mul_tau μ h).const_mul (3 * SignedMoment.signedSecondMoment μ))
  have hi := hsub.add ((integrable_tau μ h).const_mul (thirdAbsoluteMoment μ / 2 + B))
  convert hi using 1
  funext t
  unfold ContactVariation.momentSlope
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

theorem baseBracket_le_of_momentSlope_lower (μ : ProbabilityMeasure ℝ)
    (h : StandardizedLaw μ) (R B : ℝ) (hR : 0 ≤ R)
    (hs : (μ : Measure ℝ).support ⊆ Icc (-R) R)
    (hq : ∀ t : ℝ, -B ≤ ContactVariation.momentSlope μ t) :
    RawResourceEnvelope.baseBracket μ ≤ B := by
  have h4 := ConservedResource.integrable_pow_of_bounded_support μ R hs 4
  have h5 := ConservedResource.integrable_abs_pow_of_bounded_support μ R hs 5
  have hsum := hasSum_momentSlope_resource μ h R B hR hs
  have hle := tsum_gapSlopeResource_le_integral μ h
    (fun t => ContactVariation.momentSlope μ t + B)
    ((contDiff_momentSlope μ).add contDiff_const)
    (integrable_tau_momentSlope_add μ h h4 h5 B)
    (fun t => mul_nonneg (tau_nonneg μ h t) (by linarith [hq t]))
    (fun g => by linarith [hq g.val.2]) hsum.summable
  rw [hsum.tsum_eq] at hle
  have hqi := integrable_tau_momentSlope_add μ h h4 h5 0
  simp only [add_zero] at hqi
  have heq : (fun t => tau μ t * (ContactVariation.momentSlope μ t + B)) =
      (fun t => tau μ t * ContactVariation.momentSlope μ t + B * tau μ t) := by
    funext t
    ring
  rw [heq, integral_add hqi ((integrable_tau μ h).const_mul B),
    ContactZeroBiasMoment.integral_polynomialWeight μ h h4 h5,
    integral_const_mul, integral_tau μ h, mul_one] at hle
  unfold RawResourceEnvelope.baseBracket
  linarith only [hle]

/-- A global rational square certificate, with the actual signed beta. -/
theorem momentSlope_ge_neg_nine_eighths (μ : ProbabilityMeasure ℝ)
    (hρ1 : 1 ≤ thirdAbsoluteMoment μ) (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10)
    (hβ : |SignedMoment.signedSecondMoment μ| ≤ (127 : ℝ) / 500) (t : ℝ) :
    -(9 / 8 : ℝ) ≤ ContactVariation.momentSlope μ t := by
  have ht : 0 ≤ |t| := abs_nonneg t
  have hpρ := mul_le_mul_of_nonneg_right hρ (sq_nonneg t)
  have hpβ : SignedMoment.signedSecondMoment μ * t ≤ (127 / 500 : ℝ) * |t| := by
    calc
      _ ≤ |SignedMoment.signedSecondMoment μ * t| := le_abs_self _
      _ = |SignedMoment.signedSecondMoment μ| * |t| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right hβ ht
  have hsq : 0 ≤ (|t| - 13 / 10) ^ 2 * (|t| + 19 / 20) :=
    mul_nonneg (sq_nonneg _) (by positivity)
  have hid : |t| ^ 3 - (33 / 20 : ℝ) * |t| ^ 2 - (381 / 500 : ℝ) * |t| + 13 / 8 =
      (|t| - 13 / 10) ^ 2 * (|t| + 19 / 20) + (9 / 500 : ℝ) * |t| + 39 / 2000 := by
    ring
  unfold ContactVariation.momentSlope
  rw [sq_abs] at hid
  nlinarith only [hpρ, hpβ, hρ1, hsq, hid, ht]

theorem baseBracket_le_nine_eighths (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hs : (μ : Measure ℝ).support ⊆ Icc (-(12 / 5 : ℝ)) (12 / 5))
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) :
    RawResourceEnvelope.baseBracket μ ≤ (9 : ℝ) / 8 := by
  apply baseBracket_le_of_momentSlope_lower μ h (12 / 5) (9 / 8) (by norm_num) hs
  exact momentSlope_ge_neg_nine_eighths μ (Extremizer.thirdAbsoluteMoment_ge_one μ h) hρ
    (SignedMoment.abs_signed_lt_127_500 μ h hρ).le

theorem square_resource_eq (μ : ProbabilityMeasure ℝ) (B s : ℝ) (g : Gap μ) :
    gapSlopeResource μ (fun t : ℝ => B + s * t ^ 2) g = -2 * s * J1g μ g := by
  have hd : deriv (fun t : ℝ => B + s * t ^ 2) = fun t : ℝ => 2 * s * t := by
    funext t
    have hdt := (((hasDerivAt_id t).fun_pow 2).const_mul s).const_add B
    convert hdt.deriv using 1 <;> simp only [id_eq] <;> ring
  have heq : (fun t : ℝ => (t - g.val.1) * (2 * s * t)) =
      (fun t : ℝ => (2 * s) * ((t - g.val.1) * t)) := by
    funext t
    ring
  unfold gapSlopeResource
  rw [hd, heq, intervalIntegral.integral_const_mul]
  unfold J1g
  ring

theorem hasSum_square_resource (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (R B s : ℝ) (hs : (μ : Measure ℝ).support ⊆ Icc (-R) R) :
    HasSum (gapSlopeResource μ (fun t : ℝ => B + s * t ^ 2))
      (-2 * s * actualJ1 μ) := by
  convert (summable_J1g μ h R hs).hasSum.mul_left (-2 * s) using 1
  · funext g
    exact square_resource_eq μ B s g
  · rfl

/-- The replacement square moment is nonnegative and at most the square
of the already acquired support radius, including a genuine central gap. -/
theorem replacement_square_bounds (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (R : ℝ) (hR : 0 ≤ R) (hs : (μ : Measure ℝ).support ⊆ Icc (-R) R) :
    0 ≤ ContactZeroBiasMoment.fourthMoment μ / 3 + 2 * actualJ1 μ ∧
      ContactZeroBiasMoment.fourthMoment μ / 3 + 2 * actualJ1 μ ≤ R ^ 2 := by
  have h4 := ConservedResource.integrable_pow_of_bounded_support μ R hs 4
  have hsq := integrable_square_tau μ h h4
  have hsq' : Integrable (fun t : ℝ => tau μ t * (0 + 1 * t ^ 2)) := by
    convert hsq using 1
    funext t
    ring
  have hlowSum := hasSum_square_resource μ h R 0 1 hs
  have hlo := tsum_gapSlopeResource_le_integral μ h (fun t : ℝ => 0 + 1 * t ^ 2)
    (by fun_prop) hsq' (fun t => by simpa using mul_nonneg (tau_nonneg μ h t) (sq_nonneg t))
    (fun g => by positivity) hlowSum.summable
  rw [hlowSum.tsum_eq] at hlo
  have hlowInt : (∫ t : ℝ, tau μ t * (0 + 1 * t ^ 2)) =
      ContactZeroBiasMoment.fourthMoment μ / 3 := by
    change (∫ t : ℝ, tau μ t * (0 + 1 * t ^ 2)) = (∫ x : ℝ, x ^ 4 ∂(μ : Measure ℝ)) / 3
    calc
      _ = ∫ t : ℝ, t ^ 2 * tau μ t := integral_congr_ae
        (Filter.Eventually.of_forall fun t => by ring)
      _ = _ := integral_square_tau μ h h4
  rw [hlowInt] at hlo
  have hupperSum := hasSum_square_resource μ h R (R ^ 2) (-1) hs
  have hupperInt : Integrable (fun t : ℝ => tau μ t * (R ^ 2 + (-1) * t ^ 2)) := by
    convert ((integrable_tau μ h).const_mul (R ^ 2)).sub hsq using 1
    funext t
    simp only [Pi.sub_apply]
    ring
  have hnon : ∀ t : ℝ, 0 ≤ tau μ t * (R ^ 2 + (-1) * t ^ 2) := by
    intro t
    by_cases ht : t ∈ Icc (-R) R
    · have ht2 : t ^ 2 ≤ R ^ 2 := by
        have hp := mul_nonneg (sub_nonneg.mpr ht.2) (show 0 ≤ R + t by linarith [ht.1])
        nlinarith only [hp]
      exact mul_nonneg (tau_nonneg μ h t) (by linarith)
    · have hout : t < -R ∨ R < t := by
        by_cases hl : -R ≤ t
        · exact Or.inr (lt_of_not_ge fun hu => ht ⟨hl, hu⟩)
        · exact Or.inl (lt_of_not_ge hl)
      rw [tau_zero_outside_interval μ h (-R) R t hs hout, zero_mul]
  have hhi := tsum_gapSlopeResource_le_integral μ h
    (fun t : ℝ => R ^ 2 + (-1) * t ^ 2) (by fun_prop) hupperInt hnon
    (fun g => by
      have hb := hs g.property.2.1
      have hp := mul_nonneg (sub_nonneg.mpr hb.2)
        (show 0 ≤ R + g.val.2 by linarith [hb.1])
      nlinarith only [hp]) hupperSum.summable
  rw [hupperSum.tsum_eq] at hhi
  have heq : (fun t : ℝ => tau μ t * (R ^ 2 + (-1) * t ^ 2)) =
      (fun t : ℝ => R ^ 2 * tau μ t - t ^ 2 * tau μ t) := by
    funext t
    ring
  rw [heq, integral_sub ((integrable_tau μ h).const_mul (R ^ 2)) hsq,
    integral_const_mul, integral_tau μ h, mul_one, integral_square_tau μ h h4] at hhi
  unfold ContactZeroBiasMoment.fourthMoment at hlo ⊢
  constructor <;> nlinarith only [hlo, hhi]

theorem gaussianLinearGap_bounds (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (R : ℝ) (hR : 0 ≤ R) (hs : (μ : Measure ℝ).support ⊆ Icc (-R) R) :
    -(1 / 2 : ℝ) ≤ actualJ1 μ + (ContactZeroBiasMoment.fourthMoment μ - 3) / 6 ∧
      actualJ1 μ + (ContactZeroBiasMoment.fourthMoment μ - 3) / 6 ≤ (R ^ 2 - 1) / 2 := by
  have hb := replacement_square_bounds μ h R hR hs
  constructor <;> linarith

theorem gaussianLinearGap_low_moment_bounds (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hs : (μ : Measure ℝ).support ⊆ Icc (-(12 / 5 : ℝ)) (12 / 5)) :
    -(1 / 2 : ℝ) ≤ actualJ1 μ + (ContactZeroBiasMoment.fourthMoment μ - 3) / 6 ∧
      actualJ1 μ + (ContactZeroBiasMoment.fourthMoment μ - 3) / 6 ≤ (119 : ℝ) / 50 := by
  have hb := gaussianLinearGap_bounds μ h (12 / 5) (by norm_num) hs
  norm_num at hb
  exact hb

/-- A joint pointwise upper bound is integrated through the same actual
gap replacement. Neither C nor z is assumed nonnegative. -/
theorem joint_base_gaussian_le_of_pointwise (μ : ProbabilityMeasure ℝ)
    (h : StandardizedLaw μ) (R : ℝ) (hR : 0 ≤ R)
    (hs : (μ : Measure ℝ).support ⊆ Icc (-R) R) (C z B : ℝ)
    (hp : ∀ t ∈ Icc (-R) R,
      -C * ContactVariation.momentSlope μ t + z * (t ^ 2 - 1) / 2 ≤ B) :
    C * RawResourceEnvelope.baseBracket μ +
      z * (actualJ1 μ + (ContactZeroBiasMoment.fourthMoment μ - 3) / 6) ≤ B := by
  let f : ℝ → ℝ := fun t =>
    B + C * ContactVariation.momentSlope μ t - (z / 2) * (t ^ 2 - 1)
  have hf : ContDiff ℝ 1 f :=
    (contDiff_const.add (contDiff_const.mul (contDiff_momentSlope μ))).sub
      (contDiff_const.mul ((contDiff_id.pow 2).sub contDiff_const))
  have h4 := ConservedResource.integrable_pow_of_bounded_support μ R hs 4
  have h5 := ConservedResource.integrable_abs_pow_of_bounded_support μ R hs 5
  have hqi := integrable_tau_momentSlope_add μ h h4 h5 0
  simp only [add_zero] at hqi
  have hsq := integrable_square_tau μ h h4
  have hfi : Integrable (fun t : ℝ => tau μ t * f t) := by
    convert (((integrable_tau μ h).const_mul B).add (hqi.const_mul C)).sub
      ((hsq.sub (integrable_tau μ h)).const_mul (z / 2)) using 1
    funext t
    simp only [Pi.add_apply, Pi.sub_apply]
    dsimp [f]
    ring
  have hnon : ∀ t : ℝ, 0 ≤ tau μ t * f t := by
    intro t
    by_cases ht : t ∈ Icc (-R) R
    · exact mul_nonneg (tau_nonneg μ h t) (by dsimp [f]; linarith [hp t ht])
    · have hout : t < -R ∨ R < t := by
        by_cases hl : -R ≤ t
        · exact Or.inr (lt_of_not_ge fun hu => ht ⟨hl, hu⟩)
        · exact Or.inl (lt_of_not_ge hl)
      rw [tau_zero_outside_interval μ h (-R) R t hs hout, zero_mul]
  have hendpoint : ∀ g : Gap μ, 0 ≤ f g.val.2 := by
    intro g
    dsimp [f]
    linarith [hp g.val.2 (hs g.property.2.1)]
  have hres : ∀ g : Gap μ, gapSlopeResource μ f g =
      C * gapSlopeResource μ (fun t => ContactVariation.momentSlope μ t + 0) g +
        z * J1g μ g := by
    intro g
    have hd : deriv f = fun t : ℝ => C *
        (3 * t * |t| - 3 * thirdAbsoluteMoment μ * t -
          3 * SignedMoment.signedSecondMoment μ) - z * t := by
      funext t
      have hdt := (((ContactPolynomial.hasDerivAt_momentSlope μ t).const_mul C).const_add B).sub
        ((((hasDerivAt_id t).fun_pow 2).sub_const 1).const_mul (z / 2))
      have hdt' : HasDerivAt f (C *
          (3 * t * |t| - 3 * thirdAbsoluteMoment μ * t -
            3 * SignedMoment.signedSecondMoment μ) - z * t) t := by
        convert hdt using 1
        · rfl
        · norm_num [id_eq]
          ring
      exact hdt'.deriv
    have hd0 : deriv (fun t => ContactVariation.momentSlope μ t + 0) = fun t : ℝ =>
        3 * t * |t| - 3 * thirdAbsoluteMoment μ * t -
          3 * SignedMoment.signedSecondMoment μ :=
      funext fun t => ((ContactPolynomial.hasDerivAt_momentSlope μ t).add_const 0).deriv
    have heq : (fun t : ℝ => (t - g.val.1) * (C *
        (3 * t * |t| - 3 * thirdAbsoluteMoment μ * t -
          3 * SignedMoment.signedSecondMoment μ) - z * t)) =
        (fun t : ℝ => C * ((t - g.val.1) *
          (3 * t * |t| - 3 * thirdAbsoluteMoment μ * t -
            3 * SignedMoment.signedSecondMoment μ)) - z * ((t - g.val.1) * t)) := by
      funext t
      ring
    have hdc : Continuous (fun t : ℝ => (t - g.val.1) *
        (3 * t * |t| - 3 * thirdAbsoluteMoment μ * t -
          3 * SignedMoment.signedSecondMoment μ)) := by fun_prop
    unfold gapSlopeResource
    rw [hd, hd0, heq, intervalIntegral.integral_sub
      ((hdc.intervalIntegrable _ _).const_mul C)
      ((intervalIntegrable_gap1 _ _).const_mul z),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    unfold J1g
    ring
  have hsumq := hasSum_momentSlope_resource μ h R 0 hR hs
  have hsum : HasSum (gapSlopeResource μ f)
      (C * ((3 / 2 : ℝ) * SignedMoment.signedSecondMoment μ * actualJ μ +
        3 * thirdAbsoluteMoment μ * actualJ1 μ - 3 * actualJ2 μ) + z * actualJ1 μ) := by
    convert (hsumq.mul_left C).add ((summable_J1g μ h R hs).hasSum.mul_left z) using 1
    · funext g
      exact hres g
    · rfl
  have hle := tsum_gapSlopeResource_le_integral μ h f hf hfi hnon hendpoint hsum.summable
  rw [hsum.tsum_eq] at hle
  have heq : (fun t : ℝ => tau μ t * f t) = fun t : ℝ =>
      B * tau μ t + C * (tau μ t * ContactVariation.momentSlope μ t) -
        (z / 2) * (t ^ 2 * tau μ t - tau μ t) := by
    funext t
    dsimp [f]
    ring
  have hfirst : Integrable (fun t : ℝ =>
      B * tau μ t + C * (tau μ t * ContactVariation.momentSlope μ t)) :=
    ((integrable_tau μ h).const_mul B).add (hqi.const_mul C)
  have hsecond : Integrable (fun t : ℝ =>
      (z / 2) * (t ^ 2 * tau μ t - tau μ t)) :=
    (hsq.sub (integrable_tau μ h)).const_mul (z / 2)
  rw [heq, integral_sub hfirst hsecond,
    integral_add ((integrable_tau μ h).const_mul B) (hqi.const_mul C),
    integral_const_mul, integral_const_mul, integral_const_mul,
    integral_sub hsq (integrable_tau μ h), integral_square_tau μ h h4,
    ContactZeroBiasMoment.integral_polynomialWeight μ h h4 h5, integral_tau μ h] at hle
  unfold RawResourceEnvelope.baseBracket ContactZeroBiasMoment.fourthMoment
  nlinarith only [hle]

end BerryEsseen.RawGapProjectionBounds

#print axioms BerryEsseen.RawGapProjectionBounds.tsum_gapSlopeResource_le_integral
#print axioms BerryEsseen.RawGapProjectionBounds.baseBracket_le_nine_eighths
#print axioms BerryEsseen.RawGapProjectionBounds.replacement_square_bounds
#print axioms BerryEsseen.RawGapProjectionBounds.gaussianLinearGap_low_moment_bounds
#print axioms BerryEsseen.RawGapProjectionBounds.joint_base_gaussian_le_of_pointwise
