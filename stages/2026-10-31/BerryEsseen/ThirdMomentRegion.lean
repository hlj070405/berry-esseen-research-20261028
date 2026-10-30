module

public import BerryEsseen.SignedMoment
public import BerryEsseen.ZeroBias
public import BerryEsseen.CharacteristicExpansion

@[expose] public section

/-! 2026-10-29: the actual signed-third/absolute-third moment region for an
arbitrary standardized law with finite absolute third moment. This is the
existing moment inequality used by Shevtsova, arXiv:1301.2783v3; no novelty
is claimed. The proof integrates nonnegative half-cubic witnesses and then
eliminates the first absolute and signed second moments. No support or
higher-moment restriction is imposed. -/

noncomputable section

open MeasureTheory

namespace BerryEsseen.ThirdMomentRegion

open SignedMoment

/-- Both existing signed-third APIs denote the same actual integral. -/
theorem gamma_eq_characteristicExpansion (μ : ProbabilityMeasure ℝ) :
    ZeroBias.gamma μ = CharacteristicExpansion.gamma μ := rfl

theorem abs_gamma_le_third (μ : ProbabilityMeasure ℝ) :
    |ZeroBias.gamma μ| ≤ thirdAbsoluteMoment μ := by
  change |∫ x : ℝ, x ^ 3 ∂(μ : Measure ℝ)| ≤ ∫ x : ℝ, |x| ^ 3 ∂(μ : Measure ℝ)
  calc
    _ ≤ ∫ x : ℝ, |x ^ 3| ∂(μ : Measure ℝ) := abs_integral_le_integral_abs
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall fun x => abs_pow x 3)

/-- Twice the witness `Y * (a*Y-(1+s*β))^2`, where
`Y=(|x|+s*x)/2` and `s=1` or `s=-1`. Its expanded form needs only moments
of degree at most three. -/
def halfCubicWitness (a β s x : ℝ) : ℝ :=
  a ^ 2 * (|x| ^ 3 + s * x ^ 3) -
    (2 * a * (1 + s * β)) * (x ^ 2 + s * (x * |x|)) +
    (1 + s * β) ^ 2 * (|x| + s * x)

lemma halfCubicWitness_nonneg (a β s x : ℝ) (hs : s = 1 ∨ s = -1) :
    0 ≤ halfCubicWitness a β s x := by
  rcases hs with rfl | rfl
  · rcases le_total 0 x with hx | hx
    · have heq : halfCubicWitness a β 1 x = 2 * x * (a * x - (1 + β)) ^ 2 := by
        simp only [halfCubicWitness, abs_of_nonneg hx]
        ring
      rw [heq]
      exact mul_nonneg (mul_nonneg (by norm_num) hx) (sq_nonneg _)
    · have heq : halfCubicWitness a β 1 x = 0 := by
        simp only [halfCubicWitness, abs_of_nonpos hx]
        ring
      rw [heq]
  · rcases le_total 0 x with hx | hx
    · have heq : halfCubicWitness a β (-1) x = 0 := by
        simp only [halfCubicWitness, abs_of_nonneg hx]
        ring
      rw [heq]
    · have heq : halfCubicWitness a β (-1) x =
          2 * (-x) * (a * (-x) - (1 - β)) ^ 2 := by
        simp only [halfCubicWitness, abs_of_nonpos hx]
        ring
      rw [heq]
      exact mul_nonneg (mul_nonneg (by norm_num) (neg_nonneg.mpr hx)) (sq_nonneg _)

lemma integrable_halfCubicWitness (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (a β s : ℝ) : Integrable (halfCubicWitness a β s) (μ : Measure ℝ) := by
  have h3 : Integrable (fun x : ℝ => |x| ^ 3 + s * x ^ 3) (μ : Measure ℝ) :=
    h.integrable_cube.add ((ZeroBias.integrable_signed_cube μ h).const_mul s)
  have h2 : Integrable (fun x : ℝ => x ^ 2 + s * (x * |x|)) (μ : Measure ℝ) :=
    h.integrable_square.add ((integrable_signedSecondMoment μ h).const_mul s)
  have h1 : Integrable (fun x : ℝ => |x| + s * x) (μ : Measure ℝ) :=
    (integrable_firstAbsoluteMoment μ h).add (h.integrable_mean.const_mul s)
  exact ((h3.const_mul (a ^ 2)).sub (h2.const_mul (2 * a * (1 + s * β)))).add
    (h1.const_mul ((1 + s * β) ^ 2))

lemma integral_halfCubicWitness (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (s : ℝ) :
    (∫ x, halfCubicWitness (firstAbsoluteMoment μ) (signedSecondMoment μ) s x
      ∂(μ : Measure ℝ)) =
    firstAbsoluteMoment μ *
      (firstAbsoluteMoment μ * (thirdAbsoluteMoment μ + s * ZeroBias.gamma μ) -
        (1 + s * signedSecondMoment μ) ^ 2) := by
  let a := firstAbsoluteMoment μ
  let β := signedSecondMoment μ
  have h3a := h.integrable_cube
  have h3b := (ZeroBias.integrable_signed_cube μ h).const_mul s
  have h2a := h.integrable_square
  have h2b := (integrable_signedSecondMoment μ h).const_mul s
  have h1a := integrable_firstAbsoluteMoment μ h
  have h1b := h.integrable_mean.const_mul s
  have hA : Integrable (fun x : ℝ => a ^ 2 * (|x| ^ 3 + s * x ^ 3))
      (μ : Measure ℝ) := (h3a.add h3b).const_mul _
  have hB : Integrable (fun x : ℝ => (2 * a * (1 + s * β)) *
      (x ^ 2 + s * (x * |x|))) (μ : Measure ℝ) := (h2a.add h2b).const_mul _
  have hC : Integrable (fun x : ℝ => (1 + s * β) ^ 2 * (|x| + s * x))
      (μ : Measure ℝ) := (h1a.add h1b).const_mul _
  have hAB : Integrable (fun x : ℝ => a ^ 2 * (|x| ^ 3 + s * x ^ 3) -
      (2 * a * (1 + s * β)) * (x ^ 2 + s * (x * |x|))) (μ : Measure ℝ) := hA.sub hB
  change (∫ x, halfCubicWitness a β s x ∂(μ : Measure ℝ)) =
    a * (a * (thirdAbsoluteMoment μ + s * ZeroBias.gamma μ) - (1 + s * β) ^ 2)
  unfold halfCubicWitness
  rw [integral_add hAB hC, integral_sub hA hB,
    integral_const_mul, integral_const_mul, integral_const_mul,
    integral_add h3a h3b, integral_add h2a h2b, integral_add h1a h1b,
    integral_const_mul, integral_const_mul, integral_const_mul,
    h.second_moment_one, h.mean_zero]
  change a ^ 2 * (thirdAbsoluteMoment μ + s * ZeroBias.gamma μ) -
      (2 * a * (1 + s * β)) * (1 + s * β) + (1 + s * β) ^ 2 * (a + s * 0) = _
  ring

/-- The two half-axis Cauchy inequalities, proved by actual cubic witnesses. -/
theorem half_cubic_bound (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (s : ℝ) (hs : s = 1 ∨ s = -1) :
    (1 + s * signedSecondMoment μ) ^ 2 ≤
      firstAbsoluteMoment μ * (thirdAbsoluteMoment μ + s * ZeroBias.gamma μ) := by
  have ha := firstAbsoluteMoment_pos μ h
  have hn : 0 ≤ firstAbsoluteMoment μ *
      (firstAbsoluteMoment μ * (thirdAbsoluteMoment μ + s * ZeroBias.gamma μ) -
        (1 + s * signedSecondMoment μ) ^ 2) := by
    rw [← integral_halfCubicWitness μ h s]
    exact integral_nonneg fun x => halfCubicWitness_nonneg _ _ s x hs
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left ha).mp hn)

theorem positive_half_cubic_bound (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    (1 + signedSecondMoment μ) ^ 2 ≤
      firstAbsoluteMoment μ * (thirdAbsoluteMoment μ + ZeroBias.gamma μ) := by
  simpa only [one_mul] using half_cubic_bound μ h 1 (Or.inl rfl)

theorem negative_half_cubic_bound (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    (1 - signedSecondMoment μ) ^ 2 ≤
      firstAbsoluteMoment μ * (thirdAbsoluteMoment μ - ZeroBias.gamma μ) := by
  simpa only [neg_one_mul, ← sub_eq_add_neg] using
    half_cubic_bound μ h (-1) (Or.inr rfl)

/-- Polynomial elimination of the two auxiliary moments. -/
lemma region_of_auxiliary (a β γ ρ : ℝ) (ha : 0 < a)
    (h2 : a ^ 2 + β ^ 2 ≤ 1) (h3 : 1 + β ^ 2 ≤ a * ρ)
    (hplus : (1 + β) ^ 2 ≤ a * (ρ + γ))
    (hminus : (1 - β) ^ 2 ≤ a * (ρ - γ))
    (habs : |γ| ≤ ρ) :
    (γ ^ 2 + 2) ^ 2 ≤ ρ ^ 2 * (γ ^ 2 + 4) := by
  let u := 1 - β ^ 2
  let d := ρ ^ 2 - γ ^ 2
  have hu : 0 < u := by dsimp [u]; nlinarith [sq_pos_of_pos ha]
  have hu1 : u ≤ 1 := by dsimp [u]; nlinarith [sq_nonneg β]
  have hau : a ^ 2 ≤ u := by dsimp [u]; linarith
  have hr : 0 ≤ ρ := (abs_nonneg γ).trans habs
  have hd : 0 ≤ d := by
    dsimp [d]
    have hsq := (sq_le_sq₀ (abs_nonneg γ) hr).mpr habs
    simpa only [sq_abs, sub_nonneg] using hsq
  have hprod := mul_le_mul hplus hminus (sq_nonneg (1 - β))
    ((sq_nonneg (1 + β)).trans hplus)
  have hprod' : u ^ 2 ≤ a ^ 2 * d := by
    dsimp [u, d]
    nlinarith only [hprod]
  have hud : u ≤ d := by
    have hw := mul_le_mul_of_nonneg_right hau hd
    have hp : 0 ≤ u * (d - u) := by nlinarith only [hprod', hw]
    exact le_of_sub_nonneg ((mul_nonneg_iff_of_pos_left hu).mp hp)
  have hleft : 0 ≤ 2 - u := by linarith
  have hright : 0 ≤ a * ρ := mul_nonneg ha.le hr
  have hsq := (sq_le_sq₀ hleft hright).mpr (show 2 - u ≤ a * ρ by dsimp [u]; linarith)
  have hweighted := mul_le_mul_of_nonneg_right hau (sq_nonneg ρ)
  have hbase : 4 ≤ u * (ρ ^ 2 + 4 - u) := by nlinarith only [hsq, hweighted]
  have hfinal : 4 ≤ d * (γ ^ 2 + 4) := by
    by_cases hd1 : 1 ≤ d
    · have hw := mul_le_mul_of_nonneg_right hd1 (show 0 ≤ γ ^ 2 + 4 by positivity)
      nlinarith only [hw, sq_nonneg γ]
    · have hd1' : d ≤ 1 := le_of_lt (lt_of_not_ge hd1)
      have hc : 0 ≤ ρ ^ 2 + 4 - d - u := by nlinarith [sq_nonneg ρ]
      have hp := mul_nonneg (sub_nonneg.mpr hud) hc
      dsimp [d] at hp ⊢
      nlinarith only [hbase, hp]
  dsimp [d] at hfinal
  nlinarith only [hfinal]

/-- The sharp necessary signed-third/absolute-third feasibility condition.
Here `γ` is the actual signed third moment, not `E[X*|X|]`. -/
theorem signed_third_region (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    (ZeroBias.gamma μ ^ 2 + 2) ^ 2 ≤
      thirdAbsoluteMoment μ ^ 2 * (ZeroBias.gamma μ ^ 2 + 4) :=
  region_of_auxiliary _ _ _ _ (firstAbsoluteMoment_pos μ h)
    (first_sq_add_signed_sq_le_one μ h) (first_mul_third_ge_one_add_signed_sq μ h)
    (positive_half_cubic_bound μ h) (negative_half_cubic_bound μ h) (abs_gamma_le_third μ)

/-- The equivalent nonnegative polynomial used in the small-index scalar domain. -/
theorem feasibility_polynomial_nonneg (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    0 ≤ thirdAbsoluteMoment μ ^ 2 * (ZeroBias.gamma μ ^ 2 + 4) -
      (ZeroBias.gamma μ ^ 2 + 2) ^ 2 :=
  sub_nonneg.mpr (signed_third_region μ h)

theorem one_le_third (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    1 ≤ thirdAbsoluteMoment μ := by
  have ha := firstAbsoluteMoment_pos μ h
  have h2 := first_sq_add_signed_sq_le_one μ h
  have h3 := first_mul_third_ge_one_add_signed_sq μ h
  have hr : 0 ≤ thirdAbsoluteMoment μ := integral_nonneg fun x =>
    pow_nonneg (abs_nonneg x) 3
  have ha1 : firstAbsoluteMoment μ ≤ 1 := by
    nlinarith [sq_nonneg (signedSecondMoment μ), sq_nonneg (firstAbsoluteMoment μ - 1)]
  have hw := mul_le_mul_of_nonneg_right ha1 hr
  nlinarith [sq_nonneg (signedSecondMoment μ)]

lemma square_le_root_of_region (γ ρ : ℝ) (hr : 0 ≤ ρ)
    (h : (γ ^ 2 + 2) ^ 2 ≤ ρ ^ 2 * (γ ^ 2 + 4)) :
    γ ^ 2 ≤ (ρ ^ 2 - 4 + ρ * Real.sqrt (ρ ^ 2 + 8)) / 2 := by
  let s := ρ * Real.sqrt (ρ ^ 2 + 8)
  have hs : 0 ≤ s := mul_nonneg hr (Real.sqrt_nonneg _)
  have hs2 : s ^ 2 = ρ ^ 2 * (ρ ^ 2 + 8) := by
    dsimp [s]
    rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ ρ ^ 2 + 8)]
  have hcomp : (2 * γ ^ 2 + 4 - ρ ^ 2) ^ 2 ≤ s ^ 2 := by
    rw [hs2]
    nlinarith only [h]
  have hle : 2 * γ ^ 2 + 4 - ρ ^ 2 ≤ s := by
    by_cases hx : 0 ≤ 2 * γ ^ 2 + 4 - ρ ^ 2
    · exact (sq_le_sq₀ hx hs).mp hcomp
    · exact (le_of_lt (lt_of_not_ge hx)).trans hs
  dsimp [s] at hle
  linarith

/-- The explicit upper root of the sharp feasibility polynomial. -/
theorem gamma_sq_le_root (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    ZeroBias.gamma μ ^ 2 ≤
      (thirdAbsoluteMoment μ ^ 2 - 4 + thirdAbsoluteMoment μ *
        Real.sqrt (thirdAbsoluteMoment μ ^ 2 + 8)) / 2 :=
  square_le_root_of_region _ _ (by linarith [one_le_third μ h]) (signed_third_region μ h)

theorem abs_gamma_le_root (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    |ZeroBias.gamma μ| ≤
      Real.sqrt ((thirdAbsoluteMoment μ ^ 2 - 4 + thirdAbsoluteMoment μ *
        Real.sqrt (thirdAbsoluteMoment μ ^ 2 + 8)) / 2) :=
  Real.abs_le_sqrt (gamma_sq_le_root μ h)

end BerryEsseen.ThirdMomentRegion

#print axioms BerryEsseen.ThirdMomentRegion.gamma_eq_characteristicExpansion
#print axioms BerryEsseen.ThirdMomentRegion.integrable_halfCubicWitness
#print axioms BerryEsseen.ThirdMomentRegion.integral_halfCubicWitness
#print axioms BerryEsseen.ThirdMomentRegion.positive_half_cubic_bound
#print axioms BerryEsseen.ThirdMomentRegion.negative_half_cubic_bound
#print axioms BerryEsseen.ThirdMomentRegion.signed_third_region
#print axioms BerryEsseen.ThirdMomentRegion.feasibility_polynomial_nonneg
#print axioms BerryEsseen.ThirdMomentRegion.one_le_third
#print axioms BerryEsseen.ThirdMomentRegion.abs_gamma_le_root
