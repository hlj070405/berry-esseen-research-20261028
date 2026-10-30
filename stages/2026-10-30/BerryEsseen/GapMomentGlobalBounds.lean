module

public import BerryEsseen.ConservedResource

@[expose] public section

/-! 2026-10-30: global first and second signed gap-moment bounds for the
complete countable family of actual support gaps. The second bound uses
the original fourth moment through the integrable zero-bias square moment.
Only open gaps are integrated, so atoms at their endpoints are retained. -/

noncomputable section

open MeasureTheory Set
open scoped BigOperators Interval

namespace BerryEsseen.GapMomentGlobalBounds

open ZeroBias ZeroBiasHigherMoments GapDefect ContactGapResource ContactGapSum SupportGaps

/-- The first actual signed gap moment is bounded by the actual physical
gap resource, with no finite-gap or central-gap hypothesis. -/
theorem abs_actualJ1_le_R_mul_actualJ_div_two (μ : ProbabilityMeasure ℝ)
    (h : StandardizedLaw μ) (R : ℝ) (hR : 0 ≤ R)
    (hbound : (μ : Measure ℝ).support ⊆ Icc (-R) R) :
    |actualJ1 μ| ≤ R * actualJ μ / 2 := by
  have hJ1 := summable_J1g μ h R hbound
  have hJ := (gapWeight_summable μ h).mul_left (R / 2)
  calc
    |actualJ1 μ| ≤ ∑' g : Gap μ, ‖J1g μ g‖ := by
      simpa only [actualJ1, Real.norm_eq_abs] using norm_tsum_le_tsum_norm hJ1.norm
    _ ≤ ∑' g : Gap μ, (R / 2) * gapWeight μ g := by
      apply hJ1.norm.tsum_le_tsum _ hJ
      intro g
      calc
        ‖J1g μ g‖ = |J1g μ g| := Real.norm_eq_abs _
        _ ≤ R * Jg μ g / 2 := abs_J1g_le μ h R hbound g
        _ = (R / 2) * gapWeight μ g := by unfold Jg; ring
    _ = R * actualJ μ / 2 := by rw [tsum_mul_left]; unfold actualJ; ring

theorem abs_actualJ1_le_R_mul_rho (μ : ProbabilityMeasure ℝ)
    (h : StandardizedLaw μ) (R : ℝ) (hR : 0 ≤ R)
    (hbound : (μ : Measure ℝ).support ⊆ Icc (-R) R) :
    |actualJ1 μ| ≤ R * thirdAbsoluteMoment μ := by
  have h1 := abs_actualJ1_le_R_mul_actualJ_div_two μ h R hR hbound
  have h2 := mul_le_mul_of_nonneg_left (actualJ_le_two_rho μ h) hR
  linarith

def gapSquareTauIntegral (μ : ProbabilityMeasure ℝ) (g : Gap μ) : ℝ :=
  ∫ t in Ioo g.val.1 g.val.2, t ^ 2 * tau μ t

lemma gapSquareTauIntegral_nonneg (μ : ProbabilityMeasure ℝ)
    (h : StandardizedLaw μ) (g : Gap μ) : 0 ≤ gapSquareTauIntegral μ g :=
  integral_nonneg fun t => mul_nonneg (sq_nonneg t) (tau_nonneg μ h t)

lemma gapSquareTauIntegral_eq (μ : ProbabilityMeasure ℝ) (g : Gap μ) :
    gapSquareTauIntegral μ g =
      tau μ g.val.2 * (∫ t in g.val.1..g.val.2, t ^ 2) := by
  rw [intervalIntegral.integral_of_le g.property.2.2.1.le,
    integral_Ioc_eq_integral_Ioo]
  unfold gapSquareTauIntegral
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro t ht
  dsimp only
  rw [tau_constant_on_openGap μ g.val.1 g.val.2 t
    (measure_gap_eq_zero (μ : Measure ℝ) g.val g.property) ht.1 ht.2.le]
  ring

/-- Each actual gap consumes only its own zero-bias square-moment mass.
The width factor is at most `2 * R` on the bounded original support. -/
theorem abs_J2g_le_two_R_mul_gapSquareTauIntegral (μ : ProbabilityMeasure ℝ)
    (h : StandardizedLaw μ) (R : ℝ) (hR : 0 ≤ R)
    (hbound : (μ : Measure ℝ).support ⊆ Icc (-R) R) (g : Gap μ) :
    |J2g μ g| ≤ (2 * R) * gapSquareTauIntegral μ g := by
  let a := g.val.1
  let b := g.val.2
  have hab : a ≤ b := g.property.2.2.1.le
  have hd : IntervalIntegrable (fun t : ℝ => (2 * R) * t ^ 2) volume a b := by
    have hc : Continuous (fun t : ℝ => (2 * R) * t ^ 2) := by fun_prop
    exact hc.intervalIntegrable a b
  have hi := intervalIntegral.norm_integral_le_of_norm_le
    (f := fun t : ℝ => (t - a) * t * |t|) hab
    (Filter.Eventually.of_forall fun t ht => by
      change ‖(t - a) * t * |t|‖ ≤ (2 * R) * t ^ 2
      have hs : 0 ≤ t - a := sub_nonneg.mpr ht.1.le
      have ha : -R ≤ a := (hbound g.property.1).1
      have htR : t ≤ R := ht.2.trans (hbound g.property.2.1).2
      have hwidth : t - a ≤ 2 * R := by linarith
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_abs, abs_of_nonneg hs,
        mul_assoc, ← pow_two, sq_abs]
      exact mul_le_mul_of_nonneg_right hwidth (sq_nonneg t)) hd
  rw [intervalIntegral.integral_const_mul] at hi
  calc
    |J2g μ g| = tau μ b * abs (∫ t in a..b, (t - a) * t * |t|) := by
      unfold J2g
      rw [abs_mul, abs_of_nonneg (tau_nonneg μ h g.val.2)]
    _ ≤ tau μ b * ((2 * R) * (∫ t in a..b, t ^ 2)) :=
      mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using hi)
        (tau_nonneg μ h b)
    _ = _ := by rw [gapSquareTauIntegral_eq]; dsimp [a, b]; ring

/-- Countable additivity is applied to the genuine disjoint open gaps.
The square-moment integrand is globally L1 before this summation. -/
theorem gapSquareTauIntegral_hasSum (μ : ProbabilityMeasure ℝ)
    (h : StandardizedLaw μ)
    (h4 : Integrable (fun x : ℝ => x ^ 4) (μ : Measure ℝ)) :
    HasSum (gapSquareTauIntegral μ)
      (∫ t in gapUnion μ, t ^ 2 * tau μ t) := by
  have hd : Pairwise (fun g k : Gap μ =>
      Disjoint (Ioo g.val.1 g.val.2) (Ioo k.val.1 k.val.2)) := by
    intro g k hne
    apply gapSet_pairwiseDisjoint (μ : Measure ℝ).support g.property k.property
    exact fun heq => hne (Subtype.ext heq)
  exact hasSum_integral_iUnion (fun _ => measurableSet_Ioo) hd
    (integrable_square_tau μ h h4).integrableOn

theorem gapSquareTauIntegral_tsum_le (μ : ProbabilityMeasure ℝ)
    (h : StandardizedLaw μ)
    (h4 : Integrable (fun x : ℝ => x ^ 4) (μ : Measure ℝ)) :
    (∑' g : Gap μ, gapSquareTauIntegral μ g) ≤
      (∫ x : ℝ, x ^ 4 ∂(μ : Measure ℝ)) / 3 := by
  rw [(gapSquareTauIntegral_hasSum μ h h4).tsum_eq]
  calc
    (∫ t in gapUnion μ, t ^ 2 * tau μ t) ≤ ∫ t : ℝ, t ^ 2 * tau μ t :=
      setIntegral_le_integral (integrable_square_tau μ h h4)
        (Filter.Eventually.of_forall fun t => mul_nonneg (sq_nonneg t) (tau_nonneg μ h t))
    _ = _ := integral_square_tau μ h h4

/-- The stronger global second signed gap-moment bound uses the original
fourth moment and includes infinite gap families and zero in the support. -/
theorem abs_actualJ2_le_two_R_mul_fourth_div_three (μ : ProbabilityMeasure ℝ)
    (h : StandardizedLaw μ) (R : ℝ) (hR : 0 ≤ R)
    (hbound : (μ : Measure ℝ).support ⊆ Icc (-R) R) :
    |actualJ2 μ| ≤ (2 * R / 3) * (∫ x : ℝ, x ^ 4 ∂(μ : Measure ℝ)) := by
  have h4 := ConservedResource.integrable_pow_of_bounded_support μ R hbound 4
  have hJ2 := summable_J2g μ h R hR hbound
  have hsq := (gapSquareTauIntegral_hasSum μ h h4).summable
  calc
    |actualJ2 μ| ≤ ∑' g : Gap μ, ‖J2g μ g‖ := by
      simpa only [actualJ2, Real.norm_eq_abs] using norm_tsum_le_tsum_norm hJ2.norm
    _ ≤ ∑' g : Gap μ, (2 * R) * gapSquareTauIntegral μ g := by
      apply hJ2.norm.tsum_le_tsum _ (hsq.mul_left (2 * R))
      intro g
      simpa only [Real.norm_eq_abs] using
        abs_J2g_le_two_R_mul_gapSquareTauIntegral μ h R hR hbound g
    _ = (2 * R) * ∑' g : Gap μ, gapSquareTauIntegral μ g := tsum_mul_left
    _ ≤ (2 * R) * ((∫ x : ℝ, x ^ 4 ∂(μ : Measure ℝ)) / 3) :=
      mul_le_mul_of_nonneg_left (gapSquareTauIntegral_tsum_le μ h h4) (by positivity)
    _ = _ := by ring

end BerryEsseen.GapMomentGlobalBounds

#print axioms BerryEsseen.GapMomentGlobalBounds.abs_actualJ1_le_R_mul_actualJ_div_two
#print axioms BerryEsseen.GapMomentGlobalBounds.abs_actualJ1_le_R_mul_rho
#print axioms BerryEsseen.GapMomentGlobalBounds.abs_J2g_le_two_R_mul_gapSquareTauIntegral
#print axioms BerryEsseen.GapMomentGlobalBounds.gapSquareTauIntegral_hasSum
#print axioms BerryEsseen.GapMomentGlobalBounds.gapSquareTauIntegral_tsum_le
#print axioms BerryEsseen.GapMomentGlobalBounds.abs_actualJ2_le_two_R_mul_fourth_div_three
