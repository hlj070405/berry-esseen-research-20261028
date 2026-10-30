module

public import BerryEsseen.ClassicalCosineCubic
public import BerryEsseen.SymmetrizedThirdMoment
public import BerryEsseen.CharacteristicExpansion
public import Mathlib.Analysis.Convex.Deriv

@[expose] public section

/-! 2026-10-29: the supporting cosine cubic tangent at theta=3*pi/2.
The near interval uses the established global 1/10 cubic.  From 4*pi/3
onward, the residual is convex and has value and slope zero at theta.
The CF theorem integrates this scalar bound under the original law's
actual independent-difference measure, reusing its proved second and
third absolute moments.  No numerical price or extra moment is assumed. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace BerryEsseen.ClassicalThreeHalvesCosine

def a : ℝ := 4 / (3 * Real.pi ^ 2) + 2 / (3 * Real.pi)
def b : ℝ := 16 / (27 * Real.pi ^ 3) + 4 / (9 * Real.pi ^ 2)
def theta : ℝ := 3 * Real.pi / 2
def cutoff : ℝ := 4 * Real.pi / 3

def F (x : ℝ) : ℝ := 1 - Real.cos x - a * x ^ 2 + b * x ^ 3
def Fd (x : ℝ) : ℝ := Real.sin x - 2 * a * x + 3 * b * x ^ 2
def Fdd (x : ℝ) : ℝ := Real.cos x - 2 * a + 6 * b * x

lemma a_nonneg : 0 ≤ a := by unfold a; positivity
lemma b_nonneg : 0 ≤ b := by unfold b; positivity

private lemma pi_bounds : (25 : ℝ) / 8 ≤ Real.pi ∧ Real.pi ≤ 63 / 20 := by
  constructor <;> linarith [Real.pi_gt_d2, Real.pi_lt_d2]

lemma b_lt_tenth : b < 1 / 10 := by
  have hp : (3 : ℝ) ≤ Real.pi := Real.pi_gt_three.le
  have hp2 : (9 : ℝ) ≤ Real.pi ^ 2 := by
    simpa only [show (3 : ℝ) ^ 2 = 9 by norm_num] using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hp 2
  have hp3 : (27 : ℝ) ≤ Real.pi ^ 3 := by
    simpa only [show (3 : ℝ) ^ 3 = 27 by norm_num] using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hp 3
  have h1 : 16 / (27 * Real.pi ^ 3) ≤ (16 : ℝ) / 729 := by
    apply (div_le_iff₀ (by positivity : 0 < 27 * Real.pi ^ 3)).mpr
    nlinarith only [hp3]
  have h2 : 4 / (9 * Real.pi ^ 2) ≤ (4 : ℝ) / 81 := by
    apply (div_le_iff₀ (by positivity : 0 < 9 * Real.pi ^ 2)).mpr
    nlinarith only [hp2]
  unfold b
  linarith only [h1, h2]

lemma first_comparison : 0 ≤ (1 / 2 - a) - (1 / 10 - b) * cutoff := by
  have hp := pi_bounds.1
  have hpu := pi_bounds.2
  have hp2 : (25 / 8 : ℝ) ^ 2 ≤ Real.pi ^ 2 :=
    pow_le_pow_left₀ (by norm_num) hp 2
  have h1 : 44 / (81 * Real.pi ^ 2) ≤ (7 : ℝ) / 125 := by
    apply (div_le_iff₀ (by positivity : 0 < 81 * Real.pi ^ 2)).mpr
    nlinarith only [hp2]
  have h2 : 2 / (27 * Real.pi) ≤ (3 : ℝ) / 125 := by
    apply (div_le_iff₀ (by positivity : 0 < 27 * Real.pi)).mpr
    nlinarith only [hp]
  have he : (1 / 2 - a) - (1 / 10 - b) * cutoff =
      1 / 2 - 2 * Real.pi / 15 - 44 / (81 * Real.pi ^ 2) - 2 / (27 * Real.pi) := by
    unfold a b cutoff
    field_simp [Real.pi_ne_zero]
    ring
  rw [he]
  linarith only [h1, h2, hpu]

lemma middle_comparison : 0 < -(1 : ℝ) / 2 - 2 * a + 6 * b * cutoff := by
  have hp : (5 : ℝ) / 9 ≤ 20 / (9 * Real.pi) := by
    apply (le_div_iff₀ (by positivity : 0 < 9 * Real.pi)).mpr
    linarith [Real.pi_lt_four]
  have hn : 0 ≤ 56 / (27 * Real.pi ^ 2) := by positivity
  have he : -(1 : ℝ) / 2 - 2 * a + 6 * b * cutoff =
      56 / (27 * Real.pi ^ 2) + 20 / (9 * Real.pi) - 1 / 2 := by
    unfold a b cutoff
    field_simp [Real.pi_ne_zero]
    ring
  rw [he]
  linarith only [hp, hn]

lemma tail_comparison : 0 < -(1 : ℝ) - 2 * a + 12 * Real.pi * b := by
  have hp : (1 : ℝ) ≤ 4 / Real.pi := (le_div_iff₀ Real.pi_pos).mpr
    (by simpa only [one_mul] using Real.pi_lt_four.le)
  have hn : 0 < 40 / (9 * Real.pi ^ 2) := by positivity
  have he : -(1 : ℝ) - 2 * a + 12 * Real.pi * b =
      40 / (9 * Real.pi ^ 2) + 4 / Real.pi - 1 := by
    unfold a b
    field_simp [Real.pi_ne_zero]
    ring
  rw [he]
  linarith only [hp, hn]

lemma hasDerivAt_F (x : ℝ) : HasDerivAt F (Fd x) x := by
  unfold F Fd
  convert ((((hasDerivAt_const x (1 : ℝ)).fun_sub (Real.hasDerivAt_cos x)).fun_sub
    (((hasDerivAt_id' x).fun_pow 2).const_mul a)).fun_add
      (((hasDerivAt_id' x).fun_pow 3).const_mul b)) using 1
  ring

lemma hasDerivAt_Fd (x : ℝ) : HasDerivAt Fd (Fdd x) x := by
  unfold Fd Fdd
  convert ((Real.hasDerivAt_sin x).fun_sub ((hasDerivAt_id' x).const_mul (2 * a))).fun_add
    (((hasDerivAt_id' x).fun_pow 2).const_mul (3 * b)) using 1
  ring

lemma F_theta : F theta = 0 := by
  have hc : Real.cos theta = 0 := by
    rw [theta, show 3 * Real.pi / 2 = Real.pi / 2 + Real.pi by ring,
      Real.cos_add_pi, Real.cos_pi_div_two, neg_zero]
  unfold F
  rw [hc]
  unfold a b theta
  field_simp [Real.pi_ne_zero]
  ring

lemma Fd_theta : Fd theta = 0 := by
  have hs : Real.sin theta = -1 := by
    rw [theta, show 3 * Real.pi / 2 = Real.pi / 2 + Real.pi by ring,
      Real.sin_add_pi, Real.sin_pi_div_two]
  unfold Fd
  rw [hs]
  unfold a b theta
  field_simp [Real.pi_ne_zero]
  ring

lemma cos_middle_lower (x : ℝ) (hx : x ∈ Icc cutoff (2 * Real.pi)) : -(1 : ℝ) / 2 ≤ Real.cos x := by
  have hp := Real.pi_pos
  have hy : 0 ≤ 2 * Real.pi - x := by linarith [hx.2]
  have hyu : 2 * Real.pi - x ≤ 2 * Real.pi / 3 := by
    have hh := hx.1
    unfold cutoff at hh
    linarith only [hh]
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi hy
    (show 2 * Real.pi / 3 ≤ Real.pi by linarith) hyu
  have hval : Real.cos (2 * Real.pi / 3) = -(1 : ℝ) / 2 := by
    rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring,
      Real.cos_pi_sub, Real.cos_pi_div_three]
    ring
  rw [Real.cos_two_pi_sub, hval] at hc
  exact hc

lemma Fdd_nonneg (x : ℝ) (hx : cutoff ≤ x) : 0 ≤ Fdd x := by
  by_cases hm : x ≤ 2 * Real.pi
  · have hc := cos_middle_lower x ⟨hx, hm⟩
    have hb := mul_le_mul_of_nonneg_left hx (show 0 ≤ 6 * b by positivity [b_nonneg])
    unfold Fdd
    linarith [middle_comparison]
  · have hc := Real.neg_one_le_cos x
    have hb := mul_le_mul_of_nonneg_left (lt_of_not_ge hm).le
      (show 0 ≤ 6 * b by positivity [b_nonneg])
    unfold Fdd
    nlinarith only [hc, hb, tail_comparison]

lemma convexOn_F : ConvexOn ℝ (Ici cutoff) F := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (f' := Fd) (f'' := Fdd) (convex_Ici _)
    (show Continuous F from by unfold F; fun_prop).continuousOn
  · exact fun x _ => (hasDerivAt_F x).hasDerivWithinAt
  · exact fun x _ => (hasDerivAt_Fd x).hasDerivWithinAt
  · intro x hx
    exact Fdd_nonneg x (interior_subset hx)

lemma F_nonneg_of_cutoff_le (x : ℝ) (hx : cutoff ≤ x) : 0 ≤ F x := by
  have hθ : theta ∈ interior (Ici cutoff) := by
    rw [interior_Ici]
    change cutoff < theta
    unfold cutoff theta
    linarith [Real.pi_pos]
  have hd : derivWithin F (Ioi theta) theta = 0 := by
    rw [(hasDerivAt_F theta).hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioi theta)]
    exact Fd_theta
  have hm := convexOn_F.isMinOn_of_rightDeriv_eq_zero hθ hd
  have hh : F theta ≤ F x := (isMinOn_iff.mp hm) x hx
  simpa only [F_theta] using hh

theorem cos_le_support_cubic_nonneg (x : ℝ) (hx : 0 ≤ x) :
    Real.cos x ≤ 1 - a * x ^ 2 + b * x ^ 3 := by
  by_cases hs : x ≤ cutoff
  · have hh := Causalean.Stat.CLT.BerryEsseen.cos_le_quadratic_add_cubic x
    rw [abs_of_nonneg hx] at hh
    have hc := mul_le_mul_of_nonneg_left hs (sub_nonneg.mpr b_lt_tenth.le)
    have hcoef : 0 ≤ (1 / 2 - a) - (1 / 10 - b) * x := by linarith [first_comparison]
    have hp := mul_nonneg (sq_nonneg x) hcoef
    nlinarith only [hh, hp]
  · have hh := F_nonneg_of_cutoff_le x (lt_of_not_ge hs).le
    unfold F at hh
    linarith only [hh]

theorem cos_le_support_cubic (x : ℝ) :
    Real.cos x ≤ 1 - a * x ^ 2 + b * |x| ^ 3 := by
  have hh := cos_le_support_cubic_nonneg |x| (abs_nonneg x)
  simpa only [Real.cos_abs, sq_abs] using hh

def polynomial (μ : ProbabilityMeasure ℝ) (t : ℝ) : ℝ :=
  1 - 2 * a * t ^ 2 + 2 * b * (thirdAbsoluteMoment μ + 1) * |t| ^ 3

/-- The cosine is integrated under the same original law's product
measure.  The third-moment coefficient is exactly 2*(rho+1). -/
theorem charFun_norm_sq_le (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (t : ℝ) :
    ‖charFun (μ : Measure ℝ) t‖ ^ 2 ≤ polynomial μ t := by
  obtain ⟨h2, h2eq⟩ := SymmetrizedThirdMoment.scaled_difference_second_moment μ h t
  obtain ⟨h3, h3le⟩ := SymmetrizedThirdMoment.scaled_difference_third_absolute_moment μ h t
  have hcos : (∫ p : ℝ × ℝ, Real.cos (t * (p.1 - p.2))
      ∂((μ : Measure ℝ).prod (μ : Measure ℝ))) = ‖charFun (μ : Measure ℝ) t‖ ^ 2 := by
    rw [CharacteristicExpansion.norm_charFun_sq_symmetrization,
      CharacteristicExpansion.differenceMeasure_eq_map_product, integral_map (by fun_prop) (by fun_prop)]
  have hcosI : Integrable (fun p : ℝ × ℝ => Real.cos (t * (p.1 - p.2)))
      ((μ : Measure ℝ).prod (μ : Measure ℝ)) := by
    refine (integrable_const (1 : ℝ)).mono' (by fun_prop) (Filter.Eventually.of_forall ?_)
    intro p
    simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (t * (p.1 - p.2))
  have hquad : Integrable (fun p : ℝ × ℝ => 1 - a * (t * (p.1 - p.2)) ^ 2)
      ((μ : Measure ℝ).prod (μ : Measure ℝ)) :=
    (integrable_const (1 : ℝ)).sub (h2.const_mul a)
  have hbound := integral_mono hcosI (hquad.add (h3.const_mul b))
    (fun p => cos_le_support_cubic (t * (p.1 - p.2)))
  simp only [Pi.add_apply] at hbound
  rw [hcos, integral_add hquad (h3.const_mul b),
    integral_sub (integrable_const (1 : ℝ)) (h2.const_mul a),
    integral_const_mul, integral_const_mul, h2eq] at hbound
  have hthird := mul_le_mul_of_nonneg_left h3le b_nonneg
  simp only [integral_const, probReal_univ, one_smul] at hbound
  unfold polynomial
  nlinarith only [hbound, hthird]

theorem polynomial_nonneg (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (t : ℝ) :
    0 ≤ polynomial μ t := (sq_nonneg _).trans (charFun_norm_sq_le μ h t)

end BerryEsseen.ClassicalThreeHalvesCosine

#print axioms BerryEsseen.ClassicalThreeHalvesCosine.first_comparison
#print axioms BerryEsseen.ClassicalThreeHalvesCosine.Fdd_nonneg
#print axioms BerryEsseen.ClassicalThreeHalvesCosine.cos_le_support_cubic
#print axioms BerryEsseen.ClassicalThreeHalvesCosine.charFun_norm_sq_le
