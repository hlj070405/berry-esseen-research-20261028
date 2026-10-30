module

public import BerryEsseen.ClassicalDamping
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section

/-! 2026-10-29: a fixed supporting cubic for cosine, tangent at 5π/3.
This retains useful iid damping beyond the zero of the usual 1/10 cubic.
The scalar argument uses the existing global 1/10 bound, convexity on
[4π/3,2π], and a polynomial tail. It does not assume a numerical Berry--Esseen
constant or the full Prawitz piecewise envelope. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set

namespace BerryEsseen.ClassicalCosineCubic

def a : ℝ := 27 / (50 * Real.pi ^ 2) + 3 * Real.sqrt 3 / (10 * Real.pi)
def b : ℝ := 27 / (125 * Real.pi ^ 3) + 9 * Real.sqrt 3 / (50 * Real.pi ^ 2)
def theta : ℝ := 5 * Real.pi / 3
def F (x : ℝ) : ℝ := 1 - Real.cos x - a * x ^ 2 + b * x ^ 3
def Fd (x : ℝ) : ℝ := Real.sin x - 2 * a * x + 3 * b * x ^ 2
def Fdd (x : ℝ) : ℝ := Real.cos x - 2 * a + 6 * b * x

lemma pi_bounds : (3 : ℝ) ≤ Real.pi ∧ Real.pi ≤ 22 / 7 := by
  constructor
  · exact Real.pi_gt_three.le
  · linarith [Real.pi_lt_d20]

lemma root_bounds : (5 : ℝ) / 3 ≤ Real.sqrt 3 ∧ Real.sqrt 3 ≤ 7 / 4 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hn := Real.sqrt_nonneg (3 : ℝ)
  constructor <;> nlinarith

lemma a_nonneg : 0 ≤ a := by unfold a; positivity
lemma b_nonneg : 0 ≤ b := by unfold b; positivity

lemma b_le_tenth : b ≤ 1 / 10 := by
  have hp := pi_bounds.1
  have hr := root_bounds.2
  have hp3 : 27 ≤ Real.pi ^ 3 := by nlinarith [sq_nonneg (Real.pi - 3)]
  have hp2 : 9 ≤ Real.pi ^ 2 := by nlinarith
  have h1 : 27 / (125 * Real.pi ^ 3) ≤ (1 : ℝ) / 125 := by
    apply (div_le_iff₀ (by positivity : 0 < 125 * Real.pi ^ 3)).mpr
    nlinarith
  have h2 : 9 * Real.sqrt 3 / (50 * Real.pi ^ 2) ≤ (7 : ℝ) / 200 := by
    apply (div_le_iff₀ (by positivity : 0 < 50 * Real.pi ^ 2)).mpr
    nlinarith
  unfold b
  linarith

lemma first_comparison : 0 ≤ (1 / 2 - a) - (1 / 10 - b) * (4 * Real.pi / 3) := by
  have hp := pi_bounds.1
  have hpu := pi_bounds.2
  have hr := root_bounds.2
  have hp0 := Real.pi_pos
  have hp2 : 9 ≤ Real.pi ^ 2 := by nlinarith
  have h1 : 63 / (250 * Real.pi ^ 2) ≤ (7 : ℝ) / 250 := by
    apply (div_le_iff₀ (by positivity : 0 < 250 * Real.pi ^ 2)).mpr
    nlinarith
  have h2 : 3 * Real.sqrt 3 / (50 * Real.pi) ≤ (7 : ℝ) / 200 := by
    apply (div_le_iff₀ (by positivity : 0 < 50 * Real.pi)).mpr
    nlinarith
  have heq : (1 / 2 - a) - (1 / 10 - b) * (4 * Real.pi / 3) =
      1 / 2 - 2 * Real.pi / 15 - 63 / (250 * Real.pi ^ 2) -
        3 * Real.sqrt 3 / (50 * Real.pi) := by
    unfold a b
    field_simp
    <;> ring
  rw [heq]
  linarith

lemma middle_comparison : 0 ≤ -(1 : ℝ) / 2 - 2 * a + 6 * b * (4 * Real.pi / 3) := by
  have hp := Real.pi_pos
  have hpu := pi_bounds.2
  have hrl := root_bounds.1
  have hp2 : Real.pi ^ 2 ≤ (22 / 7 : ℝ) ^ 2 := by nlinarith [pi_bounds.1]
  have h1 : (3969 : ℝ) / 60500 ≤ 81 / (125 * Real.pi ^ 2) := by
    apply (le_div_iff₀ (by positivity : 0 < 125 * Real.pi ^ 2)).mpr
    nlinarith
  have h2 : (49 : ℝ) / 110 ≤ 21 * Real.sqrt 3 / (25 * Real.pi) := by
    apply (le_div_iff₀ (by positivity : 0 < 25 * Real.pi)).mpr
    nlinarith
  have heq : -(1 : ℝ) / 2 - 2 * a + 6 * b * (4 * Real.pi / 3) =
      81 / (125 * Real.pi ^ 2) + 21 * Real.sqrt 3 / (25 * Real.pi) - 1 / 2 := by
    unfold a b
    field_simp
    <;> ring
  rw [heq]
  linarith

lemma tail_comparison : a ≤ 2 * Real.pi * b := by
  have hp := Real.pi_pos
  have hpl := pi_bounds.1
  have hrl := root_bounds.1
  have hprod : 5 ≤ Real.sqrt 3 * Real.pi := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hrl) (sub_nonneg.mpr hpl)]
  have heq : 2 * Real.pi * b - a =
      (15 * Real.sqrt 3 * Real.pi - 27) / (250 * Real.pi ^ 2) := by
    unfold a b
    field_simp
    <;> ring
  have hh : 0 ≤ 2 * Real.pi * b - a := by
    rw [heq]
    exact div_nonneg (by nlinarith) (by positivity)
  linarith

lemma hasDerivAt_F (x : ℝ) : HasDerivAt F (Fd x) x := by
  convert (((hasDerivAt_const x (1 : ℝ)).sub (Real.hasDerivAt_cos x)).sub
    (((hasDerivAt_id x).pow 2).const_mul a)).add
    (((hasDerivAt_id x).pow 3).const_mul b) using 1 <;>
    (try funext y) <;> simp [F, Fd] <;> ring

lemma hasDerivAt_Fd (x : ℝ) : HasDerivAt Fd (Fdd x) x := by
  convert (((Real.hasDerivAt_sin x).sub ((hasDerivAt_id x).const_mul (2 * a))).add
    (((hasDerivAt_id x).pow 2).const_mul (3 * b))) using 1 <;>
    (try funext y) <;> simp [Fd, Fdd] <;> ring

lemma F_theta : F theta = 0 := by
  have hc : Real.cos theta = 1 / 2 := by
    rw [theta, show 5 * Real.pi / 3 = 2 * Real.pi - Real.pi / 3 by ring,
      Real.cos_two_pi_sub, Real.cos_pi_div_three]
  unfold F
  rw [hc]
  unfold a b theta
  field_simp
  <;> ring

lemma Fd_theta : Fd theta = 0 := by
  have hs : Real.sin theta = -Real.sqrt 3 / 2 := by
    rw [theta, show 5 * Real.pi / 3 = 2 * Real.pi - Real.pi / 3 by ring,
      Real.sin_two_pi_sub, Real.sin_pi_div_three]
    ring
  unfold Fd
  rw [hs]
  unfold a b theta
  field_simp
  <;> ring

lemma Fdd_middle (x : ℝ) (hx : x ∈ Icc (4 * Real.pi / 3) (2 * Real.pi)) :
    0 ≤ Fdd x := by
  have hp := Real.pi_pos
  have hy : 0 ≤ 2 * Real.pi - x := by linarith [hx.2]
  have hyu : 2 * Real.pi - x ≤ 2 * Real.pi / 3 := by linarith [hx.1]
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi hy
    (show 2 * Real.pi / 3 ≤ Real.pi by linarith) hyu
  have hval : Real.cos (2 * Real.pi / 3) = -(1 : ℝ) / 2 := by
    rw [show 2 * Real.pi / 3 = Real.pi / 3 + Real.pi / 3 by ring,
      Real.cos_add, Real.cos_pi_div_three, Real.sin_pi_div_three]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  rw [Real.cos_two_pi_sub, hval] at hc
  have hb := mul_le_mul_of_nonneg_left hx.1 (show 0 ≤ 6 * b by positivity [b_nonneg])
  unfold Fdd
  linarith [middle_comparison]

lemma F_middle (x : ℝ) (hx : x ∈ Icc (4 * Real.pi / 3) (2 * Real.pi)) : 0 ≤ F x := by
  have hp := Real.pi_pos
  have hθ : theta ∈ Icc (4 * Real.pi / 3) (2 * Real.pi) := by dsimp [theta]; constructor <;> linarith
  have hm : MonotoneOn Fd (Icc (4 * Real.pi / 3) (2 * Real.pi)) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (f' := Fdd) (convex_Icc _ _)
      (show Continuous Fd from by unfold Fd; fun_prop).continuousOn
    · exact fun u _ => (hasDerivAt_Fd u).hasDerivWithinAt
    · intro u hu
      exact Fdd_middle u (interior_subset hu)
  rcases le_total x theta with hxt | htx
  · have ha : AntitoneOn F (Icc x theta) := by
      apply antitoneOn_of_hasDerivWithinAt_nonpos (f' := Fd) (convex_Icc _ _)
        (show Continuous F from by unfold F; fun_prop).continuousOn
      · exact fun u _ => (hasDerivAt_F u).hasDerivWithinAt
      · intro u hu
        have hu' : u ∈ Icc x theta := interior_subset hu
        have huu : u ∈ Icc (4 * Real.pi / 3) (2 * Real.pi) :=
          ⟨hx.1.trans hu'.1, hu'.2.trans hθ.2⟩
        simpa only [Fd_theta] using hm huu hθ hu'.2
    have hh := ha ⟨le_rfl, hxt⟩ ⟨hxt, le_rfl⟩ hxt
    simpa only [F_theta] using hh
  · have ha : MonotoneOn F (Icc theta x) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg (f' := Fd) (convex_Icc _ _)
        (show Continuous F from by unfold F; fun_prop).continuousOn
      · exact fun u _ => (hasDerivAt_F u).hasDerivWithinAt
      · intro u hu
        have hu' : u ∈ Icc theta x := interior_subset hu
        have huu : u ∈ Icc (4 * Real.pi / 3) (2 * Real.pi) :=
          ⟨hθ.1.trans hu'.1, hu'.2.trans hx.2⟩
        simpa only [Fd_theta] using hm hθ huu hu'.1
    have hh := ha ⟨le_rfl, htx⟩ ⟨htx, le_rfl⟩ htx
    simpa only [F_theta] using hh

theorem cos_le_support_cubic_nonneg (x : ℝ) (hx : 0 ≤ x) :
    Real.cos x ≤ 1 - a * x ^ 2 + b * x ^ 3 := by
  by_cases hsmall : x ≤ 4 * Real.pi / 3
  · have h := Causalean.Stat.CLT.BerryEsseen.cos_le_quadratic_add_cubic x
    rw [abs_of_nonneg hx] at h
    have hc := mul_le_mul_of_nonneg_left hsmall (sub_nonneg.mpr b_le_tenth)
    have hcoef : 0 ≤ (1 / 2 - a) - (1 / 10 - b) * x := by linarith [first_comparison]
    nlinarith [mul_nonneg (sq_nonneg x) hcoef]
  · by_cases hmid : x ≤ 2 * Real.pi
    · have hh := F_middle x ⟨le_of_not_ge hsmall, hmid⟩
      unfold F at hh
      linarith
    · have htail : a ≤ b * x := by
        have hh := mul_le_mul_of_nonneg_left (le_of_not_ge hmid) b_nonneg
        linarith [tail_comparison]
      have hh := mul_nonneg (sq_nonneg x) (sub_nonneg.mpr htail)
      nlinarith [Real.cos_le_one x]

theorem cos_le_support_cubic (x : ℝ) :
    Real.cos x ≤ 1 - a * x ^ 2 + b * |x| ^ 3 := by
  have h := cos_le_support_cubic_nonneg |x| (abs_nonneg x)
  simpa only [Real.cos_abs, sq_abs] using h

/-- The usual independent-difference proof with the new scalar majorant.
The transport argument adapts the vendored CausalSmith Apache-2.0
`BerryEsseenWideCharFun.unit_variance_charFun_norm_sq_cubic_bound` proof;
the new input is `cos_le_support_cubic` above. The symmetrized third absolute
moment is bounded by 2(M3+1), not 2M3. -/
theorem unit_variance_charFun_norm_sq_bound
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (M3 : ℝ)
    (hmean_int : Integrable (fun x : ℝ => x) μ)
    (hmean : ∫ x : ℝ, x ∂μ = 0)
    (hvar_int : Integrable (fun x : ℝ => x ^ 2) μ)
    (hvar : ∫ x : ℝ, x ^ 2 ∂μ = 1)
    (hthird_int : Integrable (fun x : ℝ => |x| ^ 3) μ)
    (hthird : ∫ x : ℝ, |x| ^ 3 ∂μ ≤ M3) (t : ℝ) :
    ‖charFun μ t‖ ^ 2 ≤ 1 - 2 * a * t ^ 2 + 2 * b * (M3 + 1) * |t| ^ 3 := by
  have hexp : Integrable (fun p : ℝ × ℝ =>
      Complex.exp ((t * (p.1 - p.2) : ℝ) * Complex.I)) (μ.prod μ) := by
    refine (integrable_const (1 : ℝ)).mono' (by fun_prop)
      (Filter.Eventually.of_forall ?_)
    intro p
    simp only [Complex.norm_exp_ofReal_mul_I, le_refl]
  have hproduct : (∫ p : ℝ × ℝ,
      Complex.exp ((t * (p.1 - p.2) : ℝ) * Complex.I) ∂μ.prod μ) =
      charFun μ t * starRingEnd ℂ (charFun μ t) := by
    rw [← charFun_neg, charFun_apply_real, charFun_apply_real, ← integral_prod_mul]
    apply integral_congr_ae
    filter_upwards [] with p
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hcos : (∫ p : ℝ × ℝ, Real.cos (t * (p.1 - p.2)) ∂μ.prod μ) =
      ‖charFun μ t‖ ^ 2 := by
    have h := integral_re hexp
    rw [hproduct, RCLike.mul_conj, ← RCLike.ofReal_pow, RCLike.ofReal_re] at h
    simpa only [RCLike.re_to_complex, Complex.exp_ofReal_mul_I_re] using h
  have h₂₁ := hvar_int.comp_fst μ
  have h₂₂ := hvar_int.comp_snd μ
  have hmix := hmean_int.mul_prod hmean_int
  have hsum : Integrable (fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2) (μ.prod μ) := h₂₁.add h₂₂
  have hsq : Integrable (fun p : ℝ × ℝ => (p.1 - p.2) ^ 2) (μ.prod μ) := by
    convert hsum.sub (hmix.const_mul 2) using 1
    ext p
    dsimp
    ring
  have hsecond : (∫ p : ℝ × ℝ, (p.1 - p.2) ^ 2 ∂μ.prod μ) = 2 := by
    have heq : (fun p : ℝ × ℝ => (p.1 - p.2) ^ 2) =
        (fun p => (p.1 ^ 2 + p.2 ^ 2) - 2 * (p.1 * p.2)) := by funext p; ring
    rw [heq, integral_sub hsum (hmix.const_mul 2), integral_add h₂₁ h₂₂,
      integral_const_mul, integral_prod_mul (fun x : ℝ => x) (fun y : ℝ => y),
      integral_fun_fst (fun x : ℝ => x ^ 2), integral_fun_snd (fun x : ℝ => x ^ 2)]
    norm_num [hmean, hvar]
  obtain ⟨hcube, hcube_bound⟩ :=
    Causalean.Stat.CLT.BerryEsseen.symmetrized_unit_third_moment_le
      μ hmean_int hmean hvar_int hvar hthird_int
  have hcos_int : Integrable (fun p : ℝ × ℝ => Real.cos (t * (p.1 - p.2)))
      (μ.prod μ) := by
    refine (integrable_const (1 : ℝ)).mono' (by fun_prop)
      (Filter.Eventually.of_forall ?_)
    intro p
    simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (t * (p.1 - p.2))
  have hmajor_int : Integrable (fun p : ℝ × ℝ =>
      1 - (a * t ^ 2) * (p.1 - p.2) ^ 2 +
        (b * |t| ^ 3) * |p.1 - p.2| ^ 3) (μ.prod μ) :=
    ((integrable_const (1 : ℝ)).sub (hsq.const_mul (a * t ^ 2))).add
      (hcube.const_mul (b * |t| ^ 3))
  have hbound := integral_mono hcos_int hmajor_int (fun p => show
      Real.cos (t * (p.1 - p.2)) ≤
        1 - (a * t ^ 2) * (p.1 - p.2) ^ 2 +
          (b * |t| ^ 3) * |p.1 - p.2| ^ 3 from by
    have h := cos_le_support_cubic (t * (p.1 - p.2))
    simp only [mul_pow, abs_mul] at h
    convert h using 1 <;> ring)
  have hquadratic : Integrable (fun p : ℝ × ℝ =>
      1 - (a * t ^ 2) * (p.1 - p.2) ^ 2) (μ.prod μ) :=
    (integrable_const (1 : ℝ)).sub (hsq.const_mul (a * t ^ 2))
  rw [hcos, integral_add hquadratic (hcube.const_mul (b * |t| ^ 3)),
    integral_sub (integrable_const (1 : ℝ)) (hsq.const_mul (a * t ^ 2)),
    integral_const_mul, integral_const_mul, hsecond] at hbound
  have hthird_bound : (∫ p : ℝ × ℝ, |p.1 - p.2| ^ 3 ∂μ.prod μ) ≤
      2 * (M3 + 1) := by linarith
  have hscaled := mul_le_mul_of_nonneg_left hthird_bound
    (show 0 ≤ b * |t| ^ 3 from mul_nonneg b_nonneg (by positivity))
  simp only [integral_const, probReal_univ, one_smul] at hbound
  nlinarith only [hbound, hscaled]

def polynomial (μ : ProbabilityMeasure ℝ) (t : ℝ) : ℝ :=
  1 - 2 * a * t ^ 2 + 2 * b * (thirdAbsoluteMoment μ + 1) * |t| ^ 3

theorem charFun_norm_sq_le (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (t : ℝ) :
    ‖charFun (μ : Measure ℝ) t‖ ^ 2 ≤ polynomial μ t := by
  exact unit_variance_charFun_norm_sq_bound (μ : Measure ℝ) (thirdAbsoluteMoment μ)
    h.integrable_mean h.mean_zero h.integrable_square h.second_moment_one
    h.integrable_cube le_rfl t

theorem polynomial_nonneg (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (t : ℝ) :
    0 ≤ polynomial μ t := (sq_nonneg _).trans (charFun_norm_sq_le μ h t)

def modulus (μ : ProbabilityMeasure ℝ) (t : ℝ) : ℝ :=
  min 1 (Real.sqrt (polynomial μ t))

theorem charFun_norm_le (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (t : ℝ) :
    ‖charFun (μ : Measure ℝ) t‖ ≤ modulus μ t := by
  apply le_min (norm_charFun_le_one t)
  exact (Real.le_sqrt (norm_nonneg _) (polynomial_nonneg μ h t)).mpr
    (charFun_norm_sq_le μ h t)

theorem modulus_nonneg (μ : ProbabilityMeasure ℝ) (t : ℝ) : 0 ≤ modulus μ t := by
  exact le_min (by norm_num) (Real.sqrt_nonneg _)

theorem charFun_power_norm_le (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (t : ℝ) : ‖charFun (μ : Measure ℝ) t ^ n‖ ≤ modulus μ t ^ n := by
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (charFun_norm_le μ h t) n

end BerryEsseen.ClassicalCosineCubic

#print axioms BerryEsseen.ClassicalCosineCubic.cos_le_support_cubic
#print axioms BerryEsseen.ClassicalCosineCubic.charFun_norm_sq_le
#print axioms BerryEsseen.ClassicalCosineCubic.charFun_power_norm_le
