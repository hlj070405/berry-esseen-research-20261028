module

public import BerryEsseen.ClassicalCosineCubic

@[expose] public section

/-! 2026-10-29: a rational global cosine majorant whose damping
correction vanishes at 25/4; the full majorant equals one there.
The fixed-point bounds below use the official rational pi bounds, the
existing 1/10 cosine cubic, and Mathlib's sine cubic remainder. A strongly
convex middle interval pays the nonzero slope at theta=311/50 explicitly.
No floating-point assertion or external numerical certificate is used. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set

namespace BerryEsseen.ClassicalRationalCosine

def a : ℝ := 1 / 100
def b : ℝ := 1 / 625
def theta : ℝ := 311 / 50
def delta : ℝ := 2 * Real.pi - theta
def F (x : ℝ) : ℝ := 1 - Real.cos x - a * x ^ 2 + b * x ^ 3
def Fd (x : ℝ) : ℝ := Real.sin x - 2 * a * x + 3 * b * x ^ 2
def Fdd (x : ℝ) : ℝ := Real.cos x - 2 * a + 6 * b * x
def G (x : ℝ) : ℝ := F x - F theta - Fd theta * (x - theta) - (x - theta) ^ 2 / 80
def Gd (x : ℝ) : ℝ := Fd x - Fd theta - (x - theta) / 40
def Gdd (x : ℝ) : ℝ := Fdd x - 1 / 40

lemma a_nonneg : 0 ≤ a := by norm_num [a]
lemma b_nonneg : 0 ≤ b := by norm_num [b]

lemma delta_bounds : (3159 : ℝ) / 50000 ≤ delta ∧ delta ≤ 79 / 1250 := by
  unfold delta theta
  constructor
  · linarith [Real.pi_gt_d6]
  · linarith [Real.pi_lt_d4]

lemma cos_theta : Real.cos theta = Real.cos delta := by
  symm
  exact Real.cos_two_pi_sub theta

lemma sin_theta : Real.sin theta = -Real.sin delta := by
  have h := Real.sin_two_pi_sub theta
  change Real.sin delta = -Real.sin theta at h
  linarith

/-- A coarse cubic bound at the small complementary angle already leaves
strict positive room: 70980877/625000000000 > 1/10000. -/
theorem F_theta_lower : (1 : ℝ) / 10000 ≤ F theta := by
  have hd := delta_bounds
  have hd0 : 0 ≤ delta := by linarith
  have hd2 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3159 / 50000) hd.1 2
  have hd3 := pow_le_pow_left₀ hd0 hd.2 3
  have hc := Causalean.Stat.CLT.BerryEsseen.cos_le_quadratic_add_cubic delta
  rw [abs_of_nonneg hd0] at hc
  unfold F
  rw [cos_theta]
  norm_num [a, b, theta] at *
  nlinarith only [hd2, hd3, hc]

theorem Fd_theta_abs : |Fd theta| ≤ (1 : ℝ) / 500 := by
  have hd := delta_bounds
  have hd0 : 0 ≤ delta := by linarith
  have hd3 := pow_le_pow_left₀ hd0 hd.2 3
  have hslo := Real.sin_ge_sub_cube hd0
  have hshi := Real.sin_le hd0
  unfold Fd
  rw [sin_theta]
  norm_num [a, b, theta] at *
  apply abs_le.mpr
  constructor <;> nlinarith only [hd.1, hd.2, hd3, hslo, hshi]

lemma theta_middle : theta ∈ Icc (3 * Real.pi / 2) (2 * Real.pi) := by
  unfold theta
  constructor
  · linarith [Real.pi_lt_d2]
  · linarith [Real.pi_gt_d2]

lemma first_comparison : 0 ≤ (1 / 2 - a) - (1 / 10 - b) * (3 * Real.pi / 2) := by
  unfold a b
  linarith [Real.pi_lt_d2]

lemma Fdd_middle (x : ℝ) (hx : x ∈ Icc (3 * Real.pi / 2) (2 * Real.pi)) :
    (1 : ℝ) / 40 ≤ Fdd x := by
  have hy : 0 ≤ 2 * Real.pi - x := by linarith [hx.2]
  have hyu : 2 * Real.pi - x ≤ Real.pi / 2 := by linarith [hx.1]
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi hy
    (show Real.pi / 2 ≤ Real.pi by linarith [Real.pi_pos]) hyu
  rw [Real.cos_pi_div_two, Real.cos_two_pi_sub] at hc
  unfold Fdd a b
  nlinarith only [hc, hx.1, Real.pi_gt_d2]

lemma hasDerivAt_F (x : ℝ) : HasDerivAt F (Fd x) x := by
  convert (((hasDerivAt_const x (1 : ℝ)).sub (Real.hasDerivAt_cos x)).sub
    (((hasDerivAt_id x).pow 2).const_mul a)).add
    (((hasDerivAt_id x).pow 3).const_mul b) using 1 <;>
    (try funext y) <;> simp [F, Fd] <;> ring

lemma hasDerivAt_Fd (x : ℝ) : HasDerivAt Fd (Fdd x) x := by
  convert (((Real.hasDerivAt_sin x).sub ((hasDerivAt_id x).const_mul (2 * a))).add
    (((hasDerivAt_id x).pow 2).const_mul (3 * b))) using 1 <;>
    (try funext y) <;> simp [Fd, Fdd] <;> ring

lemma hasDerivAt_G (x : ℝ) : HasDerivAt G (Gd x) x := by
  convert (((hasDerivAt_F x).sub_const (F theta)).sub
    (((hasDerivAt_id x).sub_const theta).const_mul (Fd theta))).sub
    ((((hasDerivAt_id x).sub_const theta).pow 2).div_const 80) using 1 <;>
    (try funext y) <;> simp [G, Gd] <;> ring

lemma hasDerivAt_Gd (x : ℝ) : HasDerivAt Gd (Gdd x) x := by
  convert ((hasDerivAt_Fd x).sub_const (Fd theta)).sub
    (((hasDerivAt_id x).sub_const theta).div_const 40) using 1 <;>
    (try funext y) <;> simp [Gd, Gdd] <;> ring

lemma G_theta : G theta = 0 := by simp [G]
lemma Gd_theta : Gd theta = 0 := by simp [Gd]

lemma G_middle (x : ℝ) (hx : x ∈ Icc (3 * Real.pi / 2) (2 * Real.pi)) : 0 ≤ G x := by
  have hθ := theta_middle
  have hm : MonotoneOn Gd (Icc (3 * Real.pi / 2) (2 * Real.pi)) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (f' := Gdd) (convex_Icc _ _)
      (show Continuous Gd from by unfold Gd Fd; fun_prop).continuousOn
    · exact fun u _ => (hasDerivAt_Gd u).hasDerivWithinAt
    · intro u hu
      have hh := Fdd_middle u (interior_subset hu)
      unfold Gdd
      linarith
  rcases le_total x theta with hxt | htx
  · have ha : AntitoneOn G (Icc x theta) := by
      apply antitoneOn_of_hasDerivWithinAt_nonpos (f' := Gd) (convex_Icc _ _)
        (show Continuous G from by unfold G F; fun_prop).continuousOn
      · exact fun u _ => (hasDerivAt_G u).hasDerivWithinAt
      · intro u hu
        have hu' : u ∈ Icc x theta := interior_subset hu
        have huu : u ∈ Icc (3 * Real.pi / 2) (2 * Real.pi) :=
          ⟨hx.1.trans hu'.1, hu'.2.trans hθ.2⟩
        simpa only [Gd_theta] using hm huu hθ hu'.2
    have hh := ha ⟨le_rfl, hxt⟩ ⟨hxt, le_rfl⟩ hxt
    simpa only [G_theta] using hh
  · have ha : MonotoneOn G (Icc theta x) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg (f' := Gd) (convex_Icc _ _)
        (show Continuous G from by unfold G F; fun_prop).continuousOn
      · exact fun u _ => (hasDerivAt_G u).hasDerivWithinAt
      · intro u hu
        have hu' : u ∈ Icc theta x := interior_subset hu
        have huu : u ∈ Icc (3 * Real.pi / 2) (2 * Real.pi) :=
          ⟨hθ.1.trans hu'.1, hu'.2.trans hx.2⟩
        simpa only [Gd_theta] using hm hθ huu hu'.1
    have hh := ha ⟨le_rfl, htx⟩ ⟨htx, le_rfl⟩ htx
    simpa only [G_theta] using hh

theorem F_middle_lower (x : ℝ) (hx : x ∈ Icc (3 * Real.pi / 2) (2 * Real.pi)) :
    (1 : ℝ) / 50000 ≤ F x := by
  have hg := G_middle x hx
  have hs := (abs_le.mp Fd_theta_abs)
  have hc2 : (Fd theta) ^ 2 ≤ (1 : ℝ) / 250000 := by nlinarith [sq_nonneg (Fd theta)]
  unfold G at hg
  nlinarith only [hg, F_theta_lower, hc2, sq_nonneg (x - theta + 40 * Fd theta)]

theorem cos_le_support_cubic_nonneg (x : ℝ) (hx : 0 ≤ x) :
    Real.cos x ≤ 1 - a * x ^ 2 + b * x ^ 3 := by
  by_cases hsmall : x ≤ 3 * Real.pi / 2
  · have h := Causalean.Stat.CLT.BerryEsseen.cos_le_quadratic_add_cubic x
    rw [abs_of_nonneg hx] at h
    have hc := mul_le_mul_of_nonneg_left hsmall
      (show 0 ≤ 1 / 10 - b by norm_num [b])
    have hcoef : 0 ≤ (1 / 2 - a) - (1 / 10 - b) * x := by linarith [first_comparison]
    nlinarith [mul_nonneg (sq_nonneg x) hcoef]
  · by_cases hmid : x ≤ 2 * Real.pi
    · have hh := F_middle_lower x ⟨le_of_not_ge hsmall, hmid⟩
      unfold F at hh
      linarith
    · have htail : a ≤ b * x := by
        unfold a b
        linarith [Real.pi_gt_d2]
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

end BerryEsseen.ClassicalRationalCosine

#print axioms BerryEsseen.ClassicalRationalCosine.F_theta_lower
#print axioms BerryEsseen.ClassicalRationalCosine.Fd_theta_abs
#print axioms BerryEsseen.ClassicalRationalCosine.cos_le_support_cubic
#print axioms BerryEsseen.ClassicalRationalCosine.charFun_norm_sq_le
#print axioms BerryEsseen.ClassicalRationalCosine.charFun_power_norm_le
