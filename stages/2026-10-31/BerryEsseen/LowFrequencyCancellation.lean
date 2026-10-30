module

public import BerryEsseen.LowFrequencyLeading
public import Mathlib.Analysis.Convex.Jensen

@[expose] public section

/-! 2026-10-28: the actual cancellation candidate in ut:paired. J is a genuine
Lebesgue integral; its corner prices remain explicit inputs, not evaluated numbers. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators Interval
open BerryEsseen.CharacteristicExpansion BerryEsseen.LowFrequencyError BerryEsseen.LowFrequencyLeading

namespace BerryEsseen.LowFrequencyCancellation

def jIntegrand (z c x : ℝ) : ℝ := Real.exp (-(x ^ 2) / 2) * |z * x ^ 2 - c * x ^ 4|
def J (z c : ℝ) : ℝ := ∫ x in Ioi (0 : ℝ), jIntegrand z c x
/-- The actual signed coefficient c₅=aγ/6. -/
def actualC5 (μ : ProbabilityMeasure ℝ) : ℝ := quarticCoeff μ * gamma μ / 6

lemma integrable_jIntegrand (z c : ℝ) : Integrable (jIntegrand z c) := by
  have h2 := integrable_gaussian_power 2 (1 / 2) (by norm_num)
  have h4 := integrable_gaussian_power 4 (1 / 2) (by norm_num)
  have hi := ((h2.const_mul z).sub (h4.const_mul c)).abs
  convert hi using 1
  ext x
  simp only [Pi.sub_apply]
  unfold jIntegrand
  rw [show -(x ^ 2) / 2 = -((1 / 2 : ℝ) * x ^ 2) by ring]
  rw [show z * (x ^ 2 * Real.exp (-((1 / 2 : ℝ) * x ^ 2))) -
      c * (x ^ 4 * Real.exp (-((1 / 2 : ℝ) * x ^ 2))) =
      Real.exp (-((1 / 2 : ℝ) * x ^ 2)) * (z * x ^ 2 - c * x ^ 4) by ring]
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]

lemma J_nonneg (z c : ℝ) : 0 ≤ J z c := integral_nonneg fun x => by unfold jIntegrand; positivity

lemma J_sublinear (z₀ c₀ z₁ c₁ a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    J (a * z₀ + b * z₁) (a * c₀ + b * c₁) ≤ a * J z₀ c₀ + b * J z₁ c₁ := by
  unfold J
  have hi0 := (integrable_jIntegrand z₀ c₀).const_mul a
  have hi1 := (integrable_jIntegrand z₁ c₁).const_mul b
  calc
    _ ≤ ∫ x in Ioi (0 : ℝ), a * jIntegrand z₀ c₀ x + b * jIntegrand z₁ c₁ x := by
      apply integral_mono_ae (integrable_jIntegrand _ _).integrableOn (hi0.add hi1).integrableOn
      exact Eventually.of_forall fun x => by
        simp only [Pi.add_apply]
        unfold jIntegrand
        have heq : (a * z₀ + b * z₁) * x ^ 2 - (a * c₀ + b * c₁) * x ^ 4 =
            a * (z₀ * x ^ 2 - c₀ * x ^ 4) + b * (z₁ * x ^ 2 - c₁ * x ^ 4) := by ring
        rw [heq]
        have hp := abs_add_le (a * (z₀ * x ^ 2 - c₀ * x ^ 4)) (b * (z₁ * x ^ 2 - c₁ * x ^ 4))
        rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb] at hp
        convert mul_le_mul_of_nonneg_left hp (Real.exp_pos (-(x ^ 2) / 2)).le using 1 <;> ring
    _ = _ := by rw [integral_add hi0.integrableOn hi1.integrableOn, integral_const_mul, integral_const_mul]

lemma convexOn_J_left (c : ℝ) : ConvexOn ℝ univ (fun z => J z c) := by
  refine ⟨convex_univ, ?_⟩
  intro z₀ _ z₁ _ a b ha hb hab
  have heq : a * c + b * c = c := by rw [← add_mul, hab, one_mul]
  simpa only [smul_eq_mul, heq] using J_sublinear z₀ c z₁ c a b ha hb

lemma convexOn_J_right (z : ℝ) : ConvexOn ℝ univ (J z) := by
  refine ⟨convex_univ, ?_⟩
  intro c₀ _ c₁ _ a b ha hb hab
  have heq : a * z + b * z = z := by rw [← add_mul, hab, one_mul]
  simpa only [smul_eq_mul, heq] using J_sublinear z c₀ z c₁ a b ha hb

/-- A genuine closed-rectangle maximum principle for the actual integral J. -/
theorem J_le_corners (z c zlo zhi clo chi : ℝ) (hz : z ∈ Icc zlo zhi) (hc : c ∈ Icc clo chi) :
    J z c ≤ max (max (J zlo clo) (J zlo chi)) (max (J zhi clo) (J zhi chi)) := by
  have hzmax := (convexOn_J_left c).le_max_of_mem_Icc (mem_univ _) (mem_univ _) hz
  have hc0 := (convexOn_J_right zlo).le_max_of_mem_Icc (mem_univ _) (mem_univ _) hc
  have hc1 := (convexOn_J_right zhi).le_max_of_mem_Icc (mem_univ _) (mem_univ _) hc
  exact hzmax.trans (max_le_max hc0 hc1)

theorem J_le_rectangle_price (z c zlo zhi clo chi Jstar : ℝ)
    (hz : z ∈ Icc zlo zhi) (hc : c ∈ Icc clo chi)
    (h00 : J zlo clo ≤ Jstar) (h01 : J zlo chi ≤ Jstar)
    (h10 : J zhi clo ≤ Jstar) (h11 : J zhi chi ≤ Jstar) : J z c ≤ Jstar :=
  (J_le_corners z c zlo zhi clo chi hz hc).trans (max_le (max_le h00 h01) (max_le h10 h11))

/-- The signed paired core before x=sqrt(b)t. -/
def scaledCore (b z c t : ℝ) : ℝ := Real.exp (-(b / 2 * t ^ 2)) * |z * t ^ 2 - b * c * t ^ 4|

lemma scaledCore_eq (b z c t : ℝ) (hb : 0 < b) :
    scaledCore b z c t = (1 / b) * jIntegrand z c (Real.sqrt b * t) := by
  have hsq := Real.sq_sqrt hb.le
  have h4 : Real.sqrt b ^ 4 = b ^ 2 := by rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, hsq]
  unfold scaledCore jIntegrand
  simp only [mul_pow, hsq, h4]
  rw [show -(b * t ^ 2) / 2 = -(b / 2 * t ^ 2) by ring]
  rw [show z * (b * t ^ 2) - c * (b ^ 2 * t ^ 4) = b * (z * t ^ 2 - b * c * t ^ 4) by ring,
    abs_mul, abs_of_pos hb]
  field_simp [ne_of_gt hb]

lemma integrable_scaledCore (b z c : ℝ) (hb : 0 < b) : Integrable (scaledCore b z c) := by
  have hc : Integrable (fun t : ℝ => jIntegrand z c (Real.sqrt b * t)) :=
    (integrable_comp_mul_left_iff (jIntegrand z c) (ne_of_gt (Real.sqrt_pos.mpr hb))).mpr
      (integrable_jIntegrand z c)
  have hi := hc.const_mul (1 / b)
  exact hi.congr (Eventually.of_forall fun t => (scaledCore_eq b z c t hb).symm)

lemma integral_scaledCore (b z c : ℝ) (hb : 0 < b) :
    (∫ t in Ioi (0 : ℝ), scaledCore b z c t) = J z c / (b * Real.sqrt b) := by
  have heq : scaledCore b z c = (fun t => (1 / b) * jIntegrand z c (Real.sqrt b * t)) := by
    funext t; exact scaledCore_eq b z c t hb
  rw [heq, integral_const_mul, integral_comp_mul_left_Ioi (jIntegrand z c) 0 (Real.sqrt_pos.mpr hb)]
  simp only [mul_zero, smul_eq_mul, J, one_div]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

lemma integral_even_gaussian_eight (b : ℝ) (hb : 0 < b) :
    (∫ t in Ioi (0 : ℝ), t ^ 8 * Real.exp (-(b / 2 * t ^ 2))) =
      105 * gaussianMass / (b ^ 4 * Real.sqrt b) := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := (2 : ℝ)) (q := (8 : ℝ)) (b := b / 2)
    (by norm_num) (by norm_num) (by positivity)
  have hg := Real.Gamma_nat_add_half 4
  norm_num at hg
  norm_num only [show ((8 : ℝ) + 1) / 2 = 9 / 2 by norm_num,
    show -((8 : ℝ) + 1) / 2 = -(9 : ℝ) / 2 by norm_num, Real.rpow_ofNat] at h
  have hr := rpow_neg_half_nat (b / 2) (by positivity) 9
  norm_num only [Nat.cast_ofNat] at hr
  rw [hg, hr] at h
  rw [show (9 : ℕ) = 2 * 4 + 1 by norm_num, sqrt_odd_power _ (by positivity)] at h
  rw [Real.sqrt_div hb.le] at h
  unfold gaussianMass
  rw [Real.sqrt_div Real.pi_pos.le]
  convert h using 1
  · simp only [neg_mul]
  · field_simp [ne_of_gt hb, ne_of_gt (Real.sqrt_pos.mpr hb),
      ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))]
    ring_nf
    norm_num [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

lemma integral_even_gaussian_ten (b : ℝ) (hb : 0 < b) :
    (∫ t in Ioi (0 : ℝ), t ^ 10 * Real.exp (-(b / 2 * t ^ 2))) =
      945 * gaussianMass / (b ^ 5 * Real.sqrt b) := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := (2 : ℝ)) (q := (10 : ℝ)) (b := b / 2)
    (by norm_num) (by norm_num) (by positivity)
  have hg := Real.Gamma_nat_add_half 5
  norm_num at hg
  norm_num only [show ((10 : ℝ) + 1) / 2 = 11 / 2 by norm_num,
    show -((10 : ℝ) + 1) / 2 = -(11 : ℝ) / 2 by norm_num, Real.rpow_ofNat] at h
  have hr := rpow_neg_half_nat (b / 2) (by positivity) 11
  norm_num only [Nat.cast_ofNat] at hr
  rw [hg, hr] at h
  rw [show (11 : ℕ) = 2 * 5 + 1 by norm_num, sqrt_odd_power _ (by positivity)] at h
  rw [Real.sqrt_div hb.le] at h
  unfold gaussianMass
  rw [Real.sqrt_div Real.pi_pos.le]
  convert h using 1
  · simp only [neg_mul]
  · field_simp [ne_of_gt hb, ne_of_gt (Real.sqrt_pos.mpr hb),
      ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))]
    ring_nf
    norm_num [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

end BerryEsseen.LowFrequencyCancellation
#print axioms BerryEsseen.LowFrequencyCancellation.J_le_corners
#print axioms BerryEsseen.LowFrequencyCancellation.integral_scaledCore
#print axioms BerryEsseen.LowFrequencyCancellation.integral_even_gaussian_ten

namespace BerryEsseen.LowFrequencyCancellation

/-- Expanding the H rotation before taking absolute values retains cancellation
and has only a linear |H| cost. This holds for every real phase. -/
lemma trig_cancellation (A B θ v : ℝ) :
    |A * Real.sin (θ + v) - B * Real.cos (θ + v)| ≤
      |B - A * v| + |A| * (|v| ^ 3 / 6) + |B| * (v ^ 2 / 2) +
      |θ| * (|A| + |B| * |v|) := by
  have hfirst : |A * Real.sin v - B * Real.cos v| ≤
      |B - A * v| + |A| * |Real.sin v - v| + |B| * |Real.cos v - 1| := by
    calc
      _ = |(A * v - B) + A * (Real.sin v - v) - B * (Real.cos v - 1)| := by congr 1; ring
      _ ≤ |(A * v - B) + A * (Real.sin v - v)| + |B * (Real.cos v - 1)| := abs_sub _ _
      _ ≤ (|A * v - B| + |A * (Real.sin v - v)|) + |B * (Real.cos v - 1)| :=
        add_le_add (abs_add_le _ _) (le_refl _)
      _ = _ := by rw [abs_sub_comm (A * v) B]; simp only [abs_mul]
  have hsecond : |A * Real.cos v + B * Real.sin v| ≤ |A| + |B| * |Real.sin v| := by
    calc
      _ ≤ |A * Real.cos v| + |B * Real.sin v| := abs_add_le _ _
      _ = |A| * |Real.cos v| + |B| * |Real.sin v| := by simp only [abs_mul]
      _ ≤ _ := add_le_add (by simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (Real.abs_cos_le_one v) (abs_nonneg A)) (le_refl _)
  have hsin : |Real.sin v - v| ≤ |v| ^ 3 / 6 := by
    rw [abs_sub_comm]; exact Real.abs_sub_sin_le v
  have hcoarse : |A * Real.sin (θ + v) - B * Real.cos (θ + v)| ≤
      |A * Real.sin v - B * Real.cos v| + |θ| * |A * Real.cos v + B * Real.sin v| := by
    rw [show A * Real.sin (θ + v) - B * Real.cos (θ + v) =
      Real.cos θ * (A * Real.sin v - B * Real.cos v) +
      Real.sin θ * (A * Real.cos v + B * Real.sin v) by rw [Real.sin_add, Real.cos_add]; ring]
    calc
      _ ≤ |Real.cos θ * (A * Real.sin v - B * Real.cos v)| +
          |Real.sin θ * (A * Real.cos v + B * Real.sin v)| := abs_add_le _ _
      _ = |Real.cos θ| * |A * Real.sin v - B * Real.cos v| +
          |Real.sin θ| * |A * Real.cos v + B * Real.sin v| := by simp only [abs_mul]
      _ ≤ _ := add_le_add (by simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (Real.abs_cos_le_one θ) (abs_nonneg _))
        (mul_le_mul_of_nonneg_right Real.abs_sin_le_abs (abs_nonneg _))
  calc
    _ ≤ |A * Real.sin v - B * Real.cos v| + |θ| * |A * Real.cos v + B * Real.sin v| := hcoarse
    _ ≤ (|B - A * v| + |A| * |Real.sin v - v| + |B| * |Real.cos v - 1|) +
        |θ| * (|A| + |B| * |Real.sin v|) :=
      add_le_add hfirst (mul_le_mul_of_nonneg_left hsecond (abs_nonneg θ))
    _ ≤ _ := by
      exact add_le_add
        (add_le_add (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hsin (abs_nonneg A)))
          (mul_le_mul_of_nonneg_left (abs_cos_sub_one v) (abs_nonneg B)))
        (mul_le_mul_of_nonneg_left
          (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left Real.abs_sin_le_abs (abs_nonneg B))) (abs_nonneg θ))

lemma leadingIntegrand_eq (μ : ProbabilityMeasure ℝ) (n : ℕ) (H t : ℝ) (ht : 0 < t) :
    leadingIntegrand μ n H t = (n : ℝ) * Real.exp (-(((n - 1 : ℕ) : ℝ) / 2 * t ^ 2)) *
      |quarticCoeff μ * t * Real.sin (H * t + ((n - 1 : ℕ) : ℝ) * gamma μ * t ^ 3 / 6) -
        fifthCoeff μ * t ^ 2 * Real.cos (H * t + ((n - 1 : ℕ) : ℝ) * gamma μ * t ^ 3 / 6)| := by
  unfold leadingIntegrand
  rw [leading_rotation_im]
  rw [show quarticCoeff μ * t ^ 4 * Real.sin (H * t + ((n - 1 : ℕ) : ℝ) * gamma μ * t ^ 3 / 6) -
      fifthCoeff μ * t ^ 5 * Real.cos (H * t + ((n - 1 : ℕ) : ℝ) * gamma μ * t ^ 3 / 6) =
      t ^ 3 * (quarticCoeff μ * t * Real.sin (H * t + ((n - 1 : ℕ) : ℝ) * gamma μ * t ^ 3 / 6) -
      fifthCoeff μ * t ^ 2 * Real.cos (H * t + ((n - 1 : ℕ) : ℝ) * gamma μ * t ^ 3 / 6)) by ring]
  rw [abs_mul, abs_of_nonneg (show 0 ≤ (n : ℝ) * Real.exp _ by positivity),
    abs_mul, abs_of_pos (pow_pos ht 3)]
  field_simp [ne_of_gt ht]

def pairedMajor (n : ℕ) (H g aStar Z z c t : ℝ) : ℝ :=
  (n : ℝ) * scaledCore ((n : ℝ) - 1) z c t +
  ((n : ℝ) * aStar * ((n : ℝ) - 1) ^ 3 * g ^ 3 / 1296) *
    (t ^ 10 * Real.exp (-(((n : ℝ) - 1) / 2 * t ^ 2))) +
  ((n : ℝ) * Z * ((n : ℝ) - 1) ^ 2 * g ^ 2 / 72) *
    (t ^ 8 * Real.exp (-(((n : ℝ) - 1) / 2 * t ^ 2))) +
  ((n : ℝ) * |H| * aStar) * (t ^ 2 * Real.exp (-(((n : ℝ) - 1) / 2 * t ^ 2))) +
  ((n : ℝ) * |H| * Z * ((n : ℝ) - 1) * g / 6) *
    (t ^ 6 * Real.exp (-(((n : ℝ) - 1) / 2 * t ^ 2)))

/-- The genuine signed pairing is retained before every absolute value. -/
theorem leading_paired_pointwise (μ : ProbabilityMeasure ℝ) (n : ℕ) (hn : 2 < n)
    (H t g aStar Z : ℝ) (ht : 0 < t) (hg : |gamma μ| ≤ g)
    (ha : |quarticCoeff μ| ≤ aStar) (hZ : |fifthCoeff μ| ≤ Z) :
    leadingIntegrand μ n H t ≤ pairedMajor n H g aStar Z (fifthCoeff μ) (actualC5 μ) t := by
  have hn2 : (2 : ℝ) < (n : ℝ) := Nat.cast_lt.mpr hn
  have hb : 0 < (n : ℝ) - 1 := by linarith
  have hpred : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub (by omega : 1 ≤ n)]; norm_num
  have ha0 : 0 ≤ aStar := (abs_nonneg _).trans ha
  have hz0 : 0 ≤ Z := (abs_nonneg _).trans hZ
  have hg0 : 0 ≤ g := (abs_nonneg _).trans hg
  let v := ((n : ℝ) - 1) * gamma μ * t ^ 3 / 6
  let q := ((n : ℝ) - 1) * g * t ^ 3 / 6
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hv : |v| ≤ q := by
    dsimp [v, q]
    rw [abs_div, abs_mul, abs_mul, abs_of_pos hb, abs_of_nonneg (pow_nonneg ht.le 3),
      abs_of_pos (by norm_num : (0 : ℝ) < 6)]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg hb.le) (pow_nonneg ht.le 3)) (by norm_num)
  have hv3 := pow_le_pow_left₀ (abs_nonneg _) hv 3
  have hv2 := pow_le_pow_left₀ (abs_nonneg _) hv 2
  have hA : |quarticCoeff μ * t| ≤ aStar * t := by
    rw [abs_mul, abs_of_pos ht]; exact mul_le_mul_of_nonneg_right ha ht.le
  have hB : |fifthCoeff μ * t ^ 2| ≤ Z * t ^ 2 := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg t)]; exact mul_le_mul_of_nonneg_right hZ (sq_nonneg t)
  have htrig := trig_cancellation (quarticCoeff μ * t) (fifthCoeff μ * t ^ 2) (H * t) v
  have hupper : |quarticCoeff μ * t * Real.sin (H * t + v) -
      fifthCoeff μ * t ^ 2 * Real.cos (H * t + v)| ≤
      |fifthCoeff μ * t ^ 2 - quarticCoeff μ * t * v| +
      (aStar * t) * (q ^ 3 / 6) + (Z * t ^ 2) * (q ^ 2 / 2) +
      (|H| * t) * (aStar * t + Z * t ^ 2 * q) := by
    calc
      _ ≤ |fifthCoeff μ * t ^ 2 - quarticCoeff μ * t * v| +
          |quarticCoeff μ * t| * (|v| ^ 3 / 6) + |fifthCoeff μ * t ^ 2| * (v ^ 2 / 2) +
          |H * t| * (|quarticCoeff μ * t| + |fifthCoeff μ * t ^ 2| * |v|) := htrig
      _ ≤ _ := by
        rw [abs_mul H t, abs_of_pos ht, ← sq_abs v]
        exact add_le_add
          (add_le_add (add_le_add (le_refl _)
            (mul_le_mul hA (div_le_div_of_nonneg_right hv3 (by norm_num)) (by positivity) (by positivity)))
            (mul_le_mul hB (div_le_div_of_nonneg_right hv2 (by norm_num)) (by positivity) (by positivity)))
          (mul_le_mul_of_nonneg_left
            (add_le_add hA (mul_le_mul hB hv (abs_nonneg _) (by positivity))) (by positivity))
  have heq : fifthCoeff μ * t ^ 2 - quarticCoeff μ * t * v =
      fifthCoeff μ * t ^ 2 - ((n : ℝ) - 1) * actualC5 μ * t ^ 4 := by dsimp [v, actualC5]; ring
  rw [heq] at hupper
  rw [leadingIntegrand_eq μ n H t ht, hpred]
  have hh := mul_le_mul_of_nonneg_left hupper
    (show 0 ≤ (n : ℝ) * Real.exp (-(((n : ℝ) - 1) / 2 * t ^ 2)) by positivity)
  convert hh using 1
  unfold pairedMajor scaledCore
  dsimp [v, q]
  ring

end BerryEsseen.LowFrequencyCancellation
#print axioms BerryEsseen.LowFrequencyCancellation.trig_cancellation
#print axioms BerryEsseen.LowFrequencyCancellation.leading_paired_pointwise

namespace BerryEsseen.LowFrequencyCancellation

lemma integrable_pairedMajor (n : ℕ) (hn : 2 < n) (H g aStar Z z c : ℝ) :
    Integrable (pairedMajor n H g aStar Z z c) := by
  have hn2 : (2 : ℝ) < (n : ℝ) := Nat.cast_lt.mpr hn
  have hb : 0 < (n : ℝ) - 1 := by linarith
  exact (((((integrable_scaledCore _ z c hb).const_mul (n : ℝ)).add
    ((integrable_gaussian_power 10 (((n : ℝ) - 1) / 2) (by positivity)).const_mul
      ((n : ℝ) * aStar * ((n : ℝ) - 1) ^ 3 * g ^ 3 / 1296))).add
    ((integrable_gaussian_power 8 (((n : ℝ) - 1) / 2) (by positivity)).const_mul
      ((n : ℝ) * Z * ((n : ℝ) - 1) ^ 2 * g ^ 2 / 72))).add
    ((integrable_gaussian_power 2 (((n : ℝ) - 1) / 2) (by positivity)).const_mul
      ((n : ℝ) * |H| * aStar))).add
    ((integrable_gaussian_power 6 (((n : ℝ) - 1) / 2) (by positivity)).const_mul
      ((n : ℝ) * |H| * Z * ((n : ℝ) - 1) * g / 6))

lemma pairedMajor_nonneg (n : ℕ) (hn : 2 < n) (H g aStar Z z c t : ℝ)
    (hg : 0 ≤ g) (ha : 0 ≤ aStar) (hZ : 0 ≤ Z) : 0 ≤ pairedMajor n H g aStar Z z c t := by
  have hn2 : (2 : ℝ) < (n : ℝ) := Nat.cast_lt.mpr hn
  have hb : 0 < (n : ℝ) - 1 := by linarith
  unfold pairedMajor scaledCore
  positivity

/-- All four correction costs, including their exact 945, 105 and 15 moments. -/
lemma integral_pairedMajor (n : ℕ) (hn : 2 < n) (H g aStar Z z c : ℝ) :
    Real.sqrt n * (∫ t in Ioi (0 : ℝ), pairedMajor n H g aStar Z z c t) =
      factorF n * J z c + gaussianMass * factorF n / ((n : ℝ) - 1) *
        (35 * aStar * g ^ 3 / 48 + 35 * Z * g ^ 2 / 24) +
      gaussianMass * factorF n * (aStar + 5 * Z * g / (2 * ((n : ℝ) - 1))) * |H| := by
  have hn2 : (2 : ℝ) < (n : ℝ) := Nat.cast_lt.mpr hn
  have hb : 0 < (n : ℝ) - 1 := by linarith
  let f0 := fun t : ℝ => (n : ℝ) * scaledCore ((n : ℝ) - 1) z c t
  let f1 := fun t : ℝ => ((n : ℝ) * aStar * ((n : ℝ) - 1) ^ 3 * g ^ 3 / 1296) *
    (t ^ 10 * Real.exp (-(((n : ℝ) - 1) / 2 * t ^ 2)))
  let f2 := fun t : ℝ => ((n : ℝ) * Z * ((n : ℝ) - 1) ^ 2 * g ^ 2 / 72) *
    (t ^ 8 * Real.exp (-(((n : ℝ) - 1) / 2 * t ^ 2)))
  let f3 := fun t : ℝ => ((n : ℝ) * |H| * aStar) *
    (t ^ 2 * Real.exp (-(((n : ℝ) - 1) / 2 * t ^ 2)))
  let f4 := fun t : ℝ => ((n : ℝ) * |H| * Z * ((n : ℝ) - 1) * g / 6) *
    (t ^ 6 * Real.exp (-(((n : ℝ) - 1) / 2 * t ^ 2)))
  have hi0 : IntegrableOn f0 (Ioi (0 : ℝ)) := ((integrable_scaledCore _ z c hb).const_mul _).integrableOn
  have hi1 : IntegrableOn f1 (Ioi (0 : ℝ)) :=
    ((integrable_gaussian_power 10 (((n : ℝ) - 1) / 2) (by positivity)).const_mul _).integrableOn
  have hi2 : IntegrableOn f2 (Ioi (0 : ℝ)) :=
    ((integrable_gaussian_power 8 (((n : ℝ) - 1) / 2) (by positivity)).const_mul _).integrableOn
  have hi3 : IntegrableOn f3 (Ioi (0 : ℝ)) :=
    ((integrable_gaussian_power 2 (((n : ℝ) - 1) / 2) (by positivity)).const_mul _).integrableOn
  have hi4 : IntegrableOn f4 (Ioi (0 : ℝ)) :=
    ((integrable_gaussian_power 6 (((n : ℝ) - 1) / 2) (by positivity)).const_mul _).integrableOn
  have h01 : IntegrableOn (fun t => f0 t + f1 t) (Ioi (0 : ℝ)) := hi0.add hi1
  have h012 : IntegrableOn (fun t => f0 t + f1 t + f2 t) (Ioi (0 : ℝ)) := h01.add hi2
  have h0123 : IntegrableOn (fun t => f0 t + f1 t + f2 t + f3 t) (Ioi (0 : ℝ)) := h012.add hi3
  change Real.sqrt n * (∫ t in Ioi (0 : ℝ), f0 t + f1 t + f2 t + f3 t + f4 t) = _
  rw [integral_add h0123 hi4, integral_add h012 hi3, integral_add h01 hi2, integral_add hi0 hi1]
  dsimp only [f0, f1, f2, f3, f4]
  rw [integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_scaledCore _ z c hb, integral_even_gaussian_ten _ hb, integral_even_gaussian_eight _ hb,
    integral_even_gaussian_two _ hb, integral_even_gaussian_six _ hb, factorF_eq n hn]
  field_simp [ne_of_gt hb, ne_of_gt (Real.sqrt_pos.mpr hb)]
  ring

/-- The actual leading cancellation price. Jstar is still an explicit upper
price for J(actual z₅, actual signed c₅), with no corner numerics assumed solved. -/
theorem leading_paired_cost (μ : ProbabilityMeasure ℝ) (n : ℕ) (hn : 2 < n) (H g aStar Z Iu Jstar : ℝ)
    (hg : |gamma μ| ≤ g) (ha : |quarticCoeff μ| ≤ aStar) (hZ : |fifthCoeff μ| ≤ Z)
    (hIu : gaussianMass ≤ Iu) (hJ : J (fifthCoeff μ) (actualC5 μ) ≤ Jstar) :
    IntegrableOn (leadingIntegrand μ n H) (Ioc (0 : ℝ) (1 / 2)) ∧
    Real.sqrt n * (∫ t in Ioc (0 : ℝ) (1 / 2), leadingIntegrand μ n H t) ≤
      factorF n * Jstar + factorF n * Iu / ((n : ℝ) - 1) *
        (35 * aStar * g ^ 3 / 48 + 35 * Z * g ^ 2 / 24) +
      factorF n * Iu * (aStar + 5 * Z * g / (2 * ((n : ℝ) - 1))) * |H| := by
  have hg0 : 0 ≤ g := (abs_nonneg _).trans hg
  have ha0 : 0 ≤ aStar := (abs_nonneg _).trans ha
  have hZ0 : 0 ≤ Z := (abs_nonneg _).trans hZ
  have hn2 : (2 : ℝ) < (n : ℝ) := Nat.cast_lt.mpr hn
  have hb : 0 < (n : ℝ) - 1 := by linarith
  have hmajor := integrable_pairedMajor n hn H g aStar Z (fifthCoeff μ) (actualC5 μ)
  have hnmajor := pairedMajor_nonneg n hn H g aStar Z (fifthCoeff μ) (actualC5 μ)
  have hi : IntegrableOn (leadingIntegrand μ n H) (Ioc (0 : ℝ) (1 / 2)) := by
    apply hmajor.integrableOn.mono' (measurable_leadingIntegrand μ n H).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (leadingIntegrand_nonneg μ n H t ht.1.le)]
    exact leading_paired_pointwise μ n hn H t g aStar Z ht.1 hg ha hZ
  refine ⟨hi, ?_⟩
  have hfinite : (∫ t in Ioc (0 : ℝ) (1 / 2), leadingIntegrand μ n H t) ≤
      ∫ t in Ioc (0 : ℝ) (1 / 2), pairedMajor n H g aStar Z (fifthCoeff μ) (actualC5 μ) t := by
    apply integral_mono_ae hi hmajor.integrableOn
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact leading_paired_pointwise μ n hn H t g aStar Z ht.1 hg ha hZ
  have htail : (∫ t in Ioc (0 : ℝ) (1 / 2), pairedMajor n H g aStar Z (fifthCoeff μ) (actualC5 μ) t) ≤
      ∫ t in Ioi (0 : ℝ), pairedMajor n H g aStar Z (fifthCoeff μ) (actualC5 μ) t := by
    apply setIntegral_mono_set hmajor.integrableOn
    · exact Eventually.of_forall fun t => hnmajor t hg0 ha0 hZ0
    · exact Eventually.of_forall fun t ht => ht.1
  have hmass : gaussianMass * factorF n / ((n : ℝ) - 1) *
      (35 * aStar * g ^ 3 / 48 + 35 * Z * g ^ 2 / 24) +
      gaussianMass * factorF n * (aStar + 5 * Z * g / (2 * ((n : ℝ) - 1))) * |H| ≤
      factorF n * Iu / ((n : ℝ) - 1) * (35 * aStar * g ^ 3 / 48 + 35 * Z * g ^ 2 / 24) +
      factorF n * Iu * (aStar + 5 * Z * g / (2 * ((n : ℝ) - 1))) * |H| := by
    have hfn := factorF_nonneg n hn
    have hw : 0 ≤ factorF n / ((n : ℝ) - 1) * (35 * aStar * g ^ 3 / 48 + 35 * Z * g ^ 2 / 24) +
        factorF n * (aStar + 5 * Z * g / (2 * ((n : ℝ) - 1))) * |H| := by positivity
    convert mul_le_mul_of_nonneg_right hIu hw using 1 <;> ring
  calc
    _ ≤ Real.sqrt n * (∫ t in Ioi (0 : ℝ), pairedMajor n H g aStar Z (fifthCoeff μ) (actualC5 μ) t) :=
      mul_le_mul_of_nonneg_left (hfinite.trans htail) (Real.sqrt_nonneg _)
    _ = _ := integral_pairedMajor n hn H g aStar Z (fifthCoeff μ) (actualC5 μ)
    _ ≤ _ := by
      have hjprice := mul_le_mul_of_nonneg_left hJ (factorF_nonneg n hn)
      have hh := add_le_add hjprice hmass
      convert hh using 1 <;> ring

end BerryEsseen.LowFrequencyCancellation
#print axioms BerryEsseen.LowFrequencyCancellation.integral_pairedMajor
#print axioms BerryEsseen.LowFrequencyCancellation.leading_paired_cost

namespace BerryEsseen.LowFrequencyCancellation

/-- The original paired coefficients. Jstar remains an explicit corner price. -/
def pairedL0 (n : ℕ) (g aStar Z Iu Jstar : ℝ) : ℝ :=
  factorF n * Jstar + factorF n * Iu / ((n : ℝ) - 1) *
    (35 * aStar * g ^ 3 / 48 + 35 * Z * g ^ 2 / 24) + 251 * g ^ 3 / 17280

def pairedLH (n : ℕ) (g aStar Z Iu : ℝ) : ℝ :=
  factorF n * Iu * (aStar + 5 * Z * g / (2 * ((n : ℝ) - 1))) + 251 * g ^ 2 / 4800

/-- Full actual-law cancellation alternative of ut:low. The signed physical
coefficient c₅ is fixed by the law, and Jstar is an explicit unsolved price. -/
theorem low_frequency_paired (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (h6 : Integrable (fun x : ℝ => |x| ^ 6) (μ : Measure ℝ)) (n : ℕ) (hn : 2 < n)
    (H g M M6bar aStar Z Iu Jstar : ℝ) (hg : |gamma μ| ≤ g) (hgcap : g ≤ 37 / 20)
    (hM4 : moment μ 4 ≤ M) (hMupper : M ≤ 111 / 10) (hM6 : sixthMoment μ ≤ M6bar)
    (ha : |quarticCoeff μ| ≤ aStar) (hZ : |fifthCoeff μ| ≤ Z) (hIu : gaussianMass ≤ Iu) (hJ : J (fifthCoeff μ) (actualC5 μ) ≤ Jstar) :
    IntegrableOn (lowIntegrand μ n H) (Ioc (0 : ℝ) (1 / 2)) ∧
    Real.sqrt n * I0 μ n H ≤ pairedL0 n g aStar Z Iu Jstar + pairedLH n g aStar Z Iu * |H| +
      coefficientL2 n M g M6bar aStar Z / Real.sqrt n := by
  have hnNat : 0 < n := by omega
  have hn0 : 0 < (n : ℝ) := Nat.cast_pos.mpr hnNat
  have hs0 : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
  have hlead := leading_paired_cost μ n hn H g aStar Z Iu Jstar hg ha hZ hIu hJ
  have hrotation := gaussian_rotation_cost μ n hnNat H g hg
  have hfirst := first_error_cost μ h h6 n hn g M6bar hg hgcap hM6
  have hsecond := second_error_cost μ h h6 n hn g M M6bar aStar Z hg hgcap hM4 hMupper hM6 ha hZ
  have hmajor : IntegrableOn (fun t => leadingIntegrand μ n H t + rotatedGaussianIntegrand μ n H t +
      firstIntegrand μ n t + secondIntegrand μ n t) (Ioc (0 : ℝ) (1 / 2)) :=
    ((hlead.1.add hrotation.1).add hfirst.1).add hsecond.1
  have hi : IntegrableOn (lowIntegrand μ n H) (Ioc (0 : ℝ) (1 / 2)) := by
    apply hmajor.mono' (measurable_lowIntegrand μ n H).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (lowIntegrand_nonneg μ n H t ht.1.le)]
    exact lowIntegrand_bound μ n H t ht.1
  refine ⟨hi, ?_⟩
  have htotal : I0 μ n H ≤
      (∫ t in Ioc (0 : ℝ) (1 / 2), leadingIntegrand μ n H t) +
      (∫ t in Ioc (0 : ℝ) (1 / 2), rotatedGaussianIntegrand μ n H t) +
      (∫ t in Ioc (0 : ℝ) (1 / 2), firstIntegrand μ n t) +
      (∫ t in Ioc (0 : ℝ) (1 / 2), secondIntegrand μ n t) := by
    unfold I0
    calc
      _ ≤ ∫ t in Ioc (0 : ℝ) (1 / 2), leadingIntegrand μ n H t + rotatedGaussianIntegrand μ n H t +
          firstIntegrand μ n t + secondIntegrand μ n t := by
        apply integral_mono_ae hi hmajor
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        exact lowIntegrand_bound μ n H t ht.1
      _ = _ := by
        have hlr : IntegrableOn (fun t => leadingIntegrand μ n H t + rotatedGaussianIntegrand μ n H t)
            (Ioc (0 : ℝ) (1 / 2)) := hlead.1.add hrotation.1
        have hlrf : IntegrableOn (fun t => leadingIntegrand μ n H t + rotatedGaussianIntegrand μ n H t +
            firstIntegrand μ n t) (Ioc (0 : ℝ) (1 / 2)) := hlr.add hfirst.1
        rw [integral_add hlrf hsecond.1, integral_add hlr hfirst.1, integral_add hlead.1 hrotation.1]
  have herror : (∫ t in Ioc (0 : ℝ) (1 / 2), firstIntegrand μ n t) +
      (∫ t in Ioc (0 : ℝ) (1 / 2), secondIntegrand μ n t) ≤
        coefficientL2 n M g M6bar aStar Z / (n : ℝ) := by
    calc
      _ ≤ sixthPrice g M6bar / (2 * (n : ℝ) * rateA n ^ 2) +
          totalSixthPrice aStar Z (sixthPrice g M6bar) ^ 2 / (2 * (n : ℝ) * rateB n M ^ 3) :=
        add_le_add hfirst.2 hsecond.2
      _ = _ := by unfold coefficientL2; ring
  have heq : Real.sqrt n * (coefficientL2 n M g M6bar aStar Z / (n : ℝ)) =
      coefficientL2 n M g M6bar aStar Z / Real.sqrt n := by
    apply (eq_div_iff (ne_of_gt hs0)).mpr
    field_simp [ne_of_gt hn0]
    ring_nf
    rw [Real.sq_sqrt hn0.le]
    ring
  have herr := (mul_le_mul_of_nonneg_left herror hs0.le).trans_eq heq
  calc
    _ ≤ Real.sqrt n * (∫ t in Ioc (0 : ℝ) (1 / 2), leadingIntegrand μ n H t) +
        Real.sqrt n * (∫ t in Ioc (0 : ℝ) (1 / 2), rotatedGaussianIntegrand μ n H t) +
        Real.sqrt n * ((∫ t in Ioc (0 : ℝ) (1 / 2), firstIntegrand μ n t) +
          (∫ t in Ioc (0 : ℝ) (1 / 2), secondIntegrand μ n t)) := by
      convert mul_le_mul_of_nonneg_left htotal hs0.le using 1
      ring
    _ ≤ (factorF n * Jstar + factorF n * Iu / ((n : ℝ) - 1) * (35 * aStar * g ^ 3 / 48 + 35 * Z * g ^ 2 / 24) + factorF n * Iu * (aStar + 5 * Z * g / (2 * ((n : ℝ) - 1))) * |H|) +
        (251 * g ^ 3 / 17280 + 251 * g ^ 2 * |H| / 4800) +
        coefficientL2 n M g M6bar aStar Z / Real.sqrt n :=
      add_le_add (add_le_add hlead.2 hrotation.2) herr
    _ = _ := by unfold pairedL0 pairedLH; ring


/-- Closed rectangles and four explicit corner prices supply the physical J
input; no corner value or rectangle acquisition is asserted here. -/
theorem low_frequency_paired_rectangle (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (h6 : Integrable (fun x : ℝ => |x| ^ 6) (μ : Measure ℝ)) (n : ℕ) (hn : 2 < n)
    (H g M M6bar aStar Z Iu Jstar zlo zhi clo chi : ℝ)
    (hg : |gamma μ| ≤ g) (hgcap : g ≤ 37 / 20) (hM4 : moment μ 4 ≤ M) (hMupper : M ≤ 111 / 10)
    (hM6 : sixthMoment μ ≤ M6bar) (ha : |quarticCoeff μ| ≤ aStar) (hZ : |fifthCoeff μ| ≤ Z)
    (hIu : gaussianMass ≤ Iu) (hz : fifthCoeff μ ∈ Icc zlo zhi) (hc : actualC5 μ ∈ Icc clo chi)
    (h00 : J zlo clo ≤ Jstar) (h01 : J zlo chi ≤ Jstar)
    (h10 : J zhi clo ≤ Jstar) (h11 : J zhi chi ≤ Jstar) :
    IntegrableOn (lowIntegrand μ n H) (Ioc (0 : ℝ) (1 / 2)) ∧
    Real.sqrt n * I0 μ n H ≤ pairedL0 n g aStar Z Iu Jstar + pairedLH n g aStar Z Iu * |H| +
      coefficientL2 n M g M6bar aStar Z / Real.sqrt n := by
  exact low_frequency_paired μ h h6 n hn H g M M6bar aStar Z Iu Jstar hg hgcap hM4 hMupper hM6 ha hZ hIu
    (J_le_rectangle_price _ _ zlo zhi clo chi Jstar hz hc h00 h01 h10 h11)

end BerryEsseen.LowFrequencyCancellation
#print axioms BerryEsseen.LowFrequencyCancellation.low_frequency_paired
#print axioms BerryEsseen.LowFrequencyCancellation.low_frequency_paired_rectangle
