module

public import BerryEsseen.LowFrequencyCancellation
public import BerryEsseen.GaussianMills

@[expose] public section

/-! 2026-10-28: exact analytic prices for the genuine Gaussian cancellation
integral J. No corner numerics, profile enclosure, or continued fraction is asserted. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators Interval
open BerryEsseen.LowFrequencyError BerryEsseen.LowFrequencyLeading BerryEsseen.LowFrequencyCancellation
open BerryEsseen.GaussianTools BerryEsseen.GaussianMills

namespace BerryEsseen.GaussianCancellationPrice

def weight (x : ℝ) : ℝ := Real.exp (-(x ^ 2) / 2)
def tailWeight (r : ℝ) : ℝ := ∫ x in Ioi r, weight x
/-- The manuscript's actual Mills integral, not a freely specified ratio. -/
def Mills (r : ℝ) : ℝ := ∫ t in Ioi (0 : ℝ), Real.exp (-r * t - t ^ 2 / 2)

lemma weight_pos (x : ℝ) : 0 < weight x := Real.exp_pos _
lemma weight_eq_phi (x : ℝ) : weight x = Real.sqrt (2 * Real.pi) * phi x := by
  rw [phi_formula]
  unfold weight
  field_simp [ne_of_gt (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < 2 * Real.pi))]

lemma integrable_pow_weight (k : ℕ) : Integrable (fun x : ℝ => x ^ k * weight x) := by
  simpa only [weight, one_div_mul_eq_div, neg_div] using integrable_gaussian_power k (1 / 2) (by norm_num)

lemma integrable_weight : Integrable weight := by
  simpa only [pow_zero, one_mul] using integrable_pow_weight 0

lemma tailWeight_eq_phi (r : ℝ) : tailWeight r = Real.sqrt (2 * Real.pi) * tail r := by
  have heq : weight = (fun x => Real.sqrt (2 * Real.pi) * phi x) := funext weight_eq_phi
  rw [tailWeight, heq, integral_const_mul, integral_phi_Ioi]
  rfl

lemma integral_pow_weight_eq (k : ℕ) (r : ℝ) :
    (∫ x in Ioi r, x ^ k * weight x) = Real.sqrt (2 * Real.pi) * (∫ x in Ioi r, x ^ k * phi x) := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    change x ^ k * weight x = Real.sqrt (2 * Real.pi) * (x ^ k * phi x)
    rw [weight_eq_phi]
    ring

lemma hasDerivAt_cube_phi (x : ℝ) : HasDerivAt (fun t : ℝ => t ^ 3 * phi t)
    (3 * (x ^ 2 * phi x) - x ^ 4 * phi x) x := by
  convert ((hasDerivAt_id' x).fun_pow 3).fun_mul (hasDerivAt_phi x) using 1
  ring

lemma tendsto_cube_phi : Tendsto (fun x : ℝ => x ^ 3 * phi x) atTop (𝓝 (0 : ℝ)) := by
  have hd : Integrable (fun x : ℝ => 3 * (x ^ 2 * phi x) - x ^ 4 * phi x) :=
    ((integrable_pow_mul_phi 2).const_mul 3).sub (integrable_pow_mul_phi 4)
  exact tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi (a := 0)
    (fun x _ => hasDerivAt_cube_phi x) hd.integrableOn (integrable_pow_mul_phi 3).integrableOn

lemma integral_four_phi_Ioi (r : ℝ) :
    (∫ x in Ioi r, x ^ 4 * phi x) = (r ^ 3 + 3 * r) * phi r + 3 * tail r := by
  have h2 := (integrable_pow_mul_phi 2).const_mul 3
  have h4 := integrable_pow_mul_phi 4
  have hd : IntegrableOn (fun x : ℝ => 3 * (x ^ 2 * phi x) - x ^ 4 * phi x) (Ioi r) :=
    (h2.sub h4).integrableOn
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun x _ => hasDerivAt_cube_phi x) hd tendsto_cube_phi
  rw [integral_sub h2.integrableOn h4.integrableOn, integral_const_mul, integral_sq_mul_phi_Ioi] at h
  unfold tail
  linarith

lemma integral_sq_weight_Ioi (r : ℝ) :
    (∫ x in Ioi r, x ^ 2 * weight x) = r * weight r + tailWeight r := by
  rw [integral_pow_weight_eq, integral_sq_mul_phi_Ioi, weight_eq_phi, tailWeight_eq_phi]
  unfold tail
  ring

lemma integral_four_weight_Ioi (r : ℝ) :
    (∫ x in Ioi r, x ^ 4 * weight x) = (r ^ 3 + 3 * r) * weight r + 3 * tailWeight r := by
  rw [integral_pow_weight_eq, integral_four_phi_Ioi, weight_eq_phi, tailWeight_eq_phi]
  ring

lemma tailWeight_zero : tailWeight 0 = gaussianMass := by
  have h := integral_even_gaussian_two 1 (by norm_num)
  have hm : (∫ x in Ioi (0 : ℝ), x ^ 2 * weight x) = gaussianMass := by
    simpa only [weight, one_div_mul_eq_div, neg_div, div_one, Real.sqrt_one, mul_one, one_pow] using h
  have ht := integral_sq_weight_Ioi 0
  simpa only [zero_mul, zero_add] using ht.symm.trans hm

lemma tailWeight_nonneg (r : ℝ) : 0 ≤ tailWeight r := integral_nonneg fun x => (weight_pos x).le

lemma tailWeight_le_mass (r : ℝ) (hr : 0 ≤ r) : tailWeight r ≤ gaussianMass := by
  rw [← tailWeight_zero]
  unfold tailWeight
  apply setIntegral_mono_set integrable_weight.integrableOn
  · exact Eventually.of_forall fun x => (weight_pos x).le
  · exact Eventually.of_forall fun x hx => lt_of_le_of_lt hr hx

lemma weight_add (r t : ℝ) : weight (r + t) = weight r * Real.exp (-r * t - t ^ 2 / 2) := by
  unfold weight
  rw [← Real.exp_add]
  congr 1
  ring

lemma mills_integrand_eq (r t : ℝ) : Real.exp (-r * t - t ^ 2 / 2) = (weight r)⁻¹ * weight (r + t) := by
  rw [weight_add]
  field_simp [ne_of_gt (weight_pos r)]

lemma integrable_mills_integrand (r : ℝ) : Integrable (fun t : ℝ => Real.exp (-r * t - t ^ 2 / 2)) := by
  have hi : Integrable (fun t : ℝ => weight (r + t)) := integrable_weight.comp_add_left r
  exact (hi.const_mul (weight r)⁻¹).congr (Eventually.of_forall fun t => (mills_integrand_eq r t).symm)

/-- Actual translation of the Gaussian tail yields the Mills integral. -/
lemma tailWeight_eq_weight_mul_Mills (r : ℝ) : tailWeight r = weight r * Mills r := by
  have hpre : (fun x : ℝ => r + x) ⁻¹' Ioi r = Ioi 0 := by ext x; simp
  have h := (measurableEmbedding_addLeft r).setIntegral_map (μ := volume) weight (Ioi r)
  rw [map_add_left_eq_self, hpre] at h
  change tailWeight r = ∫ x in Ioi (0 : ℝ), weight (r + x) at h
  rw [h]
  have heq : (fun t : ℝ => weight (r + t)) = (fun t => weight r * Real.exp (-r * t - t ^ 2 / 2)) :=
    funext (weight_add r)
  rw [heq, integral_const_mul]
  rfl

lemma Mills_eq_millsRatio (r : ℝ) : Mills r = millsRatio r := by
  have h := tailWeight_eq_weight_mul_Mills r
  rw [tailWeight_eq_phi, weight_eq_phi] at h
  have hs : Real.sqrt (2 * Real.pi) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  have heq : tail r = phi r * Mills r := by
    apply mul_left_cancel₀ hs
    convert h using 1
    ring
  unfold millsRatio
  apply (eq_div_iff (ne_of_gt (phi_pos r))).mpr
  rw [heq]
  ring

end BerryEsseen.GaussianCancellationPrice
#print axioms BerryEsseen.GaussianCancellationPrice.integral_four_weight_Ioi
#print axioms BerryEsseen.GaussianCancellationPrice.tailWeight_eq_weight_mul_Mills
#print axioms BerryEsseen.GaussianCancellationPrice.Mills_eq_millsRatio

namespace BerryEsseen.GaussianCancellationPrice

def signedIntegrand (z c x : ℝ) : ℝ := weight x * (z * x ^ 2 - c * x ^ 4)

lemma integrable_signedIntegrand (z c : ℝ) : Integrable (signedIntegrand z c) := by
  have hi : Integrable (fun x : ℝ => z * (x ^ 2 * weight x) - c * (x ^ 4 * weight x)) :=
    ((integrable_pow_weight 2).const_mul z).sub ((integrable_pow_weight 4).const_mul c)
  convert hi using 1
  ext x
  unfold signedIntegrand
  ring

lemma integral_weight_two_zero : (∫ x in Ioi (0 : ℝ), x ^ 2 * weight x) = gaussianMass := by
  rw [integral_sq_weight_Ioi, tailWeight_zero]
  ring

lemma integral_weight_four_zero : (∫ x in Ioi (0 : ℝ), x ^ 4 * weight x) = 3 * gaussianMass := by
  rw [integral_four_weight_Ioi, tailWeight_zero]
  norm_num

lemma signedIntegral_formula (z c r : ℝ) :
    (∫ x in Ioi r, signedIntegrand z c x) =
      z * (r * weight r + tailWeight r) - c * ((r ^ 3 + 3 * r) * weight r + 3 * tailWeight r) := by
  have heq : signedIntegrand z c = (fun x => z * (x ^ 2 * weight x) - c * (x ^ 4 * weight x)) := by
    funext x; unfold signedIntegrand; ring
  rw [heq, integral_sub ((integrable_pow_weight 2).const_mul z).integrableOn
    ((integrable_pow_weight 4).const_mul c).integrableOn, integral_const_mul, integral_const_mul,
    integral_sq_weight_Ioi, integral_four_weight_Ioi]

lemma signedIntegral_zero (z c : ℝ) : (∫ x in Ioi (0 : ℝ), signedIntegrand z c x) = gaussianMass * (z - 3 * c) := by
  rw [signedIntegral_formula, tailWeight_zero]
  ring

lemma signedIntegral_root (z c r : ℝ) (hroot : c * r ^ 2 = z) :
    (∫ x in Ioi r, signedIntegrand z c x) = -3 * c * r * weight r + (z - 3 * c) * tailWeight r := by
  rw [signedIntegral_formula, ← hroot]
  ring

lemma polynomial_nonneg_before (z c r x : ℝ) (hc : 0 ≤ c) (hr : 0 ≤ r)
    (hroot : c * r ^ 2 = z) (hx0 : 0 ≤ x) (hxr : x ≤ r) : 0 ≤ z * x ^ 2 - c * x ^ 4 := by
  have hsq := (sq_le_sq₀ hx0 hr).mpr hxr
  rw [← hroot, show c * r ^ 2 * x ^ 2 - c * x ^ 4 = c * x ^ 2 * (r ^ 2 - x ^ 2) by ring]
  exact mul_nonneg (mul_nonneg hc (sq_nonneg x)) (sub_nonneg.mpr hsq)

lemma polynomial_nonpos_after (z c r x : ℝ) (hc : 0 ≤ c) (hr : 0 ≤ r)
    (hroot : c * r ^ 2 = z) (hx : r ≤ x) : z * x ^ 2 - c * x ^ 4 ≤ 0 := by
  have hsq := (sq_le_sq₀ hr (hr.trans hx)).mpr hx
  rw [← hroot, show c * r ^ 2 * x ^ 2 - c * x ^ 4 = c * x ^ 2 * (r ^ 2 - x ^ 2) by ring]
  exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hc (sq_nonneg x)) (sub_nonpos.mpr hsq)

/-- A true sign split of the absolute-value integral at its positive root. -/
theorem J_split_at_root (z c r : ℝ) (hc : 0 < c) (hr : 0 < r) (hroot : c * r ^ 2 = z) :
    J z c = gaussianMass * (z - 3 * c) + 6 * c * r * weight r + 2 * (3 * c - z) * tailWeight r := by
  have hj := intervalIntegral.integral_Ioi_sub_Ioi (integrable_jIntegrand z c).integrableOn hr.le
  have hp := intervalIntegral.integral_Ioi_sub_Ioi (integrable_signedIntegrand z c).integrableOn hr.le
  rw [intervalIntegral.integral_of_le hr.le] at hj hp
  have hbefore : (∫ x in Ioc (0 : ℝ) r, jIntegrand z c x) = ∫ x in Ioc (0 : ℝ) r, signedIntegrand z c x := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    unfold jIntegrand signedIntegrand weight
    rw [abs_of_nonneg (polynomial_nonneg_before z c r x hc.le hr.le hroot hx.1.le hx.2)]
  have hafter : (∫ x in Ioi r, jIntegrand z c x) = -(∫ x in Ioi r, signedIntegrand z c x) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    change jIntegrand z c x = -signedIntegrand z c x
    unfold jIntegrand signedIntegrand weight
    rw [abs_of_nonpos (polynomial_nonpos_after z c r x hc.le hr.le hroot hx.le)]
    ring
  rw [hbefore, hafter] at hj
  change J z c - -(∫ x in Ioi r, signedIntegrand z c x) = _ at hj
  rw [signedIntegral_zero, signedIntegral_root z c r hroot] at hp
  rw [signedIntegral_root z c r hroot] at hj
  linarith

lemma root_relation (z c : ℝ) (hz : 0 < z) (hc : 0 < c) : c * Real.sqrt (z / c) ^ 2 = z := by
  rw [Real.sq_sqrt (div_pos hz hc).le]
  field_simp [ne_of_gt hc]

lemma sqrt_product_eq (z c : ℝ) (hz : 0 < z) (hc : 0 < c) :
    Real.sqrt (z * c) = c * Real.sqrt (z / c) := by
  have hroot := root_relation z c hz hc
  have heq : (c * Real.sqrt (z / c)) ^ 2 = z * c := by
    calc
      _ = (c * Real.sqrt (z / c) ^ 2) * c := by ring
      _ = _ := by rw [hroot]
  rw [← heq, Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]

/-- Exact positive-branch formula using the actual Gaussian tail. -/
theorem J_positive_tail (z c : ℝ) (hz : 0 < z) (hc : 0 < c) :
    J z c = gaussianMass * (z - 3 * c) + 6 * Real.sqrt (z * c) * weight (Real.sqrt (z / c)) +
      2 * (3 * c - z) * tailWeight (Real.sqrt (z / c)) := by
  rw [sqrt_product_eq z c hz hc]
  convert J_split_at_root z c (Real.sqrt (z / c)) hc (Real.sqrt_pos.mpr (div_pos hz hc)) (root_relation z c hz hc) using 1
  ring

lemma abs_sub_eq_of_mul_nonpos (u v : ℝ) (huv : u * v ≤ 0) : |u - v| = |u| + |v| := by
  rcases lt_trichotomy u 0 with hu | rfl | hu
  · have hv : 0 ≤ v := (mul_nonpos_iff_neg_imp_nonneg.mp huv).1 hu
    rw [abs_of_nonpos (show u - v ≤ 0 by linarith), abs_of_nonpos hu.le, abs_of_nonneg hv]
    ring
  · simp
  · have hv : v ≤ 0 := (mul_nonpos_iff_pos_imp_nonpos.mp huv).1 hu
    rw [abs_of_nonneg (show 0 ≤ u - v by linarith), abs_of_nonneg hu.le, abs_of_nonpos hv]
    ring

/-- Opposite-sign and all zero boundaries are integrated exactly. -/
theorem J_of_mul_nonpos (z c : ℝ) (hzc : z * c ≤ 0) :
    J z c = gaussianMass * (|z| + 3 * |c|) := by
  have heq : jIntegrand z c = (fun x => |z| * (x ^ 2 * weight x) + |c| * (x ^ 4 * weight x)) := by
    funext x
    have hp : (z * x ^ 2) * (c * x ^ 4) ≤ 0 := by
      rw [show (z * x ^ 2) * (c * x ^ 4) = (z * c) * (x ^ 2 * x ^ 4) by ring]
      exact mul_nonpos_of_nonpos_of_nonneg hzc (by positivity)
    unfold jIntegrand
    rw [abs_sub_eq_of_mul_nonpos _ _ hp]
    rw [abs_mul, abs_of_nonneg (sq_nonneg x), abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ x ^ 4)]
    unfold weight
    ring
  rw [J, heq, integral_add ((integrable_pow_weight 2).const_mul |z|).integrableOn
    ((integrable_pow_weight 4).const_mul |c|).integrableOn, integral_const_mul, integral_const_mul,
    integral_weight_two_zero, integral_weight_four_zero]
  ring

lemma J_neg_neg (z c : ℝ) : J (-z) (-c) = J z c := by
  unfold J
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    unfold jIntegrand
    rw [show (-z) * x ^ 2 - (-c) * x ^ 4 = -(z * x ^ 2 - c * x ^ 4) by ring, abs_neg]

lemma J_zero_left (c : ℝ) : J 0 c = 3 * gaussianMass * |c| := by
  rw [J_of_mul_nonpos 0 c (by simp)]
  simp only [abs_zero, zero_add]
  ring

lemma J_zero_right (z : ℝ) : J z 0 = gaussianMass * |z| := by
  rw [J_of_mul_nonpos z 0 (by simp)]
  simp

end BerryEsseen.GaussianCancellationPrice
#print axioms BerryEsseen.GaussianCancellationPrice.J_split_at_root
#print axioms BerryEsseen.GaussianCancellationPrice.J_positive_tail
#print axioms BerryEsseen.GaussianCancellationPrice.J_of_mul_nonpos

namespace BerryEsseen.GaussianCancellationPrice

/-- The exact ut:mills-norm formula, with the genuine Mills integral. -/
theorem J_positive_Mills (z c : ℝ) (hz : 0 < z) (hc : 0 < c) :
    J z c = gaussianMass * (z - 3 * c) + Real.sqrt (z * c) * Real.exp (-(z / c) / 2) *
      (6 + 2 * (3 - z / c) / (z / c) * Real.sqrt (z / c) * Mills (Real.sqrt (z / c))) := by
  let a := z / c
  let r := Real.sqrt a
  have ha : 0 < a := div_pos hz hc
  have hroot : r ^ 2 = a := Real.sq_sqrt ha.le
  have hca : c * a = z := by dsimp [a]; field_simp [ne_of_gt hc]
  have hK : Real.sqrt (z * c) = c * r := sqrt_product_eq z c hz hc
  have hw : weight r = Real.exp (-a / 2) := by unfold weight; rw [hroot]
  have hcoef : (c * r) * (2 * (3 - a) / a * r) = 2 * (3 * c - z) := by
    calc
      _ = (2 * c * (3 - a) / a) * r ^ 2 := by ring
      _ = (2 * c * (3 - a) / a) * a := by rw [hroot]
      _ = 2 * c * (3 - a) := by field_simp [ne_of_gt ha]
      _ = _ := by nlinarith [hca]
  have hp := J_positive_tail z c hz hc
  change J z c = gaussianMass * (z - 3 * c) + 6 * Real.sqrt (z * c) * weight r +
    2 * (3 * c - z) * tailWeight r at hp
  rw [tailWeight_eq_weight_mul_Mills, hK] at hp
  change J z c = gaussianMass * (z - 3 * c) + Real.sqrt (z * c) * Real.exp (-a / 2) *
    (6 + 2 * (3 - a) / a * r * Mills r)
  rw [hK, ← hw]
  calc
    _ = gaussianMass * (z - 3 * c) + 6 * (c * r) * weight r +
        2 * (3 * c - z) * (weight r * Mills r) := hp
    _ = gaussianMass * (z - 3 * c) + (c * r) * weight r * (6 + (2 * (3 - a) / a * r) * Mills r) := by
      rw [show (c * r) * weight r * (6 + (2 * (3 - a) / a * r) * Mills r) =
        6 * (c * r) * weight r + ((c * r) * (2 * (3 - a) / a * r)) * weight r * Mills r by ring, hcoef]
      ring

/-- The simple alternative uses only the actual tail range 0≤T(r)≤sqrt(pi/2).
It is one analytic bound, not a certificate for all later numeric profiles. -/
theorem J_positive_alternative (z c : ℝ) (hz : 0 < z) (hc : 0 < c) :
    J z c ≤ gaussianMass * |z - 3 * c| + 6 * Real.sqrt (z * c) * Real.exp (-(z / c) / 2) := by
  let r := Real.sqrt (z / c)
  have hr : 0 < r := Real.sqrt_pos.mpr (div_pos hz hc)
  have hw : weight r = Real.exp (-(z / c) / 2) := by unfold weight; rw [Real.sq_sqrt (div_pos hz hc).le]
  have hp := J_positive_tail z c hz hc
  change J z c = gaussianMass * (z - 3 * c) + 6 * Real.sqrt (z * c) * weight r +
    2 * (3 * c - z) * tailWeight r at hp
  rw [hp, ← hw]
  by_cases hd : 0 ≤ z - 3 * c
  · rw [abs_of_nonneg hd]
    have hnon : 2 * (3 * c - z) * tailWeight r ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (tailWeight_nonneg r)
    linarith
  · have hdneg : z - 3 * c ≤ 0 := le_of_not_ge hd
    rw [abs_of_nonpos hdneg]
    have htail := mul_le_mul_of_nonneg_left (tailWeight_le_mass r hr.le)
      (show 0 ≤ 2 * (3 * c - z) by linarith)
    linarith

lemma J_same_sign_normalize (z c : ℝ) (hzc : 0 < z * c) : J z c = J |z| |c| := by
  rcases lt_trichotomy z 0 with hz | rfl | hz
  · have hc : c < 0 := by
      rcases mul_pos_iff.mp hzc with h | h
      · linarith [h.1]
      · exact h.2
    rw [abs_of_neg hz, abs_of_neg hc]
    exact (J_neg_neg z c).symm
  · simp at hzc
  · have hc : 0 < c := (mul_pos_iff_of_pos_left hz).mp hzc
    rw [abs_of_pos hz, abs_of_pos hc]

/-- All same-sign coefficients reduce simultaneously to the positive branch. -/
theorem J_same_sign_Mills (z c : ℝ) (hzc : 0 < z * c) :
    J z c = gaussianMass * (|z| - 3 * |c|) + Real.sqrt (z * c) * Real.exp (-(z / c) / 2) *
      (6 + 2 * (3 - z / c) / (z / c) * Real.sqrt (z / c) * Mills (Real.sqrt (z / c))) := by
  have hz : 0 < |z| := abs_pos.mpr (by intro heq; rw [heq, zero_mul] at hzc; linarith)
  have hc : 0 < |c| := abs_pos.mpr (by intro heq; rw [heq, mul_zero] at hzc; linarith)
  have hprod : |z| * |c| = z * c := by rw [← abs_mul, abs_of_pos hzc]
  have hratio : 0 < z / c := by
    rcases (mul_pos_iff.mp hzc) with h | h
    · exact div_pos h.1 h.2
    · exact div_pos_of_neg_of_neg h.1 h.2
  have hdiv : |z| / |c| = z / c := by rw [← abs_div, abs_of_pos hratio]
  have hp := J_positive_Mills |z| |c| hz hc
  rw [hprod, hdiv] at hp
  exact (J_same_sign_normalize z c hzc).trans hp

/-- A global signed alternative, with zero and opposite-sign boundaries treated
by their exact formula rather than by a fictitious positive square root. -/
theorem J_simple_alternative (z c : ℝ) :
    J z c ≤ gaussianMass * |z - 3 * c| + 6 * Real.sqrt (z * c) * Real.exp (-(z / c) / 2) := by
  by_cases hzc : 0 < z * c
  · rcases lt_trichotomy z 0 with hz | rfl | hz
    · have hc : c < 0 := by
        rcases mul_pos_iff.mp hzc with h | h
        · linarith [h.1]
        · exact h.2
      have hp := J_positive_alternative (-z) (-c) (by linarith) (by linarith)
      simpa only [J_neg_neg, neg_mul_neg, neg_div_neg_eq,
        show -z - 3 * -c = -(z - 3 * c) by ring, abs_neg] using hp
    · simp at hzc
    · exact J_positive_alternative z c hz ((mul_pos_iff_of_pos_left hz).mp hzc)
  · have hnon : z * c ≤ 0 := le_of_not_gt hzc
    have habs := abs_sub_eq_of_mul_nonpos z (3 * c) (show z * (3 * c) ≤ 0 by nlinarith [hnon])
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)] at habs
    rw [J_of_mul_nonpos z c hnon, Real.sqrt_eq_zero_of_nonpos hnon, habs]
    simp

end BerryEsseen.GaussianCancellationPrice
#print axioms BerryEsseen.GaussianCancellationPrice.J_positive_Mills
#print axioms BerryEsseen.GaussianCancellationPrice.J_same_sign_Mills
#print axioms BerryEsseen.GaussianCancellationPrice.J_simple_alternative
