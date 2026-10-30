module

public import BerryEsseen.HighFrequencyPeriodic
public import BerryEsseen.HighFrequencyComparator
public import BerryEsseen.RationalGaussianTail

@[expose] public section

/-! 2026-10-28: the actual continuous zero cell. The upper endpoint π/D
belongs to this cell; the core threshold 1/D belongs to the core, and its
set difference is the wing. Both original Z prices hold for each n>0;
the separate qualification for comparison across floors is not asserted here. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace BerryEsseen.HighFrequencyZeroCell

open HighFrequencyPeriodic HighFrequencyCells RationalGaussianTail

def zeroDomain (D b : ℝ) : Set ℝ := Ioi b ∩ Iic (Real.pi / D)
def zeroCore (D b : ℝ) : Set ℝ := zeroDomain D b ∩ Iic (1 / D)
def zeroWing (D b : ℝ) : Set ℝ := zeroDomain D b \ Iic (1 / D)
def zeroTail (n : ℕ) (a D b : ℝ) : ℝ := ∫ t in zeroDomain D b, fixedDistanceIntegrand n a D t

def kappa (a d : ℝ) : ℝ := a * (23 / 48 : ℝ) ^ 2 * d ^ 2

def gaussianPart (n : ℕ) (a d t : ℝ) : ℝ := Real.exp (-((n : ℝ) * kappa a d) * t ^ 2) / t ^ 3

def wingMajorant (n : ℕ) (a t : ℝ) : ℝ :=
  Real.exp (-(n : ℝ) * a * (23 / 48 : ℝ) ^ 2) * inverseCube t

def Zbasic (n : ℕ) (a d b : ℝ) : ℝ :=
  Real.exp (-((n : ℝ) * kappa a d) * b ^ 2) / (2 * b ^ 4 * kappa a d * Real.sqrt n)

def Zimproved (n : ℕ) (a d b : ℝ) : ℝ :=
  Real.sqrt n * Real.exp (-((n : ℝ) * kappa a d) * b ^ 2) / (2 * b ^ 2) *
    Lambda ((n : ℝ) * kappa a d * b ^ 2)

def wingPrice (n : ℕ) (a b : ℝ) : ℝ :=
  Real.sqrt n * Real.exp (-(n : ℝ) * a * (23 / 48 : ℝ) ^ 2) / (2 * b ^ 2)

lemma kappa_pos (a d : ℝ) (ha : 0 < a) (hd : 0 < d) : 0 < kappa a d := by
  unfold kappa
  positivity

lemma measurableSet_zeroDomain (D b : ℝ) : MeasurableSet (zeroDomain D b) :=
  measurableSet_Ioi.inter measurableSet_Iic

lemma measurableSet_zeroCore (D b : ℝ) : MeasurableSet (zeroCore D b) :=
  (measurableSet_zeroDomain D b).inter measurableSet_Iic

lemma measurableSet_zeroWing (D b : ℝ) : MeasurableSet (zeroWing D b) :=
  (measurableSet_zeroDomain D b).diff measurableSet_Iic

lemma zeroDomain_subset (D b : ℝ) : zeroDomain D b ⊆ Ioi b := inter_subset_left
lemma zeroCore_subset (D b : ℝ) : zeroCore D b ⊆ Ioi b := fun _ h => h.1.1
lemma zeroWing_subset (D b : ℝ) : zeroWing D b ⊆ Ioi b := fun _ h => h.1.1

lemma fixedDistance_nonneg (n : ℕ) (a D t : ℝ) (ht : 0 ≤ t) :
    0 ≤ fixedDistanceIntegrand n a D t := by unfold fixedDistanceIntegrand; positivity

lemma measurable_fixedDistance (n : ℕ) (a D : ℝ) : Measurable (fixedDistanceIntegrand n a D) := by
  have hc : Continuous (fun t : ℝ => Real.exp (-(n : ℝ) * a * Real.sin (t * D / 2) ^ 2)) := by fun_prop
  exact hc.measurable.div (continuous_id.pow 3).measurable

/-- Actual L¹ on the entire ray, before restricting to the zero cell. -/
lemma integrableOn_fixedDistance_Ioi (n : ℕ) (a D b : ℝ) (ha : 0 ≤ a) (hb : 0 < b) :
    IntegrableOn (fixedDistanceIntegrand n a D) (Ioi b) := by
  apply (integrableOn_inverseCube b hb).mono' (measurable_fixedDistance n a D).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 < t := hb.trans ht
  rw [Real.norm_eq_abs, abs_of_nonneg (fixedDistance_nonneg n a D t ht0.le)]
  unfold fixedDistanceIntegrand inverseCube
  apply div_le_div_of_nonneg_right _ (pow_nonneg ht0.le 3)
  apply Real.exp_le_one_iff.mpr
  nlinarith [mul_nonneg (mul_nonneg (Nat.cast_nonneg n) ha) (sq_nonneg (Real.sin (t * D / 2)))]

lemma integrableOn_zeroDomain (n : ℕ) (a D b : ℝ) (ha : 0 ≤ a) (hb : 0 < b) :
    IntegrableOn (fixedDistanceIntegrand n a D) (zeroDomain D b) :=
  (integrableOn_fixedDistance_Ioi n a D b ha hb).mono_set (zeroDomain_subset D b)

/-- Exact measurable partition, including the threshold point in the core once. -/
lemma zeroTail_split (n : ℕ) (a D b : ℝ) (ha : 0 ≤ a) (hb : 0 < b) :
    zeroTail n a D b = (∫ t in zeroCore D b, fixedDistanceIntegrand n a D t) +
      ∫ t in zeroWing D b, fixedDistanceIntegrand n a D t := by
  exact (integral_inter_add_sdiff measurableSet_Iic (integrableOn_zeroDomain n a D b ha hb)).symm

lemma core_pointwise (n : ℕ) (a D d b t : ℝ) (ha : 0 < a) (hd : 0 < d)
    (hDd : d ≤ D) (hb : 0 < b) (ht : t ∈ zeroCore D b) :
    fixedDistanceIntegrand n a D t ≤ gaussianPart n a d t := by
  have hD : 0 < D := hd.trans_le hDd
  have ht0 : 0 < t := hb.trans ht.1.1
  have hu0 : 0 ≤ t * D / 2 := by positivity
  have hucap : t * D / 2 ≤ 1 / 2 := by
    have h := (le_div_iff₀ hD).mp ht.2
    linarith
  have hs := zero_cell_sine_small (t * D / 2) hu0 hucap
  have hscale : (23 / 48 : ℝ) * d * t ≤ (23 / 24 : ℝ) * (t * D / 2) := by
    have h := mul_le_mul_of_nonneg_left hDd (show 0 ≤ (23 / 48 : ℝ) * t by positivity)
    nlinarith only [h]
  have hlow : (23 / 48 : ℝ) * d * t ≤ Real.sin (t * D / 2) := hscale.trans hs
  have hs0 : 0 ≤ Real.sin (t * D / 2) := (by positivity : 0 ≤ (23 / 48 : ℝ) * d * t).trans hlow
  have hsq := (sq_le_sq₀ (by positivity : 0 ≤ (23 / 48 : ℝ) * d * t) hs0).mpr hlow
  have hm := mul_le_mul_of_nonneg_left hsq (mul_nonneg (Nat.cast_nonneg n) ha.le)
  have he : -(n : ℝ) * a * Real.sin (t * D / 2) ^ 2 ≤ -((n : ℝ) * kappa a d) * t ^ 2 := by
    unfold kappa
    nlinarith only [hm]
  exact div_le_div_of_nonneg_right (Real.exp_le_exp.mpr he) (pow_nonneg ht0.le 3)

lemma wing_pointwise (n : ℕ) (a D d b t : ℝ) (ha : 0 < a) (hd : 0 < d)
    (hDd : d ≤ D) (hb : 0 < b) (ht : t ∈ zeroWing D b) :
    fixedDistanceIntegrand n a D t ≤ wingMajorant n a t := by
  have hD : 0 < D := hd.trans_le hDd
  have ht0 : 0 < t := hb.trans ht.1.1
  have huthresh : 1 / 2 ≤ t * D / 2 := by
    have hl : 1 / D < t := lt_of_not_ge ht.2
    have h := (div_lt_iff₀ hD).mp hl
    linarith
  have hucap : t * D / 2 ≤ Real.pi / 2 := by
    have h := (le_div_iff₀ hD).mp ht.1.2
    linarith
  have hs := zero_cell_sine_wing (t * D / 2) huthresh hucap
  have hs0 : 0 ≤ Real.sin (t * D / 2) := by linarith
  have hsq := (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 23 / 48) hs0).mpr hs
  have hm := mul_le_mul_of_nonneg_left hsq (mul_nonneg (Nat.cast_nonneg n) ha.le)
  have he : -(n : ℝ) * a * Real.sin (t * D / 2) ^ 2 ≤ -(n : ℝ) * a * (23 / 48 : ℝ) ^ 2 := by
    nlinarith only [hm]
  have h := div_le_div_of_nonneg_right (Real.exp_le_exp.mpr he) (pow_nonneg ht0.le 3)
  unfold fixedDistanceIntegrand wingMajorant inverseCube
  convert h using 1 <;> ring

lemma core_integral_le (n : ℕ) (hn : 0 < n) (a D d b : ℝ) (ha : 0 < a)
    (hd : 0 < d) (hDd : d ≤ D) (hb : 0 < b) :
    (∫ t in zeroCore D b, fixedDistanceIntegrand n a D t) ≤ ∫ t in Ioi b, gaussianPart n a d t := by
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hk := kappa_pos a d ha hd
  have hiG : IntegrableOn (gaussianPart n a d) (Ioi b) := integrableOn_gaussian_inv_cube _ _ (mul_pos hnR hk) hb
  have hiF := (integrableOn_fixedDistance_Ioi n a D b ha.le hb).mono_set (zeroCore_subset D b)
  calc
    _ ≤ ∫ t in zeroCore D b, gaussianPart n a d t := by
      apply setIntegral_mono_on hiF (hiG.mono_set (zeroCore_subset D b)) (measurableSet_zeroCore D b)
      exact fun t ht => core_pointwise n a D d b t ha hd hDd hb ht
    _ ≤ _ := setIntegral_mono_set hiG
      (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => by
        have ht0 := hb.trans ht
        unfold gaussianPart
        positivity) (zeroCore_subset D b).eventuallySubset

lemma wing_integral_le (n : ℕ) (a D d b : ℝ) (ha : 0 < a)
    (hd : 0 < d) (hDd : d ≤ D) (hb : 0 < b) :
    (∫ t in zeroWing D b, fixedDistanceIntegrand n a D t) ≤
      Real.exp (-(n : ℝ) * a * (23 / 48 : ℝ) ^ 2) / (2 * b ^ 2) := by
  have hiW : IntegrableOn (wingMajorant n a) (Ioi b) := (integrableOn_inverseCube b hb).const_mul _
  have hiF := (integrableOn_fixedDistance_Ioi n a D b ha.le hb).mono_set (zeroWing_subset D b)
  calc
    _ ≤ ∫ t in zeroWing D b, wingMajorant n a t := by
      apply setIntegral_mono_on hiF (hiW.mono_set (zeroWing_subset D b)) (measurableSet_zeroWing D b)
      exact fun t ht => wing_pointwise n a D d b t ha hd hDd hb ht
    _ ≤ ∫ t in Ioi b, wingMajorant n a t := setIntegral_mono_set hiW
      (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => by
        have ht0 := hb.trans ht
        unfold wingMajorant inverseCube
        positivity) (zeroWing_subset D b).eventuallySubset
    _ = _ := by
      change (∫ t in Ioi b, Real.exp (-(n : ℝ) * a * (23 / 48 : ℝ) ^ 2) * inverseCube t) = _
      rw [integral_const_mul, integral_inverseCube b hb]
      ring

/-- The entire zero-cell integral, with the core and wing accounted for exactly. -/
lemma zeroTail_le_raw (n : ℕ) (hn : 0 < n) (a D d b : ℝ) (ha : 0 < a)
    (hd : 0 < d) (hDd : d ≤ D) (hb : 0 < b) :
    zeroTail n a D b ≤ (∫ t in Ioi b, gaussianPart n a d t) +
      Real.exp (-(n : ℝ) * a * (23 / 48 : ℝ) ^ 2) / (2 * b ^ 2) := by
  rw [zeroTail_split n a D b ha.le hb]
  exact add_le_add (core_integral_le n hn a D d b ha hd hDd hb)
    (wing_integral_le n a D d b ha hd hDd hb)

/-- The original simpler Gaussian zero-cell price, from t^-3 ≤ t/b^4. -/
lemma gaussian_inv_cube_basic (c b : ℝ) (hc : 0 < c) (hb : 0 < b) :
    (∫ t in Ioi b, Real.exp (-c * t ^ 2) / t ^ 3) ≤
      Real.exp (-c * b ^ 2) / (2 * c * b ^ 4) := by
  have hi3 := integrableOn_gaussian_inv_cube c b hc hb
  have hi1 := (integrable_mul_exp_neg_mul_sq hc).integrableOn (s := Ioi b)
  have hle : (∫ t in Ioi b, Real.exp (-c * t ^ 2) / t ^ 3) ≤
      ∫ t in Ioi b, (1 / b ^ 4) * (t * Real.exp (-c * t ^ 2)) := by
    apply integral_mono_ae hi3 (hi1.const_mul _)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := hb.trans ht
    have hp : b ^ 4 ≤ t ^ 4 := pow_le_pow_left₀ hb.le ht.le 4
    have hw : 1 / t ^ 3 ≤ (1 / b ^ 4) * t := by
      apply (div_le_iff₀ (pow_pos ht0 3)).mpr
      calc
        1 ≤ t ^ 4 / b ^ 4 := (le_div_iff₀ (pow_pos hb 4)).mpr (by simpa only [one_mul] using hp)
        _ = _ := by ring
    have hm := mul_le_mul_of_nonneg_left hw (Real.exp_pos (-c * t ^ 2)).le
    convert hm using 1 <;> ring
  rw [integral_const_mul, HighFrequencyComparator.integral_mul_gaussian_Ioi c b hc] at hle
  convert hle using 1
  field_simp [ne_of_gt hc, ne_of_gt hb]

lemma gaussian_basic_price (n : ℕ) (hn : 0 < n) (a d b : ℝ)
    (ha : 0 < a) (hd : 0 < d) (hb : 0 < b) :
    Real.sqrt n * (∫ t in Ioi b, gaussianPart n a d t) ≤ Zbasic n a d b := by
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hk := kappa_pos a d ha hd
  have h := mul_le_mul_of_nonneg_left (gaussian_inv_cube_basic ((n : ℝ) * kappa a d) b
    (mul_pos hnR hk) hb) (Real.sqrt_nonneg (n : ℝ))
  calc
    _ ≤ Real.sqrt n * (Real.exp (-((n : ℝ) * kappa a d) * b ^ 2) /
        (2 * ((n : ℝ) * kappa a d) * b ^ 4)) := h
    _ = (Real.sqrt n / (n : ℝ)) * (Real.exp (-((n : ℝ) * kappa a d) * b ^ 2) /
        (2 * b ^ 4 * kappa a d)) := by field_simp [ne_of_gt hnR, ne_of_gt hk, ne_of_gt hb]
    _ = Zbasic n a d b := by
      rw [Real.sqrt_div_self']
      unfold Zbasic
      field_simp [ne_of_gt (Real.sqrt_pos.mpr hnR), ne_of_gt hk, ne_of_gt hb]

lemma gaussian_improved_price (n : ℕ) (hn : 0 < n) (a d b : ℝ)
    (ha : 0 < a) (hd : 0 < d) (hb : 0 < b) :
    Real.sqrt n * (∫ t in Ioi b, gaussianPart n a d t) ≤ Zimproved n a d b := by
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have h := mul_le_mul_of_nonneg_left (gaussian_inv_cube_tail ((n : ℝ) * kappa a d) b
    (mul_pos hnR (kappa_pos a d ha hd)) hb) (Real.sqrt_nonneg (n : ℝ))
  unfold gaussianPart Zimproved
  convert h using 1 <;> ring

/-- Original basic Z price for the genuine zero cell, including its entire wing. -/
theorem fixedDistance_zero_tail_basic (n : ℕ) (hn : 0 < n) (a D d b : ℝ)
    (ha : 0 < a) (hd : 0 < d) (hDd : d ≤ D) (hb : 0 < b) :
    IntegrableOn (fixedDistanceIntegrand n a D) (zeroDomain D b) ∧
      Real.sqrt n * zeroTail n a D b ≤ Zbasic n a d b + wingPrice n a b := by
  refine ⟨integrableOn_zeroDomain n a D b ha.le hb, ?_⟩
  have h := mul_le_mul_of_nonneg_left (zeroTail_le_raw n hn a D d b ha hd hDd hb) (Real.sqrt_nonneg (n : ℝ))
  calc
    _ ≤ Real.sqrt n * ((∫ t in Ioi b, gaussianPart n a d t) +
        Real.exp (-(n : ℝ) * a * (23 / 48 : ℝ) ^ 2) / (2 * b ^ 2)) := h
    _ = Real.sqrt n * (∫ t in Ioi b, gaussianPart n a d t) + wingPrice n a b := by unfold wingPrice; ring
    _ ≤ _ := add_le_add (gaussian_basic_price n hn a d b ha hd hb) le_rfl

/-- Improved rational Z price; no across-floor monotonicity is assumed here. -/
theorem fixedDistance_zero_tail_improved (n : ℕ) (hn : 0 < n) (a D d b : ℝ)
    (ha : 0 < a) (hd : 0 < d) (hDd : d ≤ D) (hb : 0 < b) :
    IntegrableOn (fixedDistanceIntegrand n a D) (zeroDomain D b) ∧
      Real.sqrt n * zeroTail n a D b ≤ Zimproved n a d b + wingPrice n a b := by
  refine ⟨integrableOn_zeroDomain n a D b ha.le hb, ?_⟩
  have h := mul_le_mul_of_nonneg_left (zeroTail_le_raw n hn a D d b ha hd hDd hb) (Real.sqrt_nonneg (n : ℝ))
  calc
    _ ≤ Real.sqrt n * ((∫ t in Ioi b, gaussianPart n a d t) +
        Real.exp (-(n : ℝ) * a * (23 / 48 : ℝ) ^ 2) / (2 * b ^ 2)) := h
    _ = Real.sqrt n * (∫ t in Ioi b, gaussianPart n a d t) + wingPrice n a b := by unfold wingPrice; ring
    _ ≤ _ := add_le_add (gaussian_improved_price n hn a d b ha hd hb) le_rfl

/-- Both Z bounds hold pointwise in n, so their minimum is also a true price. -/
theorem fixedDistance_zero_tail_min (n : ℕ) (hn : 0 < n) (a D d b : ℝ)
    (ha : 0 < a) (hd : 0 < d) (hDd : d ≤ D) (hb : 0 < b) :
    IntegrableOn (fixedDistanceIntegrand n a D) (zeroDomain D b) ∧
      Real.sqrt n * zeroTail n a D b ≤ min (Zbasic n a d b) (Zimproved n a d b) + wingPrice n a b := by
  refine ⟨integrableOn_zeroDomain n a D b ha.le hb, ?_⟩
  rcases le_total (Zbasic n a d b) (Zimproved n a d b) with h | h
  · rw [min_eq_left h]
    exact (fixedDistance_zero_tail_basic n hn a D d b ha hd hDd hb).2
  · rw [min_eq_right h]
    exact (fixedDistance_zero_tail_improved n hn a D d b ha hd hDd hb).2

end BerryEsseen.HighFrequencyZeroCell

#print axioms BerryEsseen.HighFrequencyZeroCell.zeroTail_split
#print axioms BerryEsseen.HighFrequencyZeroCell.gaussian_inv_cube_basic
#print axioms BerryEsseen.HighFrequencyZeroCell.fixedDistance_zero_tail_basic
#print axioms BerryEsseen.HighFrequencyZeroCell.fixedDistance_zero_tail_improved
#print axioms BerryEsseen.HighFrequencyZeroCell.fixedDistance_zero_tail_min
