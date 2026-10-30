module

public import BerryEsseen.LowFrequencyLeading
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

@[expose] public section

/-! 2026-10-28: exact one-dimensional nonzero-cell estimates from ut:high.
This module proves a single cell's real integral price; the infinite cell
partition and averaging over the actual conditional event are separate steps. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators Interval
open BerryEsseen.LowFrequencyError

namespace BerryEsseen.HighFrequencyCells

def pairedWeight (j v : ℝ) : ℝ := (1 / (j - v) ^ 3 + 1 / (j + v) ^ 3) / 2
def sineSlope (w : ℝ) : ℝ := 333 / 106 - (22 / 7 : ℝ) ^ 3 * w ^ 2 / 6
def cellIntegrand (j r v : ℝ) : ℝ := Real.exp (-(r * v ^ 2)) / (j + v) ^ 3

lemma pairedWeight_even (j v : ℝ) : pairedWeight j (-v) = pairedWeight j v := by
  unfold pairedWeight
  simp only [sub_eq_add_neg, neg_neg]
  ring

lemma pairedWeight_abs (j v : ℝ) : pairedWeight j v = pairedWeight j |v| := by
  rcases le_or_gt 0 v with hv | hv
  · rw [abs_of_nonneg hv]
  · rw [abs_of_neg hv, pairedWeight_even]

/-- A positive-coefficient exact remainder certificate, rather than a sampled bound. -/
lemma pairedWeight_shifted (A z : ℝ) (hA : 0 < A) (hz : 0 ≤ z) :
    (1 / A ^ 3 + 1 / (A + 2 * z) ^ 3) / 2 ≤
      1 / (A + z) ^ 3 + 6 * z ^ 2 / A ^ 5 := by
  have hAz : A + z ≠ 0 := ne_of_gt (by linarith : 0 < A + z)
  have hA2z : A + 2 * z ≠ 0 := ne_of_gt (by linarith : 0 < A + 2 * z)
  have hid : 1 / (A + z) ^ 3 + 6 * z ^ 2 / A ^ 5 -
      (1 / A ^ 3 + 1 / (A + 2 * z) ^ 3) / 2 =
      z ^ 3 * (30 * A ^ 5 + 165 * A ^ 4 * z + 360 * A ^ 3 * z ^ 2 +
        392 * A ^ 2 * z ^ 3 + 216 * A * z ^ 4 + 48 * z ^ 5) /
        (A ^ 5 * (A + z) ^ 3 * (A + 2 * z) ^ 3) := by
    field_simp [ne_of_gt hA, hAz, hA2z]
    ring
  have hn : 0 ≤ 1 / (A + z) ^ 3 + 6 * z ^ 2 / A ^ 5 -
      (1 / A ^ 3 + 1 / (A + 2 * z) ^ 3) / 2 := by
    rw [hid]
    positivity
  linarith

/-- The paper's coefficient 6 in the paired reciprocal-cube Taylor bound. -/
theorem pairedWeight_le (j w v : ℝ) (hj : 1 ≤ j) (hw : 0 < w) (hwcap : w ≤ 1 / 4)
    (hv : |v| ≤ w) : pairedWeight j v ≤ 1 / j ^ 3 + 6 * v ^ 2 / (j - w) ^ 5 := by
  have hjw : 0 < j - w := by linarith
  have hjz : 0 < j - |v| := by linarith
  have hlocal := pairedWeight_shifted (j - |v|) |v| hjz (abs_nonneg v)
  have hl : pairedWeight j |v| ≤ 1 / j ^ 3 + 6 * |v| ^ 2 / (j - |v|) ^ 5 := by
    unfold pairedWeight
    simpa only [show j - |v| + |v| = j by ring,
      show j - |v| + 2 * |v| = j + |v| by ring] using hlocal
  have hden : (j - w) ^ 5 ≤ (j - |v|) ^ 5 :=
    pow_le_pow_left₀ hjw.le (by linarith) 5
  calc
    _ = pairedWeight j |v| := pairedWeight_abs j v
    _ ≤ 1 / j ^ 3 + 6 * |v| ^ 2 / (j - |v|) ^ 5 := hl
    _ ≤ 1 / j ^ 3 + 6 * |v| ^ 2 / (j - w) ^ 5 := by
      exact add_le_add (le_refl (1 / j ^ 3)) (div_le_div_of_nonneg_left
        (show 0 ≤ 6 * |v| ^ 2 by positivity) (pow_pos hjw 5) hden)
    _ = _ := by rw [sq_abs]

lemma sineSlope_pos (w : ℝ) (hw : 0 ≤ w) (hwcap : w ≤ 1 / 4) : 0 < sineSlope w := by
  have hw2 : w ^ 2 ≤ (1 : ℝ) / 16 := by
    nlinarith [mul_nonneg (show 0 ≤ 1 / 4 - w by linarith) (show 0 ≤ w + 1 / 4 by linarith)]
  unfold sineSlope
  nlinarith

lemma sin_cubic_lower (x : ℝ) (hx : 0 ≤ x) : x - x ^ 3 / 6 ≤ Real.sin x := by
  by_cases hx0 : x = 0
  · simp [hx0]
  · exact (Real.sin_gt_sub_cube (lt_of_le_of_ne hx (Ne.symm hx0))).le

lemma core_sin_nonneg (w u : ℝ) (hw : 0 ≤ w) (hu : 0 ≤ u) (huw : u ≤ w) :
    sineSlope w * u ≤ Real.sin (Real.pi * u) := by
  have hpLo : (333 : ℝ) / 106 ≤ Real.pi := by linarith [Real.pi_gt_d6]
  have hpHi : Real.pi ≤ (22 : ℝ) / 7 := by linarith [Real.pi_lt_d4]
  have hp3 : Real.pi ^ 3 ≤ ((22 : ℝ) / 7) ^ 3 :=
    pow_le_pow_left₀ Real.pi_nonneg hpHi 3
  have hu2 : u ^ 2 ≤ w ^ 2 := (sq_le_sq₀ hu hw).mpr huw
  have hpU : Real.pi ^ 3 * u ^ 2 ≤ ((22 : ℝ) / 7) ^ 3 * w ^ 2 :=
    mul_le_mul hp3 hu2 (sq_nonneg u) (by positivity)
  have hpUU := mul_le_mul_of_nonneg_right hpU hu
  have hpLoU := mul_le_mul_of_nonneg_right hpLo hu
  have hs := sin_cubic_lower (Real.pi * u) (mul_nonneg Real.pi_nonneg hu)
  unfold sineSlope
  nlinarith

lemma abs_sin_pi_abs (v : ℝ) : |Real.sin (Real.pi * |v|)| = |Real.sin (Real.pi * v)| := by
  rcases le_or_gt 0 v with hv | hv
  · rw [abs_of_nonneg hv]
  · simp only [abs_of_neg hv, mul_neg, Real.sin_neg, abs_neg]

theorem core_sine_bound (w v : ℝ) (hw : 0 < w) (hwcap : w ≤ 1 / 4) (hv : |v| ≤ w) :
    sineSlope w * |v| ≤ |Real.sin (Real.pi * v)| := by
  calc
    _ ≤ Real.sin (Real.pi * |v|) := core_sin_nonneg w |v| hw.le (abs_nonneg v) hv
    _ ≤ |Real.sin (Real.pi * |v|)| := le_abs_self _
    _ = _ := abs_sin_pi_abs v

theorem wing_sine_bound (w v : ℝ) (hw : 0 < w) (hwcap : w ≤ 1 / 4)
    (hvlow : w ≤ |v|) (hvhigh : |v| ≤ 1 / 2) :
    sineSlope w * w ≤ |Real.sin (Real.pi * v)| := by
  have hmono : Real.sin (Real.pi * w) ≤ Real.sin (Real.pi * |v|) := by
    apply Real.sin_le_sin_of_le_of_le_pi_div_two
    · nlinarith [Real.pi_pos]
    · nlinarith [mul_le_mul_of_nonneg_left hvhigh Real.pi_nonneg]
    · exact mul_le_mul_of_nonneg_left hvlow Real.pi_nonneg
  calc
    _ ≤ Real.sin (Real.pi * w) := core_sin_nonneg w w hw.le hw.le le_rfl
    _ ≤ Real.sin (Real.pi * |v|) := hmono
    _ ≤ |Real.sin (Real.pi * |v|)| := le_abs_self _
    _ = _ := abs_sin_pi_abs v

theorem zero_cell_sine_small (u : ℝ) (hu : 0 ≤ u) (hucap : u ≤ 1 / 2) :
    23 / 24 * u ≤ Real.sin u := by
  have hu2 : u ^ 2 ≤ (1 : ℝ) / 4 := by
    nlinarith [mul_nonneg (show 0 ≤ 1 / 2 - u by linarith) (show 0 ≤ u + 1 / 2 by linarith)]
  have hu3 := mul_le_mul_of_nonneg_right hu2 hu
  nlinarith [sin_cubic_lower u hu]

theorem zero_cell_sine_wing (u : ℝ) (hu : 1 / 2 ≤ u) (hucap : u ≤ Real.pi / 2) :
    23 / 48 ≤ Real.sin u := by
  have h0 := zero_cell_sine_small (1 / 2) (by norm_num) le_rfl
  have hm : Real.sin (1 / 2) ≤ Real.sin u :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) hucap hu
  linarith

lemma gaussian_second_half (r : ℝ) (hr : 0 < r) :
    (∫ v in Ioi (0 : ℝ), v ^ 2 * Real.exp (-(r * v ^ 2))) =
      Real.sqrt (Real.pi / r) / (4 * r) := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := (2 : ℝ)) (q := (2 : ℝ)) (b := r)
    (by norm_num) (by norm_num) hr
  have hg := Real.Gamma_nat_add_half 1
  norm_num at hg
  norm_num only [show ((2 : ℝ) + 1) / 2 = 3 / 2 by norm_num,
    show -((2 : ℝ) + 1) / 2 = -(3 : ℝ) / 2 by norm_num, Real.rpow_two] at h
  have hp := BerryEsseen.LowFrequencyLeading.rpow_neg_half_nat r hr 3
  norm_num only [Nat.cast_ofNat] at hp
  rw [hg, hp] at h
  rw [show (3 : ℕ) = 2 * 1 + 1 by norm_num,
    BerryEsseen.LowFrequencyLeading.sqrt_odd_power r hr.le] at h
  simp only [pow_one] at h
  rw [Real.sqrt_div Real.pi_nonneg]
  convert h using 1
  · simp only [neg_mul]
  · field_simp [ne_of_gt hr, ne_of_gt (Real.sqrt_pos.mpr hr)]
    ring

lemma continuousOn_cellIntegrand (j r w : ℝ) (hj : 1 ≤ j) (hw : 0 ≤ w) (hwcap : w ≤ 1 / 4) :
    ContinuousOn (cellIntegrand j r) (Icc (-w) w) := by
  unfold cellIntegrand
  apply (by fun_prop : ContinuousOn (fun v : ℝ => Real.exp (-(r * v ^ 2))) (Icc (-w) w)).div
    (by fun_prop)
  intro v hv
  have : 0 < j + v := by linarith [hv.1]
  exact pow_ne_zero 3 (ne_of_gt this)

lemma cellIntegrand_pair (j r v : ℝ) :
    cellIntegrand j r (-v) + cellIntegrand j r v =
      2 * Real.exp (-(r * v ^ 2)) * pairedWeight j v := by
  unfold cellIntegrand pairedWeight
  rw [neg_sq]
  simp only [sub_eq_add_neg]
  ring

/-- Actual left/right reflection on the symmetric interval, with both integrals L¹. -/
lemma integral_cell_pairing (j r w : ℝ) (hj : 1 ≤ j) (hw : 0 ≤ w) (hwcap : w ≤ 1 / 4) :
    (∫ v in (-w)..w, cellIntegrand j r v) =
      ∫ v in (0 : ℝ)..w, cellIntegrand j r (-v) + cellIntegrand j r v := by
  have hc := continuousOn_cellIntegrand j r w hj hw hwcap
  have hi : IntervalIntegrable (cellIntegrand j r) volume (-w) w :=
    ContinuousOn.intervalIntegrable_of_Icc (by linarith) hc
  have hiL : IntervalIntegrable (cellIntegrand j r) volume (-w) 0 := by
    apply hi.mono_set
    rw [uIcc_of_le (by linarith : -w ≤ 0), uIcc_of_le (by linarith : -w ≤ w)]
    exact Icc_subset_Icc le_rfl hw
  have hiR : IntervalIntegrable (cellIntegrand j r) volume 0 w := by
    apply hi.mono_set
    rw [uIcc_of_le hw, uIcc_of_le (by linarith : -w ≤ w)]
    exact Icc_subset_Icc (by linarith) le_rfl
  have hiN : IntervalIntegrable (fun v => cellIntegrand j r (-v)) volume 0 w := by
    apply ContinuousOn.intervalIntegrable_of_Icc hw
    exact hc.comp continuous_neg.continuousOn (by intro v hv; constructor <;> linarith [hv.1, hv.2])
  rw [intervalIntegral.integral_add hiN hiR]
  rw [intervalIntegral.integral_comp_neg]
  simp only [neg_zero]
  exact (intervalIntegral.integral_add_adjacent_intervals hiL hiR).symm

/-- The original single nonzero center-cell price, with coefficients 6 and 3/r. -/
theorem nonzero_cell_cost (j r w : ℝ) (hj : 1 ≤ j) (hr : 0 < r) (hw : 0 < w) (hwcap : w ≤ 1 / 4) :
    IntegrableOn (cellIntegrand j r) (Icc (-w) w) ∧
      (∫ v in Icc (-w) w, cellIntegrand j r v) ≤
        Real.sqrt (Real.pi / r) * (1 / j ^ 3 + (3 / r) / (j - w) ^ 5) := by
  have hj0 : 0 < j := by linarith
  have hjw : 0 < j - w := by linarith
  have hc := continuousOn_cellIntegrand j r w hj hw.le hwcap
  have hi : IntegrableOn (cellIntegrand j r) (Icc (-w) w) := hc.integrableOn_Icc
  let G : ℝ → ℝ := fun v => (2 / j ^ 3) * Real.exp (-(r * v ^ 2)) +
    (12 / (j - w) ^ 5) * (v ^ 2 * Real.exp (-(r * v ^ 2)))
  have hG : Integrable G := by
    have h0 : Integrable (fun v : ℝ => Real.exp (-(r * v ^ 2))) := by
      simpa only [pow_zero, one_mul] using integrable_gaussian_power 0 r hr
    exact (h0.const_mul _).add ((integrable_gaussian_power 2 r hr).const_mul _)
  have hGpos : ∀ v, 0 ≤ G v := by intro v; dsimp only [G]; positivity
  have hp : (∫ v in (-w)..w, cellIntegrand j r v) ≤ ∫ v in (0 : ℝ)..w, G v := by
    rw [integral_cell_pairing j r w hj hw.le hwcap]
    have hpairI : IntervalIntegrable (fun v => cellIntegrand j r (-v) + cellIntegrand j r v) volume 0 w := by
      apply ContinuousOn.intervalIntegrable_of_Icc hw.le
      apply ContinuousOn.add
      · exact hc.comp continuous_neg.continuousOn (by intro v hv; constructor <;> linarith [hv.1, hv.2])
      · exact hc.mono (by intro v hv; constructor <;> linarith [hv.1, hv.2])
    apply intervalIntegral.integral_mono_on hw.le hpairI hG.intervalIntegrable
    intro v hv
    rw [cellIntegrand_pair]
    have hvabs : |v| ≤ w := by rw [abs_of_nonneg hv.1]; exact hv.2
    have hb := mul_le_mul_of_nonneg_left (pairedWeight_le j w v hj hw hwcap hvabs)
      (show 0 ≤ 2 * Real.exp (-(r * v ^ 2)) by positivity)
    convert hb using 1 <;> dsimp only [G] <;> ring
  have hExt : (∫ v in (0 : ℝ)..w, G v) ≤ ∫ v in Ioi (0 : ℝ), G v := by
    rw [intervalIntegral.integral_of_le hw.le]
    apply setIntegral_mono_set hG.integrableOn
    · exact Eventually.of_forall hGpos
    · exact Eventually.of_forall fun v hv => hv.1
  have hEval : (∫ v in Ioi (0 : ℝ), G v) =
      Real.sqrt (Real.pi / r) * (1 / j ^ 3 + (3 / r) / (j - w) ^ 5) := by
    have h0 : Integrable (fun v : ℝ => Real.exp (-(r * v ^ 2))) := by
      simpa only [pow_zero, one_mul] using integrable_gaussian_power 0 r hr
    change (∫ v in Ioi (0 : ℝ), (2 / j ^ 3) * Real.exp (-(r * v ^ 2)) +
      (12 / (j - w) ^ 5) * (v ^ 2 * Real.exp (-(r * v ^ 2)))) = _
    rw [integral_add (h0.const_mul _).integrableOn ((integrable_gaussian_power 2 r hr).const_mul _).integrableOn,
      integral_const_mul, integral_const_mul, gaussian_second_half r hr]
    have hGauss : (∫ v in Ioi (0 : ℝ), Real.exp (-(r * v ^ 2))) = Real.sqrt (Real.pi / r) / 2 := by
      simpa only [neg_mul] using integral_gaussian_Ioi r
    rw [hGauss]
    ring
  refine ⟨hi, ?_⟩
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith : -w ≤ w)]
  exact (hp.trans hExt).trans_eq hEval

end BerryEsseen.HighFrequencyCells

#print axioms BerryEsseen.HighFrequencyCells.pairedWeight_le
#print axioms BerryEsseen.HighFrequencyCells.core_sine_bound
#print axioms BerryEsseen.HighFrequencyCells.wing_sine_bound
#print axioms BerryEsseen.HighFrequencyCells.zero_cell_sine_small
#print axioms BerryEsseen.HighFrequencyCells.zero_cell_sine_wing
#print axioms BerryEsseen.HighFrequencyCells.nonzero_cell_cost
