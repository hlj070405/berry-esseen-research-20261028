module

public import BerryEsseen.PrawitzKernelMonotone
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent

@[expose] public section

/-! 2026-10-29: four explicit cotangent poles and a telescoping rational
tail bound for the actual Prawitz kernel. All kernel statements below
are on the open interval (0,1); no totalized endpoint is substituted. -/

noncomputable section

open Set Real Filter
open scoped Topology BigOperators
open Causalean.Stat.CLT.BerryEsseen

namespace BerryEsseen.PrawitzRationalKernel

/-- The poles at 2, 3, 4 and the tail beginning at 5. -/
def tailBound (z : ℝ) : ℝ :=
  1 / (4 - z ^ 2) + 1 / (9 - z ^ 2) + 1 / (16 - z ^ 2) + 9 / 40

def correctionImagBound (z : ℝ) : ℝ :=
  z / (Real.pi * (1 + z)) + z * (1 - z) * tailBound z / Real.pi

def kernelImagBound (w : ℝ) : ℝ :=
  w ^ 2 / (Real.pi * (1 - w ^ 2)) + w ^ 2 * tailBound w / Real.pi

private lemma reciprocal_tail_sum (n : ℕ) :
    (∑ j ∈ Finset.range n, 1 / (((j : ℝ) + 5) ^ 2 - 1)) =
      9 / 40 - (1 / ((n : ℝ) + 4) + 1 / ((n : ℝ) + 5)) / 2 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [Nat.cast_add, Nat.cast_one]
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have h4 : (n : ℝ) + 4 ≠ 0 := by positivity
    have h5 : (n : ℝ) + 5 ≠ 0 := by positivity
    have h6 : (n : ℝ) + 1 + 5 ≠ 0 := by positivity
    have hd : ((n : ℝ) + 5) ^ 2 - 1 ≠ 0 := by nlinarith
    field_simp
    ring

private lemma reciprocal_tail_le (z : ℝ) (hz : z ∈ Ioo (0 : ℝ) 1) (n : ℕ) :
    (∑ j ∈ Finset.range n, 1 / (((j : ℝ) + 5) ^ 2 - z ^ 2)) ≤ 9 / 40 := by
  have hzsq : z ^ 2 < 1 := by
    simpa using (sq_lt_sq₀ hz.1.le (show (0 : ℝ) ≤ 1 by norm_num)).mpr hz.2
  calc
    _ ≤ ∑ j ∈ Finset.range n, 1 / (((j : ℝ) + 5) ^ 2 - 1) := by
      apply Finset.sum_le_sum
      intro j hj
      have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      apply one_div_le_one_div_of_le
      · nlinarith
      · linarith only [hzsq]
    _ = 9 / 40 - (1 / ((n : ℝ) + 4) + 1 / ((n : ℝ) + 5)) / 2 :=
      reciprocal_tail_sum n
    _ ≤ 9 / 40 := sub_le_self _ (by positivity)

private lemma mem_integerComplement (z : ℝ) (hz : z ∈ Ioo (0 : ℝ) 1) :
    (z : ℂ) ∈ Complex.integerComplement := by
  rw [Complex.mem_integerComplement_iff]
  rintro ⟨k, hk⟩
  have hk' : (k : ℝ) = z := by exact_mod_cast congrArg Complex.re hk
  have hpos : (0 : ℤ) < k := by exact_mod_cast (show (0 : ℝ) < k by linarith [hz.1])
  have hlt : k < (1 : ℤ) := by exact_mod_cast (show (k : ℝ) < 1 by linarith [hz.2])
  omega

private lemma cotTerm_re (z : ℝ) (hz : z ∈ Ioo (0 : ℝ) 1) (j : ℕ) :
    (cotTerm (z : ℂ) j).re = -2 * z / (((j : ℝ) + 1) ^ 2 - z ^ 2) := by
  have hz0 := hz.1
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hm : z - ((j : ℝ) + 1) ≠ 0 := by linarith only [hz.2, hj]
  have hp : z + ((j : ℝ) + 1) ≠ 0 := by positivity
  have hd : ((j : ℝ) + 1) ^ 2 - z ^ 2 ≠ 0 := by
    have : 0 < ((j : ℝ) + 1) - z := by linarith only [hz.2, hj]
    nlinarith only [mul_pos this (show 0 < ((j : ℝ) + 1) + z by positivity)]
  have heq : cotTerm (z : ℂ) j =
      ((1 / (z - ((j : ℝ) + 1)) + 1 / (z + ((j : ℝ) + 1)) : ℝ) : ℂ) := by
    simp [cotTerm, Complex.ofReal_add, Complex.ofReal_sub]
  rw [heq]
  simp only [Complex.ofReal_re]
  field_simp
  ring

private lemma pole_sum_le (z : ℝ) (hz : z ∈ Ioo (0 : ℝ) 1) (n : ℕ) :
    (∑ j ∈ Finset.range (n + 4), 1 / (((j : ℝ) + 1) ^ 2 - z ^ 2)) ≤
      1 / (1 - z ^ 2) + tailBound z := by
  have hshift' : (fun j : ℕ => 1 / ((((4 + j : ℕ) : ℝ) + 1) ^ 2 - z ^ 2)) =
      (fun j : ℕ => 1 / (((j : ℝ) + 5) ^ 2 - z ^ 2)) := by
    funext j
    congr 2
    push_cast
    ring
  rw [show n + 4 = 4 + n by omega, Finset.sum_range_add, hshift']
  have hhead : (∑ j ∈ Finset.range 4, 1 / (((j : ℝ) + 1) ^ 2 - z ^ 2)) =
      1 / (1 - z ^ 2) + 1 / (4 - z ^ 2) + 1 / (9 - z ^ 2) +
        1 / (16 - z ^ 2) := by norm_num [Finset.sum_range_succ]
  rw [hhead]
  have ht := reciprocal_tail_le z hz n
  unfold tailBound
  linarith only [ht]

/-- The finite four-pole bound obtained from the genuine cotangent series. -/
theorem cot_difference_le (z : ℝ) (hz : z ∈ Ioo (0 : ℝ) 1) :
    1 / (Real.pi * z) - Real.cos (Real.pi * z) / Real.sin (Real.pi * z) ≤
      (2 * z / Real.pi) * (1 / (1 - z ^ 2) + tailBound z) := by
  have hx := mem_integerComplement z hz
  have hc := tendsto_logDeriv_euler_cot_sub hx
  have hr := (Complex.continuous_re.tendsto _).comp hc
  have hlim := hr.comp (tendsto_add_atTop_nat 4)
  have hterm (n : ℕ) :
      (∑ j ∈ Finset.range (n + 4), cotTerm (z : ℂ) j).re =
        -2 * z * (∑ j ∈ Finset.range (n + 4),
          1 / (((j : ℝ) + 1) ^ 2 - z ^ 2)) := by
    simp only [Complex.re_sum, cotTerm_re z hz, Finset.mul_sum, mul_one_div]
  have hreal : ((Real.pi : ℂ) * Complex.cot (Real.pi * (z : ℂ)) - 1 / (z : ℂ)).re =
      Real.pi * (Real.cos (Real.pi * z) / Real.sin (Real.pi * z)) - 1 / z := by
    have hcot : Complex.cot (Real.pi * (z : ℂ)) =
        ((Real.cos (Real.pi * z) / Real.sin (Real.pi * z) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, ← Complex.ofReal_cot, Real.cot_eq_cos_div_sin]
    rw [hcot]
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.div_ofReal_re, Complex.one_re,
      mul_zero, sub_zero]
  have hbound : -2 * z * (1 / (1 - z ^ 2) + tailBound z) ≤
      Real.pi * (Real.cos (Real.pi * z) / Real.sin (Real.pi * z)) - 1 / z := by
    rw [← hreal]
    apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
    filter_upwards with n
    simp only [Function.comp_apply]
    rw [hterm]
    exact mul_le_mul_of_nonpos_left (pole_sum_le z hz n) (by linarith [hz.1])
  have hp := Real.pi_pos
  have hz0 := hz.1
  rw [show (2 * z / Real.pi) * (1 / (1 - z ^ 2) + tailBound z) =
      (2 * z * (1 / (1 - z ^ 2) + tailBound z)) / Real.pi by ring]
  apply (le_div_iff₀ hp).mpr
  have hmul : (1 / (Real.pi * z) -
      Real.cos (Real.pi * z) / Real.sin (Real.pi * z)) * Real.pi =
      1 / z - Real.pi * (Real.cos (Real.pi * z) / Real.sin (Real.pi * z)) := by
    field_simp
  rw [hmul]
  linarith only [hbound]

private lemma reflectedImaginary_eq (z : ℝ) (hz : z ∈ Ioo (0 : ℝ) 1) :
    PrawitzKernelMonotone.reflectedImaginary z =
      z / 2 * (1 / (Real.pi * z) -
        Real.cos (Real.pi * z) / Real.sin (Real.pi * z)) := by
  have hz0 := hz.1.ne'
  unfold PrawitzKernelMonotone.reflectedImaginary
  field_simp

theorem cot_difference_nonneg (z : ℝ) (hz : z ∈ Ioo (0 : ℝ) 1) :
    0 ≤ 1 / (Real.pi * z) - Real.cos (Real.pi * z) / Real.sin (Real.pi * z) := by
  have hm := PrawitzKernelMonotone.reflectedImaginary_nonneg z hz
  rw [reflectedImaginary_eq z hz] at hm
  exact (mul_nonneg_iff_of_pos_left (show 0 < z / 2 by exact div_pos hz.1 (by norm_num))).mp hm

private lemma principal_correction_re (z : ℝ) (hz : z ∈ Ioo (0 : ℝ) 1) :
    (prawitzKernel z - Complex.I / ((2 * Real.pi * z : ℝ) : ℂ)).re =
      (1 - z) / 2 := by
  rw [Complex.sub_re, PrawitzKernelMonotone.kernel_re z hz,
    Complex.div_ofReal_re, Complex.I_re]
  simp

private lemma principal_correction_im (z : ℝ) (hz : z ∈ Ioo (0 : ℝ) 1) :
    (prawitzKernel z - Complex.I / ((2 * Real.pi * z : ℝ) : ℂ)).im =
      -((1 - z) * (1 / (Real.pi * z) -
        Real.cos (Real.pi * z) / Real.sin (Real.pi * z))) / 2 := by
  have hn : ¬(z = 0 ∨ 1 < |z|) := by
    rw [abs_of_pos hz.1]
    exact not_or.mpr ⟨hz.1.ne', not_lt.mpr hz.2.le⟩
  have hz0 := hz.1.ne'
  rw [prawitzKernel, ite_eq_right hn]
  simp only [abs_of_pos hz.1, Real.sign_of_pos hz.1,
    Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.div_ofReal_im]
  simp only [zero_add, zero_mul, add_zero, mul_one]
  field_simp
  ring

/-- Absolute imaginary part of the actual principal correction. -/
theorem principal_correction_im_abs_le (z : ℝ) (hz : z ∈ Ioo (0 : ℝ) 1) :
    |(prawitzKernel z - Complex.I / ((2 * Real.pi * z : ℝ) : ℂ)).im| ≤
      correctionImagBound z := by
  have hD := cot_difference_nonneg z hz
  have hp := cot_difference_le z hz
  have hmz : 0 ≤ 1 - z := sub_nonneg.mpr hz.2.le
  have hplus : 1 + z ≠ 0 := by linarith [hz.1]
  have hden : 1 - z ^ 2 ≠ 0 := by
    have h1 : 0 < 1 - z := sub_pos.mpr hz.2
    nlinarith only [mul_pos h1 (show 0 < 1 + z by linarith [hz.1])]
  rw [principal_correction_im z hz, abs_div, abs_neg, abs_mul,
    abs_of_nonneg hmz, abs_of_nonneg hD]
  rw [abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
  have hfac : 0 ≤ (1 - z) / 2 := div_nonneg hmz (by norm_num)
  calc
    _ ≤ (1 - z) / 2 * ((2 * z / Real.pi) *
        (1 / (1 - z ^ 2) + tailBound z)) := by
      convert mul_le_mul_of_nonneg_left hp hfac using 1; ring
    _ = correctionImagBound z := by
      unfold correctionImagBound
      field_simp [Real.pi_ne_zero, hplus, hden]
      ring

/-- Norm bound for the actual principal correction, with the singular term
cancelled before interval arithmetic is applied. -/
theorem principal_correction_norm_le (z : ℝ) (hz : z ∈ Ioo (0 : ℝ) 1) :
    ‖prawitzKernel z - Complex.I / ((2 * Real.pi * z : ℝ) : ℂ)‖ ≤
      Real.sqrt (((1 - z) / 2) ^ 2 + correctionImagBound z ^ 2) := by
  have hi := principal_correction_im_abs_le z hz
  have hA := (abs_nonneg _).trans hi
  have hs := (sq_le_sq₀ (abs_nonneg _) hA).mpr hi
  rw [sq_abs] at hs
  rw [Complex.norm_def, Complex.normSq_apply, principal_correction_re z hz]
  apply Real.sqrt_le_sqrt
  nlinarith only [hs]

/-- Reflected imaginary part of the actual kernel. -/
theorem reflectedImaginary_le (w : ℝ) (hw : w ∈ Ioo (0 : ℝ) 1) :
    PrawitzKernelMonotone.reflectedImaginary w ≤ kernelImagBound w := by
  have hd := cot_difference_le w hw
  have hden : 1 - w ^ 2 ≠ 0 := by
    have h1 : 0 < 1 - w := sub_pos.mpr hw.2
    nlinarith only [mul_pos h1 (show 0 < 1 + w by linarith [hw.1])]
  rw [reflectedImaginary_eq w hw]
  calc
    _ ≤ w / 2 * ((2 * w / Real.pi) *
        (1 / (1 - w ^ 2) + tailBound w)) :=
      mul_le_mul_of_nonneg_left hd (div_nonneg hw.1.le (by norm_num))
    _ = kernelImagBound w := by
      unfold kernelImagBound
      field_simp [Real.pi_ne_zero, hden]

/-- Rational four-pole bound for the genuine Prawitz kernel on (0,1). -/
theorem kernel_norm_le (z : ℝ) (hz : z ∈ Ioo (0 : ℝ) 1) :
    ‖prawitzKernel z‖ ≤
      Real.sqrt (((1 - z) / 2) ^ 2 + kernelImagBound (1 - z) ^ 2) := by
  have hw : 1 - z ∈ Ioo (0 : ℝ) 1 := by constructor <;> linarith [hz.1, hz.2]
  have hi := reflectedImaginary_le (1 - z) hw
  have hm := PrawitzKernelMonotone.reflectedImaginary_nonneg (1 - z) hw
  have hB := hm.trans hi
  have hs := (sq_le_sq₀ hm hB).mpr hi
  rw [Complex.norm_def, Complex.normSq_apply,
    PrawitzKernelMonotone.kernel_re z hz, PrawitzKernelMonotone.kernel_im z hz]
  apply Real.sqrt_le_sqrt
  nlinarith only [hs]

end BerryEsseen.PrawitzRationalKernel

#print axioms BerryEsseen.PrawitzRationalKernel.cot_difference_le
#print axioms BerryEsseen.PrawitzRationalKernel.principal_correction_norm_le
#print axioms BerryEsseen.PrawitzRationalKernel.kernel_norm_le
