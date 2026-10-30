module

public import BerryEsseen.PrawitzSmoothing
public import BerryEsseen.CharacteristicDerivative
public import Causalean.Stat.CLT.BerryEsseen.PrawitzKernelBounds

@[expose] public section

/-! 2026-10-29: monotonicity of the actual Prawitz filter on (0,1).
This permits endpoint interval bounds without the cotangent dependency
loss near 1. The totalized value at 1 is deliberately excluded. -/

noncomputable section

open MeasureTheory Set Real
open Causalean.Stat.CLT.BerryEsseen

namespace BerryEsseen.PrawitzKernelMonotone

def reflectedImaginary (w : ℝ) : ℝ :=
  (1 / Real.pi - w * (Real.cos (Real.pi * w) / Real.sin (Real.pi * w))) / 2

lemma reflectedImaginary_nonneg (w : ℝ) (hw : w ∈ Ioo (0 : ℝ) 1) :
    0 ≤ reflectedImaginary w := by
  have hx : 0 < Real.pi * w := mul_pos Real.pi_pos hw.1
  have hxπ : Real.pi * w < Real.pi := by
    simpa only [mul_one] using mul_lt_mul_of_pos_left hw.2 Real.pi_pos
  have hs := Real.sin_pos_of_mem_Ioo ⟨hx, hxπ⟩
  have hn := CharacteristicDerivative.sin_sub_mul_cos_nonneg (Real.pi * w) hx.le hxπ.le
  have heq : reflectedImaginary w =
      (Real.sin (Real.pi * w) - Real.pi * w * Real.cos (Real.pi * w)) /
        (2 * Real.pi * Real.sin (Real.pi * w)) := by
    unfold reflectedImaginary
    field_simp [Real.pi_pos.ne', hs.ne']
  rw [heq]
  exact div_nonneg hn (by positivity)

lemma hasDerivAt_reflectedImaginary (w : ℝ) (hw : w ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt reflectedImaginary
      ((Real.pi * w - Real.sin (Real.pi * w) * Real.cos (Real.pi * w)) /
        (2 * Real.sin (Real.pi * w) ^ 2)) w := by
  have hx : 0 < Real.pi * w := mul_pos Real.pi_pos hw.1
  have hxπ : Real.pi * w < Real.pi := by
    simpa only [mul_one] using mul_lt_mul_of_pos_left hw.2 Real.pi_pos
  have hs := Real.sin_pos_of_mem_Ioo ⟨hx, hxπ⟩
  have hc := (Real.hasDerivAt_cos (Real.pi * w)).comp w ((hasDerivAt_id' w).const_mul Real.pi)
  have hsin := (Real.hasDerivAt_sin (Real.pi * w)).comp w ((hasDerivAt_id' w).const_mul Real.pi)
  have hd := (((hasDerivAt_id' w).fun_mul (hc.fun_div hsin hs.ne')).const_sub
    (1 / Real.pi)).div_const 2
  convert hd using 1
  · rfl
  · simp only [Function.comp_apply, mul_one]
    field_simp [hs.ne']
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi * w)]

theorem reflectedImaginary_monotone : MonotoneOn reflectedImaginary (Ioo (0 : ℝ) 1) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun w =>
    (Real.pi * w - Real.sin (Real.pi * w) * Real.cos (Real.pi * w)) /
      (2 * Real.sin (Real.pi * w) ^ 2)) (convex_Ioo _ _)
  · exact fun w hw => (hasDerivAt_reflectedImaginary w hw).continuousAt.continuousWithinAt
  · exact fun w hw => (hasDerivAt_reflectedImaginary w (interior_subset hw)).hasDerivWithinAt
  · intro w hw
    have hw' : w ∈ Ioo (0 : ℝ) 1 := interior_subset hw
    have hs := Real.sin_le (show 0 ≤ 2 * (Real.pi * w) from
      mul_nonneg (by norm_num) (mul_nonneg Real.pi_pos.le hw'.1.le))
    rw [Real.sin_two_mul] at hs
    exact div_nonneg (by nlinarith only [hs]) (by positivity)

lemma kernel_re (z : ℝ) (hz : z ∈ Ioo (0 : ℝ) 1) :
    (prawitzKernel z).re = (1 - z) / 2 := by
  have hn : ¬(z = 0 ∨ 1 < |z|) := by
    rw [abs_of_pos hz.1]
    exact not_or.mpr ⟨hz.1.ne', not_lt.mpr hz.2.le⟩
  rw [prawitzKernel, ite_eq_right hn]
  simp only [abs_of_pos hz.1, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, sub_zero, add_zero]

lemma kernel_im (z : ℝ) (hz : z ∈ Ioo (0 : ℝ) 1) :
    (prawitzKernel z).im = reflectedImaginary (1 - z) := by
  have hn : ¬(z = 0 ∨ 1 < |z|) := by
    rw [abs_of_pos hz.1]
    exact not_or.mpr ⟨hz.1.ne', not_lt.mpr hz.2.le⟩
  have hs : 0 < Real.sin (Real.pi * z) :=
    Real.sin_pos_of_mem_Ioo ⟨mul_pos Real.pi_pos hz.1,
      by simpa only [mul_one] using mul_lt_mul_of_pos_left hz.2 Real.pi_pos⟩
  have hsin : Real.sin (Real.pi * (1 - z)) = Real.sin (Real.pi * z) := by
    rw [mul_sub, mul_one, Real.sin_pi_sub]
  have hcos : Real.cos (Real.pi * (1 - z)) = -Real.cos (Real.pi * z) := by
    rw [mul_sub, mul_one, Real.cos_pi_sub]
  rw [prawitzKernel, ite_eq_right hn]
  simp only [abs_of_pos hz.1, Complex.add_im,
    Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.I_re,
    mul_one, mul_zero, add_zero, zero_add, Real.sign_of_pos hz.1]
  unfold reflectedImaginary
  rw [hsin, hcos]
  field_simp [Real.pi_pos.ne', hs.ne']
  ring

/-- The open interval is essential: the source filter has a separately
totalized endpoint at 1, while its limit from below is zero. -/
theorem norm_kernel_antitone : AntitoneOn (fun z : ℝ => ‖prawitzKernel z‖) (Ioo (0 : ℝ) 1) := by
  intro x hx y hy hxy
  have hwx : 1 - x ∈ Ioo (0 : ℝ) 1 := by constructor <;> linarith only [hx.1, hx.2]
  have hwy : 1 - y ∈ Ioo (0 : ℝ) 1 := by constructor <;> linarith only [hy.1, hy.2]
  have hm := reflectedImaginary_monotone hwy hwx (by linarith only [hxy])
  have hm0 := reflectedImaginary_nonneg (1 - y) hwy
  have hx0 := reflectedImaginary_nonneg (1 - x) hwx
  have hr : ((1 - y) / 2) ^ 2 ≤ ((1 - x) / 2) ^ 2 := by
    apply (sq_le_sq₀ (by linarith only [hy.2]) (by linarith only [hx.2])).mpr
    linarith only [hxy]
  have hi := (sq_le_sq₀ hm0 hx0).mpr hm
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [Complex.sq_norm, Complex.normSq_apply, kernel_re y hy, kernel_im y hy,
    Complex.sq_norm, Complex.normSq_apply, kernel_re x hx, kernel_im x hx]
  simpa only [pow_two] using add_le_add hr hi

end BerryEsseen.PrawitzKernelMonotone

#print axioms BerryEsseen.PrawitzKernelMonotone.reflectedImaginary_monotone
#print axioms BerryEsseen.PrawitzKernelMonotone.norm_kernel_antitone
