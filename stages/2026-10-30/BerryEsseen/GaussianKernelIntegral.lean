module

public import BerryEsseen.GaussianPeanoRepresentation

@[expose] public section

/-! 2026-10-28: the signed mass and the L1 price of the actual Peano kernel.
Numerical norm bounds are a separate consequence of its negative-part estimates.
-/

noncomputable section

open MeasureTheory ProbabilityTheory

namespace BerryEsseen.GaussianKernelIntegral

open GaussianTools GaussianPeano GaussianPeanoRepresentation

lemma expectation_cube : expectation (fun u : ℝ => u ^ 3) = 0 := by
  have hmap : standardGaussian.map (fun u : ℝ => -u) = standardGaussian := by
    simpa only [standardGaussian, neg_zero] using
      (gaussianReal_map_neg (μ := 0) (v := 1))
  have h := integral_map (f := fun u : ℝ => u ^ 3)
    (by fun_prop : AEMeasurable (fun u : ℝ => -u) standardGaussian)
    (by fun_prop)
  rw [hmap] at h
  have hn : (∫ u : ℝ, (-u) ^ 3 ∂standardGaussian) =
      -expectation (fun u : ℝ => u ^ 3) := by
    have heq : (fun u : ℝ => (-u) ^ 3) = (fun u : ℝ => -(u ^ 3)) := by
      ext u
      ring
    rw [heq, integral_neg]
    rfl
  change expectation (fun u : ℝ => u ^ 3) = ∫ u : ℝ, (-u) ^ 3 ∂standardGaussian at h
  rw [hn] at h
  linarith

def cubic (u : ℝ) : ℝ := u ^ 3 / 6

lemma deriv_cubic : deriv cubic = (fun u : ℝ => u ^ 2 / 2) := by
  ext u
  have h := (((hasDerivAt_id' u).fun_pow 3).div_const 6).deriv
  change deriv (fun u : ℝ => u ^ 3 / 6) u = u ^ 2 / 2
  rw [h]
  ring

lemma secondDeriv_cubic : iteratedDeriv 2 cubic = (fun u : ℝ => u) := by
  rw [show (2 : ℕ) = 1 + 1 by rfl, iteratedDeriv_succ, iteratedDeriv_one, deriv_cubic]
  ext u
  have h := (((hasDerivAt_id' u).fun_pow 2).div_const 2).deriv
  convert h using 1; ring

lemma thirdDeriv_cubic : iteratedDeriv 3 cubic = (fun _ : ℝ => 1) := by
  rw [show (3 : ℕ) = 2 + 1 by rfl, iteratedDeriv_succ, secondDeriv_cubic]
  ext u
  exact (hasDerivAt_id' u).deriv

lemma contact_cubic (x : ℝ) : contact x cubic = (x ^ 3 - 3 * x) / 6 := by
  have h3 : expectation cubic = 0 := by
    change (∫ u : ℝ, u ^ 3 / 6 ∂standardGaussian) = 0
    rw [integral_div]
    change expectation (fun u : ℝ => u ^ 3) / 6 = 0
    rw [expectation_cube]
    norm_num
  have h1 : expectation (deriv cubic) = (1 : ℝ) / 2 := by
    rw [deriv_cubic]
    change (∫ u : ℝ, u ^ 2 / 2 ∂standardGaussian) = _
    rw [integral_div]
    change expectation (fun u : ℝ => u ^ 2) / 2 = _
    rw [expectation_square]
  rw [contact, h3, h1, secondDeriv_cubic, expectation_id, cubic]
  ring

theorem integral_kernel (x : ℝ) : (∫ t : ℝ, kernel x t) = (x ^ 3 - 3 * x) / 6 := by
  have hg : ContDiff ℝ 3 cubic := by unfold cubic; fun_prop
  have hb : ∀ t : ℝ, |iteratedDeriv 3 cubic t| ≤ (1 : ℝ) := by
    intro t
    rw [thirdDeriv_cubic]
    norm_num
  have h := contact_eq_integral_third_mul_kernel cubic hg 1 hb x
  simpa only [thirdDeriv_cubic, one_mul, contact_cubic] using h.symm

/-- The L1 norm is exactly the signed mass plus twice the negative mass. -/
theorem integral_abs_kernel (x : ℝ) :
    (∫ t : ℝ, |kernel x t|) = (x ^ 3 - 3 * x) / 6 +
      2 * ∫ t : ℝ, max (-kernel x t) 0 := by
  have hK := integrable_kernel x
  have heq : (fun t : ℝ => |kernel x t|) =
      (fun t : ℝ => kernel x t + 2 * max (-kernel x t) 0) := by
    ext t
    rcases le_total 0 (kernel x t) with ht | ht
    · rw [abs_of_nonneg ht, max_eq_right (neg_nonpos.mpr ht)]
      ring
    · rw [abs_of_nonpos ht, max_eq_left (neg_nonneg.mpr ht)]
      ring
  rw [heq, integral_add hK (hK.neg_part.const_mul 2), integral_const_mul, integral_kernel]

/-- A bounded third derivative prices the original contact by this actual L1 norm. -/
theorem abs_contact_le_kernel_norm (g : ℝ → ℝ) (hg : ContDiff ℝ 3 g) (M : ℝ)
    (hbound : ∀ t, |iteratedDeriv 3 g t| ≤ M) (x : ℝ) :
    |contact x g| ≤ M * ∫ t : ℝ, |kernel x t| := by
  rw [contact_eq_integral_third_mul_kernel g hg M hbound x]
  have h3 := integrable_third_mul_kernel g hg M hbound x
  have hK : Integrable (fun t : ℝ => |kernel x t|) := (integrable_kernel x).abs
  calc
    |∫ t : ℝ, iteratedDeriv 3 g t * kernel x t| ≤
        ∫ t : ℝ, |iteratedDeriv 3 g t * kernel x t| := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun t : ℝ => iteratedDeriv 3 g t * kernel x t)
    _ ≤ ∫ t : ℝ, M * |kernel x t| := by
      apply integral_mono h3.abs (hK.const_mul M)
      intro t
      change |iteratedDeriv 3 g t * kernel x t| ≤ M * |kernel x t|
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hbound t) (abs_nonneg _)
    _ = M * ∫ t : ℝ, |kernel x t| := integral_const_mul _ _

end BerryEsseen.GaussianKernelIntegral

#print axioms BerryEsseen.GaussianKernelIntegral.integral_kernel
#print axioms BerryEsseen.GaussianKernelIntegral.integral_abs_kernel
#print axioms BerryEsseen.GaussianKernelIntegral.abs_contact_le_kernel_norm
