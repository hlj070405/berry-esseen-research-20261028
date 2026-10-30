module

public import BerryEsseen.GaussianMills
public import BerryEsseen.GaussianPeano

@[expose] public section

/-! 2026-10-28: sign and reflection identities for the actual Gaussian
Peano hinge kernel. Subsequent norm estimates use this same kernel.
-/

noncomputable section

open MeasureTheory Set

namespace BerryEsseen.GaussianKernelSign

open GaussianTools GaussianMills GaussianPeano

theorem Phi_pos (t : ℝ) : 0 < Phi t := by
  have h := tail_pos (-t)
  rw [← Phi_neg (-t), neg_neg] at h
  exact h

theorem Phi_zero : Phi 0 = (1 : ℝ) / 2 := by
  have h := Phi_neg 0
  simp only [neg_zero, tail] at h
  linarith

/-- Reflection is valid even at the knot, whose quadratic coefficient vanishes. -/
theorem kernel_reflection (x t : ℝ) : kernel (-x) (-t) = -kernel x t := by
  rcases lt_trichotomy t x with h | h | h
  · have hnot : ¬ x < t := not_lt_of_ge h.le
    simp only [kernel, neg_lt_neg_iff, ite_eq_left h, ite_eq_right hnot,
      Phi_neg, phi_neg, tail]
    ring
  · subst t
    simp [kernel, Phi_neg, phi_neg, tail]
    ring
  · have hnot : ¬ t < x := not_lt_of_ge h.le
    simp only [kernel, neg_lt_neg_iff, ite_eq_left h, ite_eq_right hnot,
      Phi_neg, phi_neg, tail]
    ring

/-- The Mills bound controls the entire nonpositive half-line, without a grid. -/
theorem kernel_nonneg_of_nonpos (x t : ℝ) (hx : 2 ≤ x) (ht : t ≤ 0) :
    0 ≤ kernel x t := by
  have htx : t < x := by linarith
  have hm := tail_lower_kernel x (-t) hx (neg_nonneg.mpr ht)
  rw [← Phi_neg (-t), neg_neg, phi_neg t] at hm
  have heq : kernel x t =
      ((x - t) ^ 2 * Phi t - (2 * x - t) * phi t) / 2 := by
    simp only [kernel, ite_eq_left htx]
    ring
  rw [heq]
  apply div_nonneg _ (by norm_num)
  nlinarith [phi_neg t]

/-- Pointwise negative-part domination. The first term is supported below
`2*x`; the second above `x`, exactly as in the manuscript's tail split. -/
theorem negativePart_le (x t : ℝ) :
    max (-kernel x t) 0 ≤
      max (x - t / 2) 0 * phi t + (max (t - x) 0) ^ 2 / 2 * tail t := by
  have hp := phi_nonneg t
  have hQ := tail_nonneg t
  have hP := (Phi_pos t).le
  have hfirst : 0 ≤ max (x - t / 2) 0 * phi t := mul_nonneg (le_max_right _ _) hp
  have hsecond : 0 ≤ (max (t - x) 0) ^ 2 / 2 * tail t :=
    mul_nonneg (div_nonneg (sq_nonneg _) (by norm_num)) hQ
  apply max_le _ (add_nonneg hfirst hsecond)
  by_cases htx : t < x
  · rw [max_eq_right (by linarith : t - x ≤ 0)]
    have hcoef := le_max_left (x - t / 2) 0
    have hmul := mul_le_mul_of_nonneg_right hcoef hp
    have hgood : 0 ≤ (x - t) ^ 2 / 2 * Phi t :=
      mul_nonneg (div_nonneg (sq_nonneg _) (by norm_num)) hP
    simp only [kernel, ite_eq_left htx]
    nlinarith
  · have hxt : 0 ≤ t - x := sub_nonneg.mpr (le_of_not_gt htx)
    rw [max_eq_left hxt]
    have hcoef := le_max_left (x - t / 2) 0
    have hmul := mul_le_mul_of_nonneg_right hcoef hp
    simp only [kernel, ite_eq_right htx, tail] at *
    nlinarith

end BerryEsseen.GaussianKernelSign

#print axioms BerryEsseen.GaussianKernelSign.kernel_reflection
#print axioms BerryEsseen.GaussianKernelSign.kernel_nonneg_of_nonpos
#print axioms BerryEsseen.GaussianKernelSign.negativePart_le
