module

public import BerryEsseen.GaussianKernelSign
public import BerryEsseen.GaussianPrices

@[expose] public section

/-! 2026-10-28: continuous half-line sign control for the actual Peano kernel.
No discretization of either the support variable or the kernel argument is used.
-/

noncomputable section

open MeasureTheory Set

namespace BerryEsseen.GaussianKernelPositive

open GaussianTools GaussianMills GaussianPeano GaussianKernelSign

lemma Phi_mono : Monotone Phi := by
  intro a b hab
  exact measureReal_mono (Iic_subset_Iic.mpr hab)

lemma phi_le_of_nonneg_le (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) : phi b ≤ phi a := by
  have hb : 0 ≤ b := ha.trans hab
  have hs := (sq_le_sq₀ ha hb).mpr hab
  simp only [phi_formula]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Real.sqrt_nonneg _))
  apply Real.exp_le_exp.mpr
  linarith

def unitPolynomial (t : ℝ) : ℝ :=
  1 / 5 - t / 50 - 13 * t ^ 2 / 100 - 7 * t ^ 3 / 200 +
    3 * t ^ 4 / 100 - 3 * t ^ 5 / 400

lemma unitPolynomial_pos (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (3 : ℝ) / 80 ≤ unitPolynomial t := by
  have ht3 : t ^ 3 ≤ 1 := by
    have h := mul_nonneg (show 0 ≤ 1 - t by linarith)
      (show 0 ≤ 1 + t + t ^ 2 by nlinarith [sq_nonneg t])
    nlinarith
  have hQ : 0 ≤ (13 : ℝ) / 80 + 57 * t / 400 + t ^ 2 / 80 -
      9 * t ^ 3 / 400 + 3 * t ^ 4 / 400 := by
    nlinarith [sq_nonneg t, pow_nonneg ht0 4]
  have h := mul_nonneg (show 0 ≤ 1 - t by linarith) hQ
  have heq : unitPolynomial t - 3 / 80 = (1 - t) *
      (13 / 80 + 57 * t / 400 + t ^ 2 / 80 - 9 * t ^ 3 / 400 + 3 * t ^ 4 / 400) := by
    unfold unitPolynomial
    ring
  rw [← heq] at h
  linarith

lemma kernel_two_ge_unitPolynomial (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    unitPolynomial t ≤ kernel 2 t := by
  have hP := GaussianPrices.Phi_lower_on_unit t ht0 ht1
  have hp := GaussianPrices.phi_le_quartic t
  have hA := mul_le_mul_of_nonneg_left hP
    (div_nonneg (sq_nonneg (2 - t)) (show (0 : ℝ) ≤ 2 by norm_num))
  have hB := mul_le_mul_of_nonpos_left hp (show t / 2 - 2 ≤ 0 by linarith)
  calc
    unitPolynomial t = (2 - t) ^ 2 / 2 *
        (1 / 2 + 39 / 100 * (t - t ^ 3 / 6)) +
        (t / 2 - 2) * (2 / 5 * (1 - t ^ 2 / 2 + t ^ 4 / 8)) := by
      unfold unitPolynomial
      ring
    _ ≤ (2 - t) ^ 2 / 2 * Phi t + (t / 2 - 2) * phi t := add_le_add hA hB
    _ = kernel 2 t := by
      simp only [kernel, ite_eq_left (show t < (2 : ℝ) by linarith)]
      ring

lemma kernel_ge_kernel_two_on_unit (x t : ℝ) (hx : 2 ≤ x)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : kernel 2 t ≤ kernel x t := by
  have hPhi : (1 : ℝ) / 2 ≤ Phi t := by
    rw [← GaussianKernelSign.Phi_zero]
    exact Phi_mono ht0
  have hphi : phi t ≤ (2 : ℝ) / 5 :=
    (phi_le_of_nonneg_le 0 t (by norm_num) ht0).trans GaussianPrices.phi_zero_lt_2_5.le
  have hc : 0 ≤ x + 2 - 2 * t := by linarith
  have hm := mul_nonneg hc (show 0 ≤ Phi t - 1 / 2 by linarith)
  have hcoef : 0 ≤ (x + 2 - 2 * t) * Phi t - 2 * phi t := by nlinarith
  have hprod := mul_nonneg (show 0 ≤ x - 2 by linarith) hcoef
  have heq : 2 * (kernel x t - kernel 2 t) =
      (x - 2) * ((x + 2 - 2 * t) * Phi t - 2 * phi t) := by
    simp only [kernel, ite_eq_left (show t < x by linarith),
      ite_eq_left (show t < (2 : ℝ) by linarith)]
    ring
  rw [← heq] at hprod
  linarith

lemma kernel_nonneg_of_one_le (x t : ℝ) (ht : 1 ≤ t) (hx : 2 * t ≤ x) :
    0 ≤ kernel x t := by
  have ht0 : 0 ≤ t := by linarith
  have hPhi : (33 : ℝ) / 40 ≤ Phi t := GaussianPrices.Phi_one_ge_33_40.trans (Phi_mono ht)
  have hphi : phi t ≤ (49 : ℝ) / 200 :=
    (phi_le_of_nonneg_le 1 t (by norm_num) ht).trans GaussianPrices.phi_one_lt_49_200.le
  have hp := (Phi_pos t).le
  have hpp := phi_nonneg t
  have hmul := mul_nonneg (show 0 ≤ t - 1 by linarith) hp
  have hprice : 0 ≤ t * Phi t - 3 * phi t := by nlinarith
  have hprice' : 0 ≤ t * Phi t - phi t := by linarith
  have hw : 0 ≤ x - 2 * t := by linarith
  have hA := mul_nonneg ht0 hprice
  have hB := mul_nonneg hw hprice'
  have hC := mul_nonneg (sq_nonneg (x - 2 * t)) hp
  have heq : 2 * kernel x t = t * (t * Phi t - 3 * phi t) +
      2 * (x - 2 * t) * (t * Phi t - phi t) + (x - 2 * t) ^ 2 * Phi t := by
    simp only [kernel, ite_eq_left (show t < x by linarith)]
    ring
  nlinarith

/-- The full continuous region used to discard the kernel's negative part. -/
theorem kernel_nonneg_le_half (x t : ℝ) (hx : 2 ≤ x) (ht : t ≤ x / 2) :
    0 ≤ kernel x t := by
  by_cases ht0 : t ≤ 0
  · exact kernel_nonneg_of_nonpos x t hx ht0
  · have ht0' : 0 ≤ t := (lt_of_not_ge ht0).le
    by_cases ht1 : t ≤ 1
    · have h1 := unitPolynomial_pos t ht0' ht1
      have h2 := kernel_two_ge_unitPolynomial t ht0' ht1
      have h3 := kernel_ge_kernel_two_on_unit x t hx ht0' ht1
      linarith
    · exact kernel_nonneg_of_one_le x t (le_of_not_ge ht1) (by linarith)

end BerryEsseen.GaussianKernelPositive

#print axioms BerryEsseen.GaussianKernelPositive.kernel_nonneg_le_half
