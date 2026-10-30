module

public import BerryEsseen.GaussianKernelPositive
public import BerryEsseen.GaussianKernelIntegral
public import BerryEsseen.GaussianTailPrices

@[expose] public section

/-! 2026-10-28: the manuscript's uniform Gaussian Peano L1 bound,
assembled from continuous sign control and actual integrable tail prices.
-/

noncomputable section

open MeasureTheory Set

namespace BerryEsseen.GaussianKernelNorm

open GaussianTools GaussianMills GaussianPeano GaussianKernelSign
open GaussianKernelPositive GaussianKernelIntegral GaussianPeanoRepresentation

theorem integral_negativePart_le_prices (x : ℝ) (hx : 2 ≤ x) :
    (∫ t : ℝ, max (-kernel x t) 0) ≤
      (3 / 2 : ℝ) * phi (x / 2) + (1 / 2 : ℝ) * phi (2 * x) + phi x / x ^ 4 := by
  let band : ℝ → ℝ := (Ioc (x / 2) (2 * x)).indicator (fun t => (x - t / 2) * phi t)
  let upper : ℝ → ℝ := (Ioi x).indicator (fun t => (1 / 2 : ℝ) * ((t - x) ^ 2 * tail t))
  have hxpos : 0 < x := by linarith
  have hband : Integrable band :=
    (GaussianTailPrices.integrable_band_price x).indicator measurableSet_Ioc
  have hupper : Integrable upper :=
    (integrable_indicator_iff measurableSet_Ioi).mpr
      ((GaussianTailPrices.integrable_tail_sq_price x hxpos).const_mul (1 / 2 : ℝ))
  have hband0 (t : ℝ) : 0 ≤ band t := by
    by_cases ht : t ∈ Ioc (x / 2) (2 * x)
    · change 0 ≤ (Ioc (x / 2) (2 * x)).indicator (fun t => (x - t / 2) * phi t) t
      rw [indicator_of_mem ht]
      exact mul_nonneg (by linarith [ht.2]) (phi_nonneg t)
    · simp only [band, indicator_of_notMem ht, le_refl]
  have hupper0 (t : ℝ) : 0 ≤ upper t := by
    by_cases ht : t ∈ Ioi x
    · change 0 ≤ (Ioi x).indicator (fun t => (1 / 2 : ℝ) * ((t - x) ^ 2 * tail t)) t
      rw [indicator_of_mem ht]
      exact mul_nonneg (by norm_num) (mul_nonneg (sq_nonneg _) (tail_nonneg t))
    · simp only [upper, indicator_of_notMem ht, le_refl]
  have hupper_eq (t : ℝ) : upper t = (max (t - x) 0) ^ 2 / 2 * tail t := by
    by_cases ht : x < t
    · have hmem : t ∈ Ioi x := ht
      simp only [upper, indicator_of_mem hmem, max_eq_left (sub_nonneg.mpr ht.le)]
      ring
    · have hmem : t ∉ Ioi x := ht
      simp only [upper, indicator_of_notMem hmem,
        max_eq_right (sub_nonpos.mpr (le_of_not_gt ht))]
      norm_num
  have hpoint (t : ℝ) : max (-kernel x t) 0 ≤ band t + upper t := by
    by_cases ht : t ≤ x / 2
    · rw [max_eq_right (neg_nonpos.mpr (kernel_nonneg_le_half x t hx ht))]
      exact add_nonneg (hband0 t) (hupper0 t)
    · have hta : x / 2 < t := lt_of_not_ge ht
      have hband_eq : band t = max (x - t / 2) 0 * phi t := by
        by_cases htb : t ≤ 2 * x
        · simp only [band, indicator_of_mem (show t ∈ Ioc (x / 2) (2 * x) from ⟨hta, htb⟩),
            max_eq_left (show 0 ≤ x - t / 2 by linarith)]
        · simp only [band, indicator_of_notMem (show t ∉ Ioc (x / 2) (2 * x) from
              fun h => htb h.2), max_eq_right (show x - t / 2 ≤ 0 by linarith), zero_mul]
      rw [hband_eq, hupper_eq]
      exact negativePart_le x t
  have hN := (integrable_kernel x).neg_part
  have hle := integral_mono hN (hband.add hupper) hpoint
  change (∫ t : ℝ, max (-kernel x t) 0) ≤ ∫ t : ℝ, band t + upper t at hle
  have hsum : (∫ t : ℝ, band t + upper t) =
      (∫ t in Ioc (x / 2) (2 * x), (x - t / 2) * phi t) +
        (1 / 2 : ℝ) * ∫ t in Ioi x, (t - x) ^ 2 * tail t := by
    rw [integral_add hband hupper]
    simp only [band, upper, integral_indicator measurableSet_Ioc,
      integral_indicator measurableSet_Ioi, integral_const_mul]
  rw [hsum] at hle
  exact hle.trans (add_le_add (GaussianTailPrices.band_price_le x hx)
    (GaussianTailPrices.half_tail_sq_price_le x hx))

theorem integral_negativePart_lt_three_eighths (x : ℝ) (hx : 2 ≤ x) :
    (∫ t : ℝ, max (-kernel x t) 0) < (3 : ℝ) / 8 := by
  have h := integral_negativePart_le_prices x hx
  have h1 : phi (x / 2) < (49 : ℝ) / 200 :=
    (phi_le_of_nonneg_le 1 (x / 2) (by norm_num) (by linarith)).trans_lt
      GaussianPrices.phi_one_lt_49_200
  have h4 : phi (2 * x) < (3 : ℝ) / 20000 :=
    (phi_le_of_nonneg_le 4 (2 * x) (by norm_num) (by linarith)).trans_lt
      GaussianPrices.phi_four_lt_3_20000
  have h2 : phi x < (11 : ℝ) / 200 :=
    (phi_le_of_nonneg_le 2 x (by norm_num) hx).trans_lt GaussianPrices.phi_two_lt_11_200
  have hxpos : 0 < x := by linarith
  have hx2 : (4 : ℝ) ≤ x ^ 2 := by nlinarith [sq_nonneg (x - 2)]
  have hx4 : (16 : ℝ) ≤ x ^ 4 := by nlinarith [sq_nonneg (x ^ 2 - 4)]
  have hdiv : phi x / x ^ 4 ≤ (11 : ℝ) / 3200 := by
    apply (div_le_iff₀ (pow_pos hxpos 4)).mpr
    nlinarith
  linarith

lemma integral_abs_kernel_neg (x : ℝ) :
    (∫ t : ℝ, |kernel (-x) t|) = ∫ t : ℝ, |kernel x t| := by
  have hm : Measure.map (fun t : ℝ => -t) volume = volume := Measure.map_neg_eq_self volume
  have hmeas : AEStronglyMeasurable (fun t : ℝ => |kernel (-x) t|)
      (volume.map (fun t : ℝ => -t)) := by
    rw [hm]
    exact (integrable_kernel (-x)).abs.aestronglyMeasurable
  have h := integral_map (f := fun t : ℝ => |kernel (-x) t|)
    (by fun_prop : AEMeasurable (fun t : ℝ => -t) volume)
    hmeas
  rw [hm] at h
  calc
    (∫ t : ℝ, |kernel (-x) t|) = ∫ t : ℝ, |kernel (-x) (-t)| := h
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall fun t => by
      change |kernel (-x) (-t)| = |kernel x t|
      rw [kernel_reflection, abs_neg])

/-- The uniform kernel bound in the manuscript, on both full support rays. -/
theorem integral_abs_kernel_le (x : ℝ) (hx : 2 ≤ |x|) :
    (∫ t : ℝ, |kernel x t|) ≤ (|x| ^ 3 - 3 * |x|) / 6 + (3 : ℝ) / 4 := by
  have hpos (u : ℝ) (hu : 2 ≤ u) :
      (∫ t : ℝ, |kernel u t|) ≤ (u ^ 3 - 3 * u) / 6 + (3 : ℝ) / 4 := by
    rw [integral_abs_kernel]
    linarith [integral_negativePart_lt_three_eighths u hu]
  rcases le_total 0 x with hx0 | hx0
  · simpa only [abs_of_nonneg hx0] using hpos x (by simpa only [abs_of_nonneg hx0] using hx)
  · have h := hpos (-x) (by simpa only [abs_of_nonpos hx0] using hx)
    rw [integral_abs_kernel_neg] at h
    simpa only [abs_of_nonpos hx0] using h

/-- The full C3 Gaussian Peano price, with the manuscript's 3/4 constant. -/
theorem abs_contact_le (g : ℝ → ℝ) (hg : ContDiff ℝ 3 g) (M : ℝ)
    (hbound : ∀ t, |iteratedDeriv 3 g t| ≤ M) (x : ℝ) (hx : 2 ≤ |x|) :
    |contact x g| ≤ M * ((|x| ^ 3 - 3 * |x|) / 6 + (3 : ℝ) / 4) := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hbound 0)
  exact (abs_contact_le_kernel_norm g hg M hbound x).trans
    (mul_le_mul_of_nonneg_left (integral_abs_kernel_le x hx) hM)

end BerryEsseen.GaussianKernelNorm

#print axioms BerryEsseen.GaussianKernelNorm.integral_negativePart_lt_three_eighths
#print axioms BerryEsseen.GaussianKernelNorm.integral_abs_kernel_le
#print axioms BerryEsseen.GaussianKernelNorm.abs_contact_le
