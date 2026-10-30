module

public import BerryEsseen.ProjectedRawPricePolynomial

@[expose] public section

/-! 2026-10-30: a second joint scalar price, for an independently licensed
Fourier intercept 509/1250 and retained phase curvature at least 7/50.
These scalar certificates do not acquire either analytic license. -/

noncomputable section

namespace BerryEsseen.P39RebatedPricePolynomial

open ProjectedRawPricePolynomial

def positivePrice (y : ℝ) : ℝ :=
  (819 / 2000) * cubicMajorant y + 27 / 100000 + 509 / 1250 +
    (113 / 300 + y ^ 2 / 5) ^ 2 / (887 / 500)

theorem positivePrice_le_sixty_one_fiftieths (y : ℝ)
    (hy0 : 1 ≤ y) (hy1 : y ≤ 12 / 5) :
    positivePrice y ≤ (61 : ℝ) / 50 := by
  let u := y - (8 / 5 : ℝ)
  have hu0 : -(3 / 5 : ℝ) ≤ u := by dsimp [u]; linarith only [hy0]
  have hu1 : u ≤ (4 / 5 : ℝ) := by dsimp [u]; linarith only [hy1]
  have hu2 : u ^ 2 ≤ (16 : ℝ) / 25 := by
    have hp := mul_nonneg (by linarith only [hu0] : 0 ≤ u + 4 / 5)
      (by linarith only [hu1] : 0 ≤ 4 / 5 - u)
    nlinarith only [hp]
  have hu3 : -(3 / 5 : ℝ) * u ^ 2 ≤ u ^ 3 := by
    have hp := mul_nonneg (by linarith only [hu0] : 0 ≤ u + 3 / 5) (sq_nonneg u)
    nlinarith only [hp]
  have hu4 : u ^ 4 ≤ (16 / 25 : ℝ) * u ^ 2 := by
    have hp := mul_nonneg (sub_nonneg.mpr hu2) (sq_nonneg u)
    nlinarith only [hp]
  have he : 61 / 50 - positivePrice y =
      (101949733 / 4989375000 : ℝ) + (78655021 / 2661000000 : ℝ) * u +
      (91395617 / 106440000 : ℝ) * u ^ 2 +
      (470453 / 1774000 : ℝ) * u ^ 3 - (20 / 887 : ℝ) * u ^ 4 := by
    unfold positivePrice cubicMajorant u
    ring
  have hs := sq_nonneg (u / 2 + (78655021 / 2661000000 : ℝ))
  have huSq := sq_nonneg u
  nlinarith only [he, hu3, hu4, hs, huSq]

theorem positive_pointwise (y H C density q : ℝ)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 12 / 5) (hH : 0 ≤ H)
    (hC0 : 819 / 2000 ≤ C) (hC1 : C ≤ 20487 / 50000)
    (hd0 : 0 ≤ density) (hd1 : density ≤ 2 / 5)
    (hq : -q ≤ cubicMajorant y) :
    -C * q + H * density * (y ^ 2 - 1) / 2 ≤
      (61 / 50 : ℝ) - 509 / 1250 - (123 / 250 + 127 / 1500) * H +
        (887 / 2000) * H ^ 2 := by
  have hC : 0 ≤ C := by linarith only [hC0]
  have ha := cubicMajorant_le_nine_eighths y hy0
  have hCq := mul_le_mul_of_nonneg_left hq hC
  have hCa : C * cubicMajorant y ≤ (819 / 2000 : ℝ) * cubicMajorant y + 27 / 100000 := by
    have hp := mul_le_mul_of_nonneg_left ha
      (by linarith only [hC0] : 0 ≤ C - 819 / 2000)
    nlinarith only [hp, hC1]
  by_cases hy : y ≤ 1
  · have hySq : y ^ 2 ≤ 1 := by nlinarith only [hy0, hy]
    have hzu : H * density * (y ^ 2 - 1) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hH hd0) (by linarith only [hySq])
    have hbase : C * cubicMajorant y ≤ (20487 / 50000 : ℝ) * (9 / 8) :=
      (mul_le_mul_of_nonneg_left ha hC).trans
        (mul_le_mul_of_nonneg_right hC1 (by norm_num))
    have hs := sq_nonneg ((887 / 1000 : ℝ) * H - 173 / 300)
    nlinarith only [hCq, hbase, hzu, hs]
  · have hyLo : 1 ≤ y := le_of_not_ge hy
    have hySq : 1 ≤ y ^ 2 := by nlinarith only [hyLo]
    have hdu := mul_le_mul_of_nonneg_right hd1
      (mul_nonneg hH (sub_nonneg.mpr hySq))
    have hprice := positivePrice_le_sixty_one_fiftieths y hyLo hy1
    have hs := sq_nonneg ((887 / 1000 : ℝ) * H - (113 / 300 + y ^ 2 / 5))
    unfold positivePrice at hprice
    nlinarith only [hCq, hCa, hdu, hprice, hs]

theorem negative_axis_price (y : ℝ) :
    (20487 / 50000 : ℝ) * (9 / 8) + 509 / 1250 + (233 / 300) * y -
      (887 / 2000) * y ^ 2 ≤ (61 : ℝ) / 50 := by
  have hs := sq_nonneg ((887 / 1000 : ℝ) * y - 233 / 300)
  nlinarith only [hs]

end BerryEsseen.P39RebatedPricePolynomial

#print axioms BerryEsseen.P39RebatedPricePolynomial.positivePrice_le_sixty_one_fiftieths
#print axioms BerryEsseen.P39RebatedPricePolynomial.positive_pointwise
#print axioms BerryEsseen.P39RebatedPricePolynomial.negative_axis_price
