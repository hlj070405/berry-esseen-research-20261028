module

public import BerryEsseen.RawResourceEnvelope

@[expose] public section

/-! 2026-10-30: small rational polynomial certificates for the joint
right-endpoint projection price. The scalar inequalities retain the same
projection coordinate in the cubic moment and the Gaussian linear term.
They do not supply a probability, support or Fourier hypothesis. -/

noncomputable section

open MeasureTheory Set

namespace BerryEsseen.ProjectedRawPricePolynomial

def cubicMajorant (y : ℝ) : ℝ :=
  -y ^ 3 + (33 / 20) * y ^ 2 + (381 / 500) * y - 1 / 2

def positivePrice (y : ℝ) : ℝ :=
  (819 / 2000) * cubicMajorant y + 27 / 100000 + 79 / 125 +
    (113 / 300 + y ^ 2 / 5) ^ 2 / (607 / 500)

theorem cubicMajorant_le_nine_eighths (y : ℝ) (hy : 0 ≤ y) :
    cubicMajorant y ≤ (9 : ℝ) / 8 := by
  have hs : 0 ≤ (y - 13 / 10) ^ 2 * (y + 19 / 20) :=
    mul_nonneg (sq_nonneg _) (by linarith only [hy])
  have he : 9 / 8 - cubicMajorant y =
      (y - 13 / 10) ^ 2 * (y + 19 / 20) + (9 / 500 : ℝ) * y + 39 / 2000 := by
    unfold cubicMajorant
    ring
  nlinarith only [hs, he, hy]

theorem neg_momentSlope_le_cubicMajorant (μ : ProbabilityMeasure ℝ)
    (h : StandardizedLaw μ) (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10)
    (t : ℝ) :
    -ContactVariation.momentSlope μ t ≤ cubicMajorant |t| := by
  have hρ1 := Extremizer.thirdAbsoluteMoment_ge_one μ h
  have hβ := SignedMoment.abs_signed_lt_127_500 μ h hρ
  have hprod := mul_le_mul_of_nonneg_right hρ (sq_nonneg t)
  have hβt : SignedMoment.signedSecondMoment μ * t ≤ (127 / 500 : ℝ) * |t| := by
    calc
      _ ≤ |SignedMoment.signedSecondMoment μ * t| := le_abs_self _
      _ = |SignedMoment.signedSecondMoment μ| * |t| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right hβ.le (abs_nonneg t)
  unfold ContactVariation.momentSlope cubicMajorant
  rw [sq_abs]
  nlinarith only [hρ1, hprod, hβt]

/-- One centered quartic certificate covers the whole fixed interval. -/
theorem positivePrice_le_seventeen_tenths (y : ℝ)
    (hy0 : 1 ≤ y) (hy1 : y ≤ 12 / 5) :
    positivePrice y ≤ (17 : ℝ) / 10 := by
  let u := y - (9 / 5 : ℝ)
  have hu0 : -(4 / 5 : ℝ) ≤ u := by dsimp [u]; linarith only [hy0]
  have hu1 : u ≤ (4 / 5 : ℝ) := by dsimp [u]; linarith only [hy1]
  have hu2 : u ^ 2 ≤ (16 : ℝ) / 25 := by
    have hp := mul_nonneg (by linarith only [hu0] : 0 ≤ u + 4 / 5)
      (by linarith only [hu1] : 0 ≤ 4 / 5 - u)
    nlinarith only [hp]
  have hu3 : -(4 / 5 : ℝ) * u ^ 2 ≤ u ^ 3 := by
    have hp := mul_nonneg (by linarith only [hu0] : 0 ≤ u + 4 / 5) (sq_nonneg u)
    nlinarith only [hp]
  have hu4 : u ^ 4 ≤ (16 / 25 : ℝ) * u ^ 2 := by
    have hp := mul_nonneg (sub_nonneg.mpr hu2) (sq_nonneg u)
    nlinarith only [hp]
  have he : 17 / 10 - positivePrice y =
      (614114521 / 13657500000 : ℝ) + (12413697 / 607000000 : ℝ) * u +
      (2246357 / 2913600 : ℝ) * u ^ 2 +
      (209133 / 1214000 : ℝ) * u ^ 3 - (20 / 607 : ℝ) * u ^ 4 := by
    unfold positivePrice cubicMajorant u
    ring
  have hs := sq_nonneg (u / 2 + (12413697 / 607000000 : ℝ))
  have huSq := sq_nonneg u
  nlinarith only [he, hu3, hu4, hs, huSq]

/-- Preserve the shared y in the cubic and square terms before maximizing H.
The density may be any real number in [0,.4]; no Gaussian phase is assumed. -/
theorem positive_pointwise (y H C density q : ℝ)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 12 / 5) (hH : 0 ≤ H)
    (hC0 : 819 / 2000 ≤ C) (hC1 : C ≤ 20487 / 50000)
    (hd0 : 0 ≤ density) (hd1 : density ≤ 2 / 5)
    (hq : -q ≤ cubicMajorant y) :
    -C * q + H * density * (y ^ 2 - 1) / 2 ≤
      (17 / 10 : ℝ) - 79 / 125 - (123 / 250 + 127 / 1500) * H +
        (607 / 2000) * H ^ 2 := by
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
    have hs := sq_nonneg ((607 / 1000 : ℝ) * H - 173 / 300)
    nlinarith only [hCq, hbase, hzu, hs]
  · have hyLo : 1 ≤ y := (le_of_not_ge hy)
    have hySq : 1 ≤ y ^ 2 := by nlinarith only [hyLo]
    have hdu := mul_le_mul_of_nonneg_right hd1
      (mul_nonneg hH (sub_nonneg.mpr hySq))
    have hprice := positivePrice_le_seventeen_tenths y hyLo hy1
    have hs := sq_nonneg ((607 / 1000 : ℝ) * H - (113 / 300 + y ^ 2 / 5))
    unfold positivePrice at hprice
    nlinarith only [hCq, hCa, hdu, hprice, hs]

theorem negative_axis_price (y : ℝ) :
    (20487 / 50000 : ℝ) * (9 / 8) + 79 / 125 + (233 / 300) * y -
      (607 / 2000) * y ^ 2 ≤ (17 : ℝ) / 10 := by
  have hs := sq_nonneg ((607 / 1000 : ℝ) * y - 233 / 300)
  nlinarith only [hs]

end BerryEsseen.ProjectedRawPricePolynomial

#print axioms BerryEsseen.ProjectedRawPricePolynomial.neg_momentSlope_le_cubicMajorant
#print axioms BerryEsseen.ProjectedRawPricePolynomial.positivePrice_le_seventeen_tenths
#print axioms BerryEsseen.ProjectedRawPricePolynomial.positive_pointwise
#print axioms BerryEsseen.ProjectedRawPricePolynomial.negative_axis_price
