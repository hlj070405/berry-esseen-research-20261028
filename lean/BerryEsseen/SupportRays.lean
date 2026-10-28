module

public import BerryEsseen.AnalyticConstants
public import BerryEsseen.GaussianKernelNorm
public import BerryEsseen.GaussianContactApplication
public import BerryEsseen.SignedMoment

@[expose] public section

/-! 2026-10-28: the two initial support-ray exclusions, using the original
Gaussian Hermite projection and the original law's actual signed moments.
The support/contact and predecessor interfaces are separate from this analytic step.
-/

noncomputable section

open MeasureTheory

namespace BerryEsseen.SupportRays

open GaussianContactApplication AnalyticConstants

def cubicCost (R b r : ℝ) : ℝ :=
  -r ^ 3 + (3 / 2 : ℝ) * R * r ^ 2 + 3 * b * r + R * (2 / 125)

def gaussianPrice (r : ℝ) : ℝ :=
  (213 : ℝ) / 500 * ((r ^ 3 - 3 * r) / 6 + 3 / 4)

def envelope (R b r : ℝ) : ℝ := gaussianPrice r + (819 : ℝ) / 2000 * cubicCost R b r

def actualCost (μ : ProbabilityMeasure ℝ) (n x : ℝ) : ℝ :=
  -|x| ^ 3 + (3 / 2 : ℝ) * thirdAbsoluteMoment μ * x ^ 2 +
    3 * SignedMoment.signedSecondMoment μ * x + thirdAbsoluteMoment μ * scaleExcess n

theorem hermiteProjection_le_price (n H x : ℝ) (hn : 25 ≤ n) (hx : 2 ≤ |x|) :
    hermiteProjection n H x ≤ gaussianPrice |x| := by
  have h := GaussianKernelNorm.abs_contact_le (testFunction n H)
    (contDiff_testFunction n H) (213 / 500)
    (fun u => (abs_thirdDeriv_lt_213_500 n H u hn).le) x hx
  rw [contact_testFunction_eq_hermiteProjection n H x (by linarith)] at h
  exact (le_abs_self _).trans h

lemma cubicCost_low_neg (r : ℝ) (hr : 12 / 5 ≤ r) :
    cubicCost (11 / 10) (127 / 500) r < 0 := by
  have hy : 0 ≤ r - 12 / 5 := by linarith
  have heq : cubicCost (11 / 10) (127 / 500) r =
      -1546 / 625 - 4299 / 500 * (r - 12 / 5) -
        111 / 20 * (r - 12 / 5) ^ 2 - (r - 12 / 5) ^ 3 := by
    unfold cubicCost
    ring
  rw [heq]
  nlinarith [sq_nonneg (r - 12 / 5), pow_nonneg hy 3]

lemma envelope_low_neg (r : ℝ) (hr : 12 / 5 ≤ r) :
    envelope (11 / 10) (127 / 500) r < 0 := by
  have hy : 0 ≤ r - 12 / 5 := by linarith
  have heq : envelope (11 / 10) (127 / 500) r =
      -278919 / 1250000 - 2507001 / 1000000 * (r - 12 / 5) -
        70461 / 40000 * (r - 12 / 5) ^ 2 - 677 / 2000 * (r - 12 / 5) ^ 3 := by
    unfold envelope gaussianPrice cubicCost
    ring
  rw [heq]
  nlinarith [sq_nonneg (r - 12 / 5), pow_nonneg hy 3]

lemma cubicCost_mid_neg (r : ℝ) (hr : 13 / 5 ≤ r) :
    cubicCost (6 / 5) (44 / 125) r < 0 := by
  have hy : 0 ≤ r - 13 / 5 := by linarith
  have heq : cubicCost (6 / 5) (44 / 125) r =
      -1652 / 625 - 1233 / 125 * (r - 13 / 5) - 6 * (r - 13 / 5) ^ 2 -
        (r - 13 / 5) ^ 3 := by
    unfold cubicCost
    ring
  rw [heq]
  nlinarith [sq_nonneg (r - 13 / 5), pow_nonneg hy 3]

lemma envelope_mid_neg (r : ℝ) (hr : 13 / 5 ≤ r) :
    envelope (6 / 5) (44 / 125) r < 0 := by
  have hy : 0 ≤ r - 13 / 5 := by linarith
  have heq : envelope (6 / 5) (44 / 125) r =
      -85993 / 1250000 - 703107 / 250000 * (r - 13 / 5) -
        2379 / 1250 * (r - 13 / 5) ^ 2 - 677 / 2000 * (r - 13 / 5) ^ 3 := by
    unfold envelope gaussianPrice cubicCost
    ring
  rw [heq]
  nlinarith [sq_nonneg (r - 13 / 5), pow_nonneg hy 3]

private lemma actualCost_le (μ : ProbabilityMeasure ℝ) (n x R b : ℝ)
    (hn : 25 ≤ n) (hR : thirdAbsoluteMoment μ ≤ R)
    (hb : |SignedMoment.signedSecondMoment μ| ≤ b) :
    actualCost μ n x ≤ cubicCost R b |x| := by
  have hρ0 : 0 ≤ thirdAbsoluteMoment μ :=
    integral_nonneg fun u => pow_nonneg (abs_nonneg u) 3
  have hs := mul_le_mul_of_nonneg_right hR (sq_nonneg x)
  have hβx : SignedMoment.signedSecondMoment μ * x ≤ b * |x| := by
    calc
      _ ≤ |SignedMoment.signedSecondMoment μ * x| := le_abs_self _
      _ = |SignedMoment.signedSecondMoment μ| * |x| := abs_mul _ _
      _ ≤ b * |x| := mul_le_mul_of_nonneg_right hb (abs_nonneg x)
  have he : thirdAbsoluteMoment μ * scaleExcess n ≤ R * (2 / 125) := by
    calc
      _ ≤ thirdAbsoluteMoment μ * (2 / 125) :=
        mul_le_mul_of_nonneg_left (scaleExcess_lt_two_125 n hn).le hρ0
      _ ≤ _ := mul_le_mul_of_nonneg_right hR (by norm_num)
  unfold actualCost cubicCost
  rw [sq_abs]
  nlinarith

private lemma ray_neg_of_caps (μ : ProbabilityMeasure ℝ) (n H C x R b : ℝ)
    (hn : 25 ≤ n) (hC : esseenConstant ≤ C) (hx : 2 ≤ |x|)
    (hR : thirdAbsoluteMoment μ ≤ R) (hb : |SignedMoment.signedSecondMoment μ| ≤ b)
    (hQ : cubicCost R b |x| < 0) (hU : envelope R b |x| < 0) :
    hermiteProjection n H x + C * actualCost μ n x < 0 := by
  have hC0 : (819 : ℝ) / 2000 ≤ C := esseenConstant_gt_819_2000.le.trans hC
  have hCp : 0 ≤ C := by linarith
  have h1 := mul_le_mul_of_nonneg_left (actualCost_le μ n x R b hn hR hb) hCp
  have h2 := mul_le_mul_of_nonpos_right hC0 hQ.le
  have hP := hermiteProjection_le_price n H x hn hx
  unfold envelope at hU
  linarith

/-- The entire two-sided ray at radius 12/5, uniformly in the actual threshold. -/
theorem low_moment_ray_neg (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n H C x : ℝ) (hn : 25 ≤ n) (hC : esseenConstant ≤ C)
    (hR : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) (hx : 12 / 5 ≤ |x|) :
    hermiteProjection n H x + C * actualCost μ n x < 0 :=
  ray_neg_of_caps μ n H C x (11 / 10) (127 / 500) hn hC (by linarith) hR
    (SignedMoment.abs_signed_lt_127_500 μ h hR).le
    (cubicCost_low_neg |x| hx) (envelope_low_neg |x| hx)

/-- The entire two-sided ray at radius 13/5, with the same law's moments. -/
theorem mid_moment_ray_neg (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n H C x : ℝ) (hn : 25 ≤ n) (hC : esseenConstant ≤ C)
    (hR : thirdAbsoluteMoment μ ≤ (6 : ℝ) / 5) (hx : 13 / 5 ≤ |x|) :
    hermiteProjection n H x + C * actualCost μ n x < 0 :=
  ray_neg_of_caps μ n H C x (6 / 5) (44 / 125) hn hC (by linarith) hR
    (SignedMoment.abs_signed_lt_44_125 μ h hR).le
    (cubicCost_mid_neg |x| hx) (envelope_mid_neg |x| hx)

end BerryEsseen.SupportRays

#print axioms BerryEsseen.SupportRays.low_moment_ray_neg
#print axioms BerryEsseen.SupportRays.mid_moment_ray_neg
