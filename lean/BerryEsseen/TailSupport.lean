module

public import BerryEsseen.InitialSupport

@[expose] public section

/-! 2026-10-28: the four radial contractions in the zero-predecessor-loss
tail route. Moment caps are explicit inputs from their preceding acquisitions.
-/

noncomputable section

open MeasureTheory Set

namespace BerryEsseen.TailSupport

open GaussianTools GaussianContactApplication ContactVariation ContactMajorant
open SupportRays AnalyticConstants

lemma thirdScale_lt_207_200 (n : ℝ) (hn : 47 ≤ n) : thirdScale n < (207 : ℝ) / 200 := by
  have hn2 : 2 ≤ n := by linarith
  have hd : 0 < n - 1 := by linarith
  have hratio : n / (n - 1) ≤ (47 : ℝ) / 46 := by
    apply (div_le_iff₀ hd).mpr
    linarith
  have hpow := pow_le_pow_left₀ (div_nonneg (show 0 ≤ n by linarith) hd.le) hratio 3
  have hs : thirdScale n ^ 2 < ((207 : ℝ) / 200) ^ 2 := by
    rw [thirdScale_sq n hn2]
    exact hpow.trans_lt (by norm_num)
  exact (sq_lt_sq₀ (thirdScale_pos n hn2).le (by norm_num)).mp hs

lemma abs_thirdDeriv_le_207_500 (n H u : ℝ) (hn : 47 ≤ n) :
    |iteratedDeriv 3 (testFunction n H) u| ≤ (207 : ℝ) / 500 := by
  have hn2 : 2 ≤ n := by linarith
  calc
    _ ≤ thirdScale n * phi 0 := abs_thirdDeriv_le n H u hn2
    _ ≤ thirdScale n * (2 / 5) := mul_le_mul_of_nonneg_left
      GaussianPrices.phi_zero_lt_2_5.le (thirdScale_pos n hn2).le
    _ ≤ (207 / 200) * (2 / 5) :=
      mul_le_mul_of_nonneg_right (thirdScale_lt_207_200 n hn).le (by norm_num)
    _ = _ := by norm_num

def cost (R b r : ℝ) : ℝ := -r ^ 3 + (3 / 2 : ℝ) * R * r ^ 2 + 3 * b * r + R * (2 / 235)
def price (r : ℝ) : ℝ := (207 : ℝ) / 500 * ((r ^ 3 - 3 * r) / 6 + 3 / 4)
def bound (R b r : ℝ) : ℝ := price r + (819 : ℝ) / 2000 * cost R b r
def q1 (R b r : ℝ) : ℝ := -3 * r ^ 2 + 3 * R * r + 3 * b
def q2 (R r : ℝ) : ℝ := -3 * r + (3 / 2 : ℝ) * R
def v1 (R b r : ℝ) : ℝ := (207 : ℝ) / 500 * (r ^ 2 / 2 - 1 / 2) + (819 : ℝ) / 2000 * q1 R b r
def v2 (R r : ℝ) : ℝ := (207 : ℝ) / 1000 * r + (819 : ℝ) / 2000 * q2 R r

private lemma cubics_neg (R b a r : ℝ) (hr : a ≤ r)
    (hQ0 : cost R b a < 0) (hQ1 : q1 R b a ≤ 0) (hQ2 : q2 R a ≤ 0)
    (hV0 : bound R b a < 0) (hV1 : v1 R b a ≤ 0) (hV2 : v2 R a ≤ 0) :
    cost R b r < 0 ∧ bound R b r < 0 := by
  have hy : 0 ≤ r - a := sub_nonneg.mpr hr
  have hy2 := sq_nonneg (r - a)
  have hy3 := pow_nonneg hy 3
  have hq1 := mul_nonpos_of_nonpos_of_nonneg hQ1 hy
  have hq2 := mul_nonpos_of_nonpos_of_nonneg hQ2 hy2
  have hv1 := mul_nonpos_of_nonpos_of_nonneg hV1 hy
  have hv2 := mul_nonpos_of_nonpos_of_nonneg hV2 hy2
  have hq : cost R b r = cost R b a + q1 R b a * (r - a) +
      q2 R a * (r - a) ^ 2 - (r - a) ^ 3 := by unfold cost q1 q2; ring
  have hv : bound R b r = bound R b a + v1 R b a * (r - a) +
      v2 R a * (r - a) ^ 2 - (681 : ℝ) / 2000 * (r - a) ^ 3 := by
    unfold bound price cost v1 v2 q1 q2
    ring
  constructor
  · rw [hq]; linarith
  · rw [hv]; linarith

private lemma hermite_le_price (n H x : ℝ) (hn : 47 ≤ n) (hx : 2 ≤ |x|) :
    hermiteProjection n H x ≤ price |x| := by
  have h := GaussianKernelNorm.abs_contact_le (testFunction n H) (contDiff_testFunction n H)
    (207 / 500) (fun u => abs_thirdDeriv_le_207_500 n H u hn) x hx
  rw [contact_testFunction_eq_hermiteProjection n H x (by linarith)] at h
  exact (le_abs_self _).trans h

private lemma actualCost_le_cost (μ : ProbabilityMeasure ℝ) (n x R b : ℝ)
    (hn : 47 ≤ n) (hR : thirdAbsoluteMoment μ ≤ R)
    (hb : |SignedMoment.signedSecondMoment μ| ≤ b) : actualCost μ n x ≤ cost R b |x| := by
  have hρ0 : 0 ≤ thirdAbsoluteMoment μ := integral_nonneg fun u => pow_nonneg (abs_nonneg u) 3
  have hs := mul_le_mul_of_nonneg_right hR (sq_nonneg x)
  have hβx : SignedMoment.signedSecondMoment μ * x ≤ b * |x| := by
    calc
      _ ≤ |SignedMoment.signedSecondMoment μ * x| := le_abs_self _
      _ = |SignedMoment.signedSecondMoment μ| * |x| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right hb (abs_nonneg x)
  have he : scaleExcess n ≤ (2 : ℝ) / 235 := by
    apply (scaleExcess_lt n (by linarith)).le.trans
    apply (div_le_iff₀ (show 0 < 5 * n by linarith)).mpr
    linarith
  have hρe : thirdAbsoluteMoment μ * scaleExcess n ≤ R * (2 / 235) :=
    (mul_le_mul_of_nonneg_left he hρ0).trans (mul_le_mul_of_nonneg_right hR (by norm_num))
  unfold actualCost cost
  rw [sq_abs]
  nlinarith

/-- A closed parameter row gives a whole-ray exclusion and hence actual open support. -/
theorem support_of_row (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (hn : 47 ≤ n) (H C R b a : ℝ) (hm : PositiveClosedMaximum μ n H C)
    (hprev : PredecessorBound μ n C) (hC : esseenConstant ≤ C)
    (hR : thirdAbsoluteMoment μ ≤ R) (hb : |SignedMoment.signedSecondMoment μ| ≤ b)
    (ha : 2 ≤ a) (hQ0 : cost R b a < 0) (hQ1 : q1 R b a ≤ 0) (hQ2 : q2 R a ≤ 0)
    (hV0 : bound R b a < 0) (hV1 : v1 R b a ≤ 0) (hV2 : v2 R a ≤ 0) :
    (μ : Measure ℝ).support ⊆ Ioo (-a) a := by
  intro x hxs
  change -a < x ∧ x < a
  apply abs_lt.mp
  by_contra hnot
  have hx : a ≤ |x| := le_of_not_gt hnot
  have hnR : (47 : ℝ) ≤ n := by exact_mod_cast hn
  obtain ⟨hQ, hV⟩ := cubics_neg R b a |x| hx hQ0 hQ1 hQ2 hV0 hV1 hV2
  have hC0 : (819 : ℝ) / 2000 ≤ C := esseenConstant_gt_819_2000.le.trans hC
  have hCp : 0 ≤ C := by linarith
  have h1 := mul_le_mul_of_nonneg_left (actualCost_le_cost μ n x R b hnR hR hb) hCp
  have h2 := mul_le_mul_of_nonpos_right hC0 hQ.le
  have hP := hermite_le_price n H x hnR (ha.trans hx)
  have hneg : hermiteProjection n H x + C * actualCost μ n x < 0 := by
    unfold bound at hV
    linarith
  have hmajor := sqrt_mul_D_le μ n (by omega) H C hm hprev x
  rw [SupportContact.D_eq_zero_on_support μ h n (by omega) H C hm x hxs, mul_zero] at hmajor
  linarith

theorem initial_support (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (hn : 47 ≤ n) (H C : ℝ) (hm : PositiveClosedMaximum μ n H C)
    (hprev : PredecessorBound μ n C) (hC : esseenConstant ≤ C)
    (hR : thirdAbsoluteMoment μ ≤ (7361 : ℝ) / 4000) :
    (μ : Measure ℝ).support ⊆ Ioo (-(96 / 25 : ℝ)) (96 / 25) := by
  apply support_of_row μ h n hn H C (7361 / 4000) (643 / 1000) (96 / 25) hm hprev hC hR
    (SignedMoment.abs_signed_lt_643_1000 μ h hR).le
  all_goals norm_num [cost, q1, q2, bound, price, v1, v2]

theorem support_three (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (hn : 47 ≤ n) (H C : ℝ) (hm : PositiveClosedMaximum μ n H C)
    (hprev : PredecessorBound μ n C) (hC : esseenConstant ≤ C)
    (hR : thirdAbsoluteMoment μ ≤ (139 : ℝ) / 100)
    (hb : |SignedMoment.signedSecondMoment μ| ≤ (43 : ℝ) / 100) :
    (μ : Measure ℝ).support ⊆ Ioo (-3) 3 := by
  apply support_of_row μ h n hn H C (139 / 100) (43 / 100) 3 hm hprev hC hR hb
  all_goals norm_num [cost, q1, q2, bound, price, v1, v2]

theorem support_twenty_seven_tenths (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (hn : 47 ≤ n) (H C : ℝ) (hm : PositiveClosedMaximum μ n H C)
    (hprev : PredecessorBound μ n C) (hC : esseenConstant ≤ C)
    (hR : thirdAbsoluteMoment μ ≤ (12563 : ℝ) / 10000)
    (hb : |SignedMoment.signedSecondMoment μ| ≤ (1963 : ℝ) / 5000) :
    (μ : Measure ℝ).support ⊆ Ioo (-(27 / 10 : ℝ)) (27 / 10) := by
  apply support_of_row μ h n hn H C (12563 / 10000) (1963 / 5000) (27 / 10) hm hprev hC hR hb
  all_goals norm_num [cost, q1, q2, bound, price, v1, v2]

theorem central_support (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (hn : 47 ≤ n) (H C : ℝ) (hm : PositiveClosedMaximum μ n H C)
    (hprev : PredecessorBound μ n C) (hC : esseenConstant ≤ C)
    (hR : thirdAbsoluteMoment μ ≤ (603687 : ℝ) / 500000)
    (hb : |SignedMoment.signedSecondMoment μ| ≤ (4014 : ℝ) / 15625) :
    (μ : Measure ℝ).support ⊆ Ioo (-(5 / 2 : ℝ)) (5 / 2) := by
  apply support_of_row μ h n hn H C (603687 / 500000) (4014 / 15625) (5 / 2) hm hprev hC hR hb
  all_goals norm_num [cost, q1, q2, bound, price, v1, v2]

end BerryEsseen.TailSupport

#print axioms BerryEsseen.TailSupport.initial_support
#print axioms BerryEsseen.TailSupport.support_three
#print axioms BerryEsseen.TailSupport.support_twenty_seven_tenths
#print axioms BerryEsseen.TailSupport.central_support
