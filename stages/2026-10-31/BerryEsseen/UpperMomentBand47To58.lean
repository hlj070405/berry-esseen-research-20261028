module

public import BerryEsseen.UpperMomentN47Certified
public import BerryEsseen.UpperMomentNu235FirstIntegral
public import BerryEsseen.UpperMomentNu235RemainingIntegrals

@[expose] public section

/-! 2026-10-30: one complete closed spectral strip from the shared n47
spectrum and the real parameter node 235/4. Only actual integer sample
sizes enter the CDF client. The single p=3/2 chord cost is 256/253; both
endpoint prices are at most 253/625, so the strip costs at most 256/625.
The old 0.405 n47 result remains unchanged. -/

noncomputable section

open MeasureTheory Set

namespace BerryEsseen.UpperMomentBand47To58

open UpperMomentN47Budget (U L A V)

def a : ℝ := 752000000 / 54184321
def b : ℝ := 940000000 / 54184321
def delta47 : ℝ := 2343428020515257963 / 22000000000000000000
def delta235 : ℝ := 119 / 1250

lemma a_pos : 0 < a := by norm_num [a]
lemma b_pos : 0 < b := by norm_num [b]
lemma a_lt_b : a < b := by norm_num [a, b]
lemma d_le_a : UpperMomentSpectrumPrice.d U ≤ a := by norm_num [UpperMomentSpectrumPrice.d, U, a]

private theorem profile_le_of_integrals (s i1 i2 i3 tail : ℝ)
    (h1 : (∫ v in Ioc 0 A, UpperMomentAbsoluteProfile.first U (UpperMomentDamping.G U U) 4 s v) ≤ i1)
    (h2 : (∫ v in Ioc A 4, UpperMomentAbsoluteProfile.second (UpperMomentDamping.G U U) 4 s v) ≤ i2)
    (h3 : (∫ v in Ioc 0 A, UpperMomentAbsoluteProfile.third 4 s v) ≤ i3)
    (h4 : (1 / Real.pi) * (∫ v in Ioi A, UpperMomentAbsoluteProfile.fourth s v) ≤ tail) :
    UpperMomentAbsoluteProfile.profile U (UpperMomentDamping.G U U) A 4 s ≤
      (i1 + i2 + i3) / 2 + tail := by
  unfold UpperMomentAbsoluteProfile.profile
  norm_num only [show (2 : ℝ) / 4 = 1 / 2 by norm_num]
  linarith only [h1, h2, h3, h4]

theorem absolute47_le :
    UpperMomentAbsoluteProfile.profile U (UpperMomentDamping.G U U) A 4 a ≤ delta47 := by
  have ht := profile_le_of_integrals a _ _ _ _
    UpperMomentN47FirstIntegral.first_integral_le
    UpperMomentN47RemainingIntegrals.actual_second_integral_le_rows
    UpperMomentN47RemainingIntegrals.actual_third_integral_le_rows
    UpperMomentN47Budget.fourth_integral_le
  norm_num only [UpperMomentN47IntegralChecks.row1_sum,
    UpperMomentN47IntegralChecks.row2_sum, UpperMomentN47IntegralChecks.row3_sum,
    Int.cast_ofNat, delta47] at ht ⊢
  exact ht

theorem exp_neg_cutoff_le : Real.exp (-(111 / 20 : ℝ)) ≤ 1 / 250 := by
  have ht := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 111 / 20) 14
  norm_num [Finset.sum_range_succ] at ht
  have hl : (250 : ℝ) ≤ Real.exp (111 / 20) := by linarith only [ht]
  rw [Real.exp_neg]
  have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 250) hl
  simpa only [one_div] using hi

theorem fourth235_le :
    (1 / Real.pi) * (∫ v in Ioi A, UpperMomentAbsoluteProfile.fourth b v) ≤ 1 / 8250 := by
  have ht := UpperMomentAbsoluteProfile.fourth_integral_le b A b_pos UpperMomentN47Budget.A_pos
  have hcut : (111 : ℝ) / 20 ≤ b * A ^ 2 / 2 := by norm_num [b, A]
  have he : Real.exp (-b * A ^ 2 / 2) ≤ 1 / 250 := by
    simpa only [neg_div, neg_mul] using
      (Real.exp_le_exp.mpr (neg_le_neg hcut)).trans exp_neg_cutoff_le
  have hsp : (11 : ℝ) ≤ b * A ^ 2 := by norm_num [b, A]
  have hp := mul_le_mul_of_nonneg_right Real.pi_gt_three.le
    (mul_nonneg b_pos.le (sq_nonneg A))
  have hd : (33 : ℝ) ≤ Real.pi * b * A ^ 2 := by nlinarith only [hp, hsp]
  have hd0 : 0 < Real.pi * b * A ^ 2 :=
    mul_pos (mul_pos Real.pi_pos b_pos) (sq_pos_of_pos UpperMomentN47Budget.A_pos)
  apply ht.trans
  calc
    _ ≤ (1 / 250 : ℝ) / (Real.pi * b * A ^ 2) := div_le_div_of_nonneg_right he hd0.le
    _ ≤ (1 / 250 : ℝ) / 33 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hd
    _ = 1 / 8250 := by norm_num

theorem absolute235_le :
    UpperMomentAbsoluteProfile.profile U (UpperMomentDamping.G U U) A 4 b ≤ delta235 := by
  have ht := profile_le_of_integrals b _ _ _ _
    UpperMomentNu235FirstIntegral.first_integral_le
    UpperMomentNu235RemainingIntegrals.actual_second_integral_le_rows
    UpperMomentNu235RemainingIntegrals.actual_third_integral_le_rows fourth235_le
  norm_num only [UpperMomentNu235Checks.row1_sum, UpperMomentNu235Checks.row2_sum,
    UpperMomentNu235Checks.row3_sum, Int.cast_ofNat] at ht
  apply ht.trans
  norm_num [delta235]

private theorem scaled_endpoint_le (nu s d root : ℝ)
    (hnu : 0 < nu) (hs : s = nu / U ^ 2) (hd : 0 ≤ d)
    (hprice : UpperMomentAbsoluteProfile.profile U (UpperMomentDamping.G U U) A 4 s ≤ d)
    (hroot : Real.sqrt nu ≤ root) (hbudget : root * d ≤ (253 / 625) * L) :
    (U / L) * UpperMomentSpectrumPrice.spectralProfile U (UpperMomentDamping.G U U) A 4 s ≤ 253 / 625 := by
  have hU := UpperMomentN47Budget.U_pos
  have hL := UpperMomentN47Budget.L_pos
  have hs0 : 0 < s := hs ▸ div_pos hnu (sq_pos_of_pos hU)
  have he : Real.sqrt s = Real.sqrt nu / U := by
    rw [hs, Real.sqrt_div hnu.le, Real.sqrt_sq hU.le]
  rw [UpperMomentAbsoluteProfile.spectral_profile_eq U _ A 4 s hs0, he]
  calc
    _ ≤ (U / L) * (Real.sqrt nu / U * d) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hprice (by positivity)) (by positivity)
    _ = Real.sqrt nu * d / L := by field_simp [hU.ne', hL.ne']
    _ ≤ root * d / L := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hroot hd) hL.le
    _ ≤ 253 / 625 := (div_le_iff₀ hL).mpr hbudget

theorem endpoint47_le :
    (U / L) * UpperMomentSpectrumPrice.spectralProfile U (UpperMomentDamping.G U U) A 4 a ≤ 253 / 625 := by
  apply scaled_endpoint_le 47 a delta47 (48 / 7) (by norm_num)
    (by norm_num [a, U]) (by norm_num [delta47]) absolute47_le UpperMomentN47Budget.sqrt47_le
  norm_num [delta47, L]

theorem endpoint235_le :
    (U / L) * UpperMomentSpectrumPrice.spectralProfile U (UpperMomentDamping.G U U) A 4 b ≤ 253 / 625 := by
  have hr : Real.sqrt (235 / 4 : ℝ) ≤ 23 / 3 :=
    (Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 23 / 3)).mpr (by norm_num)
  apply scaled_endpoint_le (235 / 4) b delta235 (23 / 3) (by norm_num)
    (by norm_num [b, U]) (by norm_num [delta235]) absolute235_le hr
  norm_num [delta235, L]

theorem chord_le : Real.exp ((3 / 2 : ℝ) * ((b - a) ^ 2 / (8 * a ^ 2))) ≤ 256 / 253 := by
  have heq : (3 / 2 : ℝ) * ((b - a) ^ 2 / (8 * a ^ 2)) = 3 / 256 := by norm_num [a, b]
  rw [heq]
  have hl : (253 : ℝ) / 256 ≤ Real.exp (-(3 / 256 : ℝ)) := by
    have ht := Real.one_sub_le_exp_neg (3 / 256 : ℝ)
    linarith only [ht]
  have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 253 / 256) hl
  rw [Real.exp_neg] at hi
  norm_num only [one_div_div, one_div, inv_inv] at hi
  exact hi

theorem ratio_le (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (n : ℕ)
    (hn : 47 ≤ n) (hnhi : n ≤ 58) (hρ : thirdAbsoluteMoment μ ≤ U)
    (hL : L ≤ thirdAbsoluteMoment μ) (x : ℝ) :
    Real.sqrt n * |(normalizedIidSumLaw μ n).real (Iic x) - GaussianTools.Phi x| /
      thirdAbsoluteMoment μ ≤ 256 / 625 := by
  have hU := UpperMomentN47Budget.U_pos
  have hLp := UpperMomentN47Budget.L_pos
  have hn0 : 0 < n := by omega
  have hlow : (47 : ℝ) ≤ n := Nat.cast_le.mpr hn
  have hhigh : (n : ℝ) ≤ 235 / 4 := (Nat.cast_le.mpr hnhi).trans (by norm_num)
  have hs : UpperMomentDamping.sScale U n ∈ Icc a b := by
    constructor
    · have hh := div_le_div_of_nonneg_right hlow (sq_nonneg U)
      convert hh using 1 <;> norm_num [UpperMomentDamping.sScale, U, a]
    · have hh := div_le_div_of_nonneg_right hhigh (sq_nonneg U)
      convert hh using 1 <;> norm_num [UpperMomentDamping.sScale, U, b]
  have ht := UpperMomentSpectrumPrice.normalized_actual_cdf_ratio_le_endpoints μ h U L
    hU hLp hρ hL n hn0 A 4 a b UpperMomentN47Budget.A_pos
    (by norm_num [A]) a_pos a_lt_b hs d_le_a x
  have hmax : (U / L) * max
      (UpperMomentSpectrumPrice.spectralProfile U (UpperMomentDamping.G U U) A 4 a)
      (UpperMomentSpectrumPrice.spectralProfile U (UpperMomentDamping.G U U) A 4 b) ≤ 253 / 625 := by
    rcases le_total
      (UpperMomentSpectrumPrice.spectralProfile U (UpperMomentDamping.G U U) A 4 a)
      (UpperMomentSpectrumPrice.spectralProfile U (UpperMomentDamping.G U U) A 4 b) with hab | hba
    · simpa only [max_eq_right hab] using endpoint235_le
    · simpa only [max_eq_left hba] using endpoint47_le
  apply ht.trans
  calc
    _ = Real.exp ((3 / 2) * ((b - a) ^ 2 / (8 * a ^ 2))) * ((U / L) * max
        (UpperMomentSpectrumPrice.spectralProfile U (UpperMomentDamping.G U U) A 4 a)
        (UpperMomentSpectrumPrice.spectralProfile U (UpperMomentDamping.G U U) A 4 b)) := by ring
    _ ≤ Real.exp ((3 / 2) * ((b - a) ^ 2 / (8 * a ^ 2))) * (253 / 625) :=
      mul_le_mul_of_nonneg_left hmax (Real.exp_nonneg _)
    _ ≤ (256 / 253 : ℝ) * (253 / 625) :=
      mul_le_mul_of_nonneg_right chord_le (by norm_num)
    _ = 256 / 625 := by norm_num

theorem sharp_on_sample_band (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (n : ℕ)
    (hn : 47 ≤ n) (hnhi : n ≤ 58) (hρ : thirdAbsoluteMoment μ ≤ U)
    (hL : L ≤ thirdAbsoluteMoment μ) (x : ℝ) :
    |(normalizedIidSumLaw μ n).real (Iic x) - GaussianTools.Phi x| <
      esseenConstant * thirdAbsoluteMoment μ / Real.sqrt n := by
  have hρ0 := UpperMomentN47Budget.L_pos.trans_le hL
  have hn0 : 0 < n := by omega
  have hr : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn0)
  have ht := (div_le_iff₀ hρ0).mp (ratio_le μ h n hn hnhi hρ hL x)
  have hdelta : |(normalizedIidSumLaw μ n).real (Iic x) - GaussianTools.Phi x| ≤
      (256 / 625) * thirdAbsoluteMoment μ / Real.sqrt n :=
    (le_div_iff₀ hr).mpr (by simpa only [mul_comm] using ht)
  have hCE : (256 : ℝ) / 625 < esseenConstant :=
    lt_trans (by norm_num : (256 : ℝ) / 625 < 4097 / 10000)
      FiniteHighMomentTails.target4097_lt_esseen
  have hh := div_lt_div_of_pos_right (mul_lt_mul_of_pos_right hCE hρ0) hr
  exact hdelta.trans_lt hh

end BerryEsseen.UpperMomentBand47To58

#print axioms BerryEsseen.UpperMomentBand47To58.absolute47_le
#print axioms BerryEsseen.UpperMomentBand47To58.absolute235_le
#print axioms BerryEsseen.UpperMomentBand47To58.endpoint47_le
#print axioms BerryEsseen.UpperMomentBand47To58.endpoint235_le
#print axioms BerryEsseen.UpperMomentBand47To58.ratio_le
#print axioms BerryEsseen.UpperMomentBand47To58.sharp_on_sample_band
