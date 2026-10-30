module

public import BerryEsseen.UpperMomentAbsoluteProfile
public import BerryEsseen.FiniteHighMomentTails

@[expose] public section

/-! 2026-10-30: short rational budgets for the fixed n47 spectral point.
The real infinite tail is paid by exp(-111/25)<=3/250 and pi>3. Decimal
row sums still require the separate integral-row proofs; the final clients
explicitly retain the profile premise until that assembly is completed. -/

noncomputable section

open MeasureTheory Set

namespace BerryEsseen.UpperMomentN47Budget

def U : ℝ := 7361 / 4000
def L : ℝ := 173303 / 96000
def A : ℝ := 4 / 5
def V : ℝ := 4
def s : ℝ := 752000000 / 54184321

lemma U_pos : 0 < U := by norm_num [U]
lemma L_pos : 0 < L := by norm_num [L]
lemma A_pos : 0 < A := by norm_num [A]
lemma s_pos : 0 < s := by norm_num [s]
lemma A_le_V : A ≤ V := by norm_num [A, V]
lemma scale_eq : UpperMomentDamping.sScale U 47 = s := by
  norm_num [UpperMomentDamping.sScale, U, s]

theorem exp_neg_cutoff_le : Real.exp (-(111 / 25 : ℝ)) ≤ 3 / 250 := by
  have ht := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 111 / 25) 12
  norm_num [Finset.sum_range_succ] at ht
  have hl : (250 : ℝ) / 3 ≤ Real.exp (111 / 25) := by linarith only [ht]
  rw [Real.exp_neg]
  have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 250 / 3) hl
  norm_num only [one_div_div, one_div] at hi
  exact hi

theorem fourth_integral_le :
    (1 / Real.pi) * (∫ v in Ioi A, UpperMomentAbsoluteProfile.fourth s v) ≤
      (1 / 2200 : ℝ) := by
  have ht := UpperMomentAbsoluteProfile.fourth_integral_le s A s_pos A_pos
  have hcut : (111 : ℝ) / 25 ≤ s * A ^ 2 / 2 := by norm_num [s, A]
  have he : Real.exp (-s * A ^ 2 / 2) ≤ 3 / 250 := by
    simpa only [neg_div, neg_mul] using
      (Real.exp_le_exp.mpr (neg_le_neg hcut)).trans exp_neg_cutoff_le
  have hsp : (44 : ℝ) / 5 ≤ s * A ^ 2 := by norm_num [s, A]
  have hp := mul_le_mul_of_nonneg_right Real.pi_gt_three.le
    (mul_nonneg s_pos.le (sq_nonneg A))
  have hd : (132 : ℝ) / 5 ≤ Real.pi * s * A ^ 2 := by nlinarith only [hp, hsp]
  have hd0 : 0 < Real.pi * s * A ^ 2 :=
    mul_pos (mul_pos Real.pi_pos s_pos) (sq_pos_of_pos A_pos)
  apply ht.trans
  calc
    _ ≤ (3 / 250 : ℝ) / (Real.pi * s * A ^ 2) := div_le_div_of_nonneg_right he hd0.le
    _ ≤ (3 / 250 : ℝ) / (132 / 5) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hd
    _ = 1 / 2200 := by norm_num

theorem three_row_budget :
    (1 / 2 : ℝ) * (41180332269245895 / 10^18 + 11559820377982515 / 10^18 +
      159389667399613223 / 10^18) + 1 / 2200 < 533 / 5000 := by norm_num

theorem profile_lt_of_rows
    (h1 : (∫ v in Ioc 0 A, UpperMomentAbsoluteProfile.first U
      (UpperMomentDamping.G U U) V s v) ≤ (41180332269245895 : ℝ) / 10^18)
    (h2 : (∫ v in Ioc A V, UpperMomentAbsoluteProfile.second
      (UpperMomentDamping.G U U) V s v) ≤ (11559820377982515 : ℝ) / 10^18)
    (h3 : (∫ v in Ioc 0 A, UpperMomentAbsoluteProfile.third V s v) ≤
      (159389667399613223 : ℝ) / 10^18) :
    UpperMomentAbsoluteProfile.profile U (UpperMomentDamping.G U U) A V s < 533 / 5000 := by
  have h4 := fourth_integral_le
  have hb := three_row_budget
  dsimp only [V] at h1 h2 h3
  unfold UpperMomentAbsoluteProfile.profile
  norm_num only [V, show (2 : ℝ) / 4 = 1 / 2 by norm_num]
  linarith only [h1, h2, h3, h4, hb]

theorem sqrt47_le : Real.sqrt (47 : ℝ) ≤ 48 / 7 := by
  apply (Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 48 / 7)).mpr
  norm_num

theorem normalized_budget : Real.sqrt (47 : ℝ) * (533 / 5000) < (81 / 200) * L := by
  apply (mul_le_mul_of_nonneg_right sqrt47_le (by norm_num : (0 : ℝ) ≤ 533 / 5000)).trans_lt
  norm_num [L]

/-- This client still requires the actual profile bound. No scalar table
or row array is silently promoted to a CDF theorem by this budget module. -/
theorem actual_cdf_lt_of_profile (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hρ : thirdAbsoluteMoment μ ≤ U)
    (hprofile : UpperMomentAbsoluteProfile.profile U (UpperMomentDamping.G U U) A V s < 533 / 5000)
    (x : ℝ) :
    |(normalizedIidSumLaw μ 47).real (Iic x) - GaussianTools.Phi x| < 533 / 5000 := by
  have hh := UpperMomentAbsoluteProfile.actual_cdf_le μ h U U_pos hρ 47 (by decide)
    A V A_pos A_le_V x
  rw [scale_eq] at hh
  exact hh.trans_lt hprofile

theorem actual_cdf_lt_405_of_profile (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hρ : thirdAbsoluteMoment μ ≤ U) (hL : L ≤ thirdAbsoluteMoment μ)
    (hprofile : UpperMomentAbsoluteProfile.profile U (UpperMomentDamping.G U U) A V s < 533 / 5000)
    (x : ℝ) :
    |(normalizedIidSumLaw μ 47).real (Iic x) - GaussianTools.Phi x| <
      (81 / 200) * thirdAbsoluteMoment μ / Real.sqrt 47 := by
  have hr : 0 < Real.sqrt (47 : ℝ) := by positivity
  have hh := mul_lt_mul_of_pos_left (actual_cdf_lt_of_profile μ h hρ hprofile x) hr
  have hb := normalized_budget
  have hl := mul_le_mul_of_nonneg_left hL (by norm_num : (0 : ℝ) ≤ 81 / 200)
  apply (lt_div_iff₀ hr).mpr
  simpa only [mul_comm] using hh.trans (hb.trans_le hl)

theorem sharp_of_profile (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hρ : thirdAbsoluteMoment μ ≤ U) (hL : L ≤ thirdAbsoluteMoment μ)
    (hprofile : UpperMomentAbsoluteProfile.profile U (UpperMomentDamping.G U U) A V s < 533 / 5000)
    (x : ℝ) :
    |(normalizedIidSumLaw μ 47).real (Iic x) - GaussianTools.Phi x| <
      esseenConstant * thirdAbsoluteMoment μ / Real.sqrt 47 := by
  have htarget : (81 : ℝ) / 200 < esseenConstant :=
    lt_trans (by norm_num : (81 : ℝ) / 200 < 4097 / 10000)
      FiniteHighMomentTails.target4097_lt_esseen
  have hρ0 := L_pos.trans_le hL
  have hp := div_pos hρ0 (by positivity : (0 : ℝ) < Real.sqrt 47)
  have hb := mul_lt_mul_of_pos_right htarget hp
  have he : ∀ c : ℝ, c * (thirdAbsoluteMoment μ / Real.sqrt 47) =
      c * thirdAbsoluteMoment μ / Real.sqrt 47 := by intro c; ring
  simp_rw [he] at hb
  exact (actual_cdf_lt_405_of_profile μ h hρ hL hprofile x).trans hb

end BerryEsseen.UpperMomentN47Budget

#print axioms BerryEsseen.UpperMomentN47Budget.fourth_integral_le
#print axioms BerryEsseen.UpperMomentN47Budget.profile_lt_of_rows
#print axioms BerryEsseen.UpperMomentN47Budget.sharp_of_profile
