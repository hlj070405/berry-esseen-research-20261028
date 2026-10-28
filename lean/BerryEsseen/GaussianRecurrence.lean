module

public import BerryEsseen.Extremizer
public import BerryEsseen.GaussianEntry
public import BerryEsseen.AnalyticConstants
public import BerryEsseen.TwoMomentProduct

@[expose] public section

/-!
The Gaussian entry for the actual all-law fixed-index suprema, followed
by the original coarse entry constants. Neither extremizer attainment
nor a third-moment or support restriction is a premise of the recurrence.
-/

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace BerryEsseen.GaussianRecurrence

open Extremizer

/-- A standardized witness only establishes nonemptiness of the original
supremum domain; it does not restrict the laws in that domain. -/
def witnessLaw : ProbabilityMeasure ℝ :=
  ⟨TwoMoment.referenceLaw 1 1,
    TwoMoment.referenceLaw_isProbabilityMeasure 1 1 (by norm_num) (by norm_num)⟩

lemma witnessLaw_standardized : StandardizedLaw witnessLaw := by
  refine ⟨TwoMoment.integrable_referenceLaw 1 1 _,
    TwoMoment.integrable_referenceLaw 1 1 _,
    TwoMoment.integrable_referenceLaw 1 1 _, ?_, ?_⟩
  · exact TwoMoment.integral_referenceLaw_id 1 1 (by norm_num) (by norm_num)
  · exact TwoMoment.integral_referenceLaw_sq 1 1 (by norm_num) (by norm_num)

lemma scoreSet_nonempty (n : ℕ) : (scoreSet n).Nonempty :=
  ⟨positiveClosedScore witnessLaw n 0, witnessLaw, witnessLaw_standardized, 0, rfl⟩

def recurrencePrice (n Cprev : ℝ) : ℝ :=
  Cprev * Real.sqrt (n / (n - 1)) +
    Real.sqrt n / (15 * ((n - 1) * Real.sqrt (n - 1))) +
    2 * Real.sqrt n / (25 * (n - 1) ^ 2)

lemma iidSumProbability_succ (μ : ProbabilityMeasure ℝ) (m : ℕ) :
    (iidSumProbability μ (m + 1) : Measure ℝ) =
      (μ : Measure ℝ) ∗ (iidSumProbability μ m : Measure ℝ) := by
  simp only [coe_iidSumProbability, MixtureSum.iidSumLaw_eq_convPower, MixtureSum.convPower]

/-- The original all-law supremum supplies the predecessor comparison
for this same marginal, at every closed real threshold. -/
lemma predecessor_cdf_upper (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (m : ℕ) (hm : 0 < m) (H : ℝ) :
    (iidSumProbability μ m : Measure ℝ).real (Iic H) ≤
      GaussianTools.Phi (H / Real.sqrt m) + fixedNSup m * thirdAbsoluteMoment μ / Real.sqrt m := by
  have hs : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hm)
  have hg := global_upper_fixedNSup m hm μ hμ (H / Real.sqrt m)
  rw [normalized_closedCDF μ m hm (H / Real.sqrt m)] at hg
  have hcancel : Real.sqrt (m : ℝ) * (H / Real.sqrt m) = H := mul_div_cancel₀ H hs.ne'
  rw [hcancel] at hg
  linarith

theorem score_le_recurrencePrice (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (n : ℕ) (hn : 2 ≤ n) (H : ℝ) :
    positiveClosedScore μ n H ≤ recurrencePrice (n : ℝ) (fixedNSup (n - 1)) := by
  have hn1 : 1 ≤ n := le_trans (by decide : 1 ≤ 2) hn
  have hm : 0 < n - 1 := Nat.sub_pos_of_lt (lt_of_lt_of_le (by decide : 1 < 2) hn)
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) := by linarith
  have hv : 0 < (n : ℝ) - 1 := by linarith
  have hq : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
  have hr : 0 < Real.sqrt ((n : ℝ) - 1) := Real.sqrt_pos.mpr hv
  have hρ := thirdAbsoluteMoment_pos μ hμ
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub hn1, Nat.cast_one]
  have hprev : ∀ y : ℝ, (iidSumProbability μ (n - 1) : Measure ℝ).real (Iic y) ≤
      GaussianTools.Phi (y / Real.sqrt ((n : ℝ) - 1)) +
        fixedNSup (n - 1) * thirdAbsoluteMoment μ / Real.sqrt ((n : ℝ) - 1) := by
    intro y
    simpa only [hcast] using predecessor_cdf_upper μ hμ (n - 1) hm y
  have he := GaussianEntry.gaussian_entry μ (iidSumProbability μ (n - 1)) hμ
    (n : ℝ) H (fixedNSup (n - 1)) hnR hprev
  have hrec := iidSumProbability_succ μ (n - 1)
  rw [Nat.sub_add_cancel hn1] at hrec
  rw [← hrec] at he
  calc
    positiveClosedScore μ n H = (Real.sqrt n / thirdAbsoluteMoment μ) *
        ((iidSumProbability μ n : Measure ℝ).real (Iic H) - GaussianTools.Phi (H / Real.sqrt n)) := by
      unfold positiveClosedScore
      ring
    _ ≤ (Real.sqrt n / thirdAbsoluteMoment μ) *
        (fixedNSup (n - 1) * thirdAbsoluteMoment μ / Real.sqrt ((n : ℝ) - 1) +
          thirdAbsoluteMoment μ / (15 * (((n : ℝ) - 1) * Real.sqrt ((n : ℝ) - 1))) +
          2 * thirdAbsoluteMoment μ / (25 * ((n : ℝ) - 1) ^ 2)) :=
      mul_le_mul_of_nonneg_left he (div_nonneg hq.le hρ.le)
    _ = recurrencePrice (n : ℝ) (fixedNSup (n - 1)) := by
      unfold recurrencePrice
      rw [Real.sqrt_div hnpos.le]
      field_simp [hρ.ne', hr.ne', hv.ne']

/-- The recurrence holds for every natural index `n ≥ 2` and for the
supremum over all standardized laws, without an attainment hypothesis. -/
theorem fixedNSup_recurrence (n : ℕ) (hn : 2 ≤ n) :
    fixedNSup n ≤ fixedNSup (n - 1) * Real.sqrt ((n : ℝ) / ((n : ℝ) - 1)) +
      Real.sqrt n / (15 * (((n : ℝ) - 1) * Real.sqrt ((n : ℝ) - 1))) +
      2 * Real.sqrt n / (25 * ((n : ℝ) - 1) ^ 2) := by
  apply csSup_le (scoreSet_nonempty n)
  rintro c ⟨μ, hμ, H, rfl⟩
  exact score_le_recurrencePrice μ hμ n hn H

lemma esseenConstant_lt_41_100 : esseenConstant < (41 : ℝ) / 100 := by
  have hs10 := Real.sq_sqrt (show (0 : ℝ) ≤ 10 by norm_num)
  have h10 : Real.sqrt 10 < (3163 : ℝ) / 1000 := by
    nlinarith [Real.sqrt_nonneg (10 : ℝ)]
  have hp := Real.pi_gt_d4
  have hs2 := Real.sq_sqrt (show 0 ≤ 2 * Real.pi by positivity)
  have h2 : (2506 : ℝ) / 1000 < Real.sqrt (2 * Real.pi) := by
    nlinarith [Real.sqrt_nonneg (2 * Real.pi)]
  have hden : 0 < 6 * Real.sqrt (2 * Real.pi) := by positivity
  unfold esseenConstant
  apply (div_lt_iff₀ hden).mpr
  nlinarith

/-- Exact rational coarse pricing of the real recurrence envelope. -/
theorem coarse_real_price (N : ℝ) (hN : 26 ≤ N) :
    N * (recurrencePrice N esseenConstant - esseenConstant) < (3 : ℝ) / 10 ∧
      recurrencePrice N esseenConstant < (211 : ℝ) / 500 := by
  let v := N - 1
  let q := Real.sqrt N
  let r := Real.sqrt v
  let s := Real.sqrt (N / v)
  have hNpos : 0 < N := by linarith
  have hv : 0 < v := by dsimp [v]; linarith
  have hr : 0 < r := Real.sqrt_pos.mpr hv
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hrsq : r ^ 2 = v := Real.sq_sqrt hv.le
  have hssq : s ^ 2 = N / v := Real.sq_sqrt (div_nonneg hNpos.le hv.le)
  have hratio : N / v ≤ (26 : ℝ) / 25 := by
    apply (div_le_iff₀ hv).mpr
    dsimp [v]
    nlinarith
  have hs2 : s ^ 2 ≤ (26 : ℝ) / 25 := by rw [hssq]; exact hratio
  have hs1 : s ≤ (51 : ℝ) / 50 := by nlinarith
  have hs3 : s ^ 3 ≤ ((26 : ℝ) / 25) * (51 / 50) := by
    have hm := mul_le_mul hs2 hs1 hs (by norm_num : (0 : ℝ) ≤ 26 / 25)
    simpa only [pow_succ] using hm
  have hr5 : 5 ≤ r := by dsimp [v] at hrsq; nlinarith [Real.sqrt_nonneg v]
  have hcoef : (1 : ℝ) / 15 + 2 / (25 * r) ≤ 1 / 15 + 2 / 125 := by
    have hd : (2 : ℝ) / (25 * r) ≤ 2 / 125 := by
      apply (div_le_div_iff₀ (by positivity : 0 < 25 * r) (by norm_num : (0 : ℝ) < 125)).mpr
      nlinarith
    linarith
  have he := AnalyticConstants.scaleExcess_lt_two_125 N (by linarith)
  have hscale : N * (s - 1) < (129 : ℝ) / 250 := by
    change N * (s - 1) - 1 / 2 < 2 / 125 at he
    linarith
  have hCEpos : 0 < esseenConstant := by linarith [AnalyticConstants.esseenConstant_gt_819_2000]
  have hterm1 : esseenConstant * (N * (s - 1)) <
      ((41 : ℝ) / 100) * (129 / 250) := by
    have ha := mul_lt_mul_of_pos_left hscale hCEpos
    have hb := mul_le_mul_of_nonneg_right esseenConstant_lt_41_100.le
      (by norm_num : (0 : ℝ) ≤ 129 / 250)
    linarith
  have hterm2 : s ^ 3 * ((1 : ℝ) / 15 + 2 / (25 * r)) ≤
      (((26 : ℝ) / 25) * (51 / 50)) * (1 / 15 + 2 / 125) :=
    mul_le_mul hs3 hcoef (by positivity) (by norm_num)
  have hqsr : q = s * r := by
    dsimp [q, s]
    rw [Real.sqrt_div hNpos.le]
    dsimp [r]
    exact (div_mul_cancel₀ _ (Real.sqrt_pos.mpr hv).ne').symm
  have hNsv : N = s ^ 2 * v := by rw [hssq]; exact (div_mul_cancel₀ N hv.ne').symm
  have hcost : N * (q / (15 * (v * r)) + 2 * q / (25 * v ^ 2)) =
      s ^ 3 * ((1 : ℝ) / 15 + 2 / (25 * r)) := by
    rw [hqsr, hNsv, ← hrsq]
    field_simp [hr.ne']
  have hidentity : N * (recurrencePrice N esseenConstant - esseenConstant) =
      esseenConstant * (N * (s - 1)) + s ^ 3 * ((1 : ℝ) / 15 + 2 / (25 * r)) := by
    change N * ((esseenConstant * s + q / (15 * (v * r)) + 2 * q / (25 * v ^ 2)) - esseenConstant) = _
    calc
      _ = esseenConstant * (N * (s - 1)) + N * (q / (15 * (v * r)) + 2 * q / (25 * v ^ 2)) := by ring
      _ = _ := by rw [hcost]
  have hexcess : N * (recurrencePrice N esseenConstant - esseenConstant) < (3 : ℝ) / 10 := by
    rw [hidentity]
    nlinarith [hterm1, hterm2]
  refine ⟨hexcess, ?_⟩
  have hd : recurrencePrice N esseenConstant - esseenConstant < ((3 : ℝ) / 10) / N :=
    (lt_div_iff₀ hNpos).mpr (by nlinarith)
  have hsmall : ((3 : ℝ) / 10) / N ≤ 3 / 260 := by
    apply (div_le_iff₀ hNpos).mpr
    nlinarith
  linarith [esseenConstant_lt_41_100]

/-- The original coarse entry, now applied to the real all-law supremum
recurrence for every natural `n ≥ 26`. -/
theorem coarse_entry (n : ℕ) (hn : 26 ≤ n) (hprev : fixedNSup (n - 1) ≤ esseenConstant) :
    (n : ℝ) * (fixedNSup n - esseenConstant) < (3 : ℝ) / 10 ∧
      fixedNSup n < (211 : ℝ) / 500 := by
  have hn2 : 2 ≤ n := le_trans (by decide : 2 ≤ 26) hn
  have hnR : (26 : ℝ) ≤ n := by exact_mod_cast hn
  have hrec := fixedNSup_recurrence n hn2
  have hm := mul_le_mul_of_nonneg_right hprev (Real.sqrt_nonneg ((n : ℝ) / ((n : ℝ) - 1)))
  have hprice : fixedNSup n ≤ recurrencePrice (n : ℝ) esseenConstant := by
    unfold recurrencePrice
    linarith
  obtain ⟨he, hb⟩ := coarse_real_price (n : ℝ) hnR
  refine ⟨?_, lt_of_le_of_lt hprice hb⟩
  have hp := mul_le_mul_of_nonneg_left (sub_le_sub_right hprice esseenConstant) (Nat.cast_nonneg n)
  exact lt_of_le_of_lt hp he

end BerryEsseen.GaussianRecurrence

#print axioms BerryEsseen.GaussianRecurrence.fixedNSup_recurrence
#print axioms BerryEsseen.GaussianRecurrence.esseenConstant_lt_41_100
#print axioms BerryEsseen.GaussianRecurrence.coarse_real_price
#print axioms BerryEsseen.GaussianRecurrence.coarse_entry
