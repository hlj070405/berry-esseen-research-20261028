module

public import BerryEsseen.GaussianInitialMask

@[expose] public section

/-! 2026-10-30: monotonicity of the genuine all-law Gaussian recurrence
gives sharper INITIAL own-score masks from four fixed rational price checks.
The predecessor remains the original all-law supremum at the actual index.
These comparisons do not replace any support, resource, or charged-cap input. -/

noncomputable section

namespace BerryEsseen.GaussianMonotoneMask

open Extremizer GaussianOwnScore GaussianInitialMask GaussianRecurrence

lemma recurrencePrice_eq_ratio (N C : ℝ) (hN : 1 < N) :
    recurrencePrice N C =
      C * Real.sqrt (N / (N - 1)) +
        Real.sqrt (N / (N - 1)) / (15 * (N - 1)) +
        2 * Real.sqrt (N / (N - 1)) /
          (25 * ((N - 1) * Real.sqrt (N - 1))) := by
  have hv : 0 < N - 1 := by linarith
  have hr : 0 < Real.sqrt (N - 1) := Real.sqrt_pos.mpr hv
  have hs := Real.sq_sqrt hv.le
  unfold recurrencePrice
  rw [Real.sqrt_div (by linarith : 0 ≤ N)]
  rw [← hs]
  rw [Real.sqrt_sq hr.le]
  field_simp [hr.ne']

/-- The displayed Gaussian price decreases with the real index above one. -/
theorem recurrencePrice_antitoneOn (C : ℝ) (hC : 0 ≤ C) :
    AntitoneOn (fun N : ℝ => recurrencePrice N C) (Set.Ioi 1) := by
  intro a ha b hb hab
  change 1 < a at ha
  change 1 < b at hb
  change recurrencePrice b C ≤ recurrencePrice a C
  have hav : 0 < a - 1 := by linarith
  have hbv : 0 < b - 1 := by linarith
  have hv : a - 1 ≤ b - 1 := by linarith
  have hratio : b / (b - 1) ≤ a / (a - 1) := by
    apply (div_le_div_iff₀ hbv hav).mpr
    nlinarith only [hab]
  have hr := Real.sqrt_le_sqrt hratio
  have hs := Real.sqrt_le_sqrt hv
  have hden : (a - 1) * Real.sqrt (a - 1) ≤
      (b - 1) * Real.sqrt (b - 1) :=
    mul_le_mul hv hs (Real.sqrt_nonneg _) hbv.le
  rw [recurrencePrice_eq_ratio b C hb, recurrencePrice_eq_ratio a C ha]
  apply add_le_add
  · exact add_le_add (mul_le_mul_of_nonneg_left hr hC)
      (div_le_div₀ (Real.sqrt_nonneg _) hr (by positivity) (by linarith))
  · exact div_le_div₀ (by positivity)
      (mul_le_mul_of_nonneg_left hr (by norm_num)) (by positivity)
      (by linarith only [hden])

lemma recurrencePrice_mono_constant (N C D : ℝ) (hCD : C ≤ D) :
    recurrencePrice N C ≤ recurrencePrice N D := by
  unfold recurrencePrice
  have h := mul_le_mul_of_nonneg_right hCD (Real.sqrt_nonneg (N / (N - 1)))
  linarith only [h]

/-- Rational upper and lower square-root checks suffice at a fixed index. -/
lemma recurrencePrice_le_rational (N C R L : ℝ) (hN : 1 < N) (hC : 0 ≤ C)
    (hR : Real.sqrt (N / (N - 1)) ≤ R) (hL : 0 < L)
    (hLs : L ≤ Real.sqrt (N - 1)) :
    recurrencePrice N C ≤ C * R + R / (15 * (N - 1)) +
      2 * R / (25 * ((N - 1) * L)) := by
  have hv : 0 < N - 1 := by linarith
  have hRp : 0 ≤ R := (Real.sqrt_nonneg _).trans hR
  rw [recurrencePrice_eq_ratio N C hN]
  apply add_le_add
  · exact add_le_add (mul_le_mul_of_nonneg_left hR hC)
      (div_le_div_of_nonneg_right hR (by positivity))
  · exact div_le_div₀ (by positivity)
      (mul_le_mul_of_nonneg_left hR (by norm_num)) (by positivity)
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hLs hv.le)
        (by norm_num))

lemma price47 : recurrencePrice 47 esseenConstant <
    literatureEnvelope (initialLeft 20) := by
  have hR : Real.sqrt ((47 : ℝ) / (47 - 1)) ≤ 10108112 / 10000000 := by
    apply Real.sqrt_le_iff.mpr
    norm_num
  have hL : (67823299 : ℝ) / 10000000 ≤ Real.sqrt (47 - 1) := by
    apply (Real.le_sqrt (by norm_num) (by norm_num)).mpr
    norm_num
  have h := recurrencePrice_le_rational 47 (409733 / 1000000)
    (10108112 / 10000000) (67823299 / 10000000)
    (by norm_num) (by norm_num) hR (by norm_num) hL
  have hC := recurrencePrice_mono_constant 47 esseenConstant
    (409733 / 1000000) esseenConstant_lt_409733.le
  have hcap : (409733 / 1000000 : ℝ) * (10108112 / 10000000) +
      (10108112 / 10000000) / (15 * (47 - 1)) +
      2 * (10108112 / 10000000) / (25 * ((47 - 1) * (67823299 / 10000000))) <
      literatureEnvelope (initialLeft 20) := by
    norm_num [literatureEnvelope, initialLeft]
  exact hC.trans_lt (h.trans_lt hcap)

lemma price63 : recurrencePrice 63 esseenConstant <
    literatureEnvelope (initialLeft 21) := by
  have hR : Real.sqrt ((63 : ℝ) / (63 - 1)) ≤ 10080323 / 10000000 := by
    apply Real.sqrt_le_iff.mpr
    norm_num
  have hL : (78740078 : ℝ) / 10000000 ≤ Real.sqrt (63 - 1) := by
    apply (Real.le_sqrt (by norm_num) (by norm_num)).mpr
    norm_num
  have h := recurrencePrice_le_rational 63 (409733 / 1000000)
    (10080323 / 10000000) (78740078 / 10000000)
    (by norm_num) (by norm_num) hR (by norm_num) hL
  have hC := recurrencePrice_mono_constant 63 esseenConstant
    (409733 / 1000000) esseenConstant_lt_409733.le
  have hcap : (409733 / 1000000 : ℝ) * (10080323 / 10000000) +
      (10080323 / 10000000) / (15 * (63 - 1)) +
      2 * (10080323 / 10000000) / (25 * ((63 - 1) * (78740078 / 10000000))) <
      literatureEnvelope (initialLeft 21) := by
    norm_num [literatureEnvelope, initialLeft]
  exact hC.trans_lt (h.trans_lt hcap)

lemma price96 : recurrencePrice 96 esseenConstant <
    literatureEnvelope (initialLeft 22) := by
  have hR : Real.sqrt ((96 : ℝ) / (96 - 1)) ≤ 10052494 / 10000000 := by
    apply Real.sqrt_le_iff.mpr
    norm_num
  have hL : (97467943 : ℝ) / 10000000 ≤ Real.sqrt (96 - 1) := by
    apply (Real.le_sqrt (by norm_num) (by norm_num)).mpr
    norm_num
  have h := recurrencePrice_le_rational 96 (409733 / 1000000)
    (10052494 / 10000000) (97467943 / 10000000)
    (by norm_num) (by norm_num) hR (by norm_num) hL
  have hC := recurrencePrice_mono_constant 96 esseenConstant
    (409733 / 1000000) esseenConstant_lt_409733.le
  have hcap : (409733 / 1000000 : ℝ) * (10052494 / 10000000) +
      (10052494 / 10000000) / (15 * (96 - 1)) +
      2 * (10052494 / 10000000) / (25 * ((96 - 1) * (97467943 / 10000000))) <
      literatureEnvelope (initialLeft 22) := by
    norm_num [literatureEnvelope, initialLeft]
  exact hC.trans_lt (h.trans_lt hcap)

lemma price198 : recurrencePrice 198 esseenConstant <
    literatureEnvelope (initialLeft 23) := by
  have hR : Real.sqrt ((198 : ℝ) / (198 - 1)) ≤ 10025349 / 10000000 := by
    apply Real.sqrt_le_iff.mpr
    norm_num
  have hL : (140356688 : ℝ) / 10000000 ≤ Real.sqrt (198 - 1) := by
    apply (Real.le_sqrt (by norm_num) (by norm_num)).mpr
    norm_num
  have h := recurrencePrice_le_rational 198 (409733 / 1000000)
    (10025349 / 10000000) (140356688 / 10000000)
    (by norm_num) (by norm_num) hR (by norm_num) hL
  have hC := recurrencePrice_mono_constant 198 esseenConstant
    (409733 / 1000000) esseenConstant_lt_409733.le
  have hcap : (409733 / 1000000 : ℝ) * (10025349 / 10000000) +
      (10025349 / 10000000) / (15 * (198 - 1)) +
      2 * (10025349 / 10000000) / (25 * ((198 - 1) * (140356688 / 10000000))) <
      literatureEnvelope (initialLeft 23) := by
    norm_num [literatureEnvelope, initialLeft]
  exact hC.trans_lt (h.trans_lt hcap)

/-- Monotone pricing applies to every actual index above the checked cutoff. -/
theorem fixedNSup_lt_cap_of_cutoff (n K : ℕ) (hK : 2 ≤ K) (hnK : K ≤ n)
    (hprev : fixedNSup (n - 1) ≤ esseenConstant) (cap : ℝ)
    (hcap : recurrencePrice (K : ℝ) esseenConstant < cap) : fixedNSup n < cap := by
  have hn2 : 2 ≤ n := hK.trans hnK
  have hKR : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hnKR : (K : ℝ) ≤ n := by exact_mod_cast hnK
  have hCE : 0 ≤ esseenConstant := by
    linarith only [AnalyticConstants.esseenConstant_gt_819_2000]
  have hrec : fixedNSup n ≤ recurrencePrice (n : ℝ) (fixedNSup (n - 1)) :=
    GaussianRecurrence.fixedNSup_recurrence n hn2
  have hmono := recurrencePrice_antitoneOn esseenConstant hCE
    (show 1 < (K : ℝ) by linarith) (show 1 < (n : ℝ) by linarith) hnKR
  exact (hrec.trans (recurrencePrice_mono_constant (n : ℝ) _ _ hprev)).trans_lt
    (hmono.trans_lt hcap)

theorem fixedNSup_lt_initialLeft20 (n : ℕ) (hn : 47 ≤ n)
    (hprev : fixedNSup (n - 1) ≤ esseenConstant) :
    fixedNSup n < literatureEnvelope (initialLeft 20) :=
  fixedNSup_lt_cap_of_cutoff n 47 (by decide) hn hprev _ price47

theorem fixedNSup_lt_initialLeft21 (n : ℕ) (hn : 63 ≤ n)
    (hprev : fixedNSup (n - 1) ≤ esseenConstant) :
    fixedNSup n < literatureEnvelope (initialLeft 21) :=
  fixedNSup_lt_cap_of_cutoff n 63 (by decide) hn hprev _ price63

theorem fixedNSup_lt_initialLeft22 (n : ℕ) (hn : 96 ≤ n)
    (hprev : fixedNSup (n - 1) ≤ esseenConstant) :
    fixedNSup n < literatureEnvelope (initialLeft 22) :=
  fixedNSup_lt_cap_of_cutoff n 96 (by decide) hn hprev _ price96

theorem fixedNSup_lt_initialLeft23 (n : ℕ) (hn : 198 ≤ n)
    (hprev : fixedNSup (n - 1) ≤ esseenConstant) :
    fixedNSup n < literatureEnvelope (initialLeft 23) :=
  fixedNSup_lt_cap_of_cutoff n 198 (by decide) hn hprev _ price198

end BerryEsseen.GaussianMonotoneMask

#print axioms BerryEsseen.GaussianMonotoneMask.recurrencePrice_antitoneOn
#print axioms BerryEsseen.GaussianMonotoneMask.price47
#print axioms BerryEsseen.GaussianMonotoneMask.price63
#print axioms BerryEsseen.GaussianMonotoneMask.price96
#print axioms BerryEsseen.GaussianMonotoneMask.price198
#print axioms BerryEsseen.GaussianMonotoneMask.fixedNSup_lt_cap_of_cutoff
#print axioms BerryEsseen.GaussianMonotoneMask.fixedNSup_lt_initialLeft20
#print axioms BerryEsseen.GaussianMonotoneMask.fixedNSup_lt_initialLeft21
#print axioms BerryEsseen.GaussianMonotoneMask.fixedNSup_lt_initialLeft22
#print axioms BerryEsseen.GaussianMonotoneMask.fixedNSup_lt_initialLeft23
