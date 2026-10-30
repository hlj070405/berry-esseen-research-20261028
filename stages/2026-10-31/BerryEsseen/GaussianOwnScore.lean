module

public import BerryEsseen.GaussianRecurrence

@[expose] public section

/-! 2026-10-30: the genuine sharp predecessor removes the INITIAL
literature own-score input for every actual n>=213. This is conditional on
the original all-law predecessor, precisely as in a least-counterexample
argument. The numerical nmax of an INITIAL profile is not an index cutoff.
No finite-index assertion or original support premise is assumed away. -/

noncomputable section

namespace BerryEsseen.GaussianOwnScore

open Extremizer

def initialFloor : ℝ := 27404839 / 66655000

def literatureEnvelope (r : ℝ) : ℝ :=
  min (469 / 1000) (min ((1661 / 5000) * (1 + (429 / 1000) / r))
    ((3031 / 10000) * (1 + (323 / 500) / r)))

theorem esseenConstant_lt_409733 : esseenConstant < (409733 : ℝ) / 1000000 := by
  have hs10 := Real.sq_sqrt (show (0 : ℝ) ≤ 10 by norm_num)
  have h10 : Real.sqrt 10 < (3162278 : ℝ) / 1000000 := by
    nlinarith only [hs10, Real.sqrt_nonneg (10 : ℝ)]
  have hpi := Real.pi_gt_d20
  have hs2 := Real.sq_sqrt (show 0 ≤ 2 * Real.pi by positivity)
  have h2 : (2506628 : ℝ) / 1000000 < Real.sqrt (2 * Real.pi) := by
    nlinarith only [hpi, hs2, Real.sqrt_nonneg (2 * Real.pi)]
  have hden : 0 < 6 * Real.sqrt (2 * Real.pi) := by positivity
  unfold esseenConstant
  apply (div_lt_iff₀ hden).mpr
  nlinarith only [h10, h2]

/-- The smallest U value at any global INITIAL left grid point. -/
theorem initialFloor_le_envelope (r : ℝ) (hr : 0 < r)
    (hrmax : r ≤ (173303 : ℝ) / 96000) : initialFloor ≤ literatureEnvelope r := by
  have hinv : (96000 : ℝ) / 173303 ≤ 1 / r := by
    apply (le_div_iff₀ hr).mpr
    nlinarith only [hrmax]
  have hu := mul_le_mul_of_nonneg_left hinv
    (by norm_num : (0 : ℝ) ≤ (1661 / 5000 : ℝ) * (429 / 1000))
  have hv := mul_le_mul_of_nonneg_left hinv
    (by norm_num : (0 : ℝ) ≤ (3031 / 10000 : ℝ) * (323 / 500))
  unfold initialFloor literatureEnvelope
  apply le_min (by norm_num)
  apply le_min
  · calc
      (27404839 : ℝ) / 66655000 = 1661 / 5000 +
          (1661 / 5000) * (429 / 1000) * (96000 / 173303) := by norm_num
      _ ≤ 1661 / 5000 + (1661 / 5000) * (429 / 1000) * (1 / r) := by linarith only [hu]
      _ = _ := by ring
  · calc
      (27404839 : ℝ) / 66655000 ≤ 3031 / 10000 +
          (3031 / 10000) * (323 / 500) * (96000 / 173303) := by norm_num
      _ ≤ 3031 / 10000 + (3031 / 10000) * (323 / 500) * (1 / r) := by linarith only [hv]
      _ = _ := by ring

/-- In the original induction the all-law predecessor is already sharp.
Its genuine Gaussian recurrence pays every INITIAL own-score cap in the
infinite tail from n=213 onward, with no classical numerical theorem. -/
theorem fixedNSup_lt_initialFloor (n : ℕ) (hn : 213 ≤ n)
    (hprev : fixedNSup (n - 1) ≤ esseenConstant) : fixedNSup n < initialFloor := by
  have hn26 : 26 ≤ n := le_trans (by decide : 26 ≤ 213) hn
  have hnR : (213 : ℝ) ≤ n := by exact_mod_cast hn
  have hnp : (0 : ℝ) < n := by linarith only [hnR]
  have he := (GaussianRecurrence.coarse_entry n hn26 hprev).1
  have hd : fixedNSup n - esseenConstant < ((3 : ℝ) / 10) / (n : ℝ) := by
    apply (lt_div_iff₀ hnp).mpr
    nlinarith only [he]
  have hsmall : ((3 : ℝ) / 10) / (n : ℝ) ≤ (3 / 10 : ℝ) / 213 := by
    apply (div_le_div_iff₀ hnp (by norm_num : (0 : ℝ) < 213)).mpr
    nlinarith only [hnR]
  have htarget : (409733 : ℝ) / 1000000 + (3 / 10 : ℝ) / 213 < initialFloor := by
    norm_num [initialFloor]
  linarith only [hd, hsmall, esseenConstant_lt_409733, htarget]

theorem fixedNSup_lt_envelope (n : ℕ) (hn : 213 ≤ n)
    (hprev : fixedNSup (n - 1) ≤ esseenConstant) (r : ℝ) (hr : 0 < r)
    (hrmax : r ≤ (173303 : ℝ) / 96000) : fixedNSup n < literatureEnvelope r :=
  (fixedNSup_lt_initialFloor n hn hprev).trans_le (initialFloor_le_envelope r hr hrmax)

end BerryEsseen.GaussianOwnScore

#print axioms BerryEsseen.GaussianOwnScore.esseenConstant_lt_409733
#print axioms BerryEsseen.GaussianOwnScore.initialFloor_le_envelope
#print axioms BerryEsseen.GaussianOwnScore.fixedNSup_lt_initialFloor
#print axioms BerryEsseen.GaussianOwnScore.fixedNSup_lt_envelope
