module

public import BerryEsseen.GaussianOwnScore
public import BerryEsseen.GaussianRecurrence

@[expose] public section

/-! 2026-10-30: sharp all-law predecessors mask the explicit INITIAL
own-score envelope outside four finite index ranges. The envelope comparisons
below are algebraic properties of the displayed rational function; no
classical Berry--Esseen estimate is used. Charged caps and support inputs
remain separate premises of the original resource argument. -/

noncomputable section

namespace BerryEsseen.GaussianInitialMask

open Extremizer GaussianOwnScore

/-- The literal left endpoint of the 24-cell global INITIAL moment grid. -/
def initialLeft (i : ℕ) : ℝ := 1 + (3361 / 4000 : ℝ) * i / 24

theorem initialLeft_pos (i : ℕ) : 0 < initialLeft i := by
  have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  unfold initialLeft
  positivity

theorem initialLeft_mono {i j : ℕ} (hij : i ≤ j) : initialLeft i ≤ initialLeft j := by
  have hijR : (i : ℝ) ≤ j := by exact_mod_cast hij
  unfold initialLeft
  linarith only [hijR]

/-- Antitonicity of the explicit function, not a probabilistic upper bound. -/
theorem literatureEnvelope_antitoneOn :
    AntitoneOn literatureEnvelope (Set.Ioi (0 : ℝ)) := by
  intro a ha b hb hab
  have hinv : 1 / b ≤ 1 / a := by
    apply (div_le_div_iff₀ hb ha).mpr
    simpa using hab
  have hu := mul_le_mul_of_nonneg_left hinv
    (by norm_num : (0 : ℝ) ≤ (1661 / 5000 : ℝ) * (429 / 1000))
  have hv := mul_le_mul_of_nonneg_left hinv
    (by norm_num : (0 : ℝ) ≤ (3031 / 10000 : ℝ) * (323 / 500))
  unfold literatureEnvelope
  apply min_le_min le_rfl
  apply min_le_min
  · calc
      (1661 / 5000 : ℝ) * (1 + (429 / 1000) / b) =
          1661 / 5000 + (1661 / 5000) * (429 / 1000) * (1 / b) := by ring
      _ ≤ 1661 / 5000 + (1661 / 5000) * (429 / 1000) * (1 / a) := by
        linarith only [hu]
      _ = _ := by ring
  · calc
      (3031 / 10000 : ℝ) * (1 + (323 / 500) / b) =
          3031 / 10000 + (3031 / 10000) * (323 / 500) * (1 / b) := by ring
      _ ≤ 3031 / 10000 + (3031 / 10000) * (323 / 500) * (1 / a) := by
        linarith only [hv]
      _ = _ := by ring

theorem fixedNSup_lt_gaussian_price (n : ℕ) (hn : 26 ≤ n)
    (hprev : fixedNSup (n - 1) ≤ esseenConstant) :
    fixedNSup n < (409733 : ℝ) / 1000000 + (3 / 10 : ℝ) / n := by
  have hnR : (26 : ℝ) ≤ n := by exact_mod_cast hn
  have hnp : (0 : ℝ) < n := by linarith only [hnR]
  have he := (GaussianRecurrence.coarse_entry n hn hprev).1
  have hd : fixedNSup n - esseenConstant < (3 / 10 : ℝ) / n := by
    apply (lt_div_iff₀ hnp).mpr
    nlinarith only [he]
  linarith only [hd, esseenConstant_lt_409733]

/-- A rational cutoff pays a cap for every larger actual index. -/
theorem fixedNSup_lt_cap_of_cutoff (n K : ℕ) (hn : 26 ≤ n)
    (hprev : fixedNSup (n - 1) ≤ esseenConstant) (hK : 0 < K) (hnK : K ≤ n)
    (cap : ℝ) (hcap : (409733 : ℝ) / 1000000 + (3 / 10 : ℝ) / K ≤ cap) :
    fixedNSup n < cap := by
  have hKR : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  have hnKR : (K : ℝ) ≤ n := by exact_mod_cast hnK
  have hnp : (0 : ℝ) < n := hKR.trans_le hnKR
  have hsmall : (3 / 10 : ℝ) / n ≤ (3 / 10 : ℝ) / K := by
    apply (div_le_div_iff₀ hnp hKR).mpr
    nlinarith only [hnKR]
  have hprice := fixedNSup_lt_gaussian_price n hn hprev
  linarith only [hprice, hsmall, hcap]

/-- Every left grid point through i=19 is paid already at actual n=47. -/
theorem fixedNSup_lt_initialLeft_low (n : ℕ) (hn : 47 ≤ n)
    (hprev : fixedNSup (n - 1) ≤ esseenConstant) (i : ℕ) (hi : i ≤ 19) :
    fixedNSup n < literatureEnvelope (initialLeft i) := by
  have hn26 : 26 ≤ n := le_trans (by decide : 26 ≤ 47) hn
  have hcap := fixedNSup_lt_cap_of_cutoff n 47 hn26 hprev (by decide) hn
    (literatureEnvelope (initialLeft 19)) (by norm_num [literatureEnvelope, initialLeft])
  exact hcap.trans_le (literatureEnvelope_antitoneOn (initialLeft_pos i)
    (initialLeft_pos 19) (initialLeft_mono hi))

theorem fixedNSup_lt_initialLeft20 (n : ℕ) (hn : 48 ≤ n)
    (hprev : fixedNSup (n - 1) ≤ esseenConstant) :
    fixedNSup n < literatureEnvelope (initialLeft 20) := by
  exact fixedNSup_lt_cap_of_cutoff n 48 (le_trans (by decide : 26 ≤ 48) hn)
    hprev (by decide) hn _ (by norm_num [literatureEnvelope, initialLeft])

theorem fixedNSup_lt_initialLeft21 (n : ℕ) (hn : 66 ≤ n)
    (hprev : fixedNSup (n - 1) ≤ esseenConstant) :
    fixedNSup n < literatureEnvelope (initialLeft 21) := by
  exact fixedNSup_lt_cap_of_cutoff n 66 (le_trans (by decide : 26 ≤ 66) hn)
    hprev (by decide) hn _ (by norm_num [literatureEnvelope, initialLeft])

theorem fixedNSup_lt_initialLeft22 (n : ℕ) (hn : 101 ≤ n)
    (hprev : fixedNSup (n - 1) ≤ esseenConstant) :
    fixedNSup n < literatureEnvelope (initialLeft 22) := by
  exact fixedNSup_lt_cap_of_cutoff n 101 (le_trans (by decide : 26 ≤ 101) hn)
    hprev (by decide) hn _ (by norm_num [literatureEnvelope, initialLeft])

theorem fixedNSup_lt_initialLeft23 (n : ℕ) (hn : 213 ≤ n)
    (hprev : fixedNSup (n - 1) ≤ esseenConstant) :
    fixedNSup n < literatureEnvelope (initialLeft 23) := by
  exact fixedNSup_lt_cap_of_cutoff n 213 (le_trans (by decide : 26 ≤ 213) hn)
    hprev (by decide) hn _ (by norm_num [literatureEnvelope, initialLeft])

/-- A reusable low-moment mask for finite actual indices from n=31. -/
theorem fixedNSup_lt_envelope_of_le_eight_fifths (n : ℕ) (hn : 31 ≤ n)
    (hprev : fixedNSup (n - 1) ≤ esseenConstant) (r : ℝ) (hr : 0 < r)
    (hrmax : r ≤ (8 : ℝ) / 5) : fixedNSup n < literatureEnvelope r := by
  have hcap := fixedNSup_lt_cap_of_cutoff n 31 (le_trans (by decide : 26 ≤ 31) hn)
    hprev (by decide) hn (literatureEnvelope ((8 : ℝ) / 5))
    (by norm_num [literatureEnvelope])
  exact hcap.trans_le (literatureEnvelope_antitoneOn hr (by norm_num) hrmax)

end BerryEsseen.GaussianInitialMask

#print axioms BerryEsseen.GaussianInitialMask.literatureEnvelope_antitoneOn
#print axioms BerryEsseen.GaussianInitialMask.fixedNSup_lt_gaussian_price
#print axioms BerryEsseen.GaussianInitialMask.fixedNSup_lt_cap_of_cutoff
#print axioms BerryEsseen.GaussianInitialMask.fixedNSup_lt_initialLeft_low
#print axioms BerryEsseen.GaussianInitialMask.fixedNSup_lt_initialLeft20
#print axioms BerryEsseen.GaussianInitialMask.fixedNSup_lt_initialLeft21
#print axioms BerryEsseen.GaussianInitialMask.fixedNSup_lt_initialLeft22
#print axioms BerryEsseen.GaussianInitialMask.fixedNSup_lt_initialLeft23
#print axioms BerryEsseen.GaussianInitialMask.fixedNSup_lt_envelope_of_le_eight_fifths
