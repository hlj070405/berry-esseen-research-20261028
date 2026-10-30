module

public import BerryEsseen.HighFrequencyFloor
public import BerryEsseen.HighFrequencyDamping
public import BerryEsseen.HighFrequencyDistance
public import BerryEsseen.HighFrequencyComparator

@[expose] public section

/-! 2026-10-29: the complete six-term physical high-frequency price.
The two Boolean alternatives are fixed at the numerical floor N. All
eligibility is checked there and is inherited along the same fixed candidate;
N is not a probability-law maximizing index. -/

noncomputable section
open Set
open scoped Topology BigOperators

namespace BerryEsseen.HighFrequencyPrice

open HighFrequencyDamping HighFrequencyDistance HighFrequencyZeroCell
open HighFrequencyCells HighFrequencySeries HighFrequencyFloor RationalGaussianTail

def initialBasic (n : ℕ) (M : ℝ) : ℝ :=
  2 * Real.sqrt n * Real.exp (-(n : ℝ) * dampingRate M)

def initialImproved (n : ℕ) (M : ℝ) : ℝ :=
  2 * Real.sqrt n * Real.exp (-(n : ℝ) * chordBase M) * Lambda ((n : ℝ) * chordSlope M / 4)

def tailBasic (n : ℕ) (a d m w : ℝ) : ℝ :=
  m * nonzeroSlope n a w + Zbasic n a d cutoff + wingPrice n a cutoff

def tailImproved (n : ℕ) (a d m w : ℝ) : ℝ :=
  m * nonzeroSlope n a w + Zimproved n a d cutoff + wingPrice n a cutoff

def comparatorPrice (n : ℕ) (M : ℝ) : ℝ :=
  Real.sqrt n * Real.exp (-(n : ℝ) / 8) *
    (2 * Lambda ((n : ℝ) / 8) + Real.sqrt (M - 1) / 3)

def selectedInitial (improveA : Bool) (n : ℕ) (M : ℝ) : ℝ :=
  if improveA then min (initialBasic n M) (initialImproved n M) else initialBasic n M

def selectedTail (improveZ : Bool) (n : ℕ) (a d m w : ℝ) : ℝ :=
  if improveZ then min (tailBasic n a d m w) (tailImproved n a d m w) else tailBasic n a d m w

def selectedZero (improveZ : Bool) (n : ℕ) (a d : ℝ) : ℝ :=
  if improveZ then min (Zbasic n a d cutoff) (Zimproved n a d cutoff) else Zbasic n a d cutoff

def candidate (improveA improveZ : Bool) (n : ℕ) (M a d m w : ℝ) : ℝ :=
  selectedInitial improveA n M + selectedTail improveZ n a d m w + comparatorPrice n M

/-- The manuscript's four strict basic gates, evaluated only at N. -/
structure BasicGates (N : ℕ) (M a w : ℝ) : Prop where
  initial : 1 < 2 * (N : ℝ) * dampingRate M
  periodicWing : 1 < 2 * (N : ℝ) * a * sineSlope w ^ 2 * w ^ 2
  zeroWing : 1 < 2 * (N : ℝ) * a * (23 / 48 : ℝ) ^ 2
  comparator : 1 < 2 * (N : ℝ) / 8

/-- An enabled minimum needs both original alternatives eligible at the same N. -/
def ImprovementGates (improveA improveZ : Bool) (N : ℕ) (M a d : ℝ) : Prop :=
  (improveA = true → 0 < chordSlope M ∧ 1 < 2 * (N : ℝ) * chordBase M) ∧
  (improveZ = true → 1 / 4 ≤ (N : ℝ) * kappa a d * cutoff ^ 2)

lemma cutoff_pos : 0 < cutoff := by norm_num [cutoff]

lemma S3_original_index :
    S3 = (∑ k ∈ Finset.range 20, 1 / ((k : ℝ) + 1) ^ 3) + 1 / 800 := by
  simp only [S3, seriesTerm, powerKernel, sub_zero]

lemma S5_original_index (w : ℝ) :
    S5 w = (∑ k ∈ Finset.range 20, 1 / ((k : ℝ) + 1 - w) ^ 5) +
      1 / (4 * (20 - w) ^ 4) := rfl

lemma selectedTail_eq (improveZ : Bool) (n : ℕ) (a d m w : ℝ) :
    selectedTail improveZ n a d m w =
      m * nonzeroSlope n a w + selectedZero improveZ n a d + wingPrice n a cutoff := by
  cases improveZ
  · rfl
  · change min (m * nonzeroSlope n a w + Zbasic n a d cutoff + wingPrice n a cutoff)
        (m * nonzeroSlope n a w + Zimproved n a d cutoff + wingPrice n a cutoff) =
      m * nonzeroSlope n a w + min (Zbasic n a d cutoff) (Zimproved n a d cutoff) + wingPrice n a cutoff
    rw [min_add_add_right, min_add_add_left]

/-- Exact expansion into the original six terms, with the original physical inputs. -/
theorem candidate_six_terms (improveA improveZ : Bool) (n : ℕ) (M a d m w : ℝ) :
    candidate improveA improveZ n M a d m w =
      selectedInitial improveA n M +
      m / (4 * Real.pi ^ (3 / 2 : ℝ) * sineSlope w * Real.sqrt a) *
        (S3 + 3 * S5 w / ((n : ℝ) * a * sineSlope w ^ 2)) +
      m * Real.sqrt n / (2 * Real.pi ^ 2) *
        Real.exp (-((n : ℝ) * a) * sineSlope w ^ 2 * w ^ 2) +
      selectedZero improveZ n a d +
      Real.sqrt n * Real.exp (-(n : ℝ) * a * (23 / 48 : ℝ) ^ 2) / (2 * cutoff ^ 2) +
      comparatorPrice n M := by
  rw [candidate, selectedTail_eq]
  unfold nonzeroSlope wingPrice
  ring

lemma initialBasic_eq (n : ℕ) (M : ℝ) : initialBasic n M = 2 * sqrtExp (dampingRate M) n := by
  unfold initialBasic sqrtExp
  rw [mul_comm (dampingRate M) (n : ℝ)]
  simp only [neg_mul]
  ring

lemma initialImproved_eq (n : ℕ) (M : ℝ) :
    initialImproved n M = 2 * (sqrtExp (chordBase M) n * Lambda ((chordSlope M / 4) * n)) := by
  unfold initialImproved sqrtExp
  rw [show -(n : ℝ) * chordBase M = -(chordBase M * n) by ring,
    show (n : ℝ) * chordSlope M / 4 = (chordSlope M / 4) * n by ring]
  ring

lemma nonzeroSlope_eq (n : ℕ) (a w : ℝ) :
    nonzeroSlope n a w =
      (S3 + (3 / ((n : ℝ) * a * sineSlope w ^ 2)) * S5 w) /
        (4 * Real.pi ^ (3 / 2 : ℝ) * sineSlope w * Real.sqrt a) +
      sqrtExp (a * sineSlope w ^ 2 * w ^ 2) n / (2 * Real.pi ^ 2) := by
  unfold nonzeroSlope sqrtExp
  rw [show -((n : ℝ) * a) * sineSlope w ^ 2 * w ^ 2 =
    -((a * sineSlope w ^ 2 * w ^ 2) * n) by ring]
  ring

lemma Zbasic_eq (n : ℕ) (a d : ℝ) :
    Zbasic n a d cutoff = (1 / (2 * cutoff ^ 4 * kappa a d)) *
      invSqrtExp (kappa a d * cutoff ^ 2) n := by
  unfold Zbasic invSqrtExp
  rw [show -((n : ℝ) * kappa a d) * cutoff ^ 2 = -((kappa a d * cutoff ^ 2) * n) by ring]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

lemma Zimproved_eq (n : ℕ) (a d : ℝ) :
    Zimproved n a d cutoff = scaledRational (kappa a d * cutoff ^ 2) n / (2 * cutoff ^ 2) := by
  unfold Zimproved scaledRational
  rw [show -((n : ℝ) * kappa a d) * cutoff ^ 2 = -((kappa a d * cutoff ^ 2) * n) by ring,
    show (n : ℝ) * kappa a d * cutoff ^ 2 = (kappa a d * cutoff ^ 2) * n by ring]
  ring

lemma wingPrice_eq (n : ℕ) (a : ℝ) :
    wingPrice n a cutoff = sqrtExp (a * (23 / 48 : ℝ) ^ 2) n / (2 * cutoff ^ 2) := by
  unfold wingPrice sqrtExp
  rw [show -(n : ℝ) * a * (23 / 48 : ℝ) ^ 2 = -((a * (23 / 48 : ℝ) ^ 2) * n) by ring]

lemma comparatorPrice_eq (n : ℕ) (M : ℝ) :
    comparatorPrice n M = sqrtExp (1 / 8) n * (2 * Lambda ((n : ℝ) / 8) + Real.sqrt (M - 1) / 3) := by
  unfold comparatorPrice sqrtExp
  rw [show -(n : ℝ) / 8 = -((1 / 8 : ℝ) * n) by ring]

lemma initialBasic_nonneg (n : ℕ) (M : ℝ) : 0 ≤ initialBasic n M := by unfold initialBasic; positivity

lemma initialImproved_nonneg (n : ℕ) (M : ℝ) (hs : 0 < chordSlope M) : 0 ≤ initialImproved n M := by
  have hl := Lambda_nonneg ((n : ℝ) * chordSlope M / 4) (by positivity)
  unfold initialImproved
  positivity

lemma Zbasic_nonneg (n : ℕ) (a d : ℝ) (ha : 0 < a) (hd : 0 < d) : 0 ≤ Zbasic n a d cutoff := by
  have hk := kappa_pos a d ha hd
  unfold Zbasic
  positivity

lemma Zimproved_nonneg (n : ℕ) (a d : ℝ) (ha : 0 < a) (hd : 0 < d) : 0 ≤ Zimproved n a d cutoff := by
  have hk := kappa_pos a d ha hd
  have hl := Lambda_nonneg ((n : ℝ) * kappa a d * cutoff ^ 2) (by positivity)
  unfold Zimproved
  positivity

lemma wingPrice_nonneg (n : ℕ) (a : ℝ) : 0 ≤ wingPrice n a cutoff := by unfold wingPrice; positivity

lemma comparatorPrice_nonneg (n : ℕ) (M : ℝ) : 0 ≤ comparatorPrice n M := by
  have hl := Lambda_nonneg ((n : ℝ) / 8) (by positivity)
  unfold comparatorPrice
  positivity

lemma tailBasic_nonneg (n : ℕ) (a d m w : ℝ) (ha : 0 < a) (hd : 0 < d)
    (hm : 0 ≤ m) (hw : 0 < w) (hwcap : w ≤ 1 / 4) : 0 ≤ tailBasic n a d m w := by
  unfold tailBasic
  exact add_nonneg (add_nonneg (mul_nonneg hm (nonzeroSlope_nonneg n a w ha hw hwcap))
    (Zbasic_nonneg n a d ha hd)) (wingPrice_nonneg n a)

lemma tailImproved_nonneg (n : ℕ) (a d m w : ℝ) (ha : 0 < a) (hd : 0 < d)
    (hm : 0 ≤ m) (hw : 0 < w) (hwcap : w ≤ 1 / 4) : 0 ≤ tailImproved n a d m w := by
  unfold tailImproved
  exact add_nonneg (add_nonneg (mul_nonneg hm (nonzeroSlope_nonneg n a w ha hw hwcap))
    (Zimproved_nonneg n a d ha hd)) (wingPrice_nonneg n a)

lemma candidate_nonneg (improveA improveZ : Bool) (N n : ℕ) (M a d m w : ℝ)
    (ha : 0 < a) (hd : 0 < d) (hm : 0 ≤ m) (hw : 0 < w) (hwcap : w ≤ 1 / 4)
    (hI : ImprovementGates improveA improveZ N M a d) : 0 ≤ candidate improveA improveZ n M a d m w := by
  have hA : 0 ≤ selectedInitial improveA n M := by
    cases improveA
    · exact initialBasic_nonneg n M
    · exact le_min (initialBasic_nonneg n M) (initialImproved_nonneg n M (hI.1 rfl).1)
  have hT : 0 ≤ selectedTail improveZ n a d m w := by
    cases improveZ
    · exact tailBasic_nonneg n a d m w ha hd hm hw hwcap
    · exact le_min (tailBasic_nonneg n a d m w ha hd hm hw hwcap)
        (tailImproved_nonneg n a d m w ha hd hm hw hwcap)
  exact add_nonneg (add_nonneg hA hT) (comparatorPrice_nonneg n M)

lemma nat_sqrtExp_le (N n : ℕ) (c : ℝ) (hN : 0 < N) (hNn : N ≤ n)
    (hg : 1 ≤ 2 * (N : ℝ) * c) : sqrtExp c n ≤ sqrtExp c N :=
  sqrtExp_antitone c N (Nat.cast_pos.mpr hN) hg le_rfl (Nat.cast_le.mpr hNn) (Nat.cast_le.mpr hNn)

lemma initialBasic_le (N n : ℕ) (M : ℝ) (hN : 0 < N) (hNn : N ≤ n)
    (hg : 1 < 2 * (N : ℝ) * dampingRate M) : initialBasic n M ≤ initialBasic N M := by
  rw [initialBasic_eq, initialBasic_eq]
  exact mul_le_mul_of_nonneg_left (nat_sqrtExp_le N n _ hN hNn hg.le) (by norm_num)

lemma initialImproved_le (N n : ℕ) (M : ℝ) (hN : 0 < N) (hNn : N ≤ n)
    (hs : 0 < chordSlope M) (hg : 1 < 2 * (N : ℝ) * chordBase M) :
    initialImproved n M ≤ initialImproved N M := by
  rw [initialImproved_eq, initialImproved_eq]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact sqrtExp_mul_Lambda_antitone (chordBase M) (chordSlope M / 4) N
    (Nat.cast_pos.mpr hN) (by positivity) hg.le le_rfl (Nat.cast_le.mpr hNn) (Nat.cast_le.mpr hNn)

lemma nonzeroSlope_le (N n : ℕ) (a w : ℝ) (hN : 0 < N) (hNn : N ≤ n)
    (ha : 0 < a) (hw : 0 < w) (hwcap : w ≤ 1 / 4)
    (hg : 1 < 2 * (N : ℝ) * a * sineSlope w ^ 2 * w ^ 2) :
    nonzeroSlope n a w ≤ nonzeroSlope N a w := by
  have hNR : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hNr : (N : ℝ) ≤ n := Nat.cast_le.mpr hNn
  have hh := sineSlope_pos w hw.le hwcap
  have hden := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hNr ha.le) (sq_nonneg (sineSlope w))
  have hf : 3 / ((n : ℝ) * a * sineSlope w ^ 2) ≤ 3 / ((N : ℝ) * a * sineSlope w ^ 2) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) hden
  have hc := div_le_div_of_nonneg_right
    (add_le_add (le_rfl : S3 ≤ S3) (mul_le_mul_of_nonneg_right hf (S5_nonneg w hwcap)))
    (show 0 ≤ 4 * Real.pi ^ (3 / 2 : ℝ) * sineSlope w * Real.sqrt a by positivity)
  have hW := div_le_div_of_nonneg_right (nat_sqrtExp_le N n (a * sineSlope w ^ 2 * w ^ 2)
    hN hNn (by nlinarith only [hg])) (show (0 : ℝ) ≤ 2 * Real.pi ^ 2 by positivity)
  rw [nonzeroSlope_eq, nonzeroSlope_eq]
  exact add_le_add hc hW

lemma Zbasic_le (N n : ℕ) (a d : ℝ) (hN : 0 < N) (hNn : N ≤ n)
    (ha : 0 < a) (hd : 0 < d) : Zbasic n a d cutoff ≤ Zbasic N a d cutoff := by
  have hk := kappa_pos a d ha hd
  have hr : 0 < kappa a d * cutoff ^ 2 := mul_pos hk (sq_pos_of_pos cutoff_pos)
  rw [Zbasic_eq, Zbasic_eq]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact invSqrtExp_antitone _ hr (Nat.cast_pos.mpr hN)
    (Nat.cast_pos.mpr (hN.trans_le hNn)) (Nat.cast_le.mpr hNn)

lemma Zimproved_le (N n : ℕ) (a d : ℝ) (hNn : N ≤ n) (ha : 0 < a) (hd : 0 < d)
    (hg : 1 / 4 ≤ (N : ℝ) * kappa a d * cutoff ^ 2) :
    Zimproved n a d cutoff ≤ Zimproved N a d cutoff := by
  have hr : 0 < kappa a d * cutoff ^ 2 := mul_pos (kappa_pos a d ha hd) (sq_pos_of_pos cutoff_pos)
  rw [Zimproved_eq, Zimproved_eq]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact scaledRational_antitone _ N hr (by nlinarith only [hg]) le_rfl
    (Nat.cast_le.mpr hNn) (Nat.cast_le.mpr hNn)

lemma wingPrice_le (N n : ℕ) (a : ℝ) (hN : 0 < N) (hNn : N ≤ n)
    (hg : 1 < 2 * (N : ℝ) * a * (23 / 48 : ℝ) ^ 2) : wingPrice n a cutoff ≤ wingPrice N a cutoff := by
  rw [wingPrice_eq, wingPrice_eq]
  exact div_le_div_of_nonneg_right (nat_sqrtExp_le N n _ hN hNn (by nlinarith only [hg])) (by positivity)

lemma comparatorPrice_le (N n : ℕ) (M : ℝ) (hN : 0 < N) (hNn : N ≤ n)
    (hg : 1 < 2 * (N : ℝ) / 8) : comparatorPrice n M ≤ comparatorPrice N M := by
  have hnR : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hNR : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  have hF := nat_sqrtExp_le N n (1 / 8) hN hNn (by nlinarith only [hg])
  have hL := Lambda_antitone (show 0 ≤ (N : ℝ) / 8 by positivity)
    (show 0 ≤ (n : ℝ) / 8 by positivity) (div_le_div_of_nonneg_right (Nat.cast_le.mpr hNn) (by norm_num))
  have hB := add_le_add (mul_le_mul_of_nonneg_left hL (by norm_num : (0 : ℝ) ≤ 2))
    (le_rfl : Real.sqrt (M - 1) / 3 ≤ Real.sqrt (M - 1) / 3)
  have hLn := Lambda_nonneg ((n : ℝ) / 8) (by positivity)
  rw [comparatorPrice_eq, comparatorPrice_eq]
  exact mul_le_mul hF hB (by positivity) (sqrtExp_nonneg _ _)

lemma strict_gate_persists (N n : ℕ) (c : ℝ) (hN : 0 < N) (hNn : N ≤ n)
    (hg : 1 < 2 * (N : ℝ) * c) : 1 < 2 * (n : ℝ) * c := by
  have hc := sqrtExp_rate_pos (N : ℝ) c (Nat.cast_pos.mpr hN) hg.le
  have hm := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hNn) hc.le
  nlinarith

lemma basicGates_persist (N n : ℕ) (M a w : ℝ) (hN : 0 < N) (hNn : N ≤ n)
    (hg : BasicGates N M a w) : BasicGates n M a w := by
  refine ⟨strict_gate_persists N n _ hN hNn hg.initial, ?_, ?_, ?_⟩
  · have h := strict_gate_persists N n (a * sineSlope w ^ 2 * w ^ 2) hN hNn
      (by nlinarith only [hg.periodicWing])
    nlinarith only [h]
  · have h := strict_gate_persists N n (a * (23 / 48 : ℝ) ^ 2) hN hNn
      (by nlinarith only [hg.zeroWing])
    nlinarith only [h]
  · have h := strict_gate_persists N n (1 / 8) hN hNn (by nlinarith only [hg.comparator])
    nlinarith only [h]

lemma improvementGates_persist (improveA improveZ : Bool) (N n : ℕ) (M a d : ℝ)
    (hN : 0 < N) (hNn : N ≤ n) (ha : 0 < a) (hd : 0 < d)
    (hg : ImprovementGates improveA improveZ N M a d) :
    ImprovementGates improveA improveZ n M a d := by
  constructor
  · intro hA
    exact ⟨(hg.1 hA).1, strict_gate_persists N n _ hN hNn (hg.1 hA).2⟩
  · intro hZ
    have hr : 0 < kappa a d * cutoff ^ 2 := mul_pos (kappa_pos a d ha hd) (sq_pos_of_pos cutoff_pos)
    have h := quarter_gate_persists (N : ℝ) n _ hr (Nat.cast_le.mpr hNn) (by nlinarith only [hg.2 hZ])
    nlinarith only [h]

/-- The same fixed six-term candidate inherits its value from its qualified floor. -/
theorem candidate_le_floor (improveA improveZ : Bool) (N n : ℕ) (M a d m w : ℝ)
    (hN : 0 < N) (hNn : N ≤ n) (_hM : 1 ≤ M) (ha : 0 < a) (hd : 0 < d)
    (hm : 0 ≤ m) (hw : 0 < w) (hwcap : w ≤ 1 / 4)
    (hg : BasicGates N M a w) (hI : ImprovementGates improveA improveZ N M a d) :
    candidate improveA improveZ n M a d m w ≤ candidate improveA improveZ N M a d m w := by
  have hA : selectedInitial improveA n M ≤ selectedInitial improveA N M := by
    have hb := initialBasic_le N n M hN hNn hg.initial
    cases improveA
    · exact hb
    · exact min_le_min hb (initialImproved_le N n M hN hNn (hI.1 rfl).1 (hI.1 rfl).2)
  have hP := mul_le_mul_of_nonneg_left (nonzeroSlope_le N n a w hN hNn ha hw hwcap hg.periodicWing) hm
  have hW := wingPrice_le N n a hN hNn hg.zeroWing
  have hTB : tailBasic n a d m w ≤ tailBasic N a d m w :=
    add_le_add (add_le_add hP (Zbasic_le N n a d hN hNn ha hd)) hW
  have hT : selectedTail improveZ n a d m w ≤ selectedTail improveZ N a d m w := by
    cases improveZ
    · exact hTB
    · exact min_le_min hTB (add_le_add (add_le_add hP (Zimproved_le N n a d hNn ha hd (hI.2 rfl))) hW)
  exact add_le_add (add_le_add hA hT) (comparatorPrice_le N n M hN hNn hg.comparator)

/-- Antitonicity retains the original floor's eligibility and both Boolean choices. -/
theorem candidate_antitone (improveA improveZ : Bool) (N : ℕ) (M a d m w : ℝ)
    (hN : 0 < N) (hM : 1 ≤ M) (ha : 0 < a) (hd : 0 < d)
    (hm : 0 ≤ m) (hw : 0 < w) (hwcap : w ≤ 1 / 4)
    (hg : BasicGates N M a w) (hI : ImprovementGates improveA improveZ N M a d) :
    AntitoneOn (fun n : ℕ => candidate improveA improveZ n M a d m w) (Ici N) := by
  intro n hn k hk hnk
  exact candidate_le_floor improveA improveZ n k M a d m w (hN.trans_le hn) hnk hM ha hd hm hw hwcap
    (basicGates_persist N n M a w hN hn hg)
    (improvementGates_persist improveA improveZ N n M a d hN hn ha hd hI)

/-- The standard floor 25 is a numerical specialization, with qualification still at 25. -/
theorem candidate_le_floor25 (improveA improveZ : Bool) (n : ℕ) (M a d m w : ℝ)
    (hn : 25 ≤ n) (hM : 1 ≤ M) (ha : 0 < a) (hd : 0 < d)
    (hm : 0 ≤ m) (hw : 0 < w) (hwcap : w ≤ 1 / 4)
    (hg : BasicGates 25 M a w) (hI : ImprovementGates improveA improveZ 25 M a d) :
    candidate improveA improveZ n M a d m w ≤ candidate improveA improveZ 25 M a d m w :=
  candidate_le_floor improveA improveZ 25 n M a d m w (by norm_num) hn hM ha hd hm hw hwcap hg hI

end BerryEsseen.HighFrequencyPrice

#print axioms BerryEsseen.HighFrequencyPrice.candidate_six_terms
#print axioms BerryEsseen.HighFrequencyPrice.candidate_nonneg
#print axioms BerryEsseen.HighFrequencyPrice.candidate_le_floor
#print axioms BerryEsseen.HighFrequencyPrice.candidate_antitone
#print axioms BerryEsseen.HighFrequencyPrice.candidate_le_floor25
