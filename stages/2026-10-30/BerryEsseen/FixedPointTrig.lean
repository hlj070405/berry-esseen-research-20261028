module

public import BerryEsseen.FixedPointArithmetic
public import BerryEsseen.RationalTrigEnclosure

@[expose] public section

/-! 2026-10-30: integer interval sine and cosine for small nonnegative
arguments. Degree 32 Horner evaluation keeps both endpoints at every signed
coefficient. The genuine imaginary-exponential Taylor remainder is enclosed
by the upper endpoint of the input interval's 33rd power divided by 33!.
All arithmetic is outward rounded; no transcendental value is a witness. -/

open scoped BigOperators

namespace BerryEsseen.FixedPointTrig

open FixedPointEnclosure FixedPointArithmetic

def cosCoeff (k : ℕ) : ℤ :=
  if k % 4 = 0 then 1 else if k % 4 = 2 then -1 else 0

def sinCoeff (k : ℕ) : ℤ :=
  if k % 4 = 1 then 1 else if k % 4 = 3 then -1 else 0

def powBox (S : ℤ) (hS : 0 < S) (I : Box) : ℕ → Box
  | 0 => rat S hS 1 1 (by decide)
  | n + 1 => mul S hS (powBox S hS I n) I

def hornerBox (S : ℤ) (hS : 0 < S) (c : ℕ → ℤ) (I : Box) : ℕ → ℕ → Box
  | _, 0 => rat S hS 0 1 (by decide)
  | k, n + 1 => add (rat S hS (c k) (k.factorial : ℤ) (by exact_mod_cast k.factorial_pos))
      (mul S hS I (hornerBox S hS c I (k + 1) n))

def remainderBox (S : ℤ) (hS : 0 < S) (I : Box) : Box :=
  divInt (powBox S hS I 33) ((33 : ℕ).factorial : ℤ) (by decide)

def errorRadius (S : ℤ) (hS : 0 < S) (I : Box) : ℤ :=
  max 0 (remainderBox S hS I).hi

def symmetricError (S : ℤ) (hS : 0 < S) (I : Box) : Box :=
  ⟨-errorRadius S hS I, errorRadius S hS I, by
    have h : 0 ≤ errorRadius S hS I := le_max_left _ _
    omega⟩

def cosBox (S : ℤ) (hS : 0 < S) (I : Box) : Box :=
  add (hornerBox S hS cosCoeff I 0 33) (symmetricError S hS I)

def sinBox (S : ℤ) (hS : 0 < S) (I : Box) : Box :=
  add (hornerBox S hS sinCoeff I 0 33) (symmetricError S hS I)

/-- A candidate at another scale encloses both computed endpoints. -/
def Covers (S T : ℤ) (computed candidate : Box) : Prop :=
  candidate.lo * S ≤ computed.lo * T ∧ computed.hi * T ≤ candidate.hi * S

instance (S T : ℤ) (computed candidate : Box) : Decidable (Covers S T computed candidate) := by
  unfold Covers
  infer_instance

def coversCheck (S T : ℤ) (computed candidate : Box) : Bool :=
  decide (Covers S T computed candidate)

def sinCheck (S T : ℤ) (hS : 0 < S) (I candidate : Box) : Bool :=
  decide (0 ≤ I.lo ∧ I.hi ≤ S) && coversCheck S T (sinBox S hS I) candidate

def cosCheck (S T : ℤ) (hS : 0 < S) (I candidate : Box) : Bool :=
  decide (0 ≤ I.lo ∧ I.hi ≤ S) && coversCheck S T (cosBox S hS I) candidate

noncomputable section

def hornerValue (c : ℕ → ℤ) (x : ℝ) : ℕ → ℕ → ℝ
  | _, 0 => 0
  | k, n + 1 => (c k : ℝ) / (k.factorial : ℝ) + x * hornerValue c x (k + 1) n

theorem powBox_contains {S : ℤ} (hS : 0 < S) {I : Box} {x : ℝ}
    (hx : Contains S I x) (n : ℕ) : Contains S (powBox S hS I n) (x ^ n) := by
  induction n with
  | zero => simpa only [powBox, pow_zero, Int.cast_one, div_one] using rat_contains S hS 1 1 (by decide)
  | succ n ih => simpa only [powBox, pow_succ] using mul_contains hS ih hx

theorem hornerBox_contains {S : ℤ} (hS : 0 < S) (c : ℕ → ℤ) {I : Box} {x : ℝ}
    (hx : Contains S I x) (k n : ℕ) :
    Contains S (hornerBox S hS c I k n) (hornerValue c x k n) := by
  induction n generalizing k with
  | zero => simpa only [hornerBox, hornerValue, Int.cast_zero, zero_div] using rat_contains S hS 0 1 (by decide)
  | succ n ih =>
    apply add_contains hS
      (by simpa only [Int.cast_natCast] using
        rat_contains S hS (c k) (k.factorial : ℤ) (by exact_mod_cast k.factorial_pos))
      (mul_contains hS hx (ih (k + 1)))

lemma hornerValue_eq_sum (c : ℕ → ℤ) (x : ℝ) (k n : ℕ) :
    hornerValue c x k n =
      ∑ j ∈ Finset.range n, (c (k + j) : ℝ) * x ^ j / ((k + j).factorial : ℝ) := by
  induction n generalizing k with
  | zero => simp [hornerValue]
  | succ n ih =>
    rw [hornerValue, ih, Finset.sum_range_succ', Finset.mul_sum]
    simp only [Nat.add_zero, pow_zero, mul_one]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [show k + (j + 1) = k + 1 + j by omega, pow_succ]
    ring

lemma cosCoeff_cast (k : ℕ) : (cosCoeff k : ℝ) = (RationalTrigEnclosure.cosCoefficient k : ℝ) := by
  unfold cosCoeff RationalTrigEnclosure.cosCoefficient
  split_ifs <;> norm_num

lemma sinCoeff_cast (k : ℕ) : (sinCoeff k : ℝ) = (RationalTrigEnclosure.sinCoefficient k : ℝ) := by
  unfold sinCoeff RationalTrigEnclosure.sinCoefficient
  split_ifs <;> norm_num

lemma cos_horner_eq_re (m : ℕ) (x : ℝ) :
    hornerValue cosCoeff x 0 (m + 1) = (CharacteristicExpansion.expPolynomial m x).re := by
  rw [hornerValue_eq_sum]
  unfold CharacteristicExpansion.expPolynomial
  simp only [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [mul_pow, ← Complex.ofReal_pow]
  simp only [Nat.zero_add, Complex.div_natCast_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    RationalTrigEnclosure.I_pow_re, cosCoeff_cast]

lemma sin_horner_eq_im (m : ℕ) (x : ℝ) :
    hornerValue sinCoeff x 0 (m + 1) = (CharacteristicExpansion.expPolynomial m x).im := by
  rw [hornerValue_eq_sum]
  unfold CharacteristicExpansion.expPolynomial
  simp only [Complex.im_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [mul_pow, ← Complex.ofReal_pow]
  simp only [Complex.div_natCast_im, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add,
    RationalTrigEnclosure.I_pow_im, sinCoeff_cast]

theorem cos_horner_error (m : ℕ) (x : ℝ) :
    |Real.cos x - hornerValue cosCoeff x 0 (m + 1)| ≤
      |x| ^ (m + 1) / ((m + 1).factorial : ℝ) := by
  rw [cos_horner_eq_re]
  have hh := (Complex.abs_re_le_norm
    (CharacteristicExpansion.pureExp x - CharacteristicExpansion.expPolynomial m x)).trans
      (CharacteristicExpansion.pureExp_taylor_bound m x)
  simpa only [Complex.sub_re, CharacteristicExpansion.pureExp_real] using hh

theorem sin_horner_error (m : ℕ) (x : ℝ) :
    |Real.sin x - hornerValue sinCoeff x 0 (m + 1)| ≤
      |x| ^ (m + 1) / ((m + 1).factorial : ℝ) := by
  rw [sin_horner_eq_im]
  have hp : (CharacteristicExpansion.pureExp x).im = Real.sin x := by
    simpa only [CharacteristicExpansion.pureExp, mul_comm] using Complex.exp_ofReal_mul_I_im x
  have hh := (Complex.abs_im_le_norm
    (CharacteristicExpansion.pureExp x - CharacteristicExpansion.expPolynomial m x)).trans
      (CharacteristicExpansion.pureExp_taylor_bound m x)
  simpa only [Complex.sub_im, hp] using hh

lemma input_nonneg {S : ℤ} (hS : 0 < S) {I : Box} {x : ℝ}
    (hx : Contains S I x) (hI0 : 0 ≤ I.lo) : 0 ≤ x := by
  rw [contains_iff_real] at hx
  exact (div_nonneg (by exact_mod_cast hI0) (by exact_mod_cast hS.le)).trans hx.1

theorem remainder_le_radius {S : ℤ} (hS : 0 < S) {I : Box} {x : ℝ}
    (hx : Contains S I x) (hI0 : 0 ≤ I.lo) :
    |x| ^ 33 / ((33 : ℕ).factorial : ℝ) ≤ (qval S (errorRadius S hS I) : ℝ) := by
  have he := divInt_contains hS (show (0 : ℤ) < ((33 : ℕ).factorial : ℤ) by decide)
    (powBox_contains hS hx 33)
  have hu : (qval S (remainderBox S hS I).hi : ℝ) ≤
      (qval S (errorRadius S hS I) : ℝ) := by
    exact_mod_cast qval_mono hS (le_max_right 0 (remainderBox S hS I).hi)
  rw [abs_of_nonneg (input_nonneg hS hx hI0)]
  exact (show x ^ 33 / ((33 : ℕ).factorial : ℝ) ≤ (qval S (remainderBox S hS I).hi : ℝ) by
    simpa only [remainderBox, Int.cast_natCast] using he.2).trans hu

lemma symmetricError_contains {S : ℤ} (hS : 0 < S) {I : Box} {x e : ℝ}
    (hx : Contains S I x) (hI0 : 0 ≤ I.lo)
    (he : |e| ≤ |x| ^ 33 / ((33 : ℕ).factorial : ℝ)) :
    Contains S (symmetricError S hS I) e := by
  have hh := abs_le.mp (he.trans (remainder_le_radius hS hx hI0))
  constructor
  · simpa only [symmetricError, qval, Rat.cast_div, Rat.cast_intCast,
      Int.cast_neg, neg_div, Rat.cast_neg] using hh.1
  · exact hh.2

theorem cosBox_contains {S : ℤ} (hS : 0 < S) {I : Box} {x : ℝ}
    (hx : Contains S I x) (hI0 : 0 ≤ I.lo) (_hI1 : I.hi ≤ S) :
    Contains S (cosBox S hS I) (Real.cos x) := by
  have hh := add_contains hS (hornerBox_contains hS cosCoeff hx 0 33)
    (symmetricError_contains hS hx hI0 (cos_horner_error 32 x))
  convert hh using 1 <;> first | rfl | ring

theorem sinBox_contains {S : ℤ} (hS : 0 < S) {I : Box} {x : ℝ}
    (hx : Contains S I x) (hI0 : 0 ≤ I.lo) (_hI1 : I.hi ≤ S) :
    Contains S (sinBox S hS I) (Real.sin x) := by
  have hh := add_contains hS (hornerBox_contains hS sinCoeff hx 0 33)
    (symmetricError_contains hS hx hI0 (sin_horner_error 32 x))
  convert hh using 1 <;> first | rfl | ring

theorem covers_sound {S T : ℤ} (hS : 0 < S) (hT : 0 < T) {I K : Box} {x : ℝ}
    (hx : Contains S I x) (h : Covers S T I K) : Contains T K x := by
  rw [contains_iff_real] at hx ⊢
  have hs : (0 : ℝ) < S := by exact_mod_cast hS
  have ht : (0 : ℝ) < T := by exact_mod_cast hT
  constructor
  · apply le_trans _ hx.1
    exact (div_le_div_iff₀ ht hs).mpr (by exact_mod_cast h.1)
  · apply le_trans hx.2
    exact (div_le_div_iff₀ hs ht).mpr (by exact_mod_cast h.2)

theorem sinCheck_sound {S T : ℤ} (hS : 0 < S) (hT : 0 < T) {I K : Box} {x : ℝ}
    (hx : Contains S I x) (h : sinCheck S T hS I K = true) : Contains T K (Real.sin x) := by
  simp only [sinCheck, Bool.and_eq_true, decide_eq_true_eq, coversCheck] at h
  exact covers_sound hS hT (sinBox_contains hS hx h.1.1 h.1.2) h.2

theorem cosCheck_sound {S T : ℤ} (hS : 0 < S) (hT : 0 < T) {I K : Box} {x : ℝ}
    (hx : Contains S I x) (h : cosCheck S T hS I K = true) : Contains T K (Real.cos x) := by
  simp only [cosCheck, Bool.and_eq_true, decide_eq_true_eq, coversCheck] at h
  exact covers_sound hS hT (cosBox_contains hS hx h.1.1 h.1.2) h.2

/- A single endpoint check also exercises the 40-to-24 digit scale bridge.
It is much narrower than the downstream 18-digit candidates. -/
set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem sinCheck_threeFifths_24 :
    sinCheck (10 ^ 40) (10 ^ 24) (by decide)
      (rat (10 ^ 40) (by decide) 3 5 (by decide))
      ⟨564642473395035357200945, 564642473395035357200946, by decide⟩ = true := by
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem cosCheck_threeFifths_24 :
    cosCheck (10 ^ 40) (10 ^ 24) (by decide)
      (rat (10 ^ 40) (by decide) 3 5 (by decide))
      ⟨825335614909678297240952, 825335614909678297240953, by decide⟩ = true := by
  decide

end

end BerryEsseen.FixedPointTrig

#print axioms BerryEsseen.FixedPointTrig.cosBox_contains
#print axioms BerryEsseen.FixedPointTrig.sinBox_contains
#print axioms BerryEsseen.FixedPointTrig.cosCheck_sound
#print axioms BerryEsseen.FixedPointTrig.sinCheck_sound
#print axioms BerryEsseen.FixedPointTrig.sinCheck_threeFifths_24
#print axioms BerryEsseen.FixedPointTrig.cosCheck_threeFifths_24
