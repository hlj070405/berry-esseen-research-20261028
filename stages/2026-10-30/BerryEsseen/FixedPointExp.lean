module

public import BerryEsseen.FixedPointArithmetic
public import BerryEsseen.RationalExpEnclosure

@[expose] public section

/-! 2026-10-29: executable outward-rounded Taylor recurrence for the true
exponential.  Every arithmetic operation is the proved integer algorithm.
The two positivity premises inspect computed integer lower endpoints; they
are decidable without a transcendental oracle.  The degree is a parameter.
For x in [0,32], evaluation uses y=x/32, an exact geometric Taylor tail,
five interval squares, and a positive reciprocal. -/

namespace BerryEsseen.FixedPointExp

open FixedPointEnclosure FixedPointArithmetic

def oneBox (S : ℤ) (hS : 0 < S) : Box := rat S hS 1 1 (by decide)

theorem oneBox_contains (S : ℤ) (hS : 0 < S) : Contains S (oneBox S hS) (1 : ℝ) := by
  simpa only [oneBox, Int.cast_one, div_one] using rat_contains S hS 1 1 (by decide)

def nextTerm (S : ℤ) (hS : 0 < S) (Y T : Box) (k : ℕ) : Box :=
  divInt (mul S hS T Y) ((k + 1 : ℕ) : ℤ) (by exact_mod_cast Nat.succ_pos k)

/-- Pair (degree-m term, sum through degree m). The same rounded term is
used both in the recurrence and the accumulated sum. -/
def taylorState (S : ℤ) (hS : 0 < S) (Y : Box) : ℕ → Box × Box
  | 0 => (oneBox S hS, oneBox S hS)
  | k + 1 =>
    let state := taylorState S hS Y k
    let term := nextTerm S hS Y state.1 k
    (term, add state.2 term)

private theorem real_term_succ (y : ℝ) (k : ℕ) :
    (y ^ k / (k.factorial : ℝ)) * y / ((k + 1 : ℕ) : ℝ) =
      y ^ (k + 1) / ((k + 1).factorial : ℝ) := by
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem nextTerm_contains {S : ℤ} (hS : 0 < S) {Y T : Box} {y : ℝ} (k : ℕ)
    (hY : Contains S Y y) (hT : Contains S T (y ^ k / (k.factorial : ℝ))) :
    Contains S (nextTerm S hS Y T k) (y ^ (k + 1) / ((k + 1).factorial : ℝ)) := by
  have h := divInt_contains hS (by exact_mod_cast Nat.succ_pos k : (0 : ℤ) < (k + 1 : ℕ))
    (mul_contains hS hT hY)
  simpa only [nextTerm, Int.cast_natCast, real_term_succ] using h

theorem taylorState_contains {S : ℤ} (hS : 0 < S) {Y : Box} {y : ℝ}
    (hY : Contains S Y y) (m : ℕ) :
    Contains S (taylorState S hS Y m).1 (y ^ m / (m.factorial : ℝ)) ∧
      Contains S (taylorState S hS Y m).2 (RationalExpEnclosure.taylor m y) := by
  induction m with
  | zero =>
    constructor
    · simpa only [taylorState, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
        using oneBox_contains S hS
    · simpa [taylorState, RationalExpEnclosure.taylor] using oneBox_contains S hS
  | succ m ih =>
    have ht := nextTerm_contains hS m hY ih.1
    refine ⟨ht, ?_⟩
    have hs := add_contains hS ih.2 ht
    simpa only [taylorState, RationalExpEnclosure.taylor, Nat.succ_eq_add_one,
      Finset.sum_range_succ] using hs

def tailDen (S : ℤ) (hS : 0 < S) (Y : Box) (m : ℕ) : Box :=
  sub (oneBox S hS) (divInt Y ((m + 2 : ℕ) : ℤ) (by omega))

theorem tailDen_contains {S : ℤ} (hS : 0 < S) {Y : Box} {y : ℝ}
    (hY : Contains S Y y) (m : ℕ) :
    Contains S (tailDen S hS Y m) (1 - y / ((m + 2 : ℕ) : ℝ)) := by
  exact sub_contains hS (oneBox_contains S hS)
    (by simpa only [Int.cast_natCast] using divInt_contains hS (by omega : (0 : ℤ) < (m + 2 : ℕ)) hY)

def taylorUpper (S : ℤ) (hS : 0 < S) (Y : Box) (m : ℕ)
    (hden : 0 < (tailDen S hS Y m).lo) : Box :=
  let state := taylorState S hS Y m
  add state.2 (divPos S hS (nextTerm S hS Y state.1 m) (tailDen S hS Y m) hden)

theorem taylorUpper_contains {S : ℤ} (hS : 0 < S) {Y : Box} {y : ℝ}
    (hY : Contains S Y y) (m : ℕ) (hden : 0 < (tailDen S hS Y m).lo) :
    Contains S (taylorUpper S hS Y m hden) (RationalExpEnclosure.upper m y) := by
  have hs := taylorState_contains hS hY m
  exact add_contains hS hs.2 (divPos_contains hS hden
    (nextTerm_contains hS m hY hs.1) (tailDen_contains hS hY m))

/-- The hull guarantees an ordered executable Box without asking the caller
to supply a real-valued order witness for the two approximating functions. -/
def hull (I J : Box) : Box :=
  ⟨min I.lo J.lo, max I.hi J.hi,
    (min_le_left _ _).trans (I.ordered.trans (le_max_left _ _))⟩

theorem hull_contains_between {S : ℤ} (hS : 0 < S) {I J : Box} {a b z : ℝ}
    (ha : Contains S I a) (hb : Contains S J b) (haz : a ≤ z) (hzb : z ≤ b) :
    Contains S (hull I J) z := by
  have hi := contains_widen hS (K := hull I J) ha (min_le_left I.lo J.lo) (le_max_left I.hi J.hi)
  have hj := contains_widen hS (K := hull I J) hb (min_le_right I.lo J.lo) (le_max_right I.hi J.hi)
  exact ⟨hi.1.trans haz, hzb.trans hj.2⟩

def expSmall (S : ℤ) (hS : 0 < S) (Y : Box) (m : ℕ)
    (hden : 0 < (tailDen S hS Y m).lo) : Box :=
  hull (taylorState S hS Y m).2 (taylorUpper S hS Y m hden)

theorem expSmall_contains {S : ℤ} (hS : 0 < S) {Y : Box} {y : ℝ}
    (hY : Contains S Y y) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (m : ℕ)
    (hden : 0 < (tailDen S hS Y m).lo) :
    Contains S (expSmall S hS Y m hden) (Real.exp y) :=
  hull_contains_between hS (taylorState_contains hS hY m).2
    (taylorUpper_contains hS hY m hden)
    (RationalExpEnclosure.taylor_le_exp m y hy0)
    (RationalExpEnclosure.exp_le_upper m y hy0 hy1)

def squareTimes (S : ℤ) (hS : 0 < S) : ℕ → Box → Box
  | 0, I => I
  | k + 1, I => sq S hS (squareTimes S hS k I)

theorem squareTimes_contains {S : ℤ} (hS : 0 < S) {I : Box} {x : ℝ}
    (hx : Contains S I x) (n : ℕ) :
    Contains S (squareTimes S hS n I) (x ^ (2 ^ n)) := by
  induction n with
  | zero => simpa only [squareTimes, pow_zero, pow_one] using hx
  | succ n ih =>
    simpa only [squareTimes, pow_succ, pow_mul] using sq_contains hS ih

def reduced (X : Box) : Box := divInt X 32 (by decide)

def expPositive (S : ℤ) (hS : 0 < S) (X : Box) (m : ℕ)
    (hden : 0 < (tailDen S hS (reduced X) m).lo) : Box :=
  squareTimes S hS 5 (expSmall S hS (reduced X) m hden)

theorem expPositive_contains {S : ℤ} (hS : 0 < S) {X : Box} {x : ℝ}
    (hX : Contains S X x) (hx0 : 0 ≤ x) (hx32 : x ≤ 32) (m : ℕ)
    (hden : 0 < (tailDen S hS (reduced X) m).lo) :
    Contains S (expPositive S hS X m hden) (Real.exp x) := by
  have hY : Contains S (reduced X) (x / 32) := divInt_contains hS (by decide) hX
  have hy0 : 0 ≤ x / 32 := by positivity
  have hy1 : x / 32 ≤ 1 := (div_le_one (by norm_num : (0 : ℝ) < 32)).mpr hx32
  have hh := squareTimes_contains hS (expSmall_contains hS hY hy0 hy1 m hden) 5
  have heq : Real.exp (x / 32) ^ (2 ^ 5) = Real.exp x := by
    norm_num only [Nat.reducePow]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  simpa only [expPositive, heq] using hh

def expNeg (S : ℤ) (hS : 0 < S) (X : Box) (m : ℕ)
    (hden : 0 < (tailDen S hS (reduced X) m).lo)
    (hpos : 0 < (expPositive S hS X m hden).lo) : Box :=
  invPos S hS (expPositive S hS X m hden) hpos

theorem expNeg_contains {S : ℤ} (hS : 0 < S) {X : Box} {x : ℝ}
    (hX : Contains S X x) (hx0 : 0 ≤ x) (hx32 : x ≤ 32) (m : ℕ)
    (hden : 0 < (tailDen S hS (reduced X) m).lo)
    (hpos : 0 < (expPositive S hS X m hden).lo) :
    Contains S (expNeg S hS X m hden hpos) (Real.exp (-x)) := by
  rw [Real.exp_neg]
  exact invPos_contains hS hpos (expPositive_contains hS hX hx0 hx32 m hden)

/-- An entirely integer domain check for an input Box. -/
def InputGate (S : ℤ) (X : Box) : Prop := 0 ≤ X.lo ∧ X.hi ≤ 32 * S

instance (S : ℤ) (X : Box) : Decidable (InputGate S X) := by
  unfold InputGate
  infer_instance

theorem input_bounds {S : ℤ} (hS : 0 < S) {X : Box} {x : ℝ}
    (hX : Contains S X x) (hgate : InputGate S X) : 0 ≤ x ∧ x ≤ 32 := by
  rw [contains_iff_real] at hX
  have hs : (0 : ℝ) < S := by exact_mod_cast hS
  constructor
  · exact (div_nonneg (by exact_mod_cast hgate.1) hs.le).trans hX.1
  · apply hX.2.trans
    apply (div_le_iff₀ hs).mpr
    exact_mod_cast hgate.2

theorem expNeg_contains_of_gate {S : ℤ} (hS : 0 < S) {X : Box} {x : ℝ}
    (hX : Contains S X x) (hgate : InputGate S X) (m : ℕ)
    (hden : 0 < (tailDen S hS (reduced X) m).lo)
    (hpos : 0 < (expPositive S hS X m hden).lo) :
    Contains S (expNeg S hS X m hden hpos) (Real.exp (-x)) :=
  expNeg_contains hS hX (input_bounds hS hX hgate).1 (input_bounds hS hX hgate).2 m hden hpos

/-- The old N42 long-tail endpoint M=8 consumes exp(-M^2/4)=exp(-16).
Degree eight is used here to exercise the reduced-cost routine itself. -/
def longTailInput40 : Box := rat (10 ^ 40) (by decide) 16 1 (by decide)

theorem longTail_den_positive : 0 < (tailDen (10 ^ 40) (by decide) (reduced longTailInput40) 8).lo := by
  decide

theorem longTail_power_positive :
    0 < (expPositive (10 ^ 40) (by decide) longTailInput40 8 longTail_den_positive).lo := by
  decide

def longTailExp40 : Box := expNeg (10 ^ 40) (by decide) longTailInput40 8
  longTail_den_positive longTail_power_positive

/-- Actual evaluated endpoints, checked by the kernel using the integer
definitions above. This equality does not take an enclosure as a premise. -/
theorem longTailExp40_endpoints :
    longTailExp40.lo = 1125351747161981221007726014898487 ∧
      longTailExp40.hi = 1125351870908916614187267386596638 := by decide

theorem longTailExp40_contains : Contains (10 ^ 40) longTailExp40 (Real.exp (-16 : ℝ)) := by
  have hx : Contains (10 ^ 40) longTailInput40 (16 : ℝ) := by
    unfold longTailInput40
    simpa only [Int.cast_ofNat, Int.cast_one, div_one] using
      rat_contains (10 ^ 40) (by decide) 16 1 (by decide)
  exact expNeg_contains (by decide) hx (by norm_num) (by norm_num) 8
    longTail_den_positive longTail_power_positive

end BerryEsseen.FixedPointExp

#print axioms BerryEsseen.FixedPointExp.taylorState_contains
#print axioms BerryEsseen.FixedPointExp.expSmall_contains
#print axioms BerryEsseen.FixedPointExp.expNeg_contains
#print axioms BerryEsseen.FixedPointExp.longTailExp40_endpoints
#print axioms BerryEsseen.FixedPointExp.longTailExp40_contains
