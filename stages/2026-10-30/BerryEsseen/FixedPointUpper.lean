module

public import BerryEsseen.FixedPointExp

@[expose] public section

/-! 2026-10-29: one-sided operations for the executable endpoint price.
An extracted upper endpoint is a new exact rational value, not a singleton
enclosure of the original unknown value. Square-root upper witnesses need
only one integer. Exponential truncation is justified by monotonicity. -/

namespace BerryEsseen.FixedPointUpper

open FixedPointEnclosure FixedPointArithmetic

def point (z : ℤ) : Box := ⟨z, z, le_rfl⟩

theorem point_contains (S z : ℤ) : Contains S (point z) (qval S z : ℝ) := ⟨le_rfl, le_rfl⟩

def upperPoint (I : Box) : Box := point I.hi

theorem upperPoint_contains_value (S : ℤ) (I : Box) :
    Contains S (upperPoint I) (qval S I.hi : ℝ) := point_contains S I.hi

theorem le_upperPoint {S : ℤ} {I : Box} {x : ℝ} (hx : Contains S I x) :
    x ≤ (qval S (upperPoint I).hi : ℝ) := hx.2

theorem le_scaled_min {S u v : ℤ} {x : ℝ}
    (hu : x ≤ (qval S u : ℝ)) (hv : x ≤ (qval S v : ℝ)) :
    x ≤ (qval S (min u v) : ℝ) := by
  rcases le_total u v with h | h
  · simpa only [min_eq_left h] using hu
  · simpa only [min_eq_right h] using hv

def minimumUpper (I J : Box) : Box := point (min I.hi J.hi)

theorem le_minimumUpper {S : ℤ} {I J : Box} {x : ℝ}
    (hI : x ≤ (qval S I.hi : ℝ)) (hJ : x ≤ (qval S J.hi : ℝ)) :
    x ≤ (qval S (minimumUpper I J).hi : ℝ) := le_scaled_min hI hJ

def nonneg (I : Box) : Box := ⟨max 0 I.lo, max 0 I.hi, max_le_max le_rfl I.ordered⟩

theorem nonneg_contains {S : ℤ} (hS : 0 < S) {I : Box} {x : ℝ}
    (hx : Contains S I x) (hx0 : 0 ≤ x) : Contains S (nonneg I) x := by
  constructor
  · by_cases h : I.lo ≤ 0
    · simpa only [nonneg, max_eq_left h, qval, Int.cast_zero, zero_div, Rat.cast_zero] using hx0
    · simpa only [nonneg, max_eq_right (le_of_lt (lt_of_not_ge h))] using hx.1
  · have hh := qval_mono hS (le_max_right (0 : ℤ) I.hi)
    exact hx.2.trans (by exact_mod_cast hh)

lemma qval_nonneg {S z : ℤ} (hS : 0 < S) (hz : 0 ≤ z) : (0 : ℝ) ≤ (qval S z : ℝ) := by
  have hh : (0 : ℚ) ≤ qval S z := by
    unfold qval
    exact div_nonneg (by exact_mod_cast hz) (scale_pos hS).le
  exact Rat.cast_nonneg.mpr hh

lemma qval_scale {S : ℤ} (hS : 0 < S) : (qval S S : ℝ) = 1 := by
  unfold qval
  rw [div_self (scale_pos hS).ne']
  norm_num

def UpperSquareGate (S : ℤ) (I : Box) (u : ℤ) : Prop :=
  0 ≤ u ∧ I.hi * S ≤ u ^ 2

instance (S : ℤ) (I : Box) (u : ℤ) : Decidable (UpperSquareGate S I u) := by
  unfold UpperSquareGate
  infer_instance

/-- Only the candidate upper endpoint is needed. In particular, no host
square-root algorithm or irrelevant lower root witness is trusted. -/
theorem sqrt_le_upper {S : ℤ} (hS : 0 < S) {I : Box} {x : ℝ} {u : ℤ}
    (hx : Contains S I x) (hgate : UpperSquareGate S I u) :
    Real.sqrt x ≤ (qval S u : ℝ) := by
  have hu0 := qval_nonneg hS hgate.1
  apply (Real.sqrt_le_left hu0).mpr
  apply hx.2.trans
  have hs : (0 : ℝ) < S := by exact_mod_cast hS
  have hh : (I.hi : ℝ) * S ≤ (u : ℝ) ^ 2 := by exact_mod_cast hgate.2
  simp only [qval, Rat.cast_div, Rat.cast_intCast]
  rw [div_pow]
  apply (div_le_div_iff₀ hs (sq_pos_of_pos hs)).mpr
  nlinarith only [mul_le_mul_of_nonneg_right hh hs.le]

def clipped32 (S : ℤ) (hS : 0 < S) (X : Box) : Box :=
  minBox (nonneg X) (rat S hS 32 1 (by decide))

theorem clipped32_contains {S : ℤ} (hS : 0 < S) {X : Box} {x : ℝ}
    (hX : Contains S X x) (hx0 : 0 ≤ x) :
    Contains S (clipped32 S hS X) (min x 32) := by
  have hc := minBox_contains hS (nonneg_contains hS hX hx0)
    (rat_contains S hS 32 1 (by decide))
  simpa only [clipped32, Int.cast_ofNat, Int.cast_one, div_one] using hc

theorem clipped32_input_gate (S : ℤ) (hS : 0 < S) (X : Box) :
    FixedPointExp.InputGate S (clipped32 S hS X) := by
  simp only [FixedPointExp.InputGate, clipped32, minBox, nonneg, rat, floorDiv, ceilDiv,
    Int.ediv_one, neg_neg]
  exact ⟨le_min (le_max_left _ _) (by positivity), min_le_right _ _⟩

def expUpper (S : ℤ) (hS : 0 < S) (X : Box) (m : ℕ)
    (hden : 0 < (FixedPointExp.tailDen S hS (FixedPointExp.reduced (clipped32 S hS X)) m).lo)
    (hpos : 0 < (FixedPointExp.expPositive S hS (clipped32 S hS X) m hden).lo) : ℤ :=
  min (FixedPointExp.expNeg S hS (clipped32 S hS X) m hden hpos).hi S

/-- This covers arbitrarily large nonnegative exponents by the genuine
inequality exp(-x)<=exp(-min(x,32)), then caps by the true bound one. -/
theorem exp_neg_le_upper {S : ℤ} (hS : 0 < S) {X : Box} {x : ℝ}
    (hX : Contains S X x) (hx0 : 0 ≤ x) (m : ℕ)
    (hden : 0 < (FixedPointExp.tailDen S hS (FixedPointExp.reduced (clipped32 S hS X)) m).lo)
    (hpos : 0 < (FixedPointExp.expPositive S hS (clipped32 S hS X) m hden).lo) :
    Real.exp (-x) ≤ (qval S (expUpper S hS X m hden hpos) : ℝ) := by
  have hh := FixedPointExp.expNeg_contains_of_gate hS (clipped32_contains hS hX hx0)
    (clipped32_input_gate S hS X) m hden hpos
  have he := Real.exp_le_exp.mpr (neg_le_neg (min_le_left x 32))
  have hU := he.trans (le_upper hh)
  have hOne : Real.exp (-x) ≤ (qval S S : ℝ) := by
    rw [qval_scale hS]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr hx0)
  exact le_scaled_min hU hOne

end BerryEsseen.FixedPointUpper

#print axioms BerryEsseen.FixedPointUpper.nonneg_contains
#print axioms BerryEsseen.FixedPointUpper.sqrt_le_upper
#print axioms BerryEsseen.FixedPointUpper.clipped32_input_gate
#print axioms BerryEsseen.FixedPointUpper.exp_neg_le_upper
