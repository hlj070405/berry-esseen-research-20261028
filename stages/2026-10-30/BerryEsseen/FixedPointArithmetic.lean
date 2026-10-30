module

public import BerryEsseen.FixedPointEnclosure

@[expose] public section

/-! 2026-10-29: executable integer fixed-point arithmetic with proved
outward-rounding gates. Definitions follow the frozen Python I operation
order. Generic gate proofs replace per-operation host witnesses; kernel
evaluation computes the actual integers. There is no native backend or DAG.
Upper endpoint extraction retains only the one-sided semantics supplied by
FixedPointEnclosure.le_upper. Square roots retain the existing proved witness
gate: the imported Nat.sqrt iteration is not kernel-reducible by decide in
this pinned module interface, so no executable sqrt claim is made here. -/

namespace BerryEsseen.FixedPointArithmetic

open FixedPointEnclosure

def floorDiv (n d : ℤ) : ℤ := n / d
def ceilDiv (n d : ℤ) : ℤ := -((-n) / d)

theorem floor_mul_le (n : ℤ) {d : ℤ} (hd : 0 < d) : floorDiv n d * d ≤ n :=
  Int.ediv_mul_le n hd.ne'

theorem le_ceil_mul (n : ℤ) {d : ℤ} (hd : 0 < d) : n ≤ ceilDiv n d * d := by
  have hh := Int.ediv_mul_le (-n) hd.ne'
  unfold ceilDiv
  nlinarith only [hh]

theorem floor_mono {a b d : ℤ} (hd : 0 < d) (hab : a ≤ b) : floorDiv a d ≤ floorDiv b d :=
  Int.ediv_le_ediv hd hab

theorem ceil_mono {a b d : ℤ} (hd : 0 < d) (hab : a ≤ b) : ceilDiv a d ≤ ceilDiv b d := by
  exact neg_le_neg (Int.ediv_le_ediv hd (neg_le_neg hab))

theorem floor_le_ceil_of_le {a b d : ℤ} (hd : 0 < d) (hab : a ≤ b) :
    floorDiv a d ≤ ceilDiv b d :=
  Int.le_of_mul_le_mul_right ((floor_mul_le a hd).trans (hab.trans (le_ceil_mul b hd))) hd

theorem floor_nonneg {n d : ℤ} (hd : 0 < d) (hn : 0 ≤ n) : 0 ≤ floorDiv n d := by
  simpa only [floorDiv, Int.zero_ediv] using floor_mono hd hn

def rat (S : ℤ) (_hS : 0 < S) (p d : ℤ) (hd : 0 < d) : Box :=
  ⟨floorDiv (p * S) d, ceilDiv (p * S) d, floor_le_ceil_of_le hd le_rfl⟩

theorem rat_gate (S : ℤ) (hS : 0 < S) (p d : ℤ) (hd : 0 < d) :
    RatGate S p d (rat S hS p d hd) :=
  ⟨floor_mul_le _ hd, le_ceil_mul _ hd⟩

theorem rat_contains (S : ℤ) (hS : 0 < S) (p d : ℤ) (hd : 0 < d) :
    Contains S (rat S hS p d hd) ((p : ℝ) / d) :=
  FixedPointEnclosure.contains_rat hS hd _ (rat_gate S hS p d hd)

def add (I J : Box) : Box := ⟨I.lo + J.lo, I.hi + J.hi, add_le_add I.ordered J.ordered⟩

def neg (I : Box) : Box := ⟨-I.hi, -I.lo, neg_le_neg I.ordered⟩

def sub (I J : Box) : Box := add I (neg J)

theorem add_gate (I J : Box) : AddGate I J (add I J) := ⟨le_rfl, le_rfl⟩
theorem neg_gate (I : Box) : NegGate I (neg I) := ⟨le_rfl, le_rfl⟩
theorem sub_gate (I J : Box) : SubGate I J (sub I J) := by
  simp only [SubGate, sub, add, neg, sub_eq_add_neg, le_refl, and_self]

theorem add_contains {S : ℤ} (hS : 0 < S) {I J : Box} {x y : ℝ}
    (hx : Contains S I x) (hy : Contains S J y) : Contains S (add I J) (x + y) :=
  FixedPointEnclosure.contains_add hS hx hy (add_gate I J)

theorem neg_contains {S : ℤ} (hS : 0 < S) {I : Box} {x : ℝ}
    (hx : Contains S I x) : Contains S (neg I) (-x) :=
  FixedPointEnclosure.contains_neg hS hx (neg_gate I)

theorem sub_contains {S : ℤ} (hS : 0 < S) {I J : Box} {x y : ℝ}
    (hx : Contains S I x) (hy : Contains S J y) : Contains S (sub I J) (x - y) :=
  FixedPointEnclosure.contains_sub hS hx hy (sub_gate I J)

def productLower (I J : Box) : ℤ :=
  min (min (I.lo * J.lo) (I.lo * J.hi)) (min (I.hi * J.lo) (I.hi * J.hi))

def productUpper (I J : Box) : ℤ :=
  max (max (I.lo * J.lo) (I.lo * J.hi)) (max (I.hi * J.lo) (I.hi * J.hi))

lemma productLower_le (I J : Box) :
    productLower I J ≤ I.lo * J.lo ∧ productLower I J ≤ I.lo * J.hi ∧
      productLower I J ≤ I.hi * J.lo ∧ productLower I J ≤ I.hi * J.hi := by
  unfold productLower
  exact ⟨(min_le_left _ _).trans (min_le_left _ _),
    (min_le_left _ _).trans (min_le_right _ _),
    (min_le_right _ _).trans (min_le_left _ _),
    (min_le_right _ _).trans (min_le_right _ _)⟩

lemma le_productUpper (I J : Box) :
    I.lo * J.lo ≤ productUpper I J ∧ I.lo * J.hi ≤ productUpper I J ∧
      I.hi * J.lo ≤ productUpper I J ∧ I.hi * J.hi ≤ productUpper I J := by
  unfold productUpper
  exact ⟨(le_max_left _ _).trans (le_max_left _ _),
    (le_max_right _ _).trans (le_max_left _ _),
    (le_max_left _ _).trans (le_max_right _ _),
    (le_max_right _ _).trans (le_max_right _ _)⟩

def mul (S : ℤ) (hS : 0 < S) (I J : Box) : Box :=
  ⟨floorDiv (productLower I J) S, ceilDiv (productUpper I J) S,
    floor_le_ceil_of_le hS ((productLower_le I J).1.trans (le_productUpper I J).1)⟩

theorem mul_gate (S : ℤ) (hS : 0 < S) (I J : Box) : MulGate S I J (mul S hS I J) := by
  have hf := floor_mul_le (productLower I J) hS
  have hc := le_ceil_mul (productUpper I J) hS
  obtain ⟨hl1, hl2, hl3, hl4⟩ := productLower_le I J
  obtain ⟨hu1, hu2, hu3, hu4⟩ := le_productUpper I J
  exact ⟨⟨hf.trans hl1, hf.trans hl2, hf.trans hl3, hf.trans hl4⟩,
    ⟨hu1.trans hc, hu2.trans hc, hu3.trans hc, hu4.trans hc⟩⟩

theorem mul_contains {S : ℤ} (hS : 0 < S) {I J : Box} {x y : ℝ}
    (hx : Contains S I x) (hy : Contains S J y) : Contains S (mul S hS I J) (x * y) :=
  FixedPointEnclosure.contains_mul hS hx hy (mul_gate S hS I J)

def divInt (I : Box) (d : ℤ) (hd : 0 < d) : Box :=
  ⟨floorDiv I.lo d, ceilDiv I.hi d, floor_le_ceil_of_le hd I.ordered⟩

theorem divInt_gate (I : Box) (d : ℤ) (hd : 0 < d) : DivIntGate d I (divInt I d hd) :=
  ⟨floor_mul_le _ hd, le_ceil_mul _ hd⟩

theorem divInt_contains {S d : ℤ} (hS : 0 < S) (hd : 0 < d) {I : Box} {x : ℝ}
    (hx : Contains S I x) : Contains S (divInt I d hd) (x / (d : ℝ)) :=
  FixedPointEnclosure.contains_div_int hS hd hx (divInt_gate I d hd)

lemma inv_ordered (S : ℤ) (hS : 0 < S) (I : Box) (hI : 0 < I.lo) :
    floorDiv (S * S) I.hi ≤ ceilDiv (S * S) I.lo := by
  have hHi : 0 < I.hi := lt_of_lt_of_le hI I.ordered
  have hlo0 := floor_nonneg hHi (mul_nonneg hS.le hS.le)
  have hm := mul_le_mul_of_nonneg_left I.ordered hlo0
  exact Int.le_of_mul_le_mul_right
    (hm.trans ((floor_mul_le (S * S) hHi).trans (le_ceil_mul (S * S) hI))) hI

def invPos (S : ℤ) (hS : 0 < S) (I : Box) (hI : 0 < I.lo) : Box :=
  ⟨floorDiv (S * S) I.hi, ceilDiv (S * S) I.lo, inv_ordered S hS I hI⟩

theorem invPos_gate (S : ℤ) (hS : 0 < S) (I : Box) (hI : 0 < I.lo) :
    InvGate S I (invPos S hS I hI) :=
  ⟨floor_mul_le _ (lt_of_lt_of_le hI I.ordered), le_ceil_mul _ hI⟩

theorem invPos_contains {S : ℤ} (hS : 0 < S) {I : Box} (hI : 0 < I.lo) {x : ℝ}
    (hx : Contains S I x) : Contains S (invPos S hS I hI) x⁻¹ :=
  FixedPointEnclosure.contains_inv_pos hS hI hx (invPos_gate S hS I hI)

def divPos (S : ℤ) (hS : 0 < S) (I J : Box) (hJ : 0 < J.lo) : Box :=
  mul S hS I (invPos S hS J hJ)

theorem divPos_contains {S : ℤ} (hS : 0 < S) {I J : Box} (hJ : 0 < J.lo) {x y : ℝ}
    (hx : Contains S I x) (hy : Contains S J y) : Contains S (divPos S hS I J hJ) (x / y) := by
  rw [div_eq_mul_inv]
  exact mul_contains hS hx (invPos_contains hS hJ hy)

def squareLower (I : Box) : ℤ :=
  if I.lo ≤ 0 ∧ 0 ≤ I.hi then 0 else min (I.lo * I.lo) (I.hi * I.hi)

def squareUpper (I : Box) : ℤ := max (I.lo * I.lo) (I.hi * I.hi)

lemma squareLower_le_upper (I : Box) : squareLower I ≤ squareUpper I := by
  unfold squareLower squareUpper
  split_ifs
  · exact (mul_self_nonneg I.lo).trans (le_max_left _ _)
  · exact (min_le_left _ _).trans (le_max_left _ _)

def sq (S : ℤ) (hS : 0 < S) (I : Box) : Box :=
  ⟨floorDiv (squareLower I) S, ceilDiv (squareUpper I) S,
    floor_le_ceil_of_le hS (squareLower_le_upper I)⟩

theorem sq_gate (S : ℤ) (hS : 0 < S) (I : Box) : SqGate S I (sq S hS I) := by
  have hf := floor_mul_le (squareLower I) hS
  have hc := le_ceil_mul (squareUpper I) hS
  have hu1 : I.lo ^ 2 ≤ squareUpper I := by
    simpa only [squareUpper, pow_two] using le_max_left (I.lo * I.lo) (I.hi * I.hi)
  have hu2 : I.hi ^ 2 ≤ squareUpper I := by
    simpa only [squareUpper, pow_two] using le_max_right (I.lo * I.lo) (I.hi * I.hi)
  refine ⟨?_, hu1.trans hc, hu2.trans hc⟩
  by_cases hcross : I.lo ≤ 0 ∧ 0 ≤ I.hi
  · left
    change floorDiv (squareLower I) S ≤ 0
    simpa only [squareLower, ite_eq_left hcross, floorDiv, Int.zero_ediv] using (le_refl (0 : ℤ))
  · by_cases hpos : 0 ≤ I.lo
    · right; left
      refine ⟨hpos, hf.trans ?_⟩
      rw [squareLower, ite_eq_right hcross]
      simpa only [pow_two] using min_le_left (I.lo * I.lo) (I.hi * I.hi)
    · right; right
      refine ⟨by omega, hf.trans ?_⟩
      rw [squareLower, ite_eq_right hcross]
      simpa only [pow_two] using min_le_right (I.lo * I.lo) (I.hi * I.hi)

theorem sq_contains {S : ℤ} (hS : 0 < S) {I : Box} {x : ℝ}
    (hx : Contains S I x) : Contains S (sq S hS I) (x ^ 2) :=
  FixedPointEnclosure.contains_sq hS hx (sq_gate S hS I)

def minBox (I J : Box) : Box := ⟨min I.lo J.lo, min I.hi J.hi, min_le_min I.ordered J.ordered⟩

theorem minBox_gate (I J : Box) : MinGate I J (minBox I J) := ⟨le_rfl, le_rfl⟩

theorem minBox_contains {S : ℤ} (hS : 0 < S) {I J : Box} {x y : ℝ}
    (hx : Contains S I x) (hy : Contains S J y) : Contains S (minBox I J) (min x y) :=
  FixedPointEnclosure.contains_min hS hx hy (minBox_gate I J)

def originalPi40 : Box :=
  ⟨31415926535897932384626433832795028841344,
    31415926535897932384626433832795028842596, by decide⟩

/-- Kernel computation of the original I expression 50*PI.sqr(), with its
actual stored PI40 and output endpoints. No enclosure premise proves this
equality: it checks the executable floor/ceil/min/max definitions themselves. -/
theorem original_fifty_pi_square_eq :
    mul (10 ^ 40) (by decide) (rat (10 ^ 40) (by decide) 50 1 (by decide))
      (sq (10 ^ 40) (by decide) originalPi40) =
      (⟨4934802200544679309417245499938075567459650,
        4934802200544679309417245499938075567853000, by decide⟩ : Box) := by decide

end BerryEsseen.FixedPointArithmetic

#print axioms BerryEsseen.FixedPointArithmetic.floor_mul_le
#print axioms BerryEsseen.FixedPointArithmetic.mul_contains
#print axioms BerryEsseen.FixedPointArithmetic.invPos_contains
#print axioms BerryEsseen.FixedPointArithmetic.sq_contains
#print axioms BerryEsseen.FixedPointArithmetic.original_fifty_pi_square_eq
