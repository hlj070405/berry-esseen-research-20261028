module

public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-! 2026-10-29: exact rational expressions underlying the certificate's
exp_neg routine.  Its positive series includes indices 0 through 48, the
first omitted term has index 49, and the geometric tail ratio is y/50.
The real inequalities below are proved from Mathlib's actual exponential
series and factorial growth.  No numerical or transcendental oracle is used.
Only the analytic enclosure and rational-to-real identities are asserted;
fixed-point rounding in a consuming certificate remains a separate step. -/

namespace BerryEsseen.RationalExpEnclosure

open Finset

/-- Computable exact rational positive Taylor polynomial, including index m. -/
def taylorRat (m : ℕ) (y : ℚ) : ℚ :=
  ∑ k ∈ range (m + 1), y ^ k / (k.factorial : ℚ)

def tailRat (m : ℕ) (y : ℚ) : ℚ :=
  (y ^ (m + 1) / ((m + 1).factorial : ℚ)) / (1 - y / ((m + 2 : ℕ) : ℚ))

def upperRat (m : ℕ) (y : ℚ) : ℚ := taylorRat m y + tailRat m y

def expNegLowerRat (m : ℕ) (x : ℚ) : ℚ := (upperRat m (x / 32) ^ 32)⁻¹

def expNegUpperRat (m : ℕ) (x : ℚ) : ℚ := (taylorRat m (x / 32) ^ 32)⁻¹

noncomputable section

def taylor (m : ℕ) (y : ℝ) : ℝ := ∑ k ∈ range (m + 1), y ^ k / (k.factorial : ℝ)

def tail (m : ℕ) (y : ℝ) : ℝ :=
  (y ^ (m + 1) / ((m + 1).factorial : ℝ)) / (1 - y / ((m + 2 : ℕ) : ℝ))

def upper (m : ℕ) (y : ℝ) : ℝ := taylor m y + tail m y

def expNegLower (m : ℕ) (x : ℝ) : ℝ := (upper m (x / 32) ^ 32)⁻¹

def expNegUpper (m : ℕ) (x : ℝ) : ℝ := (taylor m (x / 32) ^ 32)⁻¹

@[simp] theorem cast_taylorRat (m : ℕ) (y : ℚ) : (taylorRat m y : ℝ) = taylor m y := by
  simp only [taylorRat, taylor, Rat.cast_sum, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast]

@[simp] theorem cast_tailRat (m : ℕ) (y : ℚ) : (tailRat m y : ℝ) = tail m y := by
  simp only [tailRat, tail, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast,
    Rat.cast_sub, Rat.cast_one]

@[simp] theorem cast_upperRat (m : ℕ) (y : ℚ) : (upperRat m y : ℝ) = upper m y := by
  simp only [upperRat, upper, Rat.cast_add, cast_taylorRat, cast_tailRat]

@[simp] theorem cast_expNegLowerRat (m : ℕ) (x : ℚ) :
    (expNegLowerRat m x : ℝ) = expNegLower m x := by
  simp only [expNegLowerRat, expNegLower, Rat.cast_inv, Rat.cast_pow,
    cast_upperRat, Rat.cast_div, Rat.cast_ofNat]

@[simp] theorem cast_expNegUpperRat (m : ℕ) (x : ℚ) :
    (expNegUpperRat m x : ℝ) = expNegUpper m x := by
  simp only [expNegUpperRat, expNegUpper, Rat.cast_inv, Rat.cast_pow,
    cast_taylorRat, Rat.cast_div, Rat.cast_ofNat]

theorem taylor_le_exp (m : ℕ) (y : ℝ) (hy : 0 ≤ y) : taylor m y ≤ Real.exp y :=
  Real.sum_le_exp_of_nonneg hy (m + 1)

theorem one_le_taylor (m : ℕ) (y : ℝ) (hy : 0 ≤ y) : 1 ≤ taylor m y := by
  unfold taylor
  calc
    (1 : ℝ) = y ^ 0 / (Nat.factorial 0 : ℝ) := by norm_num
    _ ≤ ∑ k ∈ range (m + 1), y ^ k / (k.factorial : ℝ) :=
      Finset.single_le_sum (f := fun k : ℕ => y ^ k / (k.factorial : ℝ))
        (s := range (m + 1)) (a := 0)
        (fun k _ => div_nonneg (pow_nonneg hy k) (Nat.cast_nonneg _))
        (mem_range.mpr (Nat.succ_pos m))

lemma tail_ratio_nonneg (m : ℕ) (y : ℝ) (hy : 0 ≤ y) :
    0 ≤ y / ((m + 2 : ℕ) : ℝ) := by positivity

lemma tail_ratio_lt_one (m : ℕ) (y : ℝ) (hy : y ≤ 1) :
    y / ((m + 2 : ℕ) : ℝ) < 1 := by
  have hn : (1 : ℝ) < (m + 2 : ℕ) := by exact_mod_cast (by omega : 1 < m + 2)
  exact (div_lt_one (by positivity : (0 : ℝ) < (m + 2 : ℕ))).mpr (hy.trans_lt hn)

theorem tail_nonneg (m : ℕ) (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) : 0 ≤ tail m y := by
  unfold tail
  exact div_nonneg (by positivity) (sub_pos.mpr (tail_ratio_lt_one m y hy1)).le

/-- Factorial growth makes every omitted term no larger than the first
omitted term times a power of the common geometric ratio. -/
lemma term_tail_le_geometric (n k : ℕ) (y : ℝ) (hy : 0 ≤ y) :
    y ^ (k + n) / ((k + n).factorial : ℝ) ≤
      (y ^ n / (n.factorial : ℝ)) * (y / ((n + 1 : ℕ) : ℝ)) ^ k := by
  have hfac : (n.factorial : ℝ) * ((n + 1 : ℕ) : ℝ) ^ k ≤ ((n + k).factorial : ℝ) := by
    exact_mod_cast (Nat.factorial_mul_pow_le_factorial (m := n) (n := k))
  calc
    _ = y ^ (n + k) / ((n + k).factorial : ℝ) := by rw [Nat.add_comm k n]
    _ ≤ y ^ (n + k) / ((n.factorial : ℝ) * ((n + 1 : ℕ) : ℝ) ^ k) :=
      div_le_div_of_nonneg_left (pow_nonneg hy _) (by positivity) hfac
    _ = _ := by simp only [pow_add, div_eq_mul_inv, mul_inv]; ring

theorem exp_le_upper (m : ℕ) (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) : Real.exp y ≤ upper m y := by
  have he : HasSum (fun k : ℕ => y ^ k / (k.factorial : ℝ)) (Real.exp y) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp y
  have ht : HasSum (fun k : ℕ => y ^ (k + (m + 1)) / ((k + (m + 1)).factorial : ℝ))
      (Real.exp y - taylor m y) := by
    exact (hasSum_nat_add_iff' (m + 1)).mpr he
  have hg := (hasSum_geometric_of_lt_one (tail_ratio_nonneg m y hy0)
    (tail_ratio_lt_one m y hy1)).mul_left (y ^ (m + 1) / ((m + 1).factorial : ℝ))
  have hle := hasSum_le (fun k => by
    simpa only [Nat.add_assoc, Nat.reduceAdd] using term_tail_le_geometric (m + 1) k y hy0) ht hg
  unfold upper tail
  change Real.exp y ≤ taylor m y +
    (y ^ (m + 1) / ((m + 1).factorial : ℝ)) / (1 - y / ((m + 2 : ℕ) : ℝ))
  rw [div_eq_mul_inv]
  linarith only [hle]

theorem exp_enclosure (m : ℕ) (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    taylor m y ≤ Real.exp y ∧ Real.exp y ≤ upper m y :=
  ⟨taylor_le_exp m y hy0, exp_le_upper m y hy0 hy1⟩

theorem exp_neg_enclosure (m : ℕ) (x : ℝ) (hx0 : 0 ≤ x) (hx32 : x ≤ 32) :
    expNegLower m x ≤ Real.exp (-x) ∧ Real.exp (-x) ≤ expNegUpper m x := by
  have hy0 : 0 ≤ x / 32 := by positivity
  have hy1 : x / 32 ≤ 1 := (div_le_one (by norm_num : (0 : ℝ) < 32)).mpr hx32
  have hs := taylor_le_exp m (x / 32) hy0
  have hu := exp_le_upper m (x / 32) hy0 hy1
  have hsp : 0 < taylor m (x / 32) := lt_of_lt_of_le zero_lt_one (one_le_taylor m (x / 32) hy0)
  have hex : Real.exp x = Real.exp (x / 32) ^ 32 := by
    rw [← Real.exp_nat_mul (x / 32) 32]
    congr 1
    ring
  have hspow := pow_le_pow_left₀ hsp.le hs 32
  have hupow := pow_le_pow_left₀ (Real.exp_pos (x / 32)).le hu 32
  rw [← hex] at hspow hupow
  constructor
  · have hi := one_div_le_one_div_of_le (Real.exp_pos x) hupow
    simpa only [expNegLower, Real.exp_neg, one_div] using hi
  · have hi := one_div_le_one_div_of_le (pow_pos hsp 32) hspow
    simpa only [expNegUpper, Real.exp_neg, one_div] using hi

theorem exp48_enclosure (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    taylor 48 y ≤ Real.exp y ∧
      Real.exp y ≤ taylor 48 y + (y ^ 49 / (Nat.factorial 49 : ℝ)) / (1 - y / 50) := by
  simpa only [upper, tail, Nat.reduceAdd, Nat.cast_ofNat] using exp_enclosure 48 y hy0 hy1

theorem exp_neg48_enclosure (x : ℝ) (hx0 : 0 ≤ x) (hx32 : x ≤ 32) :
    expNegLower 48 x ≤ Real.exp (-x) ∧ Real.exp (-x) ≤ expNegUpper 48 x :=
  exp_neg_enclosure 48 x hx0 hx32

theorem rational_exp_neg48_enclosure (x : ℚ) (hx0 : 0 ≤ x) (hx32 : x ≤ 32) :
    (expNegLowerRat 48 x : ℝ) ≤ Real.exp (-(x : ℝ)) ∧
      Real.exp (-(x : ℝ)) ≤ (expNegUpperRat 48 x : ℝ) := by
  rw [cast_expNegLowerRat, cast_expNegUpperRat]
  exact exp_neg48_enclosure x (by exact_mod_cast hx0) (by exact_mod_cast hx32)

/-- Endpoint evaluation also encloses an entire input interval, using the
antitonicity of the true exponential of the negative argument. -/
theorem exp_neg48_interval_enclosure (lo hi x : ℝ) (hlo : 0 ≤ lo) (horder : lo ≤ hi)
    (hhi : hi ≤ 32) (hx : x ∈ Set.Icc lo hi) :
    expNegLower 48 hi ≤ Real.exp (-x) ∧ Real.exp (-x) ≤ expNegUpper 48 lo := by
  have hl := exp_neg48_enclosure lo hlo (horder.trans hhi)
  have hh := exp_neg48_enclosure hi (hlo.trans horder) hhi
  exact ⟨hh.1.trans (Real.exp_le_exp.mpr (neg_le_neg hx.2)),
    (Real.exp_le_exp.mpr (neg_le_neg hx.1)).trans hl.2⟩

theorem rational_exp_neg48_interval_enclosure (lo hi : ℚ) (x : ℝ)
    (hlo : 0 ≤ lo) (horder : lo ≤ hi) (hhi : hi ≤ 32) (hx : x ∈ Set.Icc (lo : ℝ) (hi : ℝ)) :
    (expNegLowerRat 48 hi : ℝ) ≤ Real.exp (-x) ∧ Real.exp (-x) ≤ (expNegUpperRat 48 lo : ℝ) := by
  rw [cast_expNegLowerRat, cast_expNegUpperRat]
  exact exp_neg48_interval_enclosure lo hi x (by exact_mod_cast hlo)
    (by exact_mod_cast horder) (by exact_mod_cast hhi) hx

/-- Truncation beyond 32 uses a genuine monotonicity upper bound, without
extrapolating a Taylor enclosure outside its proved [0,32] domain. -/
theorem exp_neg_le_exp_neg32 (x : ℝ) (hx : 32 ≤ x) : Real.exp (-x) ≤ Real.exp (-32) :=
  Real.exp_le_exp.mpr (neg_le_neg hx)

theorem exp_neg_le_truncated_upper (x : ℝ) (hx : 32 ≤ x) :
    Real.exp (-x) ≤ expNegUpper 48 32 :=
  (exp_neg_le_exp_neg32 x hx).trans (exp_neg48_enclosure 32 (by norm_num) le_rfl).2

end

end BerryEsseen.RationalExpEnclosure

#print axioms BerryEsseen.RationalExpEnclosure.exp_le_upper
#print axioms BerryEsseen.RationalExpEnclosure.exp48_enclosure
#print axioms BerryEsseen.RationalExpEnclosure.exp_neg48_enclosure
#print axioms BerryEsseen.RationalExpEnclosure.rational_exp_neg48_enclosure
#print axioms BerryEsseen.RationalExpEnclosure.rational_exp_neg48_interval_enclosure
#print axioms BerryEsseen.RationalExpEnclosure.exp_neg_le_truncated_upper
