module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Algebra.Ring.GeomSum

@[expose] public section

/-! 2026-10-29: the actual Machin enclosure used by the integer interval
certificate. A finite geometric identity and its integral prove the even
arctangent remainder, without assuming convergence of a host-computed sum.
All stored endpoints are computable rationals. The final fixed endpoints
are exactly the Python PI interval at scale 10^40. -/

open MeasureTheory Set
open scoped Interval BigOperators

namespace BerryEsseen.RationalPiEnclosure

noncomputable section

def realPartial (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, (-1 : ℝ) ^ k * x ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℝ)

def geometricPolynomial (n : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, (-t ^ 2) ^ k

lemma geometricPolynomial_eq (n : ℕ) (t : ℝ) :
    geometricPolynomial n t = ∑ k ∈ Finset.range n, (-1 : ℝ) ^ k * t ^ (2 * k) := by
  unfold geometricPolynomial
  apply Finset.sum_congr rfl
  intro k _
  rw [neg_pow, ← pow_mul]

lemma continuous_geometricPolynomial (n : ℕ) : Continuous (geometricPolynomial n) := by
  unfold geometricPolynomial
  fun_prop

lemma continuous_remainder (n : ℕ) :
    Continuous (fun t : ℝ => t ^ (2 * n) / (1 + t ^ 2)) := by
  apply Continuous.div (by fun_prop) (by fun_prop)
  intro t
  positivity

lemma integral_geometricPolynomial (n : ℕ) (x : ℝ) :
    (∫ t in (0 : ℝ)..x, geometricPolynomial n t) = realPartial n x := by
  simp_rw [geometricPolynomial_eq]
  rw [intervalIntegral.integral_finsetSum (fun k _ =>
    (show Continuous (fun t : ℝ => (-1 : ℝ) ^ k * t ^ (2 * k)) by fun_prop).intervalIntegrable 0 x)]
  unfold realPartial
  apply Finset.sum_congr rfl
  intro k _
  rw [intervalIntegral.integral_const_mul, integral_pow]
  simp only [zero_pow (by omega : 2 * k + 1 ≠ 0), sub_zero, Nat.cast_add, Nat.cast_one]
  ring

lemma finite_geometric_identity (n : ℕ) (hn : Even n) (t : ℝ) :
    1 / (1 + t ^ 2) = geometricPolynomial n t + t ^ (2 * n) / (1 + t ^ 2) := by
  have hg := geom_sum_mul_neg (-t ^ 2) n
  rw [hn.neg_pow, ← pow_mul, sub_neg_eq_add] at hg
  change geometricPolynomial n t * (1 + t ^ 2) = 1 - t ^ (2 * n) at hg
  field_simp [show 1 + t ^ 2 ≠ 0 by positivity]
  nlinarith only [hg]

/-- An exact finite expansion. Its remainder identity needs no restriction
on x, and no infinite series or asymptotic interpretation. -/
theorem arctan_eq_partial_add_remainder (n : ℕ) (hn : Even n) (x : ℝ) :
    Real.arctan x = realPartial n x + ∫ t in (0 : ℝ)..x, t ^ (2 * n) / (1 + t ^ 2) := by
  calc
    _ = ∫ t in (0 : ℝ)..x, 1 / (1 + t ^ 2) := by
      rw [integral_one_div_one_add_sq, Real.arctan_zero, sub_zero]
    _ = ∫ t in (0 : ℝ)..x, (geometricPolynomial n t + t ^ (2 * n) / (1 + t ^ 2)) :=
      intervalIntegral.integral_congr (fun t _ => finite_geometric_identity n hn t)
    _ = _ := by
      rw [intervalIntegral.integral_add
        ((continuous_geometricPolynomial n).intervalIntegrable 0 x)
        ((continuous_remainder n).intervalIntegrable 0 x), integral_geometricPolynomial]

/-- Even truncation is a lower bound; the next positive term bounds the
entire remainder. This finite-integral proof is valid for every x >= 0. -/
theorem arctan_even_enclosure (n : ℕ) (hn : Even n) (x : ℝ) (hx : 0 ≤ x) :
    realPartial n x ≤ Real.arctan x ∧
      Real.arctan x ≤ realPartial n x + x ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ) := by
  have hr0 : 0 ≤ ∫ t in (0 : ℝ)..x, t ^ (2 * n) / (1 + t ^ 2) := by
    apply intervalIntegral.integral_nonneg hx
    intro t ht
    exact div_nonneg (pow_nonneg ht.1 _) (by positivity)
  have hr1 : (∫ t in (0 : ℝ)..x, t ^ (2 * n) / (1 + t ^ 2)) ≤
      x ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ) := by
    have hm := intervalIntegral.integral_mono_on (μ := volume) hx
      ((continuous_remainder n).intervalIntegrable 0 x)
      ((by fun_prop : Continuous (fun t : ℝ => t ^ (2 * n))).intervalIntegrable 0 x)
      (fun t ht => div_le_self (pow_nonneg ht.1 _) (by nlinarith [sq_nonneg t]))
    rw [integral_pow] at hm
    simpa only [zero_pow (by omega : 2 * n + 1 ≠ 0), sub_zero,
      Nat.cast_add, Nat.cast_one] using hm
  rw [arctan_eq_partial_add_remainder n hn x]
  constructor <;> linarith only [hr0, hr1]

end

/-- Exact rational sum used in atan_reciprocal(d,n). -/
def atanSum (d : ℚ) (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range n, (-1 : ℚ) ^ k /
    (((2 * k + 1 : ℕ) : ℚ) * d ^ (2 * k + 1))

def atanNext (d : ℚ) (n : ℕ) : ℚ :=
  1 / (((2 * n + 1 : ℕ) : ℚ) * d ^ (2 * n + 1))

noncomputable section

lemma cast_atanSum (d : ℚ) (n : ℕ) :
    (atanSum d n : ℝ) = realPartial n (1 / (d : ℝ)) := by
  unfold atanSum realPartial
  push_cast
  apply Finset.sum_congr rfl
  intro k _
  rw [div_pow]
  simp only [div_eq_mul_inv, mul_inv_rev, one_pow]
  ring

lemma cast_atanNext (d : ℚ) (n : ℕ) :
    (atanNext d n : ℝ) = (1 / (d : ℝ)) ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ) := by
  unfold atanNext
  push_cast
  rw [div_pow]
  simp only [div_eq_mul_inv, mul_inv_rev, one_pow]
  ring

theorem atan_reciprocal_even_enclosure (d : ℚ) (hd : 0 < d) (n : ℕ) (hn : Even n) :
    (atanSum d n : ℝ) ≤ Real.arctan (1 / (d : ℝ)) ∧
      Real.arctan (1 / (d : ℝ)) ≤ ((atanSum d n + atanNext d n : ℚ) : ℝ) := by
  have hdp : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hh := arctan_even_enclosure n hn (1 / (d : ℝ)) (by positivity)
  rw [Rat.cast_add, cast_atanSum, cast_atanNext]
  exact hh

theorem atan_reciprocal_64_enclosure (d : ℚ) (hd : 0 < d) :
    (atanSum d 64 : ℝ) ≤ Real.arctan (1 / (d : ℝ)) ∧
      Real.arctan (1 / (d : ℝ)) ≤ ((atanSum d 64 + 1 / (129 * d ^ 129) : ℚ) : ℝ) := by
  simpa only [atanNext, Nat.reduceMul, Nat.reduceAdd, Nat.cast_ofNat] using
    atan_reciprocal_even_enclosure d hd 64 (by decide)

end

def piLower : ℚ := 16 * atanSum 5 64 - 4 * (atanSum 239 64 + atanNext 239 64)
def piUpper : ℚ := 16 * (atanSum 5 64 + atanNext 5 64) - 4 * atanSum 239 64

def fixedLower : ℚ := 31415926535897932384626433832795028841344 / (10 : ℚ) ^ 40
def fixedUpper : ℚ := 31415926535897932384626433832795028842596 / (10 : ℚ) ^ 40

noncomputable section

/-- Machin's identity uses the same actual Real.pi as the analytic kernel. -/
theorem pi_enclosure : (piLower : ℝ) ≤ Real.pi ∧ Real.pi ≤ (piUpper : ℝ) := by
  have h5 := atan_reciprocal_even_enclosure (5 : ℚ) (by norm_num) 64 (by decide)
  have h239 := atan_reciprocal_even_enclosure (239 : ℚ) (by norm_num) 64 (by decide)
  rw [Rat.cast_add] at h5 h239
  norm_num only [Rat.cast_ofNat] at h5 h239
  have hpi : Real.pi = 16 * Real.arctan (1 / (5 : ℝ)) - 4 * Real.arctan (1 / (239 : ℝ)) := by
    have hh := Real.four_mul_arctan_inv_5_sub_arctan_inv_239
    simp only [← one_div] at hh
    linarith only [hh]
  unfold piLower piUpper
  push_cast
  constructor <;> linarith only [h5.1, h5.2, h239.1, h239.2, hpi]

set_option maxRecDepth 5000 in
lemma fixedLower_le_piLower : fixedLower ≤ piLower := by
  norm_num [fixedLower, piLower, atanSum, atanNext, Finset.sum_range_succ]

set_option maxRecDepth 5000 in
lemma piUpper_le_fixedUpper : piUpper ≤ fixedUpper := by
  norm_num [fixedUpper, piUpper, atanSum, atanNext, Finset.sum_range_succ]

/-- Exactly the Python PI endpoints at scale 10^40, now certified for
the actual mathematical constant rather than only for rational arithmetic. -/
theorem pi_fixed_enclosure : (fixedLower : ℝ) ≤ Real.pi ∧ Real.pi ≤ (fixedUpper : ℝ) := by
  have hl : (fixedLower : ℝ) ≤ (piLower : ℝ) := by exact_mod_cast fixedLower_le_piLower
  have hu : (piUpper : ℝ) ≤ (fixedUpper : ℝ) := by exact_mod_cast piUpper_le_fixedUpper
  exact ⟨hl.trans pi_enclosure.1, pi_enclosure.2.trans hu⟩

end

end BerryEsseen.RationalPiEnclosure

#print axioms BerryEsseen.RationalPiEnclosure.arctan_even_enclosure
#print axioms BerryEsseen.RationalPiEnclosure.atan_reciprocal_64_enclosure
#print axioms BerryEsseen.RationalPiEnclosure.pi_enclosure
#print axioms BerryEsseen.RationalPiEnclosure.pi_fixed_enclosure
