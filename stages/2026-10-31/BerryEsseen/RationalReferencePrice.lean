module

public import BerryEsseen.DoubleBinomialReference
public import BerryEsseen.StopLossShape
public import Mathlib.Data.Rat.Cast.Order

@[expose] public section

/-! 2026-10-29: Exact rational prices of the actual two-group reference law.
The measure identity and finite integration theorem are inherited from
DoubleBinomialReference; rational evaluation is connected by cast lemmas. -/

namespace BerryEsseen.RationalReferencePrice

open MeasureTheory
open scoped BigOperators

def countWeight (b z : ℚ) (n : ℕ) (j : Fin (n + 1)) : ℚ :=
  (n.choose (j : ℕ) : ℚ) * (z / (b ^ 2 + z)) ^ (j : ℕ) *
    (b ^ 2 / (b ^ 2 + z)) ^ (n - (j : ℕ))

def countAtom (b z : ℚ) (n : ℕ) (j : Fin (n + 1)) : ℚ :=
  (j : ℕ) * b - ((n - (j : ℕ) : ℕ) : ℚ) * z / b

/-- Factoring the outer binomial weight avoids recomputing it at every
inner atom. The two groups keep their own caps and variances. -/
def rationalPrice (b0 z0 : ℚ) (n0 : ℕ) (b1 z1 : ℚ) (n1 : ℕ) (A h : ℚ) : ℚ :=
  (∑ j : Fin (n0 + 1), countWeight b0 z0 n0 j *
    (∑ l : Fin (n1 + 1), countWeight b1 z1 n1 l *
      (max (countAtom b0 z0 n0 j + countAtom b1 z1 n1 l - A + h) 0) ^ 2)) / (4 * h)

theorem cast_countWeight (b z : ℚ) (n : ℕ) (j : Fin (n + 1))
    (hb : 0 < b) (hz : 0 ≤ z) :
    (countWeight b z n j : ℝ) =
      (DoubleBinomialReference.countWeight (b : ℝ) (z : ℝ) n j : ℝ) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hzR : (0 : ℝ) ≤ z := by exact_mod_cast hz
  rw [DoubleBinomialReference.coe_countWeight (b : ℝ) (z : ℝ) n j hbR hzR]
  simp only [countWeight, Rat.cast_mul, Rat.cast_pow, Rat.cast_div, Rat.cast_add,
    Rat.cast_natCast, Rat.cast_ofNat]

theorem cast_countAtom (b z : ℚ) (n : ℕ) (j : Fin (n + 1)) :
    (countAtom b z n j : ℝ) = DoubleBinomialReference.countAtom (b : ℝ) (z : ℝ) n j := by
  simp only [countAtom, DoubleBinomialReference.countAtom, Rat.cast_sub,
    Rat.cast_mul, Rat.cast_div, Rat.cast_natCast]

private theorem cast_sum {ι : Type*} [Fintype ι] (f : ι → ℚ) :
    ((∑ i, f i : ℚ) : ℝ) = ∑ i, (f i : ℝ) :=
  map_sum (Rat.castHom ℝ) f Finset.univ

/-- The rational sum equals the actual integral price; max, choose, both
binomial probabilities, and both atom locations are transported exactly. -/
theorem price_eq_cast (b0 z0 : ℚ) (n0 : ℕ) (b1 z1 : ℚ) (n1 : ℕ) (A h : ℚ)
    (hb0 : 0 < b0) (hz0 : 0 ≤ z0) (hb1 : 0 < b1) (hz1 : 0 ≤ z1) :
    StopLossShape.price (DoubleBinomialReference.law (b0 : ℝ) (z0 : ℝ) n0
      (b1 : ℝ) (z1 : ℝ) n1) (A : ℝ) (h : ℝ) =
      (rationalPrice b0 z0 n0 b1 z1 n1 A h : ℝ) := by
  have hb0R : (0 : ℝ) < b0 := by exact_mod_cast hb0
  have hz0R : (0 : ℝ) ≤ z0 := by exact_mod_cast hz0
  have hb1R : (0 : ℝ) < b1 := by exact_mod_cast hb1
  have hz1R : (0 : ℝ) ≤ z1 := by exact_mod_cast hz1
  unfold StopLossShape.price rationalPrice
  rw [DoubleBinomialReference.integral_law _ _ _ _ _ _ hb0R hz0R hb1R hz1R,
    Fintype.sum_prod_type, Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat]
  congr 1
  rw [cast_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Rat.cast_mul, cast_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  have hw0 := cast_countWeight b0 z0 n0 j hb0 hz0
  have hw1 := cast_countWeight b1 z1 n1 l hb1 hz1
  have ha0 := cast_countAtom b0 z0 n0 j
  have ha1 := cast_countAtom b1 z1 n1 l
  simp only [DoubleBinomialReference.weights, DoubleBinomialReference.atom,
    NNReal.coe_mul, Rat.cast_mul, Rat.cast_pow, Rat.cast_max, Rat.cast_add,
    Rat.cast_sub, Rat.cast_zero, hw0, hw1, ha0, ha1]
  ring

theorem Q_le_rationalPrice (b0 z0 : ℚ) (n0 : ℕ) (b1 z1 : ℚ) (n1 : ℕ) (A h : ℚ)
    (hb0 : 0 < b0) (hz0 : 0 ≤ z0) (hb1 : 0 < b1) (hz1 : 0 ≤ z1) (hh : 0 < h) :
    StopLossShape.Q (DoubleBinomialReference.law (b0 : ℝ) (z0 : ℝ) n0
      (b1 : ℝ) (z1 : ℝ) n1) (A : ℝ) ≤
      (rationalPrice b0 z0 n0 b1 z1 n1 A h : ℝ) := by
  rw [← price_eq_cast b0 z0 n0 b1 z1 n1 A h hb0 hz0 hb1 hz1]
  exact StopLossShape.Q_le_price _ _ _ (by exact_mod_cast hh)

/-- A closed rational inequality can be proved by decide +kernel and then
consumed as an upper bound on the same actual real reference-law Q. -/
theorem Q_le_of_rational_bound (b0 z0 : ℚ) (n0 : ℕ) (b1 z1 : ℚ) (n1 : ℕ) (A h U : ℚ)
    (hb0 : 0 < b0) (hz0 : 0 ≤ z0) (hb1 : 0 < b1) (hz1 : 0 ≤ z1) (hh : 0 < h)
    (hbound : rationalPrice b0 z0 n0 b1 z1 n1 A h ≤ U) :
    StopLossShape.Q (DoubleBinomialReference.law (b0 : ℝ) (z0 : ℝ) n0
      (b1 : ℝ) (z1 : ℝ) n1) (A : ℝ) ≤ (U : ℝ) := by
  exact (Q_le_rationalPrice b0 z0 n0 b1 z1 n1 A h hb0 hz0 hb1 hz1 hh).trans
    (Rat.cast_le.mpr hbound)

end BerryEsseen.RationalReferencePrice

#print axioms BerryEsseen.RationalReferencePrice.cast_countWeight
#print axioms BerryEsseen.RationalReferencePrice.cast_countAtom
#print axioms BerryEsseen.RationalReferencePrice.price_eq_cast
#print axioms BerryEsseen.RationalReferencePrice.Q_le_rationalPrice
#print axioms BerryEsseen.RationalReferencePrice.Q_le_of_rational_bound
