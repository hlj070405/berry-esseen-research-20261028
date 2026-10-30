module

public import BerryEsseen.N2RectangleBernstein

@[expose] public section

/-! 2026-10-29: generic power-polynomial identities for the original
fifteen-coefficient n2 majorant. Both polynomial interfaces use the same c. -/

noncomputable section

open scoped BigOperators

namespace BerryEsseen.N2MajorantPolynomials

open N2MomentMajorant N2RectangleBernstein

/-- The exact lexicographic PAIR order of the original fifteen rational strings. -/
def sourcePair : Fin 15 → Index :=
  ![⟨(0, 0), by decide⟩, ⟨(0, 1), by decide⟩, ⟨(0, 2), by decide⟩,
    ⟨(0, 3), by decide⟩, ⟨(0, 4), by decide⟩, ⟨(1, 1), by decide⟩,
    ⟨(1, 2), by decide⟩, ⟨(1, 3), by decide⟩, ⟨(1, 4), by decide⟩,
    ⟨(2, 2), by decide⟩, ⟨(2, 3), by decide⟩, ⟨(2, 4), by decide⟩,
    ⟨(3, 3), by decide⟩, ⟨(3, 4), by decide⟩, ⟨(4, 4), by decide⟩]

def toVector (c : Coefficients) (k : Fin 15) : ℚ := c (sourcePair k)

def fromVector (v : Fin 15 → ℚ) : Coefficients := fun ij =>
  match ij.val.1.val, ij.val.2.val with
  | 0, 0 => v 0
  | 0, 1 => v 1
  | 0, 2 => v 2
  | 0, 3 => v 3
  | 0, 4 => v 4
  | 1, 1 => v 5
  | 1, 2 => v 6
  | 1, 3 => v 7
  | 1, 4 => v 8
  | 2, 2 => v 9
  | 2, 3 => v 10
  | 2, 4 => v 11
  | 3, 3 => v 12
  | 3, 4 => v 13
  | 4, 4 => v 14
  | _, _ => 0

theorem fromVector_sourcePair (v : Fin 15 → ℚ) (k : Fin 15) :
    fromVector v (sourcePair k) = v k := by
  fin_cases k <;> rfl

theorem toVector_fromVector (v : Fin 15 → ℚ) : toVector (fromVector v) = v := by
  funext k
  exact fromVector_sourcePair v k

theorem fromVector_toVector (c : Coefficients) : fromVector (toVector c) = c := by
  funext ij
  rcases ij with ⟨⟨i, j⟩, hij⟩
  have hvals : i.val ≤ j.val := hij
  fin_cases i <;> fin_cases j <;> simp_all [fromVector, toVector, sourcePair]

private theorem index_univ : (Finset.univ : Finset Index) =
    {sourcePair 0, sourcePair 1, sourcePair 2, sourcePair 3, sourcePair 4,
      sourcePair 5, sourcePair 6, sourcePair 7, sourcePair 8, sourcePair 9,
      sourcePair 10, sourcePair 11, sourcePair 12, sourcePair 13, sourcePair 14} := by decide

/-- All unlisted entries vanish; the square feature has mean one. -/
def expectedPower (c : Coefficients) : Power :=
  let v := toVector c
  ![![v 0 + 2 * v 2 + v 9, 2 * (v 4 + v 11), v 14, 0],
    ![2 * (v 3 + v 10), 2 * v 13, 0, 0],
    ![v 12, 0, 0, 0],
    ![0, 0, 0, 0]]

theorem expectedPower_representation (c : Coefficients) (γ ρ : ℝ) :
    evalPower (expectedPower c) γ ρ = expected c γ ρ := by
  classical
  unfold expected
  rw [index_univ]
  norm_num [evalPower, expectedPower, toVector, sourcePair,
    expectedTerm, momentVector, Fin.sum_univ_succ]
  ring

/-- Substitution of the two absolute-cubic signs, with epsilon added only at (0,0). -/
def orthantPower (c : Coefficients) (sx sy ε : ℚ) : Power :=
  let v := toVector c
  ![![v 0 + ε, v 1, v 2, v 3 + sy * v 4],
    ![v 1, v 5, v 6, v 7 + sy * v 8],
    ![v 2, v 6, v 9, v 10 + sy * v 11],
    ![v 3 + sx * v 4, v 7 + sx * v 8, v 10 + sx * v 11,
      v 12 + (sx + sy) * v 13 + sx * sy * v 14]]

theorem majorant_eq_orthantPower (c : Coefficients) (sx sy ε : ℚ) (x y : ℝ)
    (hx : |x| ^ 3 = (sx : ℝ) * x ^ 3) (hy : |y| ^ 3 = (sy : ℝ) * y ^ 3) :
    majorant c x y + (ε : ℝ) = evalPower (orthantPower c sx sy ε) x y := by
  classical
  unfold majorant
  rw [index_univ]
  norm_num [evalPower, orthantPower, toVector, sourcePair, sourceTerm, basis,
    Fin.sum_univ_succ, hx, hy]
  ring

private lemma abs_cube_nonpos (x : ℝ) (hx : x ≤ 0) :
    |x| ^ 3 = ((-1 : ℚ) : ℝ) * x ^ 3 := by
  calc
    |x| ^ 3 = (-x) ^ 3 := by rw [abs_of_nonpos hx]
    _ = (-1 : ℝ) * x ^ 3 := by ring
    _ = _ := by norm_num

private lemma abs_cube_nonneg (x : ℝ) (hx : 0 ≤ x) :
    |x| ^ 3 = ((1 : ℚ) : ℝ) * x ^ 3 := by
  calc
    |x| ^ 3 = x ^ 3 := by rw [abs_of_nonneg hx]
    _ = _ := by norm_num

theorem majorant_eq_neg_neg (c : Coefficients) (ε : ℚ) (x y : ℝ)
    (hx : x ≤ 0) (hy : y ≤ 0) :
    majorant c x y + (ε : ℝ) = evalPower (orthantPower c (-1) (-1) ε) x y :=
  majorant_eq_orthantPower c (-1) (-1) ε x y (abs_cube_nonpos x hx) (abs_cube_nonpos y hy)

theorem majorant_eq_neg_pos (c : Coefficients) (ε : ℚ) (x y : ℝ)
    (hx : x ≤ 0) (hy : 0 ≤ y) :
    majorant c x y + (ε : ℝ) = evalPower (orthantPower c (-1) 1 ε) x y :=
  majorant_eq_orthantPower c (-1) 1 ε x y (abs_cube_nonpos x hx) (abs_cube_nonneg y hy)

theorem majorant_eq_pos_neg (c : Coefficients) (ε : ℚ) (x y : ℝ)
    (hx : 0 ≤ x) (hy : y ≤ 0) :
    majorant c x y + (ε : ℝ) = evalPower (orthantPower c 1 (-1) ε) x y :=
  majorant_eq_orthantPower c 1 (-1) ε x y (abs_cube_nonneg x hx) (abs_cube_nonpos y hy)

theorem majorant_eq_pos_pos (c : Coefficients) (ε : ℚ) (x y : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    majorant c x y + (ε : ℝ) = evalPower (orthantPower c 1 1 ε) x y :=
  majorant_eq_orthantPower c 1 1 ε x y (abs_cube_nonneg x hx) (abs_cube_nonneg y hy)

def pricePower (c : Coefficients) (R L : ℚ) (i j : Fin 4) : ℚ :=
  -expectedPower c i j +
    (if i = 0 ∧ j = 0 then R else if i = 0 ∧ j = 1 then L else 0)

theorem pricePower_representation (c : Coefficients) (R L : ℚ) (γ ρ : ℝ) :
    evalPower (pricePower c R L) γ ρ = (R : ℝ) + (L : ℝ) * ρ - expected c γ ρ := by
  rw [← expectedPower_representation]
  norm_num [evalPower, pricePower, Fin.sum_univ_succ]
  ring

end BerryEsseen.N2MajorantPolynomials

#print axioms BerryEsseen.N2MajorantPolynomials.fromVector_sourcePair
#print axioms BerryEsseen.N2MajorantPolynomials.fromVector_toVector
#print axioms BerryEsseen.N2MajorantPolynomials.expectedPower_representation
#print axioms BerryEsseen.N2MajorantPolynomials.majorant_eq_orthantPower
#print axioms BerryEsseen.N2MajorantPolynomials.majorant_eq_neg_neg
#print axioms BerryEsseen.N2MajorantPolynomials.majorant_eq_neg_pos
#print axioms BerryEsseen.N2MajorantPolynomials.majorant_eq_pos_neg
#print axioms BerryEsseen.N2MajorantPolynomials.majorant_eq_pos_pos
#print axioms BerryEsseen.N2MajorantPolynomials.pricePower_representation
