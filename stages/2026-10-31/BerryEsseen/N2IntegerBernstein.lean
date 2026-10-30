module

public import BerryEsseen.N2BernsteinFast

@[expose] public section

/-! 2026-10-29: denominator-cleared bicubic Bernstein evaluation.
All numerator construction is integer arithmetic. The equality with the
same actual rational power polynomial is proved first for each univariate
transform entry and then by finite summation. No stored Bernstein array,
host result, or changed box/threshold is introduced. -/

open scoped BigOperators

namespace BerryEsseen.N2IntegerBernstein

open N2RectangleBernstein N2BernsteinFast

abbrev IntPower := Fin 4 → Fin 4 → ℤ

def rationalPower (A : IntPower) (D : ℕ) : Power := fun i j => (A i j : ℚ) / (D : ℚ)

def coord (v : ℤ) (S : ℕ) : ℚ := (v : ℚ) / (S : ℚ)

/-- The exact 3*S^3 multiple of the original univariate transform. -/
def transformNum (S : ℕ) (L U : ℤ) (i p : Fin 4) : ℤ :=
  match i.val, p.val with
  | 0, 0 => 3 * (S : ℤ) ^ 3
  | 0, 1 => 3 * (S : ℤ) ^ 2 * L
  | 0, 2 => 3 * (S : ℤ) * L ^ 2
  | 0, _ => 3 * L ^ 3
  | 1, 0 => 3 * (S : ℤ) ^ 3
  | 1, 1 => (S : ℤ) ^ 2 * (2 * L + U)
  | 1, 2 => (S : ℤ) * (L ^ 2 + 2 * L * U)
  | 1, _ => 3 * L ^ 2 * U
  | 2, 0 => 3 * (S : ℤ) ^ 3
  | 2, 1 => (S : ℤ) ^ 2 * (L + 2 * U)
  | 2, 2 => (S : ℤ) * (2 * L * U + U ^ 2)
  | 2, _ => 3 * L * U ^ 2
  | _, 0 => 3 * (S : ℤ) ^ 3
  | _, 1 => 3 * (S : ℤ) ^ 2 * U
  | _, 2 => 3 * (S : ℤ) * U ^ 2
  | _, _ => 3 * U ^ 3

def bernsteinNum (A : IntPower) (S : ℕ) (lx ux ly uy : ℤ) (i j : Fin 4) : ℤ :=
  let tx := transformNum S lx ux i
  let ty := transformNum S ly uy j
  (A 0 0 * ty 0 + A 0 1 * ty 1 + A 0 2 * ty 2 + A 0 3 * ty 3) * tx 0 +
    (A 1 0 * ty 0 + A 1 1 * ty 1 + A 1 2 * ty 2 + A 1 3 * ty 3) * tx 1 +
    (A 2 0 * ty 0 + A 2 1 * ty 1 + A 2 2 * ty 2 + A 2 3 * ty 3) * tx 2 +
    (A 3 0 * ty 0 + A 3 1 * ty 1 + A 3 2 * ty 2 + A 3 3 * ty 3) * tx 3

/-- Unrolling the fixed four-term sums changes only their evaluation cost. -/
theorem bernsteinNum_eq_sum (A : IntPower) (S : ℕ) (lx ux ly uy : ℤ) (i j : Fin 4) :
    bernsteinNum A S lx ux ly uy i j =
      ∑ p : Fin 4, ∑ q : Fin 4,
        A p q * transformNum S lx ux i p * transformNum S ly uy j q := by
  simp only [bernsteinNum, Fin.sum_univ_four]
  ring

def commonDen (D S : ℕ) : ℕ := 9 * D * S ^ 6

def planeDen (S : ℕ) : ℕ := 60 * S

def planeNum (S : ℕ) (lx ux ly uy t : ℤ) (i j : Fin 4) : ℤ :=
  60 * (lx + ly) + 20 * (i.val : ℤ) * (ux - lx) +
    20 * (j.val : ℤ) * (uy - ly) - 3 * (S : ℤ) * t

theorem commonDen_pos (D S : ℕ) (hD : 0 < D) (hS : 0 < S) : 0 < commonDen D S := by
  unfold commonDen
  positivity

theorem planeDen_pos (S : ℕ) (hS : 0 < S) : 0 < planeDen S := by
  unfold planeDen
  positivity

theorem coord_strictMono (S : ℕ) (hS : 0 < S) : StrictMono (fun v : ℤ => coord v S) := by
  intro L U hLU
  unfold coord
  apply div_lt_div_of_pos_right _ (show 0 < (S : ℚ) by exact_mod_cast hS)
  exact_mod_cast hLU

theorem transformCoeff_eq_num (S : ℕ) (hS : 0 < S) (L U : ℤ) (i p : Fin 4) :
    transformCoeff (coord L S) (coord U S) i p =
      (transformNum S L U i p : ℚ) / (3 * (S : ℚ) ^ 3) := by
  have hs0 : (S : ℚ) ≠ 0 := by exact_mod_cast hS.ne'
  fin_cases i <;> fin_cases p <;>
    norm_num [transformCoeff, transformNum, coord] <;>
    push_cast <;> field_simp [hs0] <;> ring

private theorem commonDen_factor (D S : ℕ) :
    (commonDen D S : ℚ) = (D : ℚ) * (3 * (S : ℚ) ^ 3) * (3 * (S : ℚ) ^ 3) := by
  unfold commonDen
  push_cast
  ring

/-- The same fast coefficients now have one positive common denominator.
The incoming power polynomial is exactly rationalPower A D. -/
theorem fastBoxCoeff_eq_num (A : IntPower) (D S : ℕ) (hD : 0 < D) (hS : 0 < S)
    (lx ux ly uy : ℤ) (i j : Fin 4) :
    fastBoxCoeff (rationalPower A D) (coord lx S) (coord ux S) (coord ly S) (coord uy S) i j =
      (bernsteinNum A S lx ux ly uy i j : ℚ) / (commonDen D S : ℚ) := by
  have hd0 : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  have hs0 : (S : ℚ) ≠ 0 := by exact_mod_cast hS.ne'
  calc
    _ = ∑ p : Fin 4, ∑ q : Fin 4,
        ((A p q : ℚ) * (transformNum S lx ux i p : ℚ) * (transformNum S ly uy j q : ℚ)) /
          (commonDen D S : ℚ) := by
      unfold fastBoxCoeff
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro q _
      rw [rationalPower, transformCoeff_eq_num S hS, transformCoeff_eq_num S hS,
        commonDen_factor]
      field_simp [hd0, hs0] <;> ring
    _ = _ := by
      simp_rw [← Finset.sum_div]
      rw [bernsteinNum_eq_sum]
      push_cast <;> rfl

theorem planeCoeff_eq_num (S : ℕ) (hS : 0 < S) (lx ux ly uy t : ℤ) (i j : Fin 4) :
    planeCoeff (coord lx S) (coord ux S) (coord ly S) (coord uy S) ((t : ℚ) / 20) i j =
      (planeNum S lx ux ly uy t i j : ℚ) / (planeDen S : ℚ) := by
  have hs0 : (S : ℚ) ≠ 0 := by exact_mod_cast hS.ne'
  unfold planeCoeff planeNum planeDen coord
  push_cast
  field_simp [hs0] <;> ring

/-- A constant coefficient lower bound can be checked without rational gcds. -/
theorem coefficient_ge_of_num (A : IntPower) (D S : ℕ) (hD : 0 < D) (hS : 0 < S)
    (lx ux ly uy q : ℤ) (i j : Fin 4)
    (hb : q * (commonDen D S : ℤ) ≤ bernsteinNum A S lx ux ly uy i j) :
    (q : ℚ) ≤ fastBoxCoeff (rationalPower A D)
      (coord lx S) (coord ux S) (coord ly S) (coord uy S) i j := by
  rw [fastBoxCoeff_eq_num A D S hD hS]
  have hk : 0 < (commonDen D S : ℚ) := by exact_mod_cast commonDen_pos D S hD hS
  apply (le_div_iff₀ hk).mpr
  exact_mod_cast hb

private theorem cleared_line_bound (B P q mn : ℤ) (K md H : ℕ)
    (hK : 0 < K) (hmd : 0 < md) (hH : 0 < H)
    (hb : q * (K : ℤ) * (md : ℤ) * (H : ℤ) + mn * (K : ℤ) * P ≤ B * (md : ℤ) * (H : ℤ)) :
    (q : ℚ) + (mn : ℚ) / (md : ℚ) * ((P : ℚ) / (H : ℚ)) ≤ (B : ℚ) / (K : ℚ) := by
  have hk : 0 < (K : ℚ) := by exact_mod_cast hK
  have hm : 0 < (md : ℚ) := by exact_mod_cast hmd
  have hh : 0 < (H : ℚ) := by exact_mod_cast hH
  have hcast : (q : ℚ) * (K : ℚ) * (md : ℚ) * (H : ℚ) +
      (mn : ℚ) * (K : ℚ) * (P : ℚ) ≤ (B : ℚ) * (md : ℚ) * (H : ℚ) := by
    exact_mod_cast hb
  apply (mul_le_mul_iff_of_pos_right (show 0 < (K : ℚ) * (md : ℚ) * (H : ℚ) by positivity)).mp
  convert hcast using 1 <;> field_simp [hk.ne', hm.ne', hh.ne'] <;> ring

/-- The signed-line coefficient condition, cleared entirely to integers.
Slope denominators and both common denominators are explicitly positive. -/
theorem line_ge_of_num (A : IntPower) (D S md : ℕ)
    (hD : 0 < D) (hS : 0 < S) (hmd : 0 < md)
    (lx ux ly uy t q mn : ℤ) (i j : Fin 4)
    (hb : q * (commonDen D S : ℤ) * (md : ℤ) * (planeDen S : ℤ) +
      mn * (commonDen D S : ℤ) * planeNum S lx ux ly uy t i j ≤
        bernsteinNum A S lx ux ly uy i j * (md : ℤ) * (planeDen S : ℤ)) :
    (q : ℚ) + (mn : ℚ) / (md : ℚ) *
      planeCoeff (coord lx S) (coord ux S) (coord ly S) (coord uy S) ((t : ℚ) / 20) i j ≤
      fastBoxCoeff (rationalPower A D) (coord lx S) (coord ux S) (coord ly S) (coord uy S) i j := by
  rw [planeCoeff_eq_num S hS, fastBoxCoeff_eq_num A D S hD hS]
  exact cleared_line_bound (bernsteinNum A S lx ux ly uy i j) (planeNum S lx ux ly uy t i j)
    q mn (commonDen D S) md (planeDen S) (commonDen_pos D S hD hS) hmd (planeDen_pos S hS) hb

end BerryEsseen.N2IntegerBernstein

#print axioms BerryEsseen.N2IntegerBernstein.transformCoeff_eq_num
#print axioms BerryEsseen.N2IntegerBernstein.bernsteinNum_eq_sum
#print axioms BerryEsseen.N2IntegerBernstein.fastBoxCoeff_eq_num
#print axioms BerryEsseen.N2IntegerBernstein.planeCoeff_eq_num
#print axioms BerryEsseen.N2IntegerBernstein.coefficient_ge_of_num
#print axioms BerryEsseen.N2IntegerBernstein.line_ge_of_num
