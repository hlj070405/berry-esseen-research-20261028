module

public import BerryEsseen.N2RectangleBernstein

@[expose] public section

/-! 2026-10-29: exact separable bicubic box-coefficient evaluation.
The fixed 4x4 transform removes the nested affine/degree-elevation sums
from literal leaf checking. Its equality with the proved original
boxCoeff is a general kernel theorem, with no host or native oracle.
No epsilon is inserted: the incoming power polynomial is unchanged. -/

noncomputable section

open scoped BigOperators

namespace BerryEsseen.N2BernsteinFast

open N2RectangleBernstein

/-- Row i contains the Bernstein coefficients of 1,x,x²,x³ on [L,U]. -/
def transformCoeff (L U : ℚ) (i p : Fin 4) : ℚ :=
  match i.val, p.val with
  | 0, 0 => 1
  | 0, 1 => L
  | 0, 2 => L ^ 2
  | 0, _ => L ^ 3
  | 1, 0 => 1
  | 1, 1 => (2 * L + U) / 3
  | 1, 2 => (L ^ 2 + 2 * L * U) / 3
  | 1, _ => L ^ 2 * U
  | 2, 0 => 1
  | 2, 1 => (L + 2 * U) / 3
  | 2, 2 => (2 * L * U + U ^ 2) / 3
  | 2, _ => L * U ^ 2
  | _, 0 => 1
  | _, 1 => U
  | _, 2 => U ^ 2
  | _, _ => U ^ 3

def fastBoxCoeff (a : Power) (Lx Ux Ly Uy : ℚ) (i j : Fin 4) : ℚ :=
  ∑ p : Fin 4, ∑ q : Fin 4, a p q * transformCoeff Lx Ux i p * transformCoeff Ly Uy j q

private def affineEntry (L U : ℚ) (r p : Fin 4) : ℚ :=
  if r.val ≤ p.val then (Nat.choose p.val r.val : ℚ) * L ^ (p.val - r.val) * (U - L) ^ r.val else 0

private theorem transformCoeff_eq_sum (L U : ℚ) (i p : Fin 4) :
    transformCoeff L U i p = ∑ r : Fin 4, affineEntry L U r p * chooseRatio i r := by
  fin_cases i <;> fin_cases p <;>
    norm_num [transformCoeff, affineEntry, chooseRatio, Fin.sum_univ_succ] <;> ring

private theorem affinePower_eq_separable (a : Power) (Lx Ux Ly Uy : ℚ) (r s : Fin 4) :
    affinePower a Lx (Ux - Lx) Ly (Uy - Ly) r s =
      ∑ p : Fin 4, ∑ q : Fin 4, a p q * affineEntry Lx Ux r p * affineEntry Ly Uy s q := by
  unfold affinePower
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  by_cases hr : r.val ≤ p.val <;> by_cases hs : s.val ≤ q.val <;>
    simp [affineEntry, hr, hs] <;> ring

private theorem swap_four_sums (f : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℚ) :
    (∑ r : Fin 4, ∑ s : Fin 4, ∑ p : Fin 4, ∑ q : Fin 4, f r s p q) =
      ∑ p : Fin 4, ∑ q : Fin 4, ∑ r : Fin 4, ∑ s : Fin 4, f r s p q := by
  calc
    _ = ∑ r : Fin 4, ∑ p : Fin 4, ∑ s : Fin 4, ∑ q : Fin 4, f r s p q := by
      apply Finset.sum_congr rfl
      intro r _
      exact Finset.sum_comm
    _ = ∑ p : Fin 4, ∑ r : Fin 4, ∑ s : Fin 4, ∑ q : Fin 4, f r s p q := Finset.sum_comm
    _ = ∑ p : Fin 4, ∑ r : Fin 4, ∑ q : Fin 4, ∑ s : Fin 4, f r s p q := by
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro r _
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p _
      exact Finset.sum_comm

private theorem separated_product (a : ℚ) (f g : Fin 4 → ℚ) :
    a * (∑ r : Fin 4, f r) * (∑ s : Fin 4, g s) =
      ∑ r : Fin 4, ∑ s : Fin 4, a * f r * g s := by
  calc
    _ = a * ((∑ r : Fin 4, f r) * (∑ s : Fin 4, g s)) := by ring
    _ = a * (∑ r : Fin 4, ∑ s : Fin 4, f r * g s) := by rw [Finset.sum_mul_sum]
    _ = ∑ r : Fin 4, ∑ s : Fin 4, a * (f r * g s) := by simp_rw [Finset.mul_sum]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro s _
      ring

/-- Exact equality for every actual incoming bicubic power polynomial,
including negative or zero box endpoints. -/
theorem fastBoxCoeff_eq_boxCoeff (a : Power) (Lx Ux Ly Uy : ℚ) :
    fastBoxCoeff a Lx Ux Ly Uy = boxCoeff a Lx Ux Ly Uy := by
  funext i j
  symm
  unfold boxCoeff toBernstein
  simp_rw [affinePower_eq_separable, Finset.sum_mul]
  rw [swap_four_sums]
  unfold fastBoxCoeff
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  rw [transformCoeff_eq_sum, transformCoeff_eq_sum, separated_product]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  ring

theorem fast_box_representation (a : Power) (Lx Ux Ly Uy : ℚ)
    (hWx : Lx < Ux) (hWy : Ly < Uy) (x y : ℝ) :
    evalBernstein (fastBoxCoeff a Lx Ux Ly Uy) (normalize Lx Ux x) (normalize Ly Uy y) =
      evalPower a x y := by
  rw [fastBoxCoeff_eq_boxCoeff]
  exact box_representation a Lx Ux Ly Uy hWx hWy x y

theorem inside_leaf_sound (a : Power) (Lx Ux Ly Uy T : ℚ)
    (hWx : Lx < Ux) (hWy : Ly < Uy) (hsum : Ux + Uy ≤ T)
    (hb : ∀ i j, 1 ≤ fastBoxCoeff a Lx Ux Ly Uy i j) :
    ∀ x y : ℝ, InBox Lx Ux Ly Uy x y →
      N2MomentMajorant.closedIndicator (T : ℝ) x y ≤ evalPower a x y := by
  apply N2RectangleBernstein.inside_leaf_sound a Lx Ux Ly Uy T hWx hWy hsum
  intro i j
  rw [← fastBoxCoeff_eq_boxCoeff]
  exact hb i j

theorem outside_leaf_sound (a : Power) (Lx Ux Ly Uy T : ℚ)
    (hWx : Lx < Ux) (hWy : Ly < Uy) (hsum : T < Lx + Ly)
    (hb : ∀ i j, 0 ≤ fastBoxCoeff a Lx Ux Ly Uy i j) :
    ∀ x y : ℝ, InBox Lx Ux Ly Uy x y →
      N2MomentMajorant.closedIndicator (T : ℝ) x y ≤ evalPower a x y := by
  apply N2RectangleBernstein.outside_leaf_sound a Lx Ux Ly Uy T hWx hWy hsum
  intro i j
  rw [← fastBoxCoeff_eq_boxCoeff]
  exact hb i j

/-- The closed plane still uses the minus line. The outside alternative
is unchanged, with either all nonnegative coefficients or a nonnegative plus slope. -/
theorem cross_leaf_sound (a : Power) (Lx Ux Ly Uy T minus : ℚ)
    (hWx : Lx < Ux) (hWy : Ly < Uy) (hminus : minus ≤ 0)
    (hbminus : ∀ i j,
      1 + minus * planeCoeff Lx Ux Ly Uy T i j ≤ fastBoxCoeff a Lx Ux Ly Uy i j)
    (houtside : (∀ i j, 0 ≤ fastBoxCoeff a Lx Ux Ly Uy i j) ∨
      ∃ plus : ℚ, 0 ≤ plus ∧
        ∀ i j, plus * planeCoeff Lx Ux Ly Uy T i j ≤ fastBoxCoeff a Lx Ux Ly Uy i j) :
    ∀ x y : ℝ, InBox Lx Ux Ly Uy x y →
      N2MomentMajorant.closedIndicator (T : ℝ) x y ≤ evalPower a x y := by
  apply N2RectangleBernstein.cross_leaf_sound a Lx Ux Ly Uy T minus hWx hWy hminus
  · intro i j
    rw [← fastBoxCoeff_eq_boxCoeff]
    exact hbminus i j
  · rw [← fastBoxCoeff_eq_boxCoeff]
    exact houtside

end BerryEsseen.N2BernsteinFast

#print axioms BerryEsseen.N2BernsteinFast.fastBoxCoeff_eq_boxCoeff
#print axioms BerryEsseen.N2BernsteinFast.fast_box_representation
#print axioms BerryEsseen.N2BernsteinFast.inside_leaf_sound
#print axioms BerryEsseen.N2BernsteinFast.outside_leaf_sound
#print axioms BerryEsseen.N2BernsteinFast.cross_leaf_sound
