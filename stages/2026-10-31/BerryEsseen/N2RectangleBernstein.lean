module

public import BerryEsseen.N2MomentMajorant
public import Mathlib.Tactic.Ring

@[expose] public section

/-! 2026-10-29: fixed bicubic rectangular Bernstein soundness for the
original closed two-summand event. The rational coefficients are rebuilt
from the original power polynomial after each affine box substitution.
No point sampling, open-box discard, or triangle clipping is involved. -/

noncomputable section

open Set
open scoped BigOperators

namespace BerryEsseen.N2RectangleBernstein

abbrev Power := Fin 4 → Fin 4 → ℚ

def evalPower (a : Power) (x y : ℝ) : ℝ :=
  ∑ i : Fin 4, ∑ j : Fin 4, (a i j : ℝ) * x ^ i.val * y ^ j.val

def weight (i : Fin 4) (u : ℝ) : ℝ :=
  (Nat.choose 3 i.val : ℝ) * u ^ i.val * (1 - u) ^ (3 - i.val)

theorem weight_nonneg (i : Fin 4) (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
    0 ≤ weight i u := by
  have h0 : 0 ≤ u := hu.1
  have h1 : 0 ≤ 1 - u := sub_nonneg.mpr hu.2
  unfold weight
  positivity

theorem sum_weight (u : ℝ) : (∑ i : Fin 4, weight i u) = 1 := by
  norm_num [weight, Fin.sum_univ_succ]
  ring

theorem sum_coordinate_weight (u : ℝ) :
    (∑ i : Fin 4, (i.val : ℝ) / 3 * weight i u) = u := by
  norm_num [weight, Fin.sum_univ_succ]
  ring

def tensorWeight (i j : Fin 4) (u v : ℝ) : ℝ := weight i u * weight j v

def tensorEval (b : Fin 4 → Fin 4 → ℝ) (u v : ℝ) : ℝ :=
  ∑ i : Fin 4, ∑ j : Fin 4, tensorWeight i j u v * b i j

def evalBernstein (b : Power) (u v : ℝ) : ℝ :=
  tensorEval (fun i j => (b i j : ℝ)) u v

theorem tensorWeight_nonneg (i j : Fin 4) (u v : ℝ)
    (hu : u ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1) :
    0 ≤ tensorWeight i j u v :=
  mul_nonneg (weight_nonneg i u hu) (weight_nonneg j v hv)

theorem sum_tensorWeight (u v : ℝ) :
    (∑ i : Fin 4, ∑ j : Fin 4, tensorWeight i j u v) = 1 := by
  unfold tensorWeight
  simp_rw [← Finset.mul_sum, sum_weight, mul_one]
  exact sum_weight u

theorem tensorEval_const (k u v : ℝ) : tensorEval (fun _ _ => k) u v = k := by
  unfold tensorEval
  simp_rw [← Finset.sum_mul]
  rw [sum_tensorWeight, one_mul]

theorem tensor_coordinate_x (u v : ℝ) :
    tensorEval (fun i _ => (i.val : ℝ) / 3) u v = u := by
  norm_num [tensorEval, tensorWeight, weight, Fin.sum_univ_succ]
  ring

theorem tensor_coordinate_y (u v : ℝ) :
    tensorEval (fun _ j => (j.val : ℝ) / 3) u v = v := by
  norm_num [tensorEval, tensorWeight, weight, Fin.sum_univ_succ]
  ring

theorem tensorEval_add (b c : Fin 4 → Fin 4 → ℝ) (u v : ℝ) :
    tensorEval (fun i j => b i j + c i j) u v = tensorEval b u v + tensorEval c u v := by
  simp only [tensorEval, mul_add, Finset.sum_add_distrib]

theorem tensorEval_const_mul (b : Fin 4 → Fin 4 → ℝ) (k u v : ℝ) :
    tensorEval (fun i j => k * b i j) u v = k * tensorEval b u v := by
  unfold tensorEval
  calc
    _ = ∑ i : Fin 4, ∑ j : Fin 4, k * (tensorWeight i j u v * b i j) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by simp_rw [← Finset.mul_sum]

theorem tensorEval_affine (b : Fin 4 → Fin 4 → ℝ) (k ell u v : ℝ) :
    tensorEval (fun i j => k + ell * b i j) u v = k + ell * tensorEval b u v := by
  rw [tensorEval_add, tensorEval_const, tensorEval_const_mul]

theorem tensorEval_mono (b c : Fin 4 → Fin 4 → ℝ) (u v : ℝ)
    (hu : u ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1)
    (hbc : ∀ i j, b i j ≤ c i j) : tensorEval b u v ≤ tensorEval c u v := by
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_left (hbc i j) (tensorWeight_nonneg i j u v hu hv)

def chooseRatio (i r : Fin 4) : ℚ :=
  if r.val ≤ i.val then (Nat.choose i.val r.val : ℚ) / Nat.choose 3 r.val else 0

/-- The normalized degree-three tensor conversion used by the host route. -/
def toBernstein (a : Power) (i j : Fin 4) : ℚ :=
  ∑ r : Fin 4, ∑ s : Fin 4, a r s * chooseRatio i r * chooseRatio j s

theorem toBernstein_representation (a : Power) (u v : ℝ) :
    evalBernstein (toBernstein a) u v = evalPower a u v := by
  norm_num [evalBernstein, tensorEval, tensorWeight, weight, toBernstein, chooseRatio,
    evalPower, Fin.sum_univ_succ]
  push_cast
  ring

/-- Actual coefficients after x=Lx+Wx*u and y=Ly+Wy*v. -/
def affinePower (a : Power) (Lx Wx Ly Wy : ℚ) (r s : Fin 4) : ℚ :=
  ∑ p : Fin 4, ∑ q : Fin 4,
    if r.val ≤ p.val ∧ s.val ≤ q.val then
      a p q * Nat.choose p.val r.val * Lx ^ (p.val - r.val) * Wx ^ r.val *
        Nat.choose q.val s.val * Ly ^ (q.val - s.val) * Wy ^ s.val
    else 0

theorem affinePower_representation (a : Power) (Lx Wx Ly Wy : ℚ) (u v : ℝ) :
    evalPower (affinePower a Lx Wx Ly Wy) u v =
      evalPower a ((Lx : ℝ) + (Wx : ℝ) * u) ((Ly : ℝ) + (Wy : ℝ) * v) := by
  norm_num [evalPower, affinePower, Fin.sum_univ_succ]
  push_cast
  ring

def boxCoeff (a : Power) (Lx Ux Ly Uy : ℚ) : Power :=
  toBernstein (affinePower a Lx (Ux - Lx) Ly (Uy - Ly))

def normalize (L U : ℚ) (x : ℝ) : ℝ := (x - (L : ℝ)) / ((U - L : ℚ) : ℝ)

def InBox (Lx Ux Ly Uy : ℚ) (x y : ℝ) : Prop :=
  x ∈ Icc (Lx : ℝ) (Ux : ℝ) ∧ y ∈ Icc (Ly : ℝ) (Uy : ℝ)

theorem normalize_mem_Icc (L U : ℚ) (hLU : L < U) (x : ℝ)
    (hx : x ∈ Icc (L : ℝ) (U : ℝ)) : normalize L U x ∈ Icc (0 : ℝ) 1 := by
  have hw : 0 < (U : ℝ) - (L : ℝ) := by exact_mod_cast sub_pos.mpr hLU
  unfold normalize
  push_cast
  constructor
  · exact div_nonneg (sub_nonneg.mpr hx.1) hw.le
  · exact (div_le_one₀ hw).mpr (sub_le_sub_right hx.2 _)

theorem normalize_reconstruct (L U : ℚ) (hLU : L < U) (x : ℝ) :
    (L : ℝ) + ((U - L : ℚ) : ℝ) * normalize L U x = x := by
  have hw : ((U - L : ℚ) : ℝ) ≠ 0 := by exact_mod_cast (sub_pos.mpr hLU).ne'
  unfold normalize
  field_simp [hw] <;> ring

theorem box_representation (a : Power) (Lx Ux Ly Uy : ℚ) (hWx : Lx < Ux) (hWy : Ly < Uy)
    (x y : ℝ) :
    evalBernstein (boxCoeff a Lx Ux Ly Uy) (normalize Lx Ux x) (normalize Ly Uy y) =
      evalPower a x y := by
  rw [boxCoeff, toBernstein_representation, affinePower_representation,
    normalize_reconstruct Lx Ux hWx, normalize_reconstruct Ly Uy hWy]

/-- Elevated coefficients of the literal signed plane x+y-T. -/
def planeCoeff (Lx Ux Ly Uy T : ℚ) (i j : Fin 4) : ℚ :=
  Lx + (i.val : ℚ) * (Ux - Lx) / 3 + Ly + (j.val : ℚ) * (Uy - Ly) / 3 - T

theorem planeCoeff_representation (Lx Ux Ly Uy T : ℚ) (u v : ℝ) :
    evalBernstein (planeCoeff Lx Ux Ly Uy T) u v =
      (Lx : ℝ) + ((Ux - Lx : ℚ) : ℝ) * u +
        (Ly : ℝ) + ((Uy - Ly : ℚ) : ℝ) * v - (T : ℝ) := by
  norm_num [evalBernstein, tensorEval, tensorWeight, weight, planeCoeff, Fin.sum_univ_succ]
  push_cast
  ring

theorem box_plane_reconstruct (Lx Ux Ly Uy T : ℚ) (hWx : Lx < Ux) (hWy : Ly < Uy)
    (x y : ℝ) :
    evalBernstein (planeCoeff Lx Ux Ly Uy T) (normalize Lx Ux x) (normalize Ly Uy y) =
      x + y - (T : ℝ) := by
  rw [planeCoeff_representation]
  have hx := normalize_reconstruct Lx Ux hWx x
  have hy := normalize_reconstruct Ly Uy hWy y
  linarith only [hx, hy]

theorem box_lower_bound (a : Power) (Lx Ux Ly Uy q : ℚ) (hWx : Lx < Ux) (hWy : Ly < Uy)
    (hb : ∀ i j, q ≤ boxCoeff a Lx Ux Ly Uy i j) (x y : ℝ) (hxy : InBox Lx Ux Ly Uy x y) :
    (q : ℝ) ≤ evalPower a x y := by
  have hu := normalize_mem_Icc Lx Ux hWx x hxy.1
  have hv := normalize_mem_Icc Ly Uy hWy y hxy.2
  have hbr (i j : Fin 4) : (q : ℝ) ≤ (boxCoeff a Lx Ux Ly Uy i j : ℝ) := by
    exact_mod_cast hb i j
  have hm := tensorEval_mono (fun _ _ => (q : ℝ))
    (fun i j => (boxCoeff a Lx Ux Ly Uy i j : ℝ))
    (normalize Lx Ux x) (normalize Ly Uy y) hu hv hbr
  rw [tensorEval_const] at hm
  change (q : ℝ) ≤ evalBernstein (boxCoeff a Lx Ux Ly Uy) (normalize Lx Ux x) (normalize Ly Uy y) at hm
  rw [box_representation a Lx Ux Ly Uy hWx hWy x y] at hm
  exact hm

theorem box_line_lower_bound (a : Power) (Lx Ux Ly Uy T q ell : ℚ)
    (hWx : Lx < Ux) (hWy : Ly < Uy)
    (hb : ∀ i j, q + ell * planeCoeff Lx Ux Ly Uy T i j ≤ boxCoeff a Lx Ux Ly Uy i j)
    (x y : ℝ) (hxy : InBox Lx Ux Ly Uy x y) :
    (q : ℝ) + (ell : ℝ) * (x + y - (T : ℝ)) ≤ evalPower a x y := by
  have hu := normalize_mem_Icc Lx Ux hWx x hxy.1
  have hv := normalize_mem_Icc Ly Uy hWy y hxy.2
  have hbr (i j : Fin 4) :
      (q : ℝ) + (ell : ℝ) * (planeCoeff Lx Ux Ly Uy T i j : ℝ) ≤
        (boxCoeff a Lx Ux Ly Uy i j : ℝ) := by exact_mod_cast hb i j
  have hm := tensorEval_mono
    (fun i j => (q : ℝ) + (ell : ℝ) * (planeCoeff Lx Ux Ly Uy T i j : ℝ))
    (fun i j => (boxCoeff a Lx Ux Ly Uy i j : ℝ))
    (normalize Lx Ux x) (normalize Ly Uy y) hu hv hbr
  rw [tensorEval_affine] at hm
  change (q : ℝ) + (ell : ℝ) *
    evalBernstein (planeCoeff Lx Ux Ly Uy T) (normalize Lx Ux x) (normalize Ly Uy y) ≤
      evalBernstein (boxCoeff a Lx Ux Ly Uy) (normalize Lx Ux x) (normalize Ly Uy y) at hm
  rw [box_plane_reconstruct Lx Ux Ly Uy T hWx hWy x y,
    box_representation a Lx Ux Ly Uy hWx hWy x y] at hm
  exact hm

theorem inside_leaf_sound (a : Power) (Lx Ux Ly Uy T : ℚ)
    (hWx : Lx < Ux) (hWy : Ly < Uy) (hsum : Ux + Uy ≤ T)
    (hb : ∀ i j, 1 ≤ boxCoeff a Lx Ux Ly Uy i j) :
    ∀ x y : ℝ, InBox Lx Ux Ly Uy x y →
      N2MomentMajorant.closedIndicator (T : ℝ) x y ≤ evalPower a x y := by
  intro x y hxy
  have hsumR : (Ux : ℝ) + (Uy : ℝ) ≤ (T : ℝ) := by exact_mod_cast hsum
  have hin : x + y ≤ (T : ℝ) := (add_le_add hxy.1.2 hxy.2.2).trans hsumR
  rw [N2MomentMajorant.closedIndicator_of_le _ _ _ hin]
  simpa only [Rat.cast_one] using box_lower_bound a Lx Ux Ly Uy 1 hWx hWy hb x y hxy

theorem outside_leaf_sound (a : Power) (Lx Ux Ly Uy T : ℚ)
    (hWx : Lx < Ux) (hWy : Ly < Uy) (hsum : T < Lx + Ly)
    (hb : ∀ i j, 0 ≤ boxCoeff a Lx Ux Ly Uy i j) :
    ∀ x y : ℝ, InBox Lx Ux Ly Uy x y →
      N2MomentMajorant.closedIndicator (T : ℝ) x y ≤ evalPower a x y := by
  intro x y hxy
  have hsumR : (T : ℝ) < (Lx : ℝ) + (Ly : ℝ) := by exact_mod_cast hsum
  have hout : (T : ℝ) < x + y := hsumR.trans_le (add_le_add hxy.1.1 hxy.2.1)
  rw [N2MomentMajorant.closedIndicator_of_gt _ _ _ hout]
  simpa only [Rat.cast_zero] using box_lower_bound a Lx Ux Ly Uy 0 hWx hWy hb x y hxy

/-- The host signed-slope convention. Equality x+y=T always uses the
minus line and the closed inside event; the plus line is only used outside. -/
theorem cross_leaf_sound (a : Power) (Lx Ux Ly Uy T minus : ℚ)
    (hWx : Lx < Ux) (hWy : Ly < Uy) (hminus : minus ≤ 0)
    (hbminus : ∀ i j, 1 + minus * planeCoeff Lx Ux Ly Uy T i j ≤ boxCoeff a Lx Ux Ly Uy i j)
    (houtside : (∀ i j, 0 ≤ boxCoeff a Lx Ux Ly Uy i j) ∨
      ∃ plus : ℚ, 0 ≤ plus ∧
        ∀ i j, plus * planeCoeff Lx Ux Ly Uy T i j ≤ boxCoeff a Lx Ux Ly Uy i j) :
    ∀ x y : ℝ, InBox Lx Ux Ly Uy x y →
      N2MomentMajorant.closedIndicator (T : ℝ) x y ≤ evalPower a x y := by
  intro x y hxy
  by_cases hin : x + y ≤ (T : ℝ)
  · rw [N2MomentMajorant.closedIndicator_of_le _ _ _ hin]
    have hlower := box_line_lower_bound a Lx Ux Ly Uy T 1 minus hWx hWy hbminus x y hxy
    simp only [Rat.cast_one] at hlower
    have hm : (minus : ℝ) ≤ 0 := by exact_mod_cast hminus
    have hp := mul_nonneg_of_nonpos_of_nonpos hm (sub_nonpos.mpr hin)
    nlinarith only [hlower, hp]
  · have hout : (T : ℝ) < x + y := lt_of_not_ge hin
    rw [N2MomentMajorant.closedIndicator_of_gt _ _ _ hout]
    rcases houtside with hnon | ⟨plus, hplus, hbplus⟩
    · simpa only [Rat.cast_zero] using box_lower_bound a Lx Ux Ly Uy 0 hWx hWy hnon x y hxy
    · have hbound : ∀ i j, 0 + plus * planeCoeff Lx Ux Ly Uy T i j ≤ boxCoeff a Lx Ux Ly Uy i j := by
        intro i j
        simpa only [zero_add] using hbplus i j
      have hlower := box_line_lower_bound a Lx Ux Ly Uy T 0 plus hWx hWy hbound x y hxy
      simp only [Rat.cast_zero, zero_add] at hlower
      have hp0 : 0 ≤ (plus : ℝ) := by exact_mod_cast hplus
      have hp := mul_nonneg hp0 (sub_nonneg.mpr hout.le)
      nlinarith only [hlower, hp]

def midpoint (L U : ℚ) : ℚ := (L + U) / 2

theorem midpoint_strict (L U : ℚ) (hLU : L < U) : L < midpoint L U ∧ midpoint L U < U := by
  unfold midpoint
  constructor <;> linarith only [hLU]

theorem box_x_bisect_cover (Lx Ux Ly Uy : ℚ) (x y : ℝ) (hxy : InBox Lx Ux Ly Uy x y) :
    InBox Lx (midpoint Lx Ux) Ly Uy x y ∨ InBox (midpoint Lx Ux) Ux Ly Uy x y := by
  rcases le_total x (midpoint Lx Ux : ℝ) with hx | hx
  · exact Or.inl ⟨⟨hxy.1.1, hx⟩, hxy.2⟩
  · exact Or.inr ⟨⟨hx, hxy.1.2⟩, hxy.2⟩

theorem box_y_bisect_cover (Lx Ux Ly Uy : ℚ) (x y : ℝ) (hxy : InBox Lx Ux Ly Uy x y) :
    InBox Lx Ux Ly (midpoint Ly Uy) x y ∨ InBox Lx Ux (midpoint Ly Uy) Uy x y := by
  rcases le_total y (midpoint Ly Uy : ℝ) with hy | hy
  · exact Or.inl ⟨hxy.1, ⟨hxy.2.1, hy⟩⟩
  · exact Or.inr ⟨hxy.1, ⟨hy, hxy.2.2⟩⟩

theorem split_x_sound (a : Power) (Lx Ux Ly Uy T : ℚ)
    (hl : ∀ x y, InBox Lx (midpoint Lx Ux) Ly Uy x y →
      N2MomentMajorant.closedIndicator (T : ℝ) x y ≤ evalPower a x y)
    (hr : ∀ x y, InBox (midpoint Lx Ux) Ux Ly Uy x y →
      N2MomentMajorant.closedIndicator (T : ℝ) x y ≤ evalPower a x y) :
    ∀ x y, InBox Lx Ux Ly Uy x y →
      N2MomentMajorant.closedIndicator (T : ℝ) x y ≤ evalPower a x y := by
  intro x y hxy
  exact (box_x_bisect_cover Lx Ux Ly Uy x y hxy).elim (hl x y) (hr x y)

theorem split_y_sound (a : Power) (Lx Ux Ly Uy T : ℚ)
    (hl : ∀ x y, InBox Lx Ux Ly (midpoint Ly Uy) x y →
      N2MomentMajorant.closedIndicator (T : ℝ) x y ≤ evalPower a x y)
    (hr : ∀ x y, InBox Lx Ux (midpoint Ly Uy) Uy x y →
      N2MomentMajorant.closedIndicator (T : ℝ) x y ≤ evalPower a x y) :
    ∀ x y, InBox Lx Ux Ly Uy x y →
      N2MomentMajorant.closedIndicator (T : ℝ) x y ≤ evalPower a x y := by
  intro x y hxy
  exact (box_y_bisect_cover Lx Ux Ly Uy x y hxy).elim (hl x y) (hr x y)

/-- Four closed orthants cover the complete cube, including both axes
and their intersection. No sorted-coordinate or strict-edge discard occurs. -/
theorem cube_orthants_cover (R : ℚ) (x y : ℝ) (hxy : InBox (-R) R (-R) R x y) :
    InBox (-R) 0 (-R) 0 x y ∨ InBox (-R) 0 0 R x y ∨
      InBox 0 R (-R) 0 x y ∨ InBox 0 R 0 R x y := by
  simp only [InBox, mem_Icc, Rat.cast_zero] at hxy ⊢
  rcases le_total x 0 with hx | hx <;> rcases le_total y 0 with hy | hy
  · exact Or.inl ⟨⟨hxy.1.1, hx⟩, ⟨hxy.2.1, hy⟩⟩
  · exact Or.inr (Or.inl ⟨⟨hxy.1.1, hx⟩, ⟨hy, hxy.2.2⟩⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨⟨hx, hxy.1.2⟩, ⟨hxy.2.1, hy⟩⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨⟨hx, hxy.1.2⟩, ⟨hy, hxy.2.2⟩⟩))

end BerryEsseen.N2RectangleBernstein

#print axioms BerryEsseen.N2RectangleBernstein.toBernstein_representation
#print axioms BerryEsseen.N2RectangleBernstein.affinePower_representation
#print axioms BerryEsseen.N2RectangleBernstein.box_representation
#print axioms BerryEsseen.N2RectangleBernstein.inside_leaf_sound
#print axioms BerryEsseen.N2RectangleBernstein.outside_leaf_sound
#print axioms BerryEsseen.N2RectangleBernstein.cross_leaf_sound
#print axioms BerryEsseen.N2RectangleBernstein.split_x_sound
#print axioms BerryEsseen.N2RectangleBernstein.split_y_sound
#print axioms BerryEsseen.N2RectangleBernstein.cube_orthants_cover
