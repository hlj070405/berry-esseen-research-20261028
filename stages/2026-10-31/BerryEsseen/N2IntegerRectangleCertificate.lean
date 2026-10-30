module

public import BerryEsseen.N2IntegerBernstein

@[expose] public section

/-! 2026-10-29: fraction-free fixed bicubic rectangle replay.
The checker itself uses only integer/natural arithmetic. Coordinates remain
exact numerator/S values, the original threshold is t/20, and each leaf
recomputes its integer Bernstein numerators from the same incoming A.
Rational slopes are constructed only in the soundness proof, never in check. -/

namespace BerryEsseen.N2IntegerRectangleCertificate

open N2RectangleBernstein N2BernsteinFast N2IntegerBernstein

inductive Certificate where
  | inside
  | outside
  | cross (mn : ℤ) (md : ℕ) (plus : Option (ℤ × ℕ))
  | splitX (mid : ℤ) (left right : Certificate)
  | splitY (mid : ℤ) (left right : Certificate)
  | unresolved

/-- No Rat value, classical decider, stored b-array or host flag occurs in check. -/
def check (A : IntPower) (D S : ℕ) (lx ux ly uy t : ℤ) : Certificate → Bool
  | .inside => decide (lx < ux ∧ ly < uy ∧ 20 * (ux + uy) ≤ (S : ℤ) * t ∧
      ∀ i j, (commonDen D S : ℤ) ≤ bernsteinNum A S lx ux ly uy i j)
  | .outside => decide (lx < ux ∧ ly < uy ∧ (S : ℤ) * t < 20 * (lx + ly) ∧
      ∀ i j, 0 ≤ bernsteinNum A S lx ux ly uy i j)
  | .cross mn md none => decide (lx < ux ∧ ly < uy ∧ 0 < md ∧ mn ≤ 0 ∧
      (∀ i j, (commonDen D S : ℤ) * (md : ℤ) * (planeDen S : ℤ) +
        mn * (commonDen D S : ℤ) * planeNum S lx ux ly uy t i j ≤
          bernsteinNum A S lx ux ly uy i j * (md : ℤ) * (planeDen S : ℤ)) ∧
      (∀ i j, 0 ≤ bernsteinNum A S lx ux ly uy i j))
  | .cross mn md (some (pn, pd)) => decide (lx < ux ∧ ly < uy ∧ 0 < md ∧ mn ≤ 0 ∧
      (∀ i j, (commonDen D S : ℤ) * (md : ℤ) * (planeDen S : ℤ) +
        mn * (commonDen D S : ℤ) * planeNum S lx ux ly uy t i j ≤
          bernsteinNum A S lx ux ly uy i j * (md : ℤ) * (planeDen S : ℤ)) ∧
      0 < pd ∧ 0 ≤ pn ∧
      (∀ i j, pn * (commonDen D S : ℤ) * planeNum S lx ux ly uy t i j ≤
        bernsteinNum A S lx ux ly uy i j * (pd : ℤ) * (planeDen S : ℤ)))
  | .splitX mid left right => decide (2 * mid = lx + ux) &&
      (check A D S lx mid ly uy t left && check A D S mid ux ly uy t right)
  | .splitY mid left right => decide (2 * mid = ly + uy) &&
      (check A D S lx ux ly mid t left && check A D S lx ux mid uy t right)
  | .unresolved => false

private theorem and_true {p q : Bool} (h : (p && q) = true) : p = true ∧ q = true := by
  cases p <;> cases q <;> simp_all

private theorem inside_sum_of_num (S : ℕ) (hS : 0 < S) (ux uy t : ℤ)
    (h : 20 * (ux + uy) ≤ (S : ℤ) * t) : coord ux S + coord uy S ≤ (t : ℚ) / 20 := by
  have hs : 0 < (S : ℚ) := by exact_mod_cast hS
  have hc : (20 : ℚ) * ((ux : ℚ) + (uy : ℚ)) ≤ (S : ℚ) * (t : ℚ) := by exact_mod_cast h
  unfold coord
  apply (mul_le_mul_iff_of_pos_right (show 0 < (20 : ℚ) * (S : ℚ) by positivity)).mp
  convert hc using 1 <;> field_simp [hs.ne'] <;> ring

private theorem outside_sum_of_num (S : ℕ) (hS : 0 < S) (lx ly t : ℤ)
    (h : (S : ℤ) * t < 20 * (lx + ly)) : (t : ℚ) / 20 < coord lx S + coord ly S := by
  have hs : 0 < (S : ℚ) := by exact_mod_cast hS
  have hc : (S : ℚ) * (t : ℚ) < (20 : ℚ) * ((lx : ℚ) + (ly : ℚ)) := by exact_mod_cast h
  unfold coord
  apply (mul_lt_mul_iff_of_pos_right (show 0 < (20 : ℚ) * (S : ℚ) by positivity)).mp
  convert hc using 1 <;> field_simp [hs.ne'] <;> ring

private theorem coord_midpoint_of_num (S : ℕ) (hS : 0 < S) (L U mid : ℤ)
    (hmid : 2 * mid = L + U) :
    coord mid S = N2RectangleBernstein.midpoint (coord L S) (coord U S) := by
  have hs : (S : ℚ) ≠ 0 := by exact_mod_cast hS.ne'
  have hc : (2 : ℚ) * (mid : ℚ) = (L : ℚ) + (U : ℚ) := by exact_mod_cast hmid
  unfold coord N2RectangleBernstein.midpoint
  field_simp [hs]
  nlinarith only [hc]

private theorem coefficients_nonnegative (A : IntPower) (D S : ℕ) (hD : 0 < D) (hS : 0 < S)
    (lx ux ly uy : ℤ) (hb : ∀ i j, 0 ≤ bernsteinNum A S lx ux ly uy i j) :
    ∀ i j, 0 ≤ fastBoxCoeff (rationalPower A D) (coord lx S) (coord ux S) (coord ly S) (coord uy S) i j := by
  intro i j
  have hn : (0 : ℤ) * (commonDen D S : ℤ) ≤ bernsteinNum A S lx ux ly uy i j := by
    simpa only [zero_mul] using hb i j
  simpa only [Int.cast_zero] using coefficient_ge_of_num A D S hD hS lx ux ly uy 0 i j hn

private theorem minus_coefficients (A : IntPower) (D S md : ℕ)
    (hD : 0 < D) (hS : 0 < S) (hmd : 0 < md) (lx ux ly uy t mn : ℤ)
    (hb : ∀ i j, (commonDen D S : ℤ) * (md : ℤ) * (planeDen S : ℤ) +
      mn * (commonDen D S : ℤ) * planeNum S lx ux ly uy t i j ≤
        bernsteinNum A S lx ux ly uy i j * (md : ℤ) * (planeDen S : ℤ)) :
    ∀ i j, 1 + (mn : ℚ) / (md : ℚ) *
      planeCoeff (coord lx S) (coord ux S) (coord ly S) (coord uy S) ((t : ℚ) / 20) i j ≤
        fastBoxCoeff (rationalPower A D) (coord lx S) (coord ux S) (coord ly S) (coord uy S) i j := by
  intro i j
  have hn : (1 : ℤ) * (commonDen D S : ℤ) * (md : ℤ) * (planeDen S : ℤ) +
      mn * (commonDen D S : ℤ) * planeNum S lx ux ly uy t i j ≤
        bernsteinNum A S lx ux ly uy i j * (md : ℤ) * (planeDen S : ℤ) := by
    simpa only [one_mul] using hb i j
  simpa only [Int.cast_one] using line_ge_of_num A D S md hD hS hmd lx ux ly uy t 1 mn i j hn

private theorem sound_by_recursion (A : IntPower) (D S : ℕ) (hD : 0 < D) (hS : 0 < S)
    (certificate : Certificate) :
    ∀ (lx ux ly uy t : ℤ), check A D S lx ux ly uy t certificate = true →
      ∀ x y : ℝ, InBox (coord lx S) (coord ux S) (coord ly S) (coord uy S) x y →
        N2MomentMajorant.closedIndicator (((t : ℚ) / 20 : ℚ) : ℝ) x y ≤ evalPower (rationalPower A D) x y := by
  induction certificate with
  | inside =>
      intro lx ux ly uy t h
      have hc : lx < ux ∧ ly < uy ∧ 20 * (ux + uy) ≤ (S : ℤ) * t ∧
          ∀ i j, (commonDen D S : ℤ) ≤ bernsteinNum A S lx ux ly uy i j := of_decide_eq_true h
      rcases hc with ⟨hwx, hwy, hsum, hb⟩
      apply N2BernsteinFast.inside_leaf_sound (rationalPower A D)
        (coord lx S) (coord ux S) (coord ly S) (coord uy S) ((t : ℚ) / 20)
        (coord_strictMono S hS hwx) (coord_strictMono S hS hwy) (inside_sum_of_num S hS ux uy t hsum)
      intro i j
      have hn : (1 : ℤ) * (commonDen D S : ℤ) ≤ bernsteinNum A S lx ux ly uy i j := by
        simpa only [one_mul] using hb i j
      simpa only [Int.cast_one] using coefficient_ge_of_num A D S hD hS lx ux ly uy 1 i j hn
  | outside =>
      intro lx ux ly uy t h
      have hc : lx < ux ∧ ly < uy ∧ (S : ℤ) * t < 20 * (lx + ly) ∧
          ∀ i j, 0 ≤ bernsteinNum A S lx ux ly uy i j := of_decide_eq_true h
      rcases hc with ⟨hwx, hwy, hsum, hb⟩
      exact N2BernsteinFast.outside_leaf_sound (rationalPower A D)
        (coord lx S) (coord ux S) (coord ly S) (coord uy S) ((t : ℚ) / 20)
        (coord_strictMono S hS hwx) (coord_strictMono S hS hwy) (outside_sum_of_num S hS lx ly t hsum)
        (coefficients_nonnegative A D S hD hS lx ux ly uy hb)
  | cross mn md plus =>
      intro lx ux ly uy t h
      cases plus with
      | none =>
          have hc : lx < ux ∧ ly < uy ∧ 0 < md ∧ mn ≤ 0 ∧
              (∀ i j, (commonDen D S : ℤ) * (md : ℤ) * (planeDen S : ℤ) +
                mn * (commonDen D S : ℤ) * planeNum S lx ux ly uy t i j ≤
                  bernsteinNum A S lx ux ly uy i j * (md : ℤ) * (planeDen S : ℤ)) ∧
              (∀ i j, 0 ≤ bernsteinNum A S lx ux ly uy i j) := of_decide_eq_true h
          rcases hc with ⟨hwx, hwy, hmd, hmn, hbminus, hbnon⟩
          have hm : (mn : ℚ) / (md : ℚ) ≤ 0 := div_nonpos_of_nonpos_of_nonneg
            (by exact_mod_cast hmn) (by exact_mod_cast hmd.le)
          exact N2BernsteinFast.cross_leaf_sound (rationalPower A D)
            (coord lx S) (coord ux S) (coord ly S) (coord uy S) ((t : ℚ) / 20)
            ((mn : ℚ) / (md : ℚ)) (coord_strictMono S hS hwx) (coord_strictMono S hS hwy) hm
            (minus_coefficients A D S md hD hS hmd lx ux ly uy t mn hbminus)
            (Or.inl (coefficients_nonnegative A D S hD hS lx ux ly uy hbnon))
      | some plus =>
          rcases plus with ⟨pn, pd⟩
          have hc : lx < ux ∧ ly < uy ∧ 0 < md ∧ mn ≤ 0 ∧
              (∀ i j, (commonDen D S : ℤ) * (md : ℤ) * (planeDen S : ℤ) +
                mn * (commonDen D S : ℤ) * planeNum S lx ux ly uy t i j ≤
                  bernsteinNum A S lx ux ly uy i j * (md : ℤ) * (planeDen S : ℤ)) ∧
              0 < pd ∧ 0 ≤ pn ∧
              (∀ i j, pn * (commonDen D S : ℤ) * planeNum S lx ux ly uy t i j ≤
                bernsteinNum A S lx ux ly uy i j * (pd : ℤ) * (planeDen S : ℤ)) := of_decide_eq_true h
          rcases hc with ⟨hwx, hwy, hmd, hmn, hbminus, hpd, hpn, hbplus⟩
          have hm : (mn : ℚ) / (md : ℚ) ≤ 0 := div_nonpos_of_nonpos_of_nonneg
            (by exact_mod_cast hmn) (by exact_mod_cast hmd.le)
          apply N2BernsteinFast.cross_leaf_sound (rationalPower A D)
            (coord lx S) (coord ux S) (coord ly S) (coord uy S) ((t : ℚ) / 20)
            ((mn : ℚ) / (md : ℚ)) (coord_strictMono S hS hwx) (coord_strictMono S hS hwy) hm
            (minus_coefficients A D S md hD hS hmd lx ux ly uy t mn hbminus)
          refine Or.inr ⟨(pn : ℚ) / (pd : ℚ), div_nonneg (by exact_mod_cast hpn) (by exact_mod_cast hpd.le), ?_⟩
          intro i j
          have hn : (0 : ℤ) * (commonDen D S : ℤ) * (pd : ℤ) * (planeDen S : ℤ) +
              pn * (commonDen D S : ℤ) * planeNum S lx ux ly uy t i j ≤
                bernsteinNum A S lx ux ly uy i j * (pd : ℤ) * (planeDen S : ℤ) := by
            simpa only [zero_mul, zero_add] using hbplus i j
          simpa only [Int.cast_zero, zero_add] using
            line_ge_of_num A D S pd hD hS hpd lx ux ly uy t 0 pn i j hn
  | splitX mid left right ihLeft ihRight =>
      intro lx ux ly uy t h
      have hc : decide (2 * mid = lx + ux) = true ∧
          (check A D S lx mid ly uy t left && check A D S mid ux ly uy t right) = true := and_true h
      have hm : 2 * mid = lx + ux := of_decide_eq_true hc.1
      have hh := and_true hc.2
      have hl := ihLeft lx mid ly uy t hh.1
      have hr := ihRight mid ux ly uy t hh.2
      have hmid := coord_midpoint_of_num S hS lx ux mid hm
      rw [hmid] at hl hr
      exact N2RectangleBernstein.split_x_sound (rationalPower A D)
        (coord lx S) (coord ux S) (coord ly S) (coord uy S) ((t : ℚ) / 20) hl hr
  | splitY mid left right ihLeft ihRight =>
      intro lx ux ly uy t h
      have hc : decide (2 * mid = ly + uy) = true ∧
          (check A D S lx ux ly mid t left && check A D S lx ux mid uy t right) = true := and_true h
      have hm : 2 * mid = ly + uy := of_decide_eq_true hc.1
      have hh := and_true hc.2
      have hl := ihLeft lx ux ly mid t hh.1
      have hr := ihRight lx ux mid uy t hh.2
      have hmid := coord_midpoint_of_num S hS ly uy mid hm
      rw [hmid] at hl hr
      exact N2RectangleBernstein.split_y_sound (rationalPower A D)
        (coord lx S) (coord ux S) (coord ly S) (coord uy S) ((t : ℚ) / 20) hl hr
  | unresolved =>
      intro lx ux ly uy t h
      cases h

/-- The full original closed-box conclusion, with explicit positive
coefficient and coordinate denominators, follows from integer computation. -/
theorem check_sound (A : IntPower) (D S : ℕ) (hD : 0 < D) (hS : 0 < S)
    (lx ux ly uy t : ℤ) (certificate : Certificate)
    (hcheck : check A D S lx ux ly uy t certificate = true) :
    ∀ x y : ℝ, InBox (coord lx S) (coord ux S) (coord ly S) (coord uy S) x y →
      N2MomentMajorant.closedIndicator (((t : ℚ) / 20 : ℚ) : ℝ) x y ≤ evalPower (rationalPower A D) x y :=
  sound_by_recursion A D S hD hS certificate lx ux ly uy t hcheck

theorem check_unresolved (A : IntPower) (D S : ℕ) (lx ux ly uy t : ℤ) :
    check A D S lx ux ly uy t .unresolved = false := rfl

def microOnePower : IntPower := fun i j => if i.val = 0 ∧ j.val = 0 then 1 else 0

theorem micro_inside_check : check microOnePower 1 2 0 2 0 2 40 .inside = true := by decide +kernel

theorem micro_split_check :
    check microOnePower 1 2 0 2 0 2 20 (.splitX 1 (.cross 0 1 none) (.cross 0 1 none)) = true := by decide +kernel

theorem closed_plane_not_outside :
    check (fun _ _ => 0) 1 2 0 2 0 2 0 .outside = false := by decide +kernel

theorem zero_slope_den_rejected :
    check microOnePower 1 2 0 2 0 2 20 (.cross 0 0 none) = false := by decide +kernel

end BerryEsseen.N2IntegerRectangleCertificate

#print axioms BerryEsseen.N2IntegerRectangleCertificate.check_sound
#print axioms BerryEsseen.N2IntegerRectangleCertificate.check_unresolved
#print axioms BerryEsseen.N2IntegerRectangleCertificate.micro_inside_check
#print axioms BerryEsseen.N2IntegerRectangleCertificate.micro_split_check
#print axioms BerryEsseen.N2IntegerRectangleCertificate.closed_plane_not_outside
#print axioms BerryEsseen.N2IntegerRectangleCertificate.zero_slope_den_rejected
