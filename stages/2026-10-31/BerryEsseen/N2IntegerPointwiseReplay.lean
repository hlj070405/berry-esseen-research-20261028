module

public import BerryEsseen.N2IntegerRectangleCertificate
public import BerryEsseen.N2MajorantPolynomials

@[expose] public section

/-! 2026-10-29: integer arithmetic on the original four closed orthants
returns the same rational majorant, once its coefficient identity is proved. -/

noncomputable section
namespace BerryEsseen.N2IntegerPointwiseReplay

open N2IntegerBernstein N2IntegerRectangleCertificate N2RectangleBernstein
  N2MajorantPolynomials N2MomentMajorant

def signX : Fin 4 → ℚ := ![-1, -1, 1, 1]
def signY : Fin 4 → ℚ := ![-1, 1, -1, 1]

def fourChecks (powers : Fin 4 → IntPower) (D S : ℕ) (t : ℤ)
    (trees : Fin 4 → Certificate) : Bool :=
  check (powers 0) D S (-6 * (S : ℤ)) 0 (-6 * (S : ℤ)) 0 t (trees 0) &&
    (check (powers 1) D S (-6 * (S : ℤ)) 0 0 (6 * (S : ℤ)) t (trees 1) &&
      (check (powers 2) D S 0 (6 * (S : ℤ)) (-6 * (S : ℤ)) 0 t (trees 2) &&
        check (powers 3) D S 0 (6 * (S : ℤ)) 0 (6 * (S : ℤ)) t (trees 3)))

private theorem and_true {p q : Bool} (h : (p && q) = true) : p = true ∧ q = true := by
  cases p <;> cases q <;> simp_all

private theorem coord_mul (k : ℤ) (S : ℕ) (hS : 0 < S) : coord (k * (S : ℤ)) S = k := by
  have hS0 : (S : ℚ) ≠ 0 := by exact_mod_cast hS.ne'
  unfold coord
  push_cast
  field_simp [hS0]

theorem pointwise_of_fourChecks (c : Coefficients) (ε : ℚ)
    (powers : Fin 4 → IntPower) (D S : ℕ) (t : ℤ) (trees : Fin 4 → Certificate)
    (hD : 0 < D) (hS : 0 < S)
    (hpowers : ∀ o : Fin 4,
      rationalPower (powers o) D = orthantPower c (signX o) (signY o) ε)
    (hcheck : fourChecks powers D S t trees = true) :
    ∀ x y : ℝ, |x| ≤ 6 → |y| ≤ 6 →
      closedIndicator (((t : ℚ) / 20 : ℚ) : ℝ) x y ≤ majorant c x y + (ε : ℝ) := by
  have hs := and_true hcheck
  have hs1 := and_true hs.2
  have hs2 := and_true hs1.2
  have hn6 := coord_mul (-6) S hS
  have hp6 := coord_mul 6 S hS
  have hz : coord 0 S = 0 := by simp [coord]
  have h0 := check_sound (powers 0) D S hD hS (-6 * (S : ℤ)) 0 (-6 * (S : ℤ)) 0
    t (trees 0) hs.1
  have h1 := check_sound (powers 1) D S hD hS (-6 * (S : ℤ)) 0 0 (6 * (S : ℤ))
    t (trees 1) hs1.1
  have h2 := check_sound (powers 2) D S hD hS 0 (6 * (S : ℤ)) (-6 * (S : ℤ)) 0
    t (trees 2) hs2.1
  have h3 := check_sound (powers 3) D S hD hS 0 (6 * (S : ℤ)) 0 (6 * (S : ℤ))
    t (trees 3) hs2.2
  rw [hn6, hz, hpowers 0] at h0
  rw [hn6, hz, hp6, hpowers 1] at h1
  rw [hz, hn6, hp6, hpowers 2] at h2
  rw [hz, hp6, hpowers 3] at h3
  intro x y hx hy
  have hxy : InBox (-6) 6 (-6) 6 x y := by
    norm_num only [InBox]
    exact ⟨abs_le.mp hx, abs_le.mp hy⟩
  rcases cube_orthants_cover 6 x y hxy with hb0 | hb1 | hb2 | hb3
  · have hb := h0 x y hb0
    change closedIndicator (((t : ℚ) / 20 : ℚ) : ℝ) x y ≤
      evalPower (orthantPower c (-1) (-1) ε) x y at hb
    rw [← majorant_eq_neg_neg c ε x y
      (by simpa only [Rat.cast_zero] using hb0.1.2)
      (by simpa only [Rat.cast_zero] using hb0.2.2)] at hb
    exact hb
  · have hb := h1 x y hb1
    change closedIndicator (((t : ℚ) / 20 : ℚ) : ℝ) x y ≤
      evalPower (orthantPower c (-1) 1 ε) x y at hb
    rw [← majorant_eq_neg_pos c ε x y
      (by simpa only [Rat.cast_zero] using hb1.1.2)
      (by simpa only [Rat.cast_zero] using hb1.2.1)] at hb
    exact hb
  · have hb := h2 x y hb2
    change closedIndicator (((t : ℚ) / 20 : ℚ) : ℝ) x y ≤
      evalPower (orthantPower c 1 (-1) ε) x y at hb
    rw [← majorant_eq_pos_neg c ε x y
      (by simpa only [Rat.cast_zero] using hb2.1.1)
      (by simpa only [Rat.cast_zero] using hb2.2.2)] at hb
    exact hb
  · have hb := h3 x y hb3
    change closedIndicator (((t : ℚ) / 20 : ℚ) : ℝ) x y ≤
      evalPower (orthantPower c 1 1 ε) x y at hb
    rw [← majorant_eq_pos_pos c ε x y
      (by simpa only [Rat.cast_zero] using hb3.1.1)
      (by simpa only [Rat.cast_zero] using hb3.2.1)] at hb
    exact hb

end BerryEsseen.N2IntegerPointwiseReplay

#print axioms BerryEsseen.N2IntegerPointwiseReplay.pointwise_of_fourChecks
