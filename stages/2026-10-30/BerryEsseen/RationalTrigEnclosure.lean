module

public import BerryEsseen.CharacteristicExpansion

@[expose] public section

/-! 2026-10-29: rational trigonometric enclosures for the actual Prawitz
kernel evaluator. The imaginary exponential Taylor theorem supplies the
global remainder; the real argument may then move inside a midpoint cell.
No trigonometric value or host interval flag is assumed. -/

open scoped BigOperators

namespace BerryEsseen.RationalTrigEnclosure

def cosCoefficient (k : ℕ) : ℚ :=
  if k % 4 = 0 then 1 else if k % 4 = 2 then -1 else 0

def sinCoefficient (k : ℕ) : ℚ :=
  if k % 4 = 1 then 1 else if k % 4 = 3 then -1 else 0

def cosTaylorQ (m : ℕ) (q : ℚ) : ℚ :=
  ∑ k ∈ Finset.range (m + 1), cosCoefficient k * q ^ k / (k.factorial : ℚ)

def sinTaylorQ (m : ℕ) (q : ℚ) : ℚ :=
  ∑ k ∈ Finset.range (m + 1), sinCoefficient k * q ^ k / (k.factorial : ℚ)

def errorQ (m : ℕ) (q : ℚ) : ℚ :=
  |q| ^ (m + 1) / ((m + 1).factorial : ℚ)

noncomputable section

lemma I_pow_re (k : ℕ) : (Complex.I ^ k).re = (cosCoefficient k : ℝ) := by
  have hk := Nat.mod_lt k (by decide : 0 < 4)
  have hcases : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by omega
  rw [Complex.I_pow_eq_pow_mod]
  rcases hcases with h | h | h | h <;> norm_num [cosCoefficient, h]

lemma I_pow_im (k : ℕ) : (Complex.I ^ k).im = (sinCoefficient k : ℝ) := by
  have hk := Nat.mod_lt k (by decide : 0 < 4)
  have hcases : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by omega
  rw [Complex.I_pow_eq_pow_mod]
  rcases hcases with h | h | h | h <;> norm_num [sinCoefficient, h]

lemma cosTaylorQ_cast (m : ℕ) (q : ℚ) :
    (cosTaylorQ m q : ℝ) = (CharacteristicExpansion.expPolynomial m (q : ℝ)).re := by
  unfold cosTaylorQ CharacteristicExpansion.expPolynomial
  push_cast
  simp only [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [mul_pow]
  simp only [← Rat.cast_pow, Complex.div_natCast_re, Complex.mul_re,
    Complex.ratCast_re, Complex.ratCast_im, mul_zero, sub_zero, I_pow_re]

lemma sinTaylorQ_cast (m : ℕ) (q : ℚ) :
    (sinTaylorQ m q : ℝ) = (CharacteristicExpansion.expPolynomial m (q : ℝ)).im := by
  unfold sinTaylorQ CharacteristicExpansion.expPolynomial
  push_cast
  simp only [Complex.im_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [mul_pow]
  simp only [← Rat.cast_pow, Complex.div_natCast_im, Complex.mul_im,
    Complex.ratCast_re, Complex.ratCast_im, mul_zero, zero_add, I_pow_im]

lemma errorQ_cast (m : ℕ) (q : ℚ) :
    (errorQ m q : ℝ) = |(q : ℝ)| ^ (m + 1) / ((m + 1).factorial : ℝ) := by
  unfold errorQ
  push_cast
  rfl

theorem cos_at_rational_error (m : ℕ) (q : ℚ) :
    |Real.cos (q : ℝ) - (cosTaylorQ m q : ℝ)| ≤ (errorQ m q : ℝ) := by
  rw [cosTaylorQ_cast, errorQ_cast]
  have hh := (Complex.abs_re_le_norm
    (CharacteristicExpansion.pureExp (q : ℝ) - CharacteristicExpansion.expPolynomial m (q : ℝ))).trans
      (CharacteristicExpansion.pureExp_taylor_bound m (q : ℝ))
  simpa only [Complex.sub_re, CharacteristicExpansion.pureExp_real] using hh

theorem sin_at_rational_error (m : ℕ) (q : ℚ) :
    |Real.sin (q : ℝ) - (sinTaylorQ m q : ℝ)| ≤ (errorQ m q : ℝ) := by
  rw [sinTaylorQ_cast, errorQ_cast]
  have hp (x : ℝ) : (CharacteristicExpansion.pureExp x).im = Real.sin x := by
    simpa only [CharacteristicExpansion.pureExp, mul_comm] using Complex.exp_ofReal_mul_I_im x
  have hh := (Complex.abs_im_le_norm
    (CharacteristicExpansion.pureExp (q : ℝ) - CharacteristicExpansion.expPolynomial m (q : ℝ))).trans
      (CharacteristicExpansion.pureExp_taylor_bound m (q : ℝ))
  simpa only [Complex.sub_im, hp] using hh

theorem cos_midpoint_enclosure (m : ℕ) (q r : ℚ) (x : ℝ)
    (hx : |x - (q : ℝ)| ≤ (r : ℝ)) :
    ((cosTaylorQ m q - errorQ m q - r : ℚ) : ℝ) ≤ Real.cos x ∧
      Real.cos x ≤ ((cosTaylorQ m q + errorQ m q + r : ℚ) : ℝ) := by
  have ht := (abs_sub_le (Real.cos x) (Real.cos (q : ℝ)) (cosTaylorQ m q : ℝ)).trans
    (add_le_add ((Real.abs_cos_sub_cos_le x (q : ℝ)).trans hx) (cos_at_rational_error m q))
  have hb := abs_le.mp ht
  push_cast
  constructor <;> linarith only [hb.1, hb.2]

theorem sin_midpoint_enclosure (m : ℕ) (q r : ℚ) (x : ℝ)
    (hx : |x - (q : ℝ)| ≤ (r : ℝ)) :
    ((sinTaylorQ m q - errorQ m q - r : ℚ) : ℝ) ≤ Real.sin x ∧
      Real.sin x ≤ ((sinTaylorQ m q + errorQ m q + r : ℚ) : ℝ) := by
  have ht := (abs_sub_le (Real.sin x) (Real.sin (q : ℝ)) (sinTaylorQ m q : ℝ)).trans
    (add_le_add ((Real.abs_sin_sub_sin_le x (q : ℝ)).trans hx) (sin_at_rational_error m q))
  have hb := abs_le.mp ht
  push_cast
  constructor <;> linarith only [hb.1, hb.2]

end

end BerryEsseen.RationalTrigEnclosure

#print axioms BerryEsseen.RationalTrigEnclosure.cos_at_rational_error
#print axioms BerryEsseen.RationalTrigEnclosure.sin_at_rational_error
#print axioms BerryEsseen.RationalTrigEnclosure.cos_midpoint_enclosure
#print axioms BerryEsseen.RationalTrigEnclosure.sin_midpoint_enclosure
