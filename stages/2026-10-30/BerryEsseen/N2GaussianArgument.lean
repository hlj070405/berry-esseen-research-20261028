module

public import BerryEsseen.RationalGaussianPrices

@[expose] public section

/-! 2026-10-29: sign-aware exact rational Gaussian argument gates.
One rounded lower price is evaluated once, outside the rectangle leaves. -/

noncomputable section
open MeasureTheory Set

namespace BerryEsseen.N2GaussianArgument
open GaussianTools RationalGaussianPrices

def ArgumentGate (t z : ℚ) : Prop :=
  (t ≤ 0 ∧ z ≤ 0 ∧ t ^ 2 ≤ 2 * z ^ 2) ∨
    (0 ≤ t ∧ 0 ≤ z ∧ 2 * z ^ 2 ≤ t ^ 2)

theorem argument_le (t z : ℚ) (hgate : ArgumentGate t z) :
    (z : ℝ) ≤ (t : ℝ) / Real.sqrt 2 := by
  have hspos : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hs : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  apply (le_div_iff₀ hspos).mpr
  rcases hgate with ⟨ht, hz, hsq⟩ | ⟨ht, hz, hsq⟩
  · have htR : (t : ℝ) ≤ 0 := by exact_mod_cast ht
    have hzR : (z : ℝ) ≤ 0 := by exact_mod_cast hz
    have hg : (t : ℝ) ^ 2 ≤ 2 * (z : ℝ) ^ 2 := by exact_mod_cast hsq
    have hleft : (z : ℝ) * Real.sqrt 2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hzR hspos.le
    have hsqR : (t : ℝ) ^ 2 ≤ ((z : ℝ) * Real.sqrt 2) ^ 2 := by
      rw [mul_pow, hs]
      nlinarith only [hg]
    have hn := (sq_le_sq₀ (neg_nonneg.mpr htR) (neg_nonneg.mpr hleft)).mp
      (by simpa only [neg_sq] using hsqR)
    linarith only [hn]
  · have htR : 0 ≤ (t : ℝ) := by exact_mod_cast ht
    have hzR : 0 ≤ (z : ℝ) := by exact_mod_cast hz
    have hg : 2 * (z : ℝ) ^ 2 ≤ (t : ℝ) ^ 2 := by exact_mod_cast hsq
    have hleft : 0 ≤ (z : ℝ) * Real.sqrt 2 := mul_nonneg hzR hspos.le
    apply (sq_le_sq₀ hleft htR).mp
    rw [mul_pow, hs]
    nlinarith only [hg]

/-- The rational rounding hypothesis is checked once per original row;
all subsequent leaves use only the small rational R. -/
theorem rounded_price_le_Phi (m : ℕ) (t z R : ℚ)
    (hgate : ArgumentGate t z) (hR : R ≤ PhiLower m z) :
    (R : ℝ) ≤ Phi ((t : ℝ) / Real.sqrt 2) := by
  have hRreal : (R : ℝ) ≤ (PhiLower m z : ℝ) := by exact_mod_cast hR
  have hm : Phi (z : ℝ) ≤ Phi ((t : ℝ) / Real.sqrt 2) :=
    measureReal_mono (Iic_subset_Iic.mpr (argument_le t z hgate))
  exact hRreal.trans ((Phi_rational_bounds m z).1.trans hm)

end BerryEsseen.N2GaussianArgument

#print axioms BerryEsseen.N2GaussianArgument.argument_le
#print axioms BerryEsseen.N2GaussianArgument.rounded_price_le_Phi
