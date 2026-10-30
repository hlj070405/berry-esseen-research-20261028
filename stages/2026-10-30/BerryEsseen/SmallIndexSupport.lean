module

public import BerryEsseen.SupportContact
public import BerryEsseen.GaussianPrices

@[expose] public section

/-! 2026-10-29: full two-sided radius-six exclusions for the actual contact
variation at indices two and three. Only lower normalized contact costs enter. -/

noncomputable section

open MeasureTheory Set

namespace BerryEsseen.SmallIndexSupport

open GaussianTools GaussianPrices ContactVariation

/-- The exact density has its global `t * phi t` maximum at one. -/
theorem mul_phi_le_phi_one (t : ℝ) : t * phi t ≤ phi 1 := by
  have ht : t ≤ Real.exp ((t ^ 2 - 1) / 2) := by
    have he := Real.add_one_le_exp ((t ^ 2 - 1) / 2)
    nlinarith [sq_nonneg (t - 1)]
  have heq : phi t * Real.exp ((t ^ 2 - 1) / 2) = phi 1 := by
    rw [phi_eq_phi_zero_mul_exp t, phi_eq_phi_zero_mul_exp 1]
    rw [mul_assoc, ← Real.exp_add]
    congr 1
    congr 1
    ring
  calc
    t * phi t ≤ Real.exp ((t ^ 2 - 1) / 2) * phi t :=
      mul_le_mul_of_nonneg_right ht (phi_nonneg t)
    _ = phi 1 := by rw [mul_comm]; exact heq

/-- Both signs of the actual Gaussian argument are covered. -/
theorem abs_mul_phi_le_quarter (t : ℝ) : |t * phi t| ≤ (1 : ℝ) / 4 := by
  have habs : phi |t| = phi t := by simp only [phi_formula, sq_abs]
  have hmax := mul_phi_le_phi_one |t|
  rw [habs] at hmax
  rw [abs_mul, abs_of_nonneg (phi_nonneg t)]
  linarith [phi_one_lt_49_200]

theorem phi_le_two_fifths (t : ℝ) : phi t ≤ (2 : ℝ) / 5 := by
  have he : Real.exp (-(t ^ 2 / 2)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg t])
  rw [phi_eq_phi_zero_mul_exp]
  exact (mul_le_mul_of_nonneg_left he (phi_nonneg 0)).trans
    (by simpa only [mul_one] using phi_zero_lt_2_5.le)

/-- This is a bound on the actual first variation, including its genuine CDFs. -/
theorem D_le_gaussian_bound (μ : ProbabilityMeasure ℝ) (n : ℕ) (H C x : ℝ)
    (hx : 1 ≤ |x|) :
    D μ n H C x ≤ (n : ℝ) + (2 : ℝ) / 5 * Real.sqrt n * |x| +
      (|x| ^ 2 - 1) / 8 - (C / Real.sqrt n) * momentSlope μ x := by
  have hcdf :
      (MixtureSum.iidSumLaw (μ : Measure ℝ) (n - 1)).real (Iic (H - x)) -
        (MixtureSum.iidSumLaw (μ : Measure ℝ) n).real (Iic H) ≤ 1 := by
    have hu : (MixtureSum.iidSumLaw (μ : Measure ℝ) (n - 1)).real
        (Iic (H - x)) ≤ 1 := measureReal_le_one
    have hl : 0 ≤ (MixtureSum.iidSumLaw (μ : Measure ℝ) n).real (Iic H) :=
      measureReal_nonneg
    linarith
  have hn := mul_le_mul_of_nonneg_left hcdf (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hlin : phi (H / Real.sqrt n) * (Real.sqrt n * x) ≤
      (2 : ℝ) / 5 * Real.sqrt n * |x| := by
    calc
      _ ≤ phi (H / Real.sqrt n) * (Real.sqrt n * |x|) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (le_abs_self x) (Real.sqrt_nonneg _))
          (phi_nonneg _)
      _ ≤ _ := by
        have hb := mul_le_mul_of_nonneg_right (phi_le_two_fifths (H / Real.sqrt n))
          (mul_nonneg (Real.sqrt_nonneg (n : ℝ)) (abs_nonneg x))
        nlinarith only [hb]
  have hsq : 0 ≤ x ^ 2 - 1 := by nlinarith [sq_abs x]
  have hquad : phi (H / Real.sqrt n) *
      ((H / Real.sqrt n) / 2 * (x ^ 2 - 1)) ≤ (|x| ^ 2 - 1) / 8 := by
    have ht : H / Real.sqrt n * phi (H / Real.sqrt n) ≤ (1 : ℝ) / 4 :=
      (le_abs_self _).trans (abs_mul_phi_le_quarter _)
    have hm := mul_le_mul_of_nonneg_right ht hsq
    rw [sq_abs]
    nlinarith only [hm]
  unfold D
  nlinarith only [hn, hlin, hquad]

theorem abs_signedSecondMoment_le_one (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    |SignedMoment.signedSecondMoment μ| ≤ 1 := by
  have hb := SignedMoment.first_sq_add_signed_sq_le_one μ h
  have hs : |SignedMoment.signedSecondMoment μ| ^ 2 ≤ 1 := by
    rw [sq_abs]
    nlinarith [sq_nonneg (SignedMoment.firstAbsoluteMoment μ)]
  nlinarith [abs_nonneg (SignedMoment.signedSecondMoment μ)]

theorem momentSlope_lower (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (R x : ℝ) (hR : thirdAbsoluteMoment μ ≤ R) :
    |x| ^ 3 - (3 / 2 : ℝ) * R * |x| ^ 2 - 3 * |x| ≤ momentSlope μ x := by
  have hρ : 0 ≤ thirdAbsoluteMoment μ :=
    integral_nonneg fun t => pow_nonneg (abs_nonneg t) 3
  have hcap := mul_le_mul_of_nonneg_right hR (sq_nonneg x)
  have hβ : SignedMoment.signedSecondMoment μ * x ≤ |x| := by
    calc
      _ ≤ |SignedMoment.signedSecondMoment μ * x| := le_abs_self _
      _ = |SignedMoment.signedSecondMoment μ| * |x| := abs_mul _ _
      _ ≤ 1 * |x| := mul_le_mul_of_nonneg_right
        (abs_signedSecondMoment_le_one μ h) (abs_nonneg x)
      _ = |x| := one_mul _
  unfold momentSlope
  rw [sq_abs]
  nlinarith only [hρ, hcap, hβ]

theorem cubic_floor_nonneg (R r : ℝ) (hR : R ≤ 2) (hr : 6 ≤ r) :
    0 ≤ r ^ 3 - (3 / 2 : ℝ) * R * r ^ 2 - 3 * r := by
  have hq : 0 ≤ r ^ 2 - 3 * r - 3 := by
    nlinarith [mul_nonneg (show 0 ≤ r - 6 by linarith) (show 0 ≤ r + 3 by linarith)]
  have hb := mul_nonneg (show 0 ≤ r by linarith) hq
  have hc : (3 / 2 : ℝ) * R * r ^ 2 ≤ 3 * r ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg r)
  nlinarith only [hb, hc]

/-- A nonnegative actual moment slope permits lowering the normalized cost. -/
theorem D_le_ray_bound (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (H C x R c : ℝ) (hR : thirdAbsoluteMoment μ ≤ R) (hR2 : R ≤ 2)
    (hc : 0 ≤ c) (hcost : c ≤ C / Real.sqrt n) (hx : 6 ≤ |x|) :
    D μ n H C x ≤ (n : ℝ) + (2 : ℝ) / 5 * Real.sqrt n * |x| +
      (|x| ^ 2 - 1) / 8 - c * (|x| ^ 3 - (3 / 2 : ℝ) * R * |x| ^ 2 - 3 * |x|) := by
  have hfloor := cubic_floor_nonneg R |x| hR2 hx
  have hslope := momentSlope_lower μ h R x hR
  have hM : 0 ≤ momentSlope μ x := hfloor.trans hslope
  have hpaid : c * (|x| ^ 3 - (3 / 2 : ℝ) * R * |x| ^ 2 - 3 * |x|) ≤
      (C / Real.sqrt n) * momentSlope μ x :=
    (mul_le_mul_of_nonneg_left hslope hc).trans (mul_le_mul_of_nonneg_right hcost hM)
  have hd := D_le_gaussian_bound μ n H C x (by linarith)
  linarith

private lemma two_polynomial_pos (r : ℝ) (hr : 6 ≤ r) :
    0 < (2 / 7 : ℝ) * r ^ 3 - 55 / 56 * r ^ 2 - 10 / 7 * r - 15 / 8 := by
  have hz : 0 ≤ r - 6 := by linarith
  have heq : (2 / 7 : ℝ) * r ^ 3 - 55 / 56 * r ^ 2 - 10 / 7 * r - 15 / 8 =
      891 / 56 + 247 / 14 * (r - 6) + 233 / 56 * (r - 6) ^ 2 +
        2 / 7 * (r - 6) ^ 3 := by ring
  rw [heq]
  positivity

private lemma three_polynomial_pos (r : ℝ) (hr : 6 ≤ r) :
    0 < (59 / 250 : ℝ) * r ^ 3 - 631 / 800 * r ^ 2 - 176 / 125 * r - 23 / 8 := by
  have hz : 0 ≤ r - 6 := by linarith
  have heq : (59 / 250 : ℝ) * r ^ 3 - 631 / 800 * r ^ 2 - 176 / 125 * r - 23 / 8 =
      5629 / 500 + 2923 / 200 * (r - 6) + 13837 / 4000 * (r - 6) ^ 2 +
        59 / 250 * (r - 6) ^ 3 := by ring
  rw [heq]
  positivity

/-- Uniformly in the original threshold, the entire two-sided ray is excluded. -/
theorem D_two_neg (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (H C x : ℝ)
    (hρ : thirdAbsoluteMoment μ ≤ 2) (hcost : (2 : ℝ) / 7 ≤ C / Real.sqrt 2)
    (hx : 6 ≤ |x|) : D μ 2 H C x < 0 := by
  have hd := D_le_ray_bound μ h 2 H C x 2 (2 / 7) hρ (by norm_num)
    (by norm_num) (by simpa using hcost) hx
  have hs : (2 : ℝ) / 5 * Real.sqrt 2 ≤ 4 / 7 := by
    have he := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hn := Real.sqrt_nonneg (2 : ℝ)
    nlinarith
  have hl := mul_le_mul_of_nonneg_right hs (abs_nonneg x)
  have hp := two_polynomial_pos |x| hx
  rw [sq_abs] at hp
  norm_num at hd
  nlinarith only [hd, hl, hp]

theorem D_three_neg (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (H C x : ℝ)
    (hρ : thirdAbsoluteMoment μ ≤ (15 : ℝ) / 8)
    (hcost : (59 : ℝ) / 250 ≤ C / Real.sqrt 3)
    (hx : 6 ≤ |x|) : D μ 3 H C x < 0 := by
  have hd := D_le_ray_bound μ h 3 H C x (15 / 8) (59 / 250) hρ (by norm_num)
    (by norm_num) (by simpa using hcost) hx
  have hs : (2 : ℝ) / 5 * Real.sqrt 3 ≤ 7 / 10 := by
    have he := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
    have hn := Real.sqrt_nonneg (3 : ℝ)
    nlinarith
  have hl := mul_le_mul_of_nonneg_right hs (abs_nonneg x)
  have hp := three_polynomial_pos |x| hx
  rw [sq_abs] at hp
  norm_num at hd
  nlinarith only [hd, hl, hp]

/-- The actual support, including its atoms, lies strictly inside radius six. -/
theorem support_two (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (H C : ℝ)
    (hm : PositiveClosedMaximum μ 2 H C) (hρ : thirdAbsoluteMoment μ ≤ 2)
    (hcost : (2 : ℝ) / 7 ≤ C / Real.sqrt 2) :
    (μ : Measure ℝ).support ⊆ Ioo (-6) 6 := by
  intro x hxs
  apply abs_lt.mp
  by_contra hnot
  have hd := D_two_neg μ h H C x hρ hcost (le_of_not_gt hnot)
  rw [SupportContact.D_eq_zero_on_support μ h 2 (by norm_num) H C hm x hxs] at hd
  exact (lt_irrefl 0) hd

theorem support_three (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (H C : ℝ)
    (hm : PositiveClosedMaximum μ 3 H C)
    (hρ : thirdAbsoluteMoment μ ≤ (15 : ℝ) / 8)
    (hcost : (59 : ℝ) / 250 ≤ C / Real.sqrt 3) :
    (μ : Measure ℝ).support ⊆ Ioo (-6) 6 := by
  intro x hxs
  apply abs_lt.mp
  by_contra hnot
  have hd := D_three_neg μ h H C x hρ hcost (le_of_not_gt hnot)
  rw [SupportContact.D_eq_zero_on_support μ h 3 (by norm_num) H C hm x hxs] at hd
  exact (lt_irrefl 0) hd

theorem support_two_of_C_lower (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (H C : ℝ) (hm : PositiveClosedMaximum μ 2 H C) (hρ : thirdAbsoluteMoment μ ≤ 2)
    (hC : (2 : ℝ) / 7 * Real.sqrt 2 ≤ C) :
    (μ : Measure ℝ).support ⊆ Ioo (-6) 6 :=
  support_two μ h H C hm hρ ((le_div_iff₀ (Real.sqrt_pos.mpr (by norm_num))).mpr hC)

theorem support_three_of_C_lower (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (H C : ℝ) (hm : PositiveClosedMaximum μ 3 H C)
    (hρ : thirdAbsoluteMoment μ ≤ (15 : ℝ) / 8)
    (hC : (59 : ℝ) / 250 * Real.sqrt 3 ≤ C) :
    (μ : Measure ℝ).support ⊆ Ioo (-6) 6 :=
  support_three μ h H C hm hρ ((le_div_iff₀ (Real.sqrt_pos.mpr (by norm_num))).mpr hC)

end BerryEsseen.SmallIndexSupport

#print axioms BerryEsseen.SmallIndexSupport.abs_mul_phi_le_quarter
#print axioms BerryEsseen.SmallIndexSupport.D_le_gaussian_bound
#print axioms BerryEsseen.SmallIndexSupport.D_le_ray_bound
#print axioms BerryEsseen.SmallIndexSupport.D_two_neg
#print axioms BerryEsseen.SmallIndexSupport.D_three_neg
#print axioms BerryEsseen.SmallIndexSupport.support_two
#print axioms BerryEsseen.SmallIndexSupport.support_three
