module

public import BerryEsseen.ConservedResource

@[expose] public section

/-! 2026-10-29: quadratic envelopes of the literal actual raw resource.
The signed third moment is never reflected. Numerical coefficient and
Fourier prices remain explicit certificates about these actual quantities. -/

noncomputable section

open MeasureTheory

namespace BerryEsseen.RawResourceEnvelope

open GaussianTools

def baseBracket (μ : ProbabilityMeasure ℝ) : ℝ :=
  (3 / 2 : ℝ) * SignedMoment.signedSecondMoment μ * GapDefect.actualJ μ +
    3 * thirdAbsoluteMoment μ * ContactGapSum.actualJ1 μ -
      3 * ContactGapSum.actualJ2 μ - ContactZeroBiasMoment.Kq μ

def baseTerm (μ : ProbabilityMeasure ℝ) (C : ℝ) : ℝ := C * baseBracket μ

def linearTerm (μ : ProbabilityMeasure ℝ) (n : ℕ) (H C : ℝ) : ℝ :=
  C * ContactWeightedMoment.K1 μ + phi (H / Real.sqrt n) *
    (ContactGapSum.actualJ1 μ + (ContactZeroBiasMoment.fourthMoment μ - 3) / 6)

def quadTerm (μ : ProbabilityMeasure ℝ) (n : ℕ) (H C : ℝ) : ℝ :=
  C * thirdAbsoluteMoment μ + ZeroBias.gamma μ * phi (H / Real.sqrt n) / 2

theorem raw_eq_actual_terms (μ : ProbabilityMeasure ℝ) (n : ℕ) (H C : ℝ) :
    ConservedResource.raw μ n H C = baseTerm μ C + H * linearTerm μ n H C -
      H ^ 2 * quadTerm μ n H C + FourierRemainder.value μ n H := by
  unfold ConservedResource.raw baseTerm baseBracket linearTerm quadTerm
  rfl

/-- The half-axis price uses the positive part of the slope. -/
def halfAxisPrice (A F Q : ℝ) : ℝ := A + max F 0 ^ 2 / (4 * Q)

theorem quadratic_le_halfAxisPrice (A F Q y : ℝ) (hQ : 0 < Q) (hy : 0 ≤ y) :
    A + F * y - Q * y ^ 2 ≤ halfAxisPrice A F Q := by
  have hF : F * y ≤ max F 0 * y := mul_le_mul_of_nonneg_right (le_max_left F 0) hy
  have hquad : max F 0 * y - Q * y ^ 2 ≤ max F 0 ^ 2 / (4 * Q) := by
    apply (le_div_iff₀ (show 0 < 4 * Q by positivity)).mpr
    nlinarith only [sq_nonneg (2 * Q * y - max F 0)]
  unfold halfAxisPrice
  nlinarith only [hF, hquad]

/-- This price is attained on y≥0. In particular a negative slope attains
its maximum at zero, rather than at a fictitious negative vertex. -/
theorem halfAxisPrice_attained (A F Q : ℝ) (hQ : 0 < Q) :
    ∃ y : ℝ, 0 ≤ y ∧ A + F * y - Q * y ^ 2 = halfAxisPrice A F Q := by
  by_cases hF : 0 ≤ F
  · refine ⟨F / (2 * Q), div_nonneg hF (by positivity), ?_⟩
    unfold halfAxisPrice
    rw [max_eq_left hF]
    field_simp [hQ.ne']
    ring
  · refine ⟨0, le_rfl, ?_⟩
    simp [halfAxisPrice, max_eq_right (le_of_not_ge hF)]

/-- The original positive-H half-axis, derived from actual coefficients
and the actual Fourier remainder rather than from a free raw-error premise. -/
theorem raw_le_positive_envelope (μ : ProbabilityMeasure ℝ) (n : ℕ) (H C A Fhi Q KF sF : ℝ)
    (hH : 0 ≤ H) (hbase : baseTerm μ C ≤ A) (hlinear : linearTerm μ n H C ≤ Fhi)
    (hquad : Q ≤ quadTerm μ n H C)
    (hFourier : |FourierRemainder.value μ n H| ≤ KF + sF * |H|) :
    ConservedResource.raw μ n H C ≤ A + KF + (Fhi + sF) * |H| - Q * H ^ 2 := by
  have hlin := mul_le_mul_of_nonneg_left hlinear hH
  have hq := mul_le_mul_of_nonneg_left hquad (sq_nonneg H)
  have hE := (le_abs_self (FourierRemainder.value μ n H)).trans hFourier
  rw [abs_of_nonneg hH] at hE ⊢
  rw [raw_eq_actual_terms]
  nlinarith only [hbase, hlin, hq, hE]

/-- Multiplication by negative H uses the lower linear coefficient. -/
theorem raw_le_negative_envelope (μ : ProbabilityMeasure ℝ) (n : ℕ) (H C A Flo Q KF sF : ℝ)
    (hH : H ≤ 0) (hbase : baseTerm μ C ≤ A) (hlinear : Flo ≤ linearTerm μ n H C)
    (hquad : Q ≤ quadTerm μ n H C)
    (hFourier : |FourierRemainder.value μ n H| ≤ KF + sF * |H|) :
    ConservedResource.raw μ n H C ≤ A + KF + (sF - Flo) * |H| - Q * H ^ 2 := by
  have hlin := mul_le_mul_of_nonpos_left hlinear hH
  have hq := mul_le_mul_of_nonneg_left hquad (sq_nonneg H)
  have hE := (le_abs_self (FourierRemainder.value μ n H)).trans hFourier
  rw [abs_of_nonpos hH] at hE ⊢
  rw [raw_eq_actual_terms]
  nlinarith only [hbase, hlin, hq, hE]

def twoSidedPrice (A Flo Fhi Q KF sF : ℝ) : ℝ :=
  max (halfAxisPrice (A + KF) (Fhi + sF) Q) (halfAxisPrice (A + KF) (sF - Flo) Q)

/-- Every real original H is controlled by one of the two genuine
half-axis maxima. No sign restriction is placed on either effective slope. -/
theorem raw_le_twoSidedPrice (μ : ProbabilityMeasure ℝ) (n : ℕ) (H C A Flo Fhi Q KF sF : ℝ)
    (hbase : baseTerm μ C ≤ A)
    (hlinear : Flo ≤ linearTerm μ n H C ∧ linearTerm μ n H C ≤ Fhi)
    (hquad : Q ≤ quadTerm μ n H C) (hQ : 0 < Q)
    (hFourier : |FourierRemainder.value μ n H| ≤ KF + sF * |H|) :
    ConservedResource.raw μ n H C ≤ twoSidedPrice A Flo Fhi Q KF sF := by
  rcases le_total 0 H with hH | hH
  · have he := raw_le_positive_envelope μ n H C A Fhi Q KF sF hH hbase hlinear.2 hquad hFourier
    have hp := quadratic_le_halfAxisPrice (A + KF) (Fhi + sF) Q |H| hQ (abs_nonneg H)
    rw [sq_abs] at hp
    exact he.trans (hp.trans (le_max_left _ _))
  · have he := raw_le_negative_envelope μ n H C A Flo Q KF sF hH hbase hlinear.1 hquad hFourier
    have hp := quadratic_le_halfAxisPrice (A + KF) (sF - Flo) Q |H| hQ (abs_nonneg H)
    rw [sq_abs] at hp
    exact he.trans (hp.trans (le_max_right _ _))

/-- Uniform coefficient certificates yield an entire-real-H raw bound.
These hypotheses do not claim that numerical moment prices are already known. -/
theorem raw_le_uniform_twoSidedPrice (μ : ProbabilityMeasure ℝ) (n : ℕ)
    (C A Flo Fhi Q KF sF : ℝ) (hbase : baseTerm μ C ≤ A)
    (hlinear : ∀ H : ℝ, Flo ≤ linearTerm μ n H C ∧ linearTerm μ n H C ≤ Fhi)
    (hquad : ∀ H : ℝ, Q ≤ quadTerm μ n H C) (hQ : 0 < Q)
    (hFourier : ∀ H : ℝ, |FourierRemainder.value μ n H| ≤ KF + sF * |H|) :
    ∀ H : ℝ, ConservedResource.raw μ n H C ≤ twoSidedPrice A Flo Fhi Q KF sF := by
  intro H
  exact raw_le_twoSidedPrice μ n H C A Flo Fhi Q KF sF hbase (hlinear H) (hquad H) hQ (hFourier H)

/-- A single explicit subtraction of an already licensed phase quadratic
adds its curvature once. This does not assert any new lower bound on the
actual quadTerm and does not supply the phase certificate itself. -/
theorem raw_sub_quadratic_le_twoSidedPrice (μ : ProbabilityMeasure ℝ) (n : ℕ)
    (H C A Flo Fhi Q curv KF sF : ℝ) (hbase : baseTerm μ C ≤ A)
    (hlinear : Flo ≤ linearTerm μ n H C ∧ linearTerm μ n H C ≤ Fhi)
    (hquad : Q ≤ quadTerm μ n H C) (hQcurv : 0 < Q + curv)
    (hFourier : |FourierRemainder.value μ n H| ≤ KF + sF * |H|) :
    ConservedResource.raw μ n H C - curv * H ^ 2 ≤
      twoSidedPrice A Flo Fhi (Q + curv) KF sF := by
  rcases le_total 0 H with hH | hH
  · have he := raw_le_positive_envelope μ n H C A Fhi Q KF sF hH hbase hlinear.2 hquad hFourier
    have hshift : ConservedResource.raw μ n H C - curv * H ^ 2 ≤
        A + KF + (Fhi + sF) * |H| - (Q + curv) * H ^ 2 := by nlinarith only [he]
    have hp := quadratic_le_halfAxisPrice (A + KF) (Fhi + sF) (Q + curv) |H|
      hQcurv (abs_nonneg H)
    rw [sq_abs] at hp
    exact hshift.trans (hp.trans (le_max_left _ _))
  · have he := raw_le_negative_envelope μ n H C A Flo Q KF sF hH hbase hlinear.1 hquad hFourier
    have hshift : ConservedResource.raw μ n H C - curv * H ^ 2 ≤
        A + KF + (sF - Flo) * |H| - (Q + curv) * H ^ 2 := by nlinarith only [he]
    have hp := quadratic_le_halfAxisPrice (A + KF) (sF - Flo) (Q + curv) |H|
      hQcurv (abs_nonneg H)
    rw [sq_abs] at hp
    exact hshift.trans (hp.trans (le_max_right _ _))

/-- The actual signed gamma is bounded below before multiplying by the
nonnegative Gaussian density. For negative g0 the upper density endpoint is used. -/
theorem quadTerm_ge_signed_price (μ : ProbabilityMeasure ℝ) (n : ℕ)
    (H C Clo rhoLo g0 Lphi Uphi : ℝ)
    (hClo0 : 0 ≤ Clo) (hC : Clo ≤ C) (hrho0 : 0 ≤ rhoLo)
    (hrho : rhoLo ≤ thirdAbsoluteMoment μ) (hgamma : g0 ≤ ZeroBias.gamma μ)
    (hL0 : 0 ≤ Lphi) (hL : Lphi ≤ phi (H / Real.sqrt n))
    (hU : phi (H / Real.sqrt n) ≤ Uphi) :
    Clo * rhoLo + min (Lphi * g0) (Uphi * g0) / 2 ≤ quadTerm μ n H C := by
  have hC0 : 0 ≤ C := hClo0.trans hC
  have hprod : Clo * rhoLo ≤ C * thirdAbsoluteMoment μ := mul_le_mul hC hrho hrho0 hC0
  have hphi0 : 0 ≤ phi (H / Real.sqrt n) := hL0.trans hL
  have hgammaPhi := mul_le_mul_of_nonneg_right hgamma hphi0
  have hendpoint : min (Lphi * g0) (Uphi * g0) ≤ phi (H / Real.sqrt n) * g0 := by
    rcases le_total 0 g0 with hg0 | hg0
    · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_right hL hg0)
    · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_right hU hg0)
  unfold quadTerm
  nlinarith only [hprod, hgammaPhi, hendpoint]

/-- Bounding a bracket from above requires nonnegative C. A negative
bracket price then correctly uses the lower endpoint of the C interval. -/
theorem baseTerm_le_signed_bracket_price (μ : ProbabilityMeasure ℝ) (C Cl Cu B : ℝ)
    (hCl0 : 0 ≤ Cl) (hCl : Cl ≤ C) (hCu : C ≤ Cu) (hB : baseBracket μ ≤ B) :
    baseTerm μ C ≤ if B < 0 then Cl * B else Cu * B := by
  have hC0 : 0 ≤ C := hCl0.trans hCl
  have hb := mul_le_mul_of_nonneg_left hB hC0
  unfold baseTerm
  by_cases hsign : B < 0
  · rw [if_pos hsign]
    exact hb.trans (mul_le_mul_of_nonpos_right hCl hsign.le)
  · rw [if_neg hsign]
    exact hb.trans (mul_le_mul_of_nonneg_right hCu (le_of_not_gt hsign))

end BerryEsseen.RawResourceEnvelope

#print axioms BerryEsseen.RawResourceEnvelope.quadratic_le_halfAxisPrice
#print axioms BerryEsseen.RawResourceEnvelope.halfAxisPrice_attained
#print axioms BerryEsseen.RawResourceEnvelope.raw_le_twoSidedPrice
#print axioms BerryEsseen.RawResourceEnvelope.raw_le_uniform_twoSidedPrice
#print axioms BerryEsseen.RawResourceEnvelope.raw_sub_quadratic_le_twoSidedPrice
#print axioms BerryEsseen.RawResourceEnvelope.quadTerm_ge_signed_price
#print axioms BerryEsseen.RawResourceEnvelope.baseTerm_le_signed_bracket_price
