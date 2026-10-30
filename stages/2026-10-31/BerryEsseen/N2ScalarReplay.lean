module

public import BerryEsseen.N2ScalarCertificate
public import BerryEsseen.N2MajorantPolynomials
public import BerryEsseen.ThirdMomentRegion
public import BerryEsseen.GaussianTools

@[expose] public section

/-! 2026-10-29: a verified physical-moment certificate prices the
expectation for the same original standardized law. The pointwise lift
is paid once using the actual lower bound rho >= 1. -/

noncomputable section
open MeasureTheory

namespace BerryEsseen.N2ScalarReplay
open N2RectangleBernstein N2MomentMajorant N2MajorantPolynomials GaussianTools

theorem expected_le_of_check (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hρ : thirdAbsoluteMoment μ ≤ 2) (c : Coefficients) (R L : ℚ)
    (certificate : N2ScalarCertificate.Certificate)
    (hc : N2ScalarCertificate.check (pricePower c R L) (-2) 2 1 2 certificate = true) :
    expected c (ZeroBias.gamma μ) (thirdAbsoluteMoment μ) ≤
      (R : ℝ) + (L : ℝ) * thirdAbsoluteMoment μ := by
  have hr := ThirdMomentRegion.one_le_third μ h
  have hg : |ZeroBias.gamma μ| ≤ 2 := (ThirdMomentRegion.abs_gamma_le_third μ).trans hρ
  have hb : InBox (-2) 2 1 2 (ZeroBias.gamma μ) (thirdAbsoluteMoment μ) := by
    norm_num only [InBox]
    exact ⟨abs_le.mp hg, ⟨hr, hρ⟩⟩
  have hf : 0 ≤ N2MomentRectangle.feasibility (ZeroBias.gamma μ) (thirdAbsoluteMoment μ) := by
    exact ThirdMomentRegion.feasibility_polynomial_nonneg μ h
  have hp := N2ScalarCertificate.check_sound (pricePower c R L) (-2) 2 1 2 certificate hc
    (ZeroBias.gamma μ) (thirdAbsoluteMoment μ) hb hr hρ hf
  rw [pricePower_representation] at hp
  linarith only [hp]

theorem lifted_price_of_check (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hρ : thirdAbsoluteMoment μ ≤ 2) (c : Coefficients) (R L ε : ℚ)
    (certificate : N2ScalarCertificate.Certificate)
    (hc : N2ScalarCertificate.check (pricePower c R L) (-2) 2 1 2 certificate = true)
    (t : ℝ) (hG : (R : ℝ) ≤ Phi t) (hε : 0 ≤ ε) :
    expected c (ZeroBias.gamma μ) (thirdAbsoluteMoment μ) + (ε : ℝ) ≤
      Phi t + ((L + ε : ℚ) : ℝ) * thirdAbsoluteMoment μ := by
  have hb := expected_le_of_check μ h hρ c R L certificate hc
  have hr := ThirdMomentRegion.one_le_third μ h
  have he : 0 ≤ (ε : ℝ) := by exact_mod_cast hε
  have hpaid : (ε : ℝ) ≤ (ε : ℝ) * thirdAbsoluteMoment μ := by nlinarith only [hr, he]
  push_cast
  nlinarith only [hb, hG, hpaid]

end BerryEsseen.N2ScalarReplay

#print axioms BerryEsseen.N2ScalarReplay.expected_le_of_check
#print axioms BerryEsseen.N2ScalarReplay.lifted_price_of_check
