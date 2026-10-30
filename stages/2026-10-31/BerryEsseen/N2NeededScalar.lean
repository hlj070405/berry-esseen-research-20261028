module

public import BerryEsseen.N2NeededData
public import BerryEsseen.N2ScalarReplay

@[expose] public section

/-! 2026-10-29: all original needed n2 scalar trees, rows005..069.
The unchanged closed rectangle is gamma in [-2,2], rho in [1,2], with
the actual moment-region constraint. Each kernel replay uses this row's
shared original coefficients and literal rounded R; no Gaussian formula
or stored Bernstein coefficient enters a leaf. The 93 existing nodes
are transcribed without mathematical host replay or new subdivisions. -/

namespace BerryEsseen.N2NeededScalar

open MeasureTheory N2MomentMajorant N2MajorantPolynomials N2NeededData N2ScalarCertificate

def trees : Fin 65 → Certificate :=
  ![
    -- original row005
    Certificate.accept,
    -- original row006
    Certificate.accept,
    -- original row007
    Certificate.accept,
    -- original row008
    Certificate.accept,
    -- original row009
    Certificate.accept,
    -- original row010
    Certificate.accept,
    -- original row011
    Certificate.accept,
    -- original row012
    Certificate.accept,
    -- original row013
    Certificate.accept,
    -- original row014
    (Certificate.splitGamma (0 / 1 : ℚ)
  Certificate.accept
  Certificate.accept),
    -- original row015
    (Certificate.splitGamma (0 / 1 : ℚ)
  Certificate.accept
  Certificate.accept),
    -- original row016
    (Certificate.splitGamma (0 / 1 : ℚ)
  Certificate.accept
  Certificate.accept),
    -- original row017
    (Certificate.splitGamma (0 / 1 : ℚ)
  Certificate.accept
  Certificate.accept),
    -- original row018
    (Certificate.splitGamma (0 / 1 : ℚ)
  Certificate.accept
  Certificate.accept),
    -- original row019
    (Certificate.splitGamma (0 / 1 : ℚ)
  Certificate.accept
  Certificate.accept),
    -- original row020
    Certificate.accept,
    -- original row021
    Certificate.accept,
    -- original row022
    Certificate.accept,
    -- original row023
    (Certificate.splitGamma (0 / 1 : ℚ)
  Certificate.accept
  Certificate.accept),
    -- original row024
    Certificate.accept,
    -- original row025
    Certificate.accept,
    -- original row026
    Certificate.accept,
    -- original row027
    Certificate.accept,
    -- original row028
    Certificate.accept,
    -- original row029
    Certificate.accept,
    -- original row030
    Certificate.accept,
    -- original row031
    (Certificate.splitGamma (0 / 1 : ℚ)
  (Certificate.splitGamma (-1 / 1 : ℚ)
    (Certificate.splitGamma (-3 / 2 : ℚ)
      (Certificate.splitRho (3 / 2 : ℚ)
        Certificate.discard
        Certificate.accept)
      Certificate.accept)
    Certificate.accept)
  (Certificate.splitGamma (1 / 1 : ℚ)
    Certificate.accept
    (Certificate.splitGamma (3 / 2 : ℚ)
      Certificate.accept
      (Certificate.splitRho (3 / 2 : ℚ)
        Certificate.discard
        Certificate.accept)))),
    -- original row032
    Certificate.accept,
    -- original row033
    Certificate.accept,
    -- original row034
    Certificate.accept,
    -- original row035
    Certificate.accept,
    -- original row036
    Certificate.accept,
    -- original row037
    Certificate.accept,
    -- original row038
    Certificate.accept,
    -- original row039
    Certificate.accept,
    -- original row040
    Certificate.accept,
    -- original row041
    Certificate.accept,
    -- original row042
    Certificate.accept,
    -- original row043
    Certificate.accept,
    -- original row044
    Certificate.accept,
    -- original row045
    Certificate.accept,
    -- original row046
    Certificate.accept,
    -- original row047
    Certificate.accept,
    -- original row048
    Certificate.accept,
    -- original row049
    Certificate.accept,
    -- original row050
    Certificate.accept,
    -- original row051
    Certificate.accept,
    -- original row052
    Certificate.accept,
    -- original row053
    Certificate.accept,
    -- original row054
    Certificate.accept,
    -- original row055
    Certificate.accept,
    -- original row056
    Certificate.accept,
    -- original row057
    Certificate.accept,
    -- original row058
    Certificate.accept,
    -- original row059
    Certificate.accept,
    -- original row060
    Certificate.accept,
    -- original row061
    Certificate.accept,
    -- original row062
    Certificate.accept,
    -- original row063
    Certificate.accept,
    -- original row064
    Certificate.accept,
    -- original row065
    Certificate.accept,
    -- original row066
    Certificate.accept,
    -- original row067
    Certificate.accept,
    -- original row068
    Certificate.accept,
    -- original row069
    Certificate.accept]

theorem checks (i : Fin 65) :
    check (pricePower (coefficients i) (gaussianR i) (2 / 7)) (-2) 2 1 2 (trees i) = true := by
  fin_cases i <;> decide +kernel

/-- The same actual law and the same source row are used on both sides. -/
theorem expectedPrice (i : Fin 65) (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (hρ : thirdAbsoluteMoment μ ≤ 2) :
    expected (coefficients i) (ZeroBias.gamma μ) (thirdAbsoluteMoment μ) ≤
      (gaussianR i : ℝ) + (2 : ℝ) / 7 * thirdAbsoluteMoment μ := by
  have hp := N2ScalarReplay.expected_le_of_check μ hμ hρ (coefficients i) (gaussianR i)
    (2 / 7) (trees i) (checks i)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hp
  exact hp

end BerryEsseen.N2NeededScalar

#print axioms BerryEsseen.N2NeededScalar.checks
#print axioms BerryEsseen.N2NeededScalar.expectedPrice
