module

public import BerryEsseen.N2NeededGaussian
public import BerryEsseen.N2NeededScalar
public import BerryEsseen.N2MajorantInterval
public import BerryEsseen.N2FiniteCover

@[expose] public section

/-! 2026-10-29: all scalar and Gaussian prices are concrete kernel
theorems. The remaining pointwise family is explicit until its replay
has been completed; this file does not assert that replay is finished. -/

noncomputable section
open MeasureTheory Set

namespace BerryEsseen.N2NeededAssembly
open N2NeededData N2MomentMajorant GaussianTools

def cost : ℝ := 2 / 7 + 1 / 1000

def PointwiseFamily : Prop := ∀ (i : Fin 65) (x y : ℝ), |x| ≤ 6 → |y| ≤ 6 →
  closedIndicator (upperQ i : ℝ) x y ≤ majorant (coefficients i) x y + (1 : ℝ) / 1000

theorem actual_price (i : Fin 65) (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hρ : thirdAbsoluteMoment μ ≤ 2) :
    expected (coefficients i) (ZeroBias.gamma μ) (thirdAbsoluteMoment μ) + (1 : ℝ) / 1000 ≤
      Phi (N2FiniteCover.lower i / Real.sqrt 2) + cost * thirdAbsoluteMoment μ := by
  have hp := N2ScalarReplay.lifted_price_of_check μ h hρ (coefficients i) (gaussianR i)
    (2 / 7) (1 / 1000) (N2NeededScalar.trees i) (N2NeededScalar.checks i)
    (N2FiniteCover.lower i / Real.sqrt 2) (N2NeededGaussian.lowerPrice_real i) (by norm_num)
  simpa only [cost, Rat.cast_add, Rat.cast_div, Rat.cast_ofNat, Rat.cast_one] using hp

theorem rowBounds_of_pointwise (hpoints : PointwiseFamily) (i : Fin 65) :
    N2FiniteCover.RowBound cost i := by
  intro μ h hρ hR H hH
  have hpoint : ∀ x y : ℝ, |x| ≤ 6 → |y| ≤ 6 →
      closedIndicator (N2FiniteCover.upper i) x y ≤
        majorant (coefficients i) x y + (1 : ℝ) / 1000 := by
    intro x y hx hy
    simpa only [upperQ_cast] using hpoints i x y hx hy
  exact N2MajorantInterval.original_interval μ h (coefficients i) 6
    (N2FiniteCover.lower i) (N2FiniteCover.upper i) H (1 / 1000) cost hR hH hpoint
    (actual_price i μ h hρ)

/-- Only the still-unproved pointwise family is a hypothesis here. -/
theorem sharp_two_of_pointwise (hpoints : PointwiseFamily) :
    Reflection.AbsoluteClosedBound 2 esseenConstant := by
  apply N2FiniteCover.absoluteClosedBound_of_rows cost
  · dsimp [cost]
    norm_num
  · exact N2CompactReduction.lifted_price_lt_esseen
  · exact rowBounds_of_pointwise hpoints

end BerryEsseen.N2NeededAssembly

#print axioms BerryEsseen.N2NeededAssembly.actual_price
#print axioms BerryEsseen.N2NeededAssembly.rowBounds_of_pointwise
#print axioms BerryEsseen.N2NeededAssembly.sharp_two_of_pointwise
