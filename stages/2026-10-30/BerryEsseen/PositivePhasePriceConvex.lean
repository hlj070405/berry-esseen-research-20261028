module

public import BerryEsseen.GaussianTools
public import BerryEsseen.StopLossShape
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Convex.Jensen

@[expose] public section

/-! 2026-10-29: complete positive-Gaussian-phase convexity of the actual
reference-law price. The native Gaussian derivative identities establish
concavity on the closed nonnegative half-line. The integral-infimum Q is
used through its proved global convexity, with no differentiability or
attainment assumption, and closed degenerate phase intervals are allowed. -/

noncomputable section

open MeasureTheory Set

namespace BerryEsseen.PositivePhasePriceConvex

open GaussianTools

/-- The actual Gaussian density is antitone on the closed nonnegative
half-line, including zero where its derivative vanishes. -/
theorem phi_antitoneOn_nonnegative : AntitoneOn phi (Ici (0 : ℝ)) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici (0 : ℝ)) continuous_phi.continuousOn
  · intro x _
    exact (hasDerivAt_phi x).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [deriv_phi]
    have hx0 : 0 ≤ x := interior_subset hx
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hx0) (phi_nonneg x)

/-- Concavity of the native closed Gaussian CDF on its actual correct
side. This is derived from Φ′=φ and φ′=-xφ, not supplied as a hypothesis. -/
theorem Phi_concaveOn_nonnegative : ConcaveOn ℝ (Ici (0 : ℝ)) Phi := by
  apply AntitoneOn.concaveOn_of_deriv (convex_Ici (0 : ℝ))
  · exact (continuous_iff_continuousAt.mpr (fun x => (hasDerivAt_Phi x).continuousAt)).continuousOn
  · intro x _
    exact (hasDerivAt_Phi x).differentiableAt.differentiableWithinAt
  · intro x hx y hy hxy
    rw [deriv_Phi, deriv_Phi]
    exact phi_antitoneOn_nonnegative (interior_subset hx) (interior_subset hy) hxy

/-- D, eta, A, m, V and K, as well as the reference law, are fixed as phase
varies. Q is the literal integral-infimum price of StopLossShape. -/
def phasePrice (ν : Measure ℝ) (D eta A m V K t : ℝ) : ℝ :=
  D + eta * (t + StopLossShape.Q ν (A + t)) - Phi ((m + t) / Real.sqrt V) - K

theorem gaussian_argument_nonnegative (m V l u t : ℝ)
    (hV : 0 < V) (hleft : 0 ≤ m + l) (ht : t ∈ Icc l u) :
    (m + t) / Real.sqrt V ∈ Ici (0 : ℝ) := by
  apply div_nonneg _ (Real.sqrt_pos.mpr hV).le
  linarith only [hleft, ht.1]

/-- The whole closed phase interval is convex, although Q may have kinks.
Only the leftmost Gaussian argument must be nonnegative. -/
theorem phasePrice_convexOn (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hSq : Integrable (fun z : ℝ => z ^ 2) ν)
    (D eta A m V K l u : ℝ) (hV : 0 < V) (heta : 0 ≤ eta) (hleft : 0 ≤ m + l) :
    ConvexOn ℝ (Icc l u) (phasePrice ν D eta A m V K) := by
  refine ⟨convex_Icc l u, ?_⟩
  intro x hx y hy a b ha hb hab
  have hQ := (StopLossShape.Q_convex ν hSq).2 (mem_univ (A + x)) (mem_univ (A + y)) ha hb hab
  have hQarg : a * (A + x) + b * (A + y) = A + (a * x + b * y) := by
    calc
      _ = (a + b) * A + (a * x + b * y) := by ring
      _ = _ := by rw [hab]; ring
  change StopLossShape.Q ν (a * (A + x) + b * (A + y)) ≤
    a * StopLossShape.Q ν (A + x) + b * StopLossShape.Q ν (A + y) at hQ
  rw [hQarg] at hQ
  have hQeta := mul_le_mul_of_nonneg_left hQ heta
  have hPx := gaussian_argument_nonnegative m V l u x hV hleft hx
  have hPy := gaussian_argument_nonnegative m V l u y hV hleft hy
  have hPhi := Phi_concaveOn_nonnegative.2 hPx hPy ha hb hab
  change a * Phi ((m + x) / Real.sqrt V) + b * Phi ((m + y) / Real.sqrt V) ≤
    Phi (a * ((m + x) / Real.sqrt V) + b * ((m + y) / Real.sqrt V)) at hPhi
  have hPhiarg : a * ((m + x) / Real.sqrt V) + b * ((m + y) / Real.sqrt V) =
      (m + (a * x + b * y)) / Real.sqrt V := by
    calc
      _ = ((a + b) * m + (a * x + b * y)) / Real.sqrt V := by ring
      _ = _ := by rw [hab]; ring
  rw [hPhiarg] at hPhi
  have hconst : (a + b) * (D - K) = D - K := by rw [hab]; ring
  change phasePrice ν D eta A m V K (a * x + b * y) ≤
    a * phasePrice ν D eta A m V K x + b * phasePrice ν D eta A m V K y
  unfold phasePrice
  nlinarith only [hQeta, hPhi, hconst]

/-- The maximum of this actual price over its entire phase interval is
bounded by its two face values, including when the interval is a singleton. -/
theorem phasePrice_le_endpoints (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hSq : Integrable (fun z : ℝ => z ^ 2) ν)
    (D eta A m V K l u t : ℝ) (hV : 0 < V) (heta : 0 ≤ eta)
    (hleft : 0 ≤ m + l) (hlu : l ≤ u) (ht : t ∈ Icc l u) :
    phasePrice ν D eta A m V K t ≤
      max (phasePrice ν D eta A m V K l) (phasePrice ν D eta A m V K u) := by
  exact (phasePrice_convexOn ν hSq D eta A m V K l u hV heta hleft).le_max_of_mem_Icc
    (show l ∈ Icc l u from ⟨le_rfl, hlu⟩) (show u ∈ Icc l u from ⟨hlu, le_rfl⟩) ht

theorem phasePrice_le_of_endpoints (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hSq : Integrable (fun z : ℝ => z ^ 2) ν)
    (D eta A m V K l u B : ℝ) (hV : 0 < V) (heta : 0 ≤ eta)
    (hleft : 0 ≤ m + l) (hlu : l ≤ u)
    (hl : phasePrice ν D eta A m V K l ≤ B)
    (hu : phasePrice ν D eta A m V K u ≤ B) :
    ∀ t ∈ Icc l u, phasePrice ν D eta A m V K t ≤ B := by
  intro t ht
  exact (phasePrice_le_endpoints ν hSq D eta A m V K l u t hV heta hleft hlu ht).trans
    (max_le hl hu)

end BerryEsseen.PositivePhasePriceConvex

#print axioms BerryEsseen.PositivePhasePriceConvex.phi_antitoneOn_nonnegative
#print axioms BerryEsseen.PositivePhasePriceConvex.Phi_concaveOn_nonnegative
#print axioms BerryEsseen.PositivePhasePriceConvex.phasePrice_convexOn
#print axioms BerryEsseen.PositivePhasePriceConvex.phasePrice_le_endpoints
#print axioms BerryEsseen.PositivePhasePriceConvex.phasePrice_le_of_endpoints
