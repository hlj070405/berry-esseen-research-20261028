module

public import BerryEsseen.P39LowCountVarianceAcquisition
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

@[expose] public section

/-! 2026-10-31: acquire a coupled inward/noise cap for the same actual
N26/P39 maximum. The cubic budget uses the convex chord of the actual
scale squared, including lambda=0. Endpoint square-root caps are rational;
neither a free scale profile nor diagnostic floating-point prices enter.
-/

noncomputable section

namespace BerryEsseen.P39CoupledInwardNoise

open MeasureTheory Set
open CanonicalSign CentralGap NoiseCoordinates
open P39Count11VarianceAcquisition (retainedCost)

def noiseUpper : ℝ := 793 / 2500
def cubeIntercept : ℝ := (6 / 25) * (49 / 100)
def cubeSlope : ℝ :=
  ((1261 / 5000) * (201 / 400) - (6 / 25) * (49 / 100)) / noiseUpper

def gapCoefficient : ℝ :=
  ConservedTransfer.kappa * 6 * 26 * (2379 / 10000) * (15 / 16)

def noiseCoefficient : ℝ := ConservedTransfer.kappa * 3 * (154 / 25) * (131 / 400)
def netNoiseCoefficient : ℝ := noiseCoefficient - (92 / 75) * cubeSlope
def rhsIntercept : ℝ := (92 / 75) * cubeIntercept

/-- A positive algorithmic cap; its licensing for the actual inward sum
is proved below, not assumed as a resource profile. -/
def d (lambda : ℝ) : ℝ := 39 / 625 - (79 / 500) * lambda

theorem rational_gates :
    rhsIntercept < gapCoefficient * (39 / 625) ∧
      gapCoefficient * (79 / 500) < netNoiseCoefficient := by
  norm_num [rhsIntercept, gapCoefficient, netNoiseCoefficient, noiseCoefficient,
    cubeIntercept, cubeSlope, noiseUpper, ConservedTransfer.kappa]

theorem coefficient_values : gapCoefficient = (92502657 : ℝ) / 40000000 ∧
    netNoiseCoefficient = (7274989027 : ℝ) / 19825000000 ∧
    rhsIntercept = (2254 : ℝ) / 15625 := by
  norm_num [gapCoefficient, netNoiseCoefficient, noiseCoefficient, rhsIntercept,
    cubeIntercept, cubeSlope, noiseUpper, ConservedTransfer.kappa]

private lemma rpow_three_halves (x : ℝ) (hx : 0 ≤ x) :
    x ^ ((3 : ℝ) / 2) = Real.sqrt x ^ 3 :=
  (Real.rpow_div_two_eq_sqrt (x := x) (3 : ℝ) hx).trans (Real.rpow_ofNat _ 3)

/-- The scale cube is paid by a convex chord in its actual noise.
Only the variance identity and the proved noise interval are required. -/
theorem scale_cube_le_chord (v c lambda : ℝ) (hv : v ≤ (6 : ℝ) / 25)
    (hc : 0 ≤ c) (hl : lambda ∈ Icc (0 : ℝ) noiseUpper)
    (hscale : c ^ 2 = v + lambda / 26) :
    c ^ 3 ≤ cubeIntercept + cubeSlope * lambda := by
  let theta : ℝ := lambda / noiseUpper
  have hU : 0 < noiseUpper := by norm_num [noiseUpper]
  have ht0 : 0 ≤ theta := div_nonneg hl.1 hU.le
  have ht1 : theta ≤ 1 := (div_le_one₀ hU).mpr hl.2
  have hm : (1 - theta) * (6 / 25 : ℝ) + theta * (1261 / 5000) =
      (6 / 25 : ℝ) + lambda / 26 := by
    dsimp [theta, noiseUpper]
    ring
  have hv0 : (6 / 25 : ℝ) ∈ Ici 0 := by norm_num
  have hv1 : (1261 / 5000 : ℝ) ∈ Ici 0 := by norm_num
  have hconv := (convexOn_rpow (p := (3 : ℝ) / 2) (by norm_num)).2 hv0 hv1
    (show 0 ≤ 1 - theta by linarith only [ht1]) ht0 (by ring : (1 - theta) + theta = 1)
  change ((1 - theta) * (6 / 25 : ℝ) + theta * (1261 / 5000)) ^ ((3 : ℝ) / 2) ≤
    (1 - theta) * (6 / 25 : ℝ) ^ ((3 : ℝ) / 2) +
      theta * (1261 / 5000 : ℝ) ^ ((3 : ℝ) / 2) at hconv
  rw [hm] at hconv
  have hr0 : Real.sqrt (6 / 25 : ℝ) ≤ (49 : ℝ) / 100 := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6 / 25),
      Real.sqrt_nonneg (6 / 25 : ℝ)]
  have hr1 : Real.sqrt (1261 / 5000 : ℝ) ≤ (201 : ℝ) / 400 := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1261 / 5000),
      Real.sqrt_nonneg (1261 / 5000 : ℝ)]
  have hf0 : (6 / 25 : ℝ) ^ ((3 : ℝ) / 2) ≤ (6 / 25 : ℝ) * (49 / 100) := by
    rw [rpow_three_halves _ (by norm_num), pow_succ,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6 / 25)]
    exact mul_le_mul_of_nonneg_left hr0 (by norm_num)
  have hf1 : (1261 / 5000 : ℝ) ^ ((3 : ℝ) / 2) ≤ (1261 / 5000 : ℝ) * (201 / 400) := by
    rw [rpow_three_halves _ (by norm_num), pow_succ,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1261 / 5000)]
    exact mul_le_mul_of_nonneg_left hr1 (by norm_num)
  have hc2 : c ^ 2 ≤ (6 / 25 : ℝ) + lambda / 26 := by linarith only [hscale, hv]
  have hpow := Real.rpow_le_rpow (sq_nonneg c) hc2 (by norm_num : (0 : ℝ) ≤ (3 : ℝ) / 2)
  rw [rpow_three_halves _ (sq_nonneg c), Real.sqrt_sq hc] at hpow
  have hface := add_le_add
    (mul_le_mul_of_nonneg_left hf0 (show 0 ≤ 1 - theta by linarith only [ht1]))
    (mul_le_mul_of_nonneg_left hf1 ht0)
  calc
    _ ≤ ((6 / 25 : ℝ) + lambda / 26) ^ ((3 : ℝ) / 2) := hpow
    _ ≤ (1 - theta) * ((6 / 25 : ℝ) * (49 / 100)) +
        theta * ((1261 / 5000 : ℝ) * (201 / 400)) := hconv.trans hface
    _ = cubeIntercept + cubeSlope * lambda := by
      dsimp [theta, cubeIntercept, cubeSlope, noiseUpper]
      ring

theorem noise_bracket_lower (p a b alpha : ℝ)
    (hp : p ∈ Icc (39 / 100 : ℝ) (2 / 5)) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hdelta : a + b ≤ (1 : ℝ) / 16) (halpha : alpha ∈ Icc (0 : ℝ) 1) :
    (154 / 25 : ℝ) * (131 / 400) ≤
      (Real.sqrt 10 + 3) * (p - a) * (1 - alpha) +
        (Real.sqrt 10 + 1) * ((1 - p) - b) * alpha := by
  have hA : (131 : ℝ) / 400 ≤ p - a := by linarith only [hp.1, hdelta, hb]
  have hB : (43 : ℝ) / 80 ≤ (1 - p) - b := by linarith only [hp.2, hdelta, ha]
  have h0 := mul_le_mul
    (show (154 : ℝ) / 25 ≤ Real.sqrt 10 + 3 by linarith only [P39InwardBudget.sqrt_ten_lower]) hA
    (by norm_num : (0 : ℝ) ≤ 131 / 400) (by positivity : 0 ≤ Real.sqrt 10 + 3)
  have h1raw := mul_le_mul
    (show (104 : ℝ) / 25 ≤ Real.sqrt 10 + 1 by linarith only [P39InwardBudget.sqrt_ten_lower]) hB
    (by norm_num : (0 : ℝ) ≤ 43 / 80) (by positivity : 0 ≤ Real.sqrt 10 + 1)
  have h1 : (154 / 25 : ℝ) * (131 / 400) ≤ (Real.sqrt 10 + 1) * ((1 - p) - b) :=
    (by norm_num : (154 / 25 : ℝ) * (131 / 400) ≤ (104 / 25) * (43 / 80)).trans h1raw
  have hw0 := mul_le_mul_of_nonneg_right h0 (sub_nonneg.mpr halpha.2)
  have hw1 := mul_le_mul_of_nonneg_right h1 halpha.1
  nlinarith only [hw0, hw1]

/-- The chord and actual retained resource yield a coupled cap, rather
than independently maximizing the inward and noise coordinates. -/
theorem coupled_bound_of_resource (p c a b lambda alpha : ℝ)
    (hp : p ∈ Icc (39 / 100 : ℝ) (2 / 5)) (hc : 0 ≤ c)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hdelta : a + b ≤ (1 : ℝ) / 16)
    (hl : lambda ∈ Icc (0 : ℝ) noiseUpper) (halpha : alpha ∈ Icc (0 : ℝ) 1)
    (hscale : c ^ 2 = p * (1 - p) + lambda / 26)
    (hbudget : retainedCost p (1 - p) a b lambda alpha ≤ (92 / 75 : ℝ) * c ^ 3) :
    a + b + (79 / 500) * lambda < (39 : ℝ) / 625 := by
  obtain ⟨hpq0, hpq1⟩ := P39InwardBudget.probability_variance_bounds p hp
  have hp0 : 0 ≤ p := by linarith only [hp.1]
  have hq0 : 0 ≤ 1 - p := by linarith only [hp.2]
  have hk := ConservedTransfer.kappa_pos.le
  have hquad := mul_nonneg (add_nonneg ha hb) (sub_nonneg.mpr hdelta)
  have hgap : (15 / 16 : ℝ) * (a + b) ≤ CanonicalInwardBudget.gapMass a b := by
    unfold CanonicalInwardBudget.gapMass
    nlinarith only [hquad, mul_nonneg ha hb]
  have hprod := mul_le_mul hpq0 hgap (show 0 ≤ (15 / 16 : ℝ) * (a + b) by positivity)
    (mul_nonneg hp0 hq0)
  have hG := mul_le_mul_of_nonneg_left hprod
    (show 0 ≤ ConservedTransfer.kappa * 6 * 26 by positivity)
  have hbracket := noise_bracket_lower p a b alpha hp ha hb hdelta halpha
  have hk3 : 0 ≤ ConservedTransfer.kappa * 3 := mul_nonneg hk (by norm_num)
  have hN := mul_le_mul_of_nonneg_left hbracket
    (mul_nonneg hk3 hl.1)
  have hleft : gapCoefficient * (a + b) + noiseCoefficient * lambda ≤
      retainedCost p (1 - p) a b lambda alpha := by
    unfold gapCoefficient noiseCoefficient retainedCost
    nlinarith only [hG, hN]
  have hcube := scale_cube_le_chord (p * (1 - p)) c lambda hpq1 hc hl hscale
  have hright := mul_le_mul_of_nonneg_left hcube (by norm_num : (0 : ℝ) ≤ 92 / 75)
  have hplane : gapCoefficient * (a + b) + netNoiseCoefficient * lambda ≤ rhsIntercept := by
    unfold netNoiseCoefficient rhsIntercept
    nlinarith only [hleft, hbudget, hright]
  norm_num only [gapCoefficient, netNoiseCoefficient, noiseCoefficient, rhsIntercept,
    cubeIntercept, cubeSlope, noiseUpper, ConservedTransfer.kappa] at hplane
  nlinarith only [hplane, hl.1]

theorem d_bounds (lambda : ℝ) (hl : lambda ∈ Icc (0 : ℝ) noiseUpper) :
    0 < d lambda ∧ d lambda ≤ (1 : ℝ) / 16 := by
  have h0 := hl.1
  have h1 := hl.2
  unfold noiseUpper at h1
  unfold d
  constructor <;> linarith only [h0, h1]

/-- Every scalar input is acquired from this same original N26 maximum,
including its full C25 predecessor and actual scale/noise identity. -/
theorem original_coupled_bound (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (H C : ℝ) (hm : ContactVariation.PositiveClosedMaximum μ 26 H C)
    (hprev : Extremizer.fixedNSup 25 ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10)
    (hp : p μ ∈ Icc (39 / 100 : ℝ) (2 / 5)) :
    a0 μ h + a1 μ h + (79 / 500) * noiseLevel μ h 26 < (39 : ℝ) / 625 := by
  have hd := (P39InwardBudget.original_inward_lt_sixteenth μ h H C hm hprev hC hρ hp).le
  have hl0 : 0 ≤ noiseLevel μ h 26 :=
    mul_nonneg (Nat.cast_nonneg 26) (noiseVariance_nonneg μ h)
  have hl1 := (P39LowCountVarianceAcquisition.original_noiseLevel_lt μ h H C hm hprev hC hρ hp).le
  have hscale : scale μ h ^ 2 = p μ * (1 - p μ) + noiseLevel μ h 26 / 26 := by
    rw [CanonicalSign.scale_sq]
    unfold noiseLevel q
    ring
  exact coupled_bound_of_resource (p μ) (scale μ h) (a0 μ h) (a1 μ h)
    (noiseLevel μ h 26) (ConditionalResidual.actualAllocation μ h) hp (scale_pos μ h).le
    (a0_nonneg μ h) (a1_nonneg μ h) hd ⟨hl0, hl1⟩
    (PhysicalResourcePlane.actualAllocation_mem_Icc μ h) hscale
    (P39Count11VarianceAcquisition.original_retained_budget μ h H C hm hprev hC hρ)

theorem original_inward_lt_d (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (H C : ℝ) (hm : ContactVariation.PositiveClosedMaximum μ 26 H C)
    (hprev : Extremizer.fixedNSup 25 ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10)
    (hp : p μ ∈ Icc (39 / 100 : ℝ) (2 / 5)) :
    a0 μ h + a1 μ h < d (noiseLevel μ h 26) := by
  have hh := original_coupled_bound μ h H C hm hprev hC hρ hp
  unfold d
  linarith only [hh]

theorem original_d_bounds (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (H C : ℝ) (hm : ContactVariation.PositiveClosedMaximum μ 26 H C)
    (hprev : Extremizer.fixedNSup 25 ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10)
    (hp : p μ ∈ Icc (39 / 100 : ℝ) (2 / 5)) :
    0 < d (noiseLevel μ h 26) ∧ d (noiseLevel μ h 26) ≤ (1 : ℝ) / 16 :=
  d_bounds _ ⟨mul_nonneg (Nat.cast_nonneg 26) (noiseVariance_nonneg μ h),
    (P39LowCountVarianceAcquisition.original_noiseLevel_lt μ h H C hm hprev hC hρ hp).le⟩

end BerryEsseen.P39CoupledInwardNoise

#print axioms BerryEsseen.P39CoupledInwardNoise.scale_cube_le_chord
#print axioms BerryEsseen.P39CoupledInwardNoise.coupled_bound_of_resource
#print axioms BerryEsseen.P39CoupledInwardNoise.d_bounds
#print axioms BerryEsseen.P39CoupledInwardNoise.original_coupled_bound
#print axioms BerryEsseen.P39CoupledInwardNoise.original_inward_lt_d
#print axioms BerryEsseen.P39CoupledInwardNoise.original_d_bounds
