module

public import BerryEsseen.CanonicalResidualMomentBounds
public import BerryEsseen.CanonicalInwardBudget
public import BerryEsseen.MomentBudgetNoise
public import BerryEsseen.P39Count11VarianceAcquisition
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

@[expose] public section

noncomputable section

namespace BerryEsseen.P39CoarseNoiseIncrement

open MeasureTheory Set
open CanonicalSign CentralGap

def base (p : ℝ) : ℝ := P39Reference.v p * (1 - 2 * P39Reference.v p)
def coefficient (p : ℝ) : ℝ := 3 * p - 7 / 80

/-- A lower price obtained from the actual cubic identity and inward cap. -/
def coarseFloor (p s : ℝ) : ℝ :=
  (base p + coefficient p * s) / Real.sqrt (P39Reference.v p + s) ^ 3

def coarseDerivative (p s : ℝ) : ℝ :=
  (coefficient p * P39Reference.v p - 3 * base p / 2 - coefficient p * s / 2) /
    ((P39Reference.v p + s) ^ 2 * Real.sqrt (P39Reference.v p + s))

def compensatedFloor (p s : ℝ) : ℝ := coarseFloor p s - (19 / 10 : ℝ) * s

theorem strip_variance_bounds {p : ℝ} (hp : p ∈ Icc (39 / 100 : ℝ) (2 / 5)) :
    (2379 / 10000 : ℝ) ≤ P39Reference.v p ∧ P39Reference.v p ≤ 6 / 25 := by
  have hL := mul_nonneg (sub_nonneg.mpr hp.1)
    (show 0 ≤ 61 / 100 - p by linarith only [hp.2])
  have hU := mul_nonneg (sub_nonneg.mpr hp.2)
    (show 0 ≤ 3 / 5 - p by linarith only [hp.2])
  unfold P39Reference.v
  constructor <;> nlinarith only [hL, hU]

theorem base_le {p : ℝ} (hp : p ∈ Icc (39 / 100 : ℝ) (2 / 5)) :
    base p ≤ 78 / 625 := by
  have hv := strip_variance_bounds hp
  have hpoly := mul_nonneg (sub_nonneg.mpr hv.2)
    (show 0 ≤ 1 - 2 * ((6 / 25 : ℝ) + P39Reference.v p) by linarith only [hv.2])
  unfold base
  nlinarith only [hpoly]

/-- The numerical gate is entirely rational; no old small-delta or
quarter-variance gate is used. -/
theorem derivative_ge {p s : ℝ} (hp : p ∈ Icc (39 / 100 : ℝ) (2 / 5))
    (hs : s ∈ Icc (0 : ℝ) (17 / 1300)) :
    (19 / 10 : ℝ) ≤ coarseDerivative p s := by
  have hv := strip_variance_bounds hp
  have hbase := base_le hp
  have hA : coefficient p ∈ Icc (433 / 400 : ℝ) (89 / 80) := by
    unfold coefficient
    constructor <;> linarith only [hp.1, hp.2]
  have hA0 : 0 ≤ coefficient p := by linarith only [hA.1]
  have hR0 : 0 < P39Reference.v p + s := by linarith only [hv.1, hs.1]
  have hR1 : P39Reference.v p + s ≤ 51 / 200 := by linarith only [hv.2, hs.2]
  have hroot : Real.sqrt (P39Reference.v p + s) ≤ 51 / 100 := by
    have hsq := Real.sq_sqrt hR0.le
    have hnn := Real.sqrt_nonneg (P39Reference.v p + s)
    nlinarith only [hsq, hnn, hR1]
  have hsq : (P39Reference.v p + s) ^ 2 ≤ (51 / 200 : ℝ) ^ 2 :=
    (sq_le_sq₀ hR0.le (by norm_num)).mpr hR1
  have hden := mul_le_mul hsq hroot (Real.sqrt_nonneg _)
    (by norm_num : (0 : ℝ) ≤ (51 / 200) ^ 2)
  have hav := mul_le_mul hA.1 hv.1 (by norm_num : (0 : ℝ) ≤ 2379 / 10000) hA0
  have has := mul_le_mul hA.2 hs.2 hs.1 (by norm_num : (0 : ℝ) ≤ 89 / 80)
  have hgate :
      (19 / 10 : ℝ) * ((51 / 200) ^ 2 * (51 / 100)) <
        (433 / 400) * (2379 / 10000) - (3 / 2) * (78 / 625) -
          (1 / 2) * (89 / 80) * (17 / 1300) := by norm_num
  unfold coarseDerivative
  apply (le_div_iff₀ (mul_pos (sq_pos_of_pos hR0) (Real.sqrt_pos.mpr hR0))).mpr
  have hprice := mul_le_mul_of_nonneg_left hden (by norm_num : (0 : ℝ) ≤ 19 / 10)
  nlinarith only [hprice, hgate, hav, has, hbase]

theorem hasDerivAt_coarseFloor {p s : ℝ}
    (hp : p ∈ Icc (39 / 100 : ℝ) (2 / 5)) (hs : 0 ≤ s) :
    HasDerivAt (coarseFloor p) (coarseDerivative p s) s := by
  have hv := strip_variance_bounds hp
  have hR : 0 < P39Reference.v p + s := by linarith only [hv.1, hs]
  have hd := MomentBudgetNoise.hasDerivAt_value
    (v := P39Reference.v p) (a := base p) (b := coefficient p) (c := 0) hR
  convert hd using 1
  · funext t
    simp only [coarseFloor, MomentBudgetNoise.value, zero_mul, add_zero]
  · unfold coarseDerivative MomentBudgetNoise.first
    ring

theorem hasDerivAt_compensatedFloor {p s : ℝ}
    (hp : p ∈ Icc (39 / 100 : ℝ) (2 / 5)) (hs : 0 ≤ s) :
    HasDerivAt (compensatedFloor p) (coarseDerivative p s - 19 / 10) s := by
  convert (hasDerivAt_coarseFloor hp hs).sub
    ((hasDerivAt_id' s).const_mul (19 / 10 : ℝ)) using 1
  · funext t
    rfl
  · ring

theorem compensatedFloor_monotone {p s1 : ℝ}
    (hp : p ∈ Icc (39 / 100 : ℝ) (2 / 5)) (hs1 : s1 ≤ 17 / 1300) :
    MonotoneOn (compensatedFloor p) (Icc 0 s1) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 s1)
  · intro s hs
    exact (hasDerivAt_compensatedFloor hp hs.1).continuousAt.continuousWithinAt
  · intro s hs
    have hs' : s ∈ Icc (0 : ℝ) s1 := interior_subset hs
    exact (hasDerivAt_compensatedFloor hp hs'.1).hasDerivWithinAt
  · intro s hs
    have hs' : s ∈ Icc (0 : ℝ) s1 := interior_subset hs
    have hd := derivative_ge hp (show s ∈ Icc (0 : ℝ) (17 / 1300) from
      ⟨hs'.1, hs'.2.trans hs1⟩)
    linarith only [hd]

theorem zero_noise_eq_rho0 {p : ℝ} (hp : p ∈ Icc (39 / 100 : ℝ) (2 / 5)) :
    coarseFloor p 0 = P39Reference.rho0 p := by
  have hv : 0 < P39Reference.v p := by linarith only [(strip_variance_bounds hp).1]
  unfold coarseFloor base P39Reference.rho0
  simp only [mul_zero, add_zero]
  rw [pow_succ, Real.sq_sqrt hv.le]
  field_simp [hv.ne', (Real.sqrt_pos.mpr hv).ne']

theorem coarseFloor_ge_rho0_add_noise {p s : ℝ}
    (hp : p ∈ Icc (39 / 100 : ℝ) (2 / 5)) (hs : s ∈ Icc (0 : ℝ) (17 / 1300)) :
    P39Reference.rho0 p + (19 / 10 : ℝ) * s ≤ coarseFloor p s := by
  have hm := compensatedFloor_monotone hp hs.2
    (show (0 : ℝ) ∈ Icc 0 s from ⟨le_rfl, hs.1⟩)
    (show s ∈ Icc (0 : ℝ) s from ⟨hs.1, le_rfl⟩) hs.1
  unfold compensatedFloor at hm
  rw [zero_noise_eq_rho0 hp] at hm
  linarith only [hm]

/-- The first cubic bounds need only the existing genuine L1 cube moments. -/
theorem residual_cubic_cap_bounds (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    MomentBudget.residualCubicMoment (residual0 μ h) ≤
        a0 μ h * MomentBudget.residualSecondMoment (residual0 μ h) ∧
      -(a1 μ h) * MomentBudget.residualSecondMoment (residual1 μ h) ≤
        MomentBudget.residualCubicMoment (residual1 μ h) := by
  have h0 := residual0_centered μ h
  have h1 := residual1_centered μ h
  constructor
  · have hi := integral_mono_ae h0.integrable_third
      (h0.integrable_second.const_mul (a0 μ h))
      ((residual0_upper μ h).mono fun u hu => by
        have hh := mul_le_mul_of_nonneg_right hu (sq_nonneg u)
        change u ^ 3 ≤ a0 μ h * u ^ 2
        nlinarith only [hh])
    rw [integral_const_mul] at hi
    exact hi
  · have hi := integral_mono_ae (h1.integrable_second.const_mul (-a1 μ h))
      h1.integrable_third ((residual1_lower μ h).mono fun u hu => by
        have hh := mul_le_mul_of_nonneg_right hu (sq_nonneg u)
        change -(a1 μ h) * u ^ 2 ≤ u ^ 3
        nlinarith only [hh])
    rw [integral_const_mul] at hi
    exact hi

/-- The floor is below the original law's actual rho, using its actual
canonical inward caps and actual noise. No allocation is discarded by
replacing a signed cubic with an absolute moment. -/
theorem coarseFloor_le_actual_thirdMoment (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hp : p μ ∈ Icc (39 / 100 : ℝ) (2 / 5))
    (hcap : a0 μ h + a1 μ h ≤ (7 : ℝ) / 80) :
    coarseFloor (p μ) (noiseVariance μ h) ≤ thirdAbsoluteMoment μ := by
  have ht := CanonicalResidualMomentBounds.absoluteThirdMoment_identity μ h
  obtain ⟨ht0, ht1⟩ := residual_cubic_cap_bounds μ h
  have hp0 := (p_pos μ h).le
  have hq0 := (q_pos μ h).le
  have hv0 := MomentBudget.residualSecondMoment_nonneg (residual0 μ h)
  have hv1 := MomentBudget.residualSecondMoment_nonneg (residual1 μ h)
  have ha0 := a0_nonneg μ h
  have ha1 := a1_nonneg μ h
  have hs := noiseVariance_nonneg μ h
  have hpq : 0 ≤ q μ - p μ := by unfold q; linarith only [hp.2]
  have htc0 := mul_le_mul_of_nonneg_left ht0 hq0
  have htc1 := mul_le_mul_of_nonneg_left ht1 hp0
  have hmore := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hp0) hpq) hv1
  have hcross0 := mul_nonneg (mul_nonneg hq0 ha1) hv0
  have hcross1 := mul_nonneg (mul_nonneg hp0 ha0) hv1
  have hds := mul_le_mul_of_nonneg_right hcap hs
  have hscaled : base (p μ) + coefficient (p μ) * noiseVariance μ h ≤
      thirdAbsoluteMoment μ * scale μ h ^ 3 := by
    dsimp only [base, coefficient, P39Reference.v, noiseVariance, q,
      MomentBudget.residualSecondMoment, MomentBudget.residualCubicMoment] at ht htc0 htc1 hmore hcross0 hcross1 hds ⊢
    nlinarith only [ht, htc0, htc1, hmore, hcross0, hcross1, hds]
  have hc : 0 < Real.sqrt (P39Reference.v (p μ) + noiseVariance μ h) := by
    rw [show P39Reference.v (p μ) = p μ * q μ by rfl, ← scale_eq_sqrt μ h]
    exact scale_pos μ h
  unfold coarseFloor
  apply (div_le_iff₀ (pow_pos hc 3)).mpr
  rw [show P39Reference.v (p μ) = p μ * q μ by rfl, ← scale_eq_sqrt μ h]
  exact hscaled

theorem canonical_thirdMoment_ge_rho0_add_noise
    (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hp : p μ ∈ Icc (39 / 100 : ℝ) (2 / 5))
    (hcap : a0 μ h + a1 μ h ≤ (7 : ℝ) / 80)
    (hnoise : noiseVariance μ h ≤ (17 : ℝ) / 1300) :
    P39Reference.rho0 (p μ) + (19 / 10 : ℝ) * noiseVariance μ h ≤ thirdAbsoluteMoment μ :=
  (coarseFloor_ge_rho0_add_noise hp ⟨noiseVariance_nonneg μ h, hnoise⟩).trans
    (coarseFloor_le_actual_thirdMoment μ h hp hcap)

/-- The actual n=26 maximum and the full C25 predecessor acquire both
caps used by the rho credit; neither is an incoming profile assumption. -/
theorem original_thirdMoment_ge_rho0_add_noise
    (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (H C : ℝ)
    (hm : ContactVariation.PositiveClosedMaximum μ 26 H C)
    (hprev : Extremizer.fixedNSup 25 ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10)
    (hp : p μ ∈ Icc (39 / 100 : ℝ) (2 / 5)) :
    P39Reference.rho0 (p μ) + (19 / 10 : ℝ) * noiseVariance μ h ≤ thirdAbsoluteMoment μ := by
  have hcap := CanonicalInwardBudget.original_inward_lt_seven_eightieths
    μ h 26 (by norm_num) H C hm hprev hC hρ
  have hnoise := P39Count11VarianceAcquisition.original_noiseVariance_le
    μ h H C hm hprev hC hρ hp
  exact canonical_thirdMoment_ge_rho0_add_noise μ h hp hcap.le hnoise

end BerryEsseen.P39CoarseNoiseIncrement

#print axioms BerryEsseen.P39CoarseNoiseIncrement.derivative_ge
#print axioms BerryEsseen.P39CoarseNoiseIncrement.hasDerivAt_coarseFloor
#print axioms BerryEsseen.P39CoarseNoiseIncrement.coarseFloor_ge_rho0_add_noise
#print axioms BerryEsseen.P39CoarseNoiseIncrement.residual_cubic_cap_bounds
#print axioms BerryEsseen.P39CoarseNoiseIncrement.coarseFloor_le_actual_thirdMoment
#print axioms BerryEsseen.P39CoarseNoiseIncrement.canonical_thirdMoment_ge_rho0_add_noise
#print axioms BerryEsseen.P39CoarseNoiseIncrement.original_thirdMoment_ge_rho0_add_noise
