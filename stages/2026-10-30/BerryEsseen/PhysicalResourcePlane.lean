module

public import BerryEsseen.JointDefect
public import BerryEsseen.ConditionalResidual

@[expose] public section

/-! 2026-10-28: actual-law affine resource prices from the full joint defect.
The inward caps, canonical noise and total allocation belong to one original
standardized law, including its zero-noise boundary. -/

noncomputable section

open MeasureTheory Set

namespace BerryEsseen.PhysicalResourcePlane

open CanonicalSign CentralGap NoiseCoordinates GapDefect JointDefect

theorem actualAllocation_eq_allocation (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    ConditionalResidual.actualAllocation μ h = allocation μ h := rfl

theorem actualAllocation_zero_of_noise_zero (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hs : noiseVariance μ h = 0) : ConditionalResidual.actualAllocation μ h = 0 := by
  simp [ConditionalResidual.actualAllocation, hs]

private lemma theta_parts_zero_of_noise_zero (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hs : noiseVariance μ h = 0) : thetaMinus μ h = 0 ∧ thetaPlus μ h = 0 := by
  have hz : scale μ h ^ 2 * theta μ h = 0 := by rw [scale_sq_mul_theta, hs]
  have ht : theta μ h = 0 := (mul_eq_zero.mp hz).resolve_left (pow_ne_zero 2 (scale_pos μ h).ne')
  have hm := thetaMinus_nonneg μ h
  have hp := thetaPlus_nonneg μ h
  change thetaMinus μ h + thetaPlus μ h = 0 at ht
  constructor <;> linarith

theorem actualAllocation_mem_Icc (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    ConditionalResidual.actualAllocation μ h ∈ Icc (0 : ℝ) 1 := by
  by_cases hs : noiseVariance μ h = 0
  · rw [actualAllocation_zero_of_noise_zero μ h hs]
    constructor <;> norm_num
  · have hpos : 0 < noiseVariance μ h := lt_of_le_of_ne (noiseVariance_nonneg μ h) (Ne.symm hs)
    have ht := theta_pos_of_noise_pos μ h hpos
    rw [actualAllocation_eq_allocation, allocation_eq_physical μ h hpos]
    refine ⟨div_nonneg (thetaPlus_nonneg μ h) ht.le, ?_⟩
    apply (div_le_iff₀ ht).mpr
    simp only [one_mul, theta]
    linarith [thetaMinus_nonneg μ h]

/-- This multiplication identity includes zero noise; no zero-noise ratio is postulated. -/
theorem actualAllocation_mul_theta (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    ConditionalResidual.actualAllocation μ h * theta μ h = thetaPlus μ h := by
  by_cases hs : noiseVariance μ h = 0
  · obtain ⟨hm, hp⟩ := theta_parts_zero_of_noise_zero μ h hs
    have ht : theta μ h = 0 := by unfold theta; rw [hm, hp]; ring
    rw [ht, hp]
    ring
  · have hpos : 0 < noiseVariance μ h := lt_of_le_of_ne (noiseVariance_nonneg μ h) (Ne.symm hs)
    rw [actualAllocation_eq_allocation, allocation_eq_physical μ h hpos]
    exact div_mul_cancel₀ _ (theta_pos_of_noise_pos μ h hpos).ne'

theorem firstMoment_over_scale (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    positiveFirstMoment μ / scale μ h = 1 - theta μ h := positiveFirstMoment_div_scale μ h

/-- The actual inward caps are `c*Delta`, using the canonical normalization `c`. -/
theorem inner0_eq_scale_delta (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    a0 μ h = scale μ h * deltaMinus μ := by
  have hb : scale μ h * barAminus μ = p μ := by
    rw [barAminus_eq_neg_mean0 μ h]
    nlinarith [scale_center0 μ h]
  unfold a0 deltaMinus
  nlinarith only [hb]

theorem inner1_eq_scale_delta (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    a1 μ h = scale μ h * deltaPlus μ := by
  have hb : scale μ h * barAplus μ = q μ := by
    rw [barAplus_eq_mean1 μ h]
    nlinarith [scale_center1 μ h]
  unfold a1 deltaPlus
  nlinarith only [hb]

/-- Both variance shares use the same actual `lambda_n = n*s` and allocation, also at `s=0`. -/
theorem theta_parts_eq_noise_coordinates (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (hn : 0 < n) :
    thetaMinus μ h = noiseLevel μ h n * (1 - ConditionalResidual.actualAllocation μ h) *
        (1 - theta μ h) / ((n : ℝ) * (p μ * q μ)) ∧
      thetaPlus μ h = noiseLevel μ h n * ConditionalResidual.actualAllocation μ h *
        (1 - theta μ h) / ((n : ℝ) * (p μ * q μ)) := by
  have hv := mul_pos (p_pos μ h) (q_pos μ h)
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have ha := actualAllocation_mul_theta μ h
  have hm : (1 - ConditionalResidual.actualAllocation μ h) * theta μ h = thetaMinus μ h := by
    have ht : theta μ h = thetaMinus μ h + thetaPlus μ h := rfl
    nlinarith only [ha, ht]
  have hl : noiseLevel μ h n * (1 - theta μ h) = (n : ℝ) * (p μ * q μ) * theta μ h := by
    rw [noiseLevel_eq_physical]
    rw [div_mul_cancel₀ _ (sub_pos.mpr (theta_lt_one μ h)).ne']
    ring
  constructor
  · apply (eq_div_iff (mul_pos hnR hv).ne').mpr
    calc
      thetaMinus μ h * ((n : ℝ) * (p μ * q μ)) =
          ((n : ℝ) * (p μ * q μ)) * ((1 - ConditionalResidual.actualAllocation μ h) * theta μ h) := by
        rw [hm]
        ring
      _ = (noiseLevel μ h n * (1 - theta μ h)) * (1 - ConditionalResidual.actualAllocation μ h) := by
        rw [hl]
        ring
      _ = _ := by ring
  · apply (eq_div_iff (mul_pos hnR hv).ne').mpr
    calc
      thetaPlus μ h * ((n : ℝ) * (p μ * q μ)) =
          ((n : ℝ) * (p μ * q μ)) * (ConditionalResidual.actualAllocation μ h * theta μ h) := by
        rw [ha]
        ring
      _ = (noiseLevel μ h n * (1 - theta μ h)) * ConditionalResidual.actualAllocation μ h := by
        rw [hl]
        ring
      _ = _ := by ring

def distanceToStar (l u : ℝ) : ℝ := max 0 (max (l - pStar) (pStar - u))

def biasPrice (l u Θ vmax : ℝ) : ℝ :=
  (6 + 2 * Real.sqrt 10) * (1 - Θ) ^ ((3 : ℝ) / 2) / Real.sqrt vmax * distanceToStar l u ^ 2

def gapPrice (Θ Al Bl : ℝ) : ℝ := 6 * (1 - Θ) * (Al + Bl)
def thetaPriceMinus (Al : ℝ) : ℝ := 3 * (Real.sqrt 10 + 3) * Al
def thetaPricePlus (Bl : ℝ) : ℝ := 3 * (Real.sqrt 10 + 1) * Bl
def noisePriceMinus (n : ℕ) (Θ Al vmax : ℝ) : ℝ :=
  thetaPriceMinus Al * (1 - Θ) / ((n : ℝ) * vmax)
def noisePricePlus (n : ℕ) (Θ Bl vmax : ℝ) : ℝ :=
  thetaPricePlus Bl * (1 - Θ) / ((n : ℝ) * vmax)

lemma distanceToStar_nonneg (l u : ℝ) : 0 ≤ distanceToStar l u := le_max_left _ _

lemma distanceToStar_le_abs (l u x : ℝ) (hx : x ∈ Icc l u) :
    distanceToStar l u ≤ |x - pStar| := by
  unfold distanceToStar
  apply max_le (abs_nonneg _)
  apply max_le
  · linarith [le_abs_self (x - pStar), hx.1]
  · linarith [neg_le_abs (x - pStar), hx.2]

theorem biasPrice_le_actual (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (l u Θ vmax : ℝ) (hl : 0 < l) (hu : u < 1) (hp : p μ ∈ Icc l u)
    (hΘ : Θ < 1) (hθ : theta μ h ≤ Θ) (hvm : 0 < vmax) (hv : p μ * q μ ≤ vmax) :
    biasPrice l u Θ vmax ≤
      ((6 + 2 * Real.sqrt 10) * (1 - theta μ h) ^ ((3 : ℝ) / 2) / Real.sqrt (p μ * q μ)) *
        (p μ - pStar) ^ 2 := by
  have hp0 : 0 < p μ := hl.trans_le hp.1
  have hq0 : 0 < q μ := by unfold q; linarith [hp.2]
  have hv0 := mul_pos hp0 hq0
  have hc : 0 < 1 - theta μ h := sub_pos.mpr (theta_lt_one μ h)
  have hpow := Real.rpow_le_rpow (sub_pos.mpr hΘ).le (sub_le_sub_left hθ 1)
    (by norm_num : (0 : ℝ) ≤ (3 : ℝ) / 2)
  have hnum := mul_le_mul_of_nonneg_left hpow (show (0 : ℝ) ≤ 6 + 2 * Real.sqrt 10 by positivity)
  have h1 := div_le_div_of_nonneg_right hnum (Real.sqrt_pos.mpr hvm).le
  have h2 := div_le_div_of_nonneg_left
    (show 0 ≤ (6 + 2 * Real.sqrt 10) * (1 - theta μ h) ^ ((3 : ℝ) / 2) by positivity)
    (Real.sqrt_pos.mpr hv0) (Real.sqrt_le_sqrt hv)
  have hcoef := h1.trans h2
  have hd := distanceToStar_le_abs l u (p μ) hp
  have hsq := (sq_le_sq₀ (distanceToStar_nonneg l u) (abs_nonneg (p μ - pStar))).mpr hd
  rw [sq_abs] at hsq
  have hactual : 0 ≤ (6 + 2 * Real.sqrt 10) * (1 - theta μ h) ^ ((3 : ℝ) / 2) /
      Real.sqrt (p μ * q μ) := by positivity
  exact (mul_le_mul_of_nonneg_right hcoef (sq_nonneg (distanceToStar l u))).trans
    (mul_le_mul_of_nonneg_left hsq hactual)

theorem gapPrice_le_actual (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (Θ Al Bl : ℝ) (hθ : theta μ h ≤ Θ) (hAm : Al ≤ Aminus μ) (hAp : Bl ≤ Aplus μ)
    (hS : 0 ≤ Al + Bl) :
    gapPrice Θ Al Bl * (a0 μ h + a1 μ h) ≤
      6 * positiveFirstMoment μ * ((Aminus μ + Aplus μ) * (deltaMinus μ + deltaPlus μ) +
        deltaMinus μ * deltaPlus μ) := by
  have hm := positiveFirstMoment_pos μ h
  have hc := scale_pos μ h
  have hid : positiveFirstMoment μ = (1 - theta μ h) * scale μ h :=
    (div_eq_iff hc.ne').mp (firstMoment_over_scale μ h)
  have hcap : (1 - Θ) * scale μ h ≤ positiveFirstMoment μ := by
    calc
      _ ≤ (1 - theta μ h) * scale μ h :=
        mul_le_mul_of_nonneg_right (sub_le_sub_left hθ 1) hc.le
      _ = _ := hid.symm
  have hbase : (1 - Θ) * scale μ h * (Al + Bl) ≤
      positiveFirstMoment μ * (Aminus μ + Aplus μ) :=
    (mul_le_mul_of_nonneg_right hcap hS).trans
      (mul_le_mul_of_nonneg_left (add_le_add hAm hAp) hm.le)
  have hdm := deltaMinus_nonneg μ h
  have hdp := deltaPlus_nonneg μ h
  have hprod := mul_le_mul_of_nonneg_right hbase (add_nonneg hdm hdp)
  have hextra := mul_nonneg hm.le (mul_nonneg hdm hdp)
  rw [inner0_eq_scale_delta μ h, inner1_eq_scale_delta μ h]
  unfold gapPrice
  nlinarith only [hprod, hextra]

lemma noiseRatio_le_actual (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (hn : 0 < n) (Θ vmax : ℝ) (hθ : theta μ h ≤ Θ)
    (hvm : 0 < vmax) (hv : p μ * q μ ≤ vmax) :
    (1 - Θ) / ((n : ℝ) * vmax) ≤
      (1 - theta μ h) / ((n : ℝ) * (p μ * q μ)) := by
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hv0 := mul_pos (p_pos μ h) (q_pos μ h)
  have h1 := div_le_div_of_nonneg_right (sub_le_sub_left hθ 1) (mul_pos hnR hvm).le
  have h2 := div_le_div_of_nonneg_left (sub_pos.mpr (theta_lt_one μ h)).le
    (mul_pos hnR hv0) (mul_le_mul_of_nonneg_left hv hnR.le)
  exact h1.trans h2

theorem noisePrice_le_actual (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (hn : 0 < n) (Θ Al Bl vmax : ℝ) (hθ : theta μ h ≤ Θ)
    (hvm : 0 < vmax) (hv : p μ * q μ ≤ vmax) (hAl : 0 ≤ Al) (hBl : 0 ≤ Bl)
    (hAm : Al ≤ Aminus μ) (hAp : Bl ≤ Aplus μ) :
    noiseLevel μ h n * ((1 - ConditionalResidual.actualAllocation μ h) * noisePriceMinus n Θ Al vmax +
        ConditionalResidual.actualAllocation μ h * noisePricePlus n Θ Bl vmax) ≤
      3 * (Real.sqrt 10 + 3) * Aminus μ * thetaMinus μ h +
        3 * (Real.sqrt 10 + 1) * Aplus μ * thetaPlus μ h := by
  have ha := actualAllocation_mem_Icc μ h
  have hl : 0 ≤ noiseLevel μ h n := by
    unfold noiseLevel
    exact mul_nonneg (Nat.cast_nonneg _) (noiseVariance_nonneg μ h)
  have hkm : 0 ≤ thetaPriceMinus Al := by unfold thetaPriceMinus; positivity
  have hkp : 0 ≤ thetaPricePlus Bl := by unfold thetaPricePlus; positivity
  have hw : 0 ≤ noiseLevel μ h n * (1 - ConditionalResidual.actualAllocation μ h) * thetaPriceMinus Al +
      noiseLevel μ h n * ConditionalResidual.actualAllocation μ h * thetaPricePlus Bl :=
    add_nonneg (mul_nonneg (mul_nonneg hl (sub_nonneg.mpr ha.2)) hkm)
      (mul_nonneg (mul_nonneg hl ha.1) hkp)
  obtain ⟨hm, hp⟩ := theta_parts_eq_noise_coordinates μ h n hn
  calc
    _ = (noiseLevel μ h n * (1 - ConditionalResidual.actualAllocation μ h) * thetaPriceMinus Al +
        noiseLevel μ h n * ConditionalResidual.actualAllocation μ h * thetaPricePlus Bl) *
        ((1 - Θ) / ((n : ℝ) * vmax)) := by
      unfold noisePriceMinus noisePricePlus
      ring
    _ ≤ (noiseLevel μ h n * (1 - ConditionalResidual.actualAllocation μ h) * thetaPriceMinus Al +
        noiseLevel μ h n * ConditionalResidual.actualAllocation μ h * thetaPricePlus Bl) *
        ((1 - theta μ h) / ((n : ℝ) * (p μ * q μ))) :=
      mul_le_mul_of_nonneg_left (noiseRatio_le_actual μ h n hn Θ vmax hθ hvm hv) hw
    _ = thetaPriceMinus Al * thetaMinus μ h + thetaPricePlus Bl * thetaPlus μ h := by
      rw [hm, hp]
      ring
    _ ≤ _ := by
      have hm' := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hAm (thetaMinus_nonneg μ h))
        (show (0 : ℝ) ≤ 3 * (Real.sqrt 10 + 3) by positivity)
      have hp' := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hAp (thetaPlus_nonneg μ h))
        (show (0 : ℝ) ≤ 3 * (Real.sqrt 10 + 1) by positivity)
      unfold thetaPriceMinus thetaPricePlus
      nlinarith only [hm', hp']

/-- The physical affine lower budget uses the actual inward caps, noise and allocation. -/
theorem actual_resource_lower_bound (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hz : (0 : ℝ) ∉ (μ : Measure ℝ).support) (n : ℕ) (hn : 0 < n)
    (l u Θ Al Bl vmax : ℝ) (hl : 0 < l) (hu : u < 1) (hp : p μ ∈ Icc l u)
    (hΘ : Θ < 1) (hθ : theta μ h ≤ Θ) (hAl : 0 < Al) (hBl : 0 < Bl)
    (hAm : Al ≤ Aminus μ) (hAp : Bl ≤ Aplus μ) (hvm : 0 < vmax) (hv : p μ * q μ ≤ vmax) :
    biasPrice l u Θ vmax + gapPrice Θ Al Bl * (a0 μ h + a1 μ h) +
      noiseLevel μ h n * ((1 - ConditionalResidual.actualAllocation μ h) * noisePriceMinus n Θ Al vmax +
        ConditionalResidual.actualAllocation μ h * noisePricePlus n Θ Bl vmax) ≤ actualPhysicalDefect μ := by
  have hb := biasPrice_le_actual μ h l u Θ vmax hl hu hp hΘ hθ hvm hv
  have hg := gapPrice_le_actual μ h Θ Al Bl hθ hAm hAp (add_nonneg hAl.le hBl.le)
  have hn' := noisePrice_le_actual μ h n hn Θ Al Bl vmax hθ hvm hv hAl.le hBl.le hAm hAp
  have hj := joint_defect μ h hz
  linarith only [hb, hg, hn', hj]

/-- A genuine upper bound on the same actual defect yields one coupled resource plane. -/
theorem actual_resource_plane (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hz : (0 : ℝ) ∉ (μ : Measure ℝ).support) (n : ℕ) (hn : 0 < n)
    (l u Θ Al Bl vmax Dbar : ℝ) (hl : 0 < l) (hu : u < 1) (hp : p μ ∈ Icc l u)
    (hΘ : Θ < 1) (hθ : theta μ h ≤ Θ) (hAl : 0 < Al) (hBl : 0 < Bl)
    (hAm : Al ≤ Aminus μ) (hAp : Bl ≤ Aplus μ) (hvm : 0 < vmax) (hv : p μ * q μ ≤ vmax)
    (hD : actualPhysicalDefect μ ≤ Dbar) :
    gapPrice Θ Al Bl * (a0 μ h + a1 μ h) +
      noiseLevel μ h n * ((1 - ConditionalResidual.actualAllocation μ h) * noisePriceMinus n Θ Al vmax +
        ConditionalResidual.actualAllocation μ h * noisePricePlus n Θ Bl vmax) ≤ Dbar - biasPrice l u Θ vmax := by
  have hb := actual_resource_lower_bound μ h hz n hn l u Θ Al Bl vmax hl hu hp hΘ hθ hAl hBl hAm hAp hvm hv
  linarith only [hb, hD]

theorem actual_resource_plane_of_small (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hsmall : actualPhysicalDefect μ < (Real.sqrt 10 - 1) * thirdAbsoluteMoment μ)
    (n : ℕ) (hn : 0 < n) (l u Θ Al Bl vmax Dbar : ℝ)
    (hl : 0 < l) (hu : u < 1) (hp : p μ ∈ Icc l u) (hΘ : Θ < 1) (hθ : theta μ h ≤ Θ)
    (hAl : 0 < Al) (hBl : 0 < Bl) (hAm : Al ≤ Aminus μ) (hAp : Bl ≤ Aplus μ)
    (hvm : 0 < vmax) (hv : p μ * q μ ≤ vmax) (hD : actualPhysicalDefect μ ≤ Dbar) :
    gapPrice Θ Al Bl * (a0 μ h + a1 μ h) +
      noiseLevel μ h n * ((1 - ConditionalResidual.actualAllocation μ h) * noisePriceMinus n Θ Al vmax +
        ConditionalResidual.actualAllocation μ h * noisePricePlus n Θ Bl vmax) ≤ Dbar - biasPrice l u Θ vmax :=
  actual_resource_plane μ h (zero_notMem_support_of_defect_small μ h hsmall) n hn l u Θ Al Bl vmax Dbar
    hl hu hp hΘ hθ hAl hBl hAm hAp hvm hv hD

end BerryEsseen.PhysicalResourcePlane

#print axioms BerryEsseen.PhysicalResourcePlane.inner0_eq_scale_delta
#print axioms BerryEsseen.PhysicalResourcePlane.inner1_eq_scale_delta
#print axioms BerryEsseen.PhysicalResourcePlane.theta_parts_eq_noise_coordinates
#print axioms BerryEsseen.PhysicalResourcePlane.biasPrice_le_actual
#print axioms BerryEsseen.PhysicalResourcePlane.gapPrice_le_actual
#print axioms BerryEsseen.PhysicalResourcePlane.noisePrice_le_actual
#print axioms BerryEsseen.PhysicalResourcePlane.actual_resource_lower_bound
#print axioms BerryEsseen.PhysicalResourcePlane.actual_resource_plane
#print axioms BerryEsseen.PhysicalResourcePlane.actual_resource_plane_of_small
