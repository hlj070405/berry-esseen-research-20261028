module

public import BerryEsseen.P39CoupledInwardNoise
public import BerryEsseen.P39LeftAllocationReduction
public import BerryEsseen.BernoulliMomentFloor

@[expose] public section

/-! 2026-10-31: a continuous cubic credit for the actual P39 moment floor.
The moving cap is d(26*s), obtained from the same original resource.
The proof retains zero noise, uses the genuine square-root envelope, and
pays all remaining coefficients by rational nonnegative polynomials.
-/

noncomputable section

namespace BerryEsseen.P39CoupledMomentCredit

open MeasureTheory Set
open CanonicalSign CentralGap NoiseCoordinates

def cap0 : ℝ := 39 / 625
def capSlope : ℝ := 1027 / 250
def noiseUpper : ℝ := 61 / 5000
def delta (s : ℝ) : ℝ := cap0 - capSlope * s
def credit (s : ℝ) : ℝ := (27 / 10) * s + 220 * s ^ 2 + 13000 * s ^ 3
def denominator (p s : ℝ) : ℝ := Real.sqrt (P39Reference.v p + s) ^ 3
def numerator (p s : ℝ) : ℝ :=
  P39Reference.v p * (1 - 2 * P39Reference.v p) + (3 * p - delta s) * s +
    s ^ 2 / ((1 - p) * delta s)
def denominatorUpper (s : ℝ) : ℝ := 147 / 1250 + (147 / 200) * s + (771 / 1000) * s ^ 2
def geometricConstant : ℝ := 62500 / 2379
def geometricRatio : ℝ := 395 / 6
def gapLower (s : ℝ) : ℝ :=
  (3213 / 10000) * s + (capSlope - 5 / 6 + geometricConstant) * s ^ 2 +
    geometricConstant * geometricRatio * s ^ 3 + geometricConstant * geometricRatio ^ 2 * s ^ 4

theorem delta_eq_d (s : ℝ) : delta s = P39CoupledInwardNoise.d (26 * s) := by
  unfold delta cap0 capSlope P39CoupledInwardNoise.d
  ring

theorem delta_bounds (s : ℝ) (hs : s ∈ Icc (0 : ℝ) noiseUpper) :
    0 < delta s ∧ delta s ≤ cap0 := by
  have h0 := hs.1
  have h1 := hs.2
  unfold delta cap0 capSlope noiseUpper at *
  constructor <;> linarith only [h0, h1]

theorem denominator_pos (p s : ℝ) (hp : p ∈ Icc (39 / 100 : ℝ) (2 / 5)) (hs : 0 ≤ s) :
    0 < denominator p s := by
  have hv := (P39InwardBudget.probability_variance_bounds p hp).1
  have hvp : 0 < P39Reference.v p + s := by
    unfold P39Reference.v
    linarith only [hv, hs]
  exact pow_pos (Real.sqrt_pos.mpr hvp) 3

private theorem gDelta_zero_eq (p s : ℝ) (hp : p < 1) (hd : 0 < delta s) :
    MomentBudget.gDelta p s (delta s) 0 = numerator p s / denominator p s := by
  have hq : 0 < 1 - p := sub_pos.mpr hp
  have hL : (1 / Real.sqrt (1 - p)) ^ 2 = 1 / (1 - p) := by
    rw [div_pow, Real.sq_sqrt hq.le]
    norm_num
  have hterm : (1 / Real.sqrt (1 - p)) ^ 2 * s ^ 2 / delta s =
      s ^ 2 / ((1 - p) * delta s) := by
    rw [hL]
    field_simp [hq.ne', hd.ne']
  unfold MomentBudget.gDelta numerator denominator P39Reference.v
  simp only [zero_mul, sub_zero, zero_div, add_zero]
  rw [hterm]

/-- The Bernoulli part times the actual denominator is bounded without
dividing by the noise. The rational 5/6 gate uses v>=2379/10000. -/
theorem rho0_denominator_upper (p s : ℝ)
    (hp : p ∈ Icc (39 / 100 : ℝ) (2 / 5)) (hs : 0 ≤ s) :
    P39Reference.rho0 p * denominator p s ≤
      P39Reference.v p * (1 - 2 * P39Reference.v p) +
        (3 / 2) * (1 - 2 * P39Reference.v p) * s + (5 / 6) * s ^ 2 := by
  let v := P39Reference.v p
  obtain ⟨hv0, hv1⟩ := P39InwardBudget.probability_variance_bounds p hp
  change (2379 : ℝ) / 10000 ≤ v at hv0
  change v ≤ (6 : ℝ) / 25 at hv1
  have hv : 0 < v := by linarith only [hv0]
  have hr : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv
  have hk : 0 ≤ 1 - 2 * v := by linarith only [hv1]
  have he : P39Reference.rho0 p * v = (1 - 2 * v) * Real.sqrt v := by
    change ((1 - 2 * v) / Real.sqrt v) * v = _
    calc
      _ = ((1 - 2 * v) / Real.sqrt v) * Real.sqrt v ^ 2 := by rw [Real.sq_sqrt hv.le]
      _ = _ := by field_simp [hr.ne']
  have hE := mul_le_mul_of_nonneg_left (BernoulliMomentFloor.sqrt_cubic_envelope hv.le hs) hk
  have hcoef : (3 / 8 : ℝ) * (1 - 2 * v) ≤ (5 / 6) * v := by nlinarith only [hv0]
  have hcoef2 := mul_le_mul_of_nonneg_right hcoef (sq_nonneg s)
  apply (mul_le_mul_iff_left₀ hv).mp
  calc
    _ = (1 - 2 * v) * (Real.sqrt v * denominator p s) := by rw [mul_assoc, mul_comm (denominator p s) v, ← mul_assoc, he]; ring
    _ ≤ (1 - 2 * v) * (v ^ 2 + 3 * v * s / 2 + 3 * s ^ 2 / 8) := hE
    _ ≤ (v * (1 - 2 * v) + (3 / 2) * (1 - 2 * v) * s + (5 / 6) * s ^ 2) * v := by
      nlinarith only [hcoef2]

theorem denominator_le_upper (p s : ℝ)
    (hp : p ∈ Icc (39 / 100 : ℝ) (2 / 5)) (hs : 0 ≤ s) :
    denominator p s ≤ denominatorUpper s := by
  let v := P39Reference.v p
  let r := Real.sqrt v
  obtain ⟨hv0, hv1⟩ := P39InwardBudget.probability_variance_bounds p hp
  change (2379 : ℝ) / 10000 ≤ v at hv0
  change v ≤ (6 : ℝ) / 25 at hv1
  have hv : 0 < v := by linarith only [hv0]
  have hr : 0 < r := Real.sqrt_pos.mpr hv
  have hr2 : r ^ 2 = v := Real.sq_sqrt hv.le
  have hr0 : (487 : ℝ) / 1000 ≤ r := by nlinarith only [hr2, hr, hv0]
  have hr1 : r ≤ (49 : ℝ) / 100 := by nlinarith only [hr2, hr, hv1]
  have hvr : v * r ≤ (147 : ℝ) / 1250 := by
    have hi := mul_le_mul hv1 hr1 hr.le (by norm_num : (0 : ℝ) ≤ 6 / 25)
    nlinarith only [hi]
  have hc : v ^ 2 ≤ (147 / 1250 : ℝ) * r := by
    calc
      _ = v * r ^ 2 := by rw [hr2]; ring
      _ = (v * r) * r := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hvr hr.le
  have hl : (3 / 2 : ℝ) * v ≤ (147 / 200) * r := by
    have hh := mul_le_mul_of_nonneg_left hr1 (show 0 ≤ (3 / 2 : ℝ) * r by positivity)
    nlinarith only [hh, hr2]
  have hq : (3 / 8 : ℝ) ≤ (771 / 1000) * r := by linarith only [hr0]
  have hls := mul_le_mul_of_nonneg_right hl hs
  have hqs := mul_le_mul_of_nonneg_right hq (sq_nonneg s)
  have hE := BernoulliMomentFloor.sqrt_cubic_envelope hv.le hs
  apply (mul_le_mul_iff_right₀ hr).mp
  apply le_trans hE
  unfold denominatorUpper
  nlinarith only [hc, hls, hqs]

theorem geometric_inverse_lower (p s : ℝ)
    (hp : p ∈ Icc (39 / 100 : ℝ) (2 / 5)) (hs : s ∈ Icc (0 : ℝ) noiseUpper) :
    geometricConstant * (1 + geometricRatio * s + (geometricRatio * s) ^ 2) ≤
      1 / ((1 - p) * delta s) := by
  have hd := (delta_bounds s hs).1
  have hq : 0 < 1 - p := by linarith only [hp.2]
  have hqu : 1 - p ≤ (61 : ℝ) / 100 := by linarith only [hp.1]
  have hs0 := hs.1
  have hK : 0 ≤ geometricConstant * (1 + geometricRatio * s + (geometricRatio * s) ^ 2) := by
    unfold geometricConstant geometricRatio
    positivity
  have hprod := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hqu hd.le) hK
  have he : geometricConstant * (1 + geometricRatio * s + (geometricRatio * s) ^ 2) *
      ((61 / 100 : ℝ) * delta s) = 1 - (geometricRatio * s) ^ 3 := by
    unfold geometricConstant geometricRatio delta cap0 capSlope
    ring
  apply (le_div_iff₀ (mul_pos hq hd)).mpr
  calc
    _ ≤ geometricConstant * (1 + geometricRatio * s + (geometricRatio * s) ^ 2) *
        ((61 / 100 : ℝ) * delta s) := hprod
    _ = 1 - (geometricRatio * s) ^ 3 := he
    _ ≤ 1 := by
      have hu : 0 ≤ (geometricRatio * s) ^ 3 := by unfold geometricRatio; positivity
      linarith only [hu]

theorem numerator_gap_lower (p s : ℝ)
    (hp : p ∈ Icc (39 / 100 : ℝ) (2 / 5)) (hs : s ∈ Icc (0 : ℝ) noiseUpper) :
    gapLower s ≤ numerator p s - P39Reference.rho0 p * denominator p s := by
  have hR := rho0_denominator_upper p s hp hs.1
  have hv := (P39InwardBudget.probability_variance_bounds p hp).1
  have hB : (3213 : ℝ) / 10000 ≤ 3 * p + 3 * P39Reference.v p - 3 / 2 - cap0 := by
    unfold cap0 P39Reference.v
    linarith only [hp.1, hv]
  have hBs := mul_le_mul_of_nonneg_right hB hs.1
  have hi := geometric_inverse_lower p s hp hs
  have his := mul_le_mul_of_nonneg_right hi (sq_nonneg s)
  have he : numerator p s -
      (P39Reference.v p * (1 - 2 * P39Reference.v p) +
        (3 / 2) * (1 - 2 * P39Reference.v p) * s + (5 / 6) * s ^ 2) =
      (3 * p + 3 * P39Reference.v p - 3 / 2 - cap0) * s +
        (capSlope - 5 / 6 + 1 / ((1 - p) * delta s)) * s ^ 2 := by
    unfold numerator delta
    simp only [div_eq_mul_inv]
    ring
  have hpoly : gapLower s ≤
      (3 * p + 3 * P39Reference.v p - 3 / 2 - cap0) * s +
        (capSlope - 5 / 6 + 1 / ((1 - p) * delta s)) * s ^ 2 := by
    unfold gapLower
    nlinarith only [hBs, his]
  rw [← he] at hpoly
  exact hpoly.trans (sub_le_sub_left hR (numerator p s))

theorem polynomial_remainder (s : ℝ) :
    gapLower s - credit s * denominatorUpper s =
      (189 / 50000 : ℝ) * s + (2679879 / 1586000) * s ^ 2 +
        (2637944071 / 71370000) * s ^ 3 + (11135293181267 / 107055000) * s ^ 4 +
        10023 * s ^ 4 * (noiseUpper - s) := by
  unfold gapLower credit denominatorUpper geometricConstant geometricRatio capSlope noiseUpper
  ring

theorem polynomial_budget (s : ℝ) (hs : s ∈ Icc (0 : ℝ) noiseUpper) :
    credit s * denominatorUpper s ≤ gapLower s := by
  have hs0 := hs.1
  have hs1 : 0 ≤ noiseUpper - s := sub_nonneg.mpr hs.2
  apply sub_nonneg.mp
  rw [polynomial_remainder]
  positivity

/-- The whole continuous P39/noise domain, not a table of diagnostic points. -/
theorem gDelta_credit_lower (p s : ℝ)
    (hp : p ∈ Icc (39 / 100 : ℝ) (2 / 5)) (hs : s ∈ Icc (0 : ℝ) noiseUpper) :
    P39Reference.rho0 p + credit s ≤ MomentBudget.gDelta p s (delta s) 0 := by
  have hd := (delta_bounds s hs).1
  rw [gDelta_zero_eq p s (by linarith only [hp.2]) hd]
  apply (le_div_iff₀ (denominator_pos p s hp hs.1)).mpr
  have hcredit : 0 ≤ credit s := by unfold credit; have := hs.1; positivity
  have hD := mul_le_mul_of_nonneg_left (denominator_le_upper p s hp hs.1) hcredit
  have hP := polynomial_budget s hs
  have hN := numerator_gap_lower p s hp hs
  nlinarith only [hD, hP, hN]

/-- Original-law acquisition of the moving-cap moment credit. -/
theorem original_thirdMoment_credit (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (H C : ℝ) (hm : ContactVariation.PositiveClosedMaximum μ 26 H C)
    (hprev : Extremizer.fixedNSup 25 ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10)
    (hp : p μ ∈ Icc (39 / 100 : ℝ) (2 / 5)) :
    P39Reference.rho0 (p μ) + credit (noiseVariance μ h) ≤ thirdAbsoluteMoment μ := by
  have hsU := P39LowCountVarianceAcquisition.original_noiseVariance_lt μ h H C hm hprev hC hρ hp
  have hs : noiseVariance μ h ∈ Icc (0 : ℝ) noiseUpper := by
    refine ⟨noiseVariance_nonneg μ h, ?_⟩
    unfold noiseUpper
    linarith only [hsU]
  have he : delta (noiseVariance μ h) = P39CoupledInwardNoise.d (noiseLevel μ h 26) := by
    change delta (noiseVariance μ h) = P39CoupledInwardNoise.d (26 * noiseVariance μ h)
    exact delta_eq_d _
  have hcap := (P39CoupledInwardNoise.original_inward_lt_d μ h H C hm hprev hC hρ hp).le
  rw [← he] at hcap
  have hfloor := P39LeftAllocationReduction.actual_zero_allocation_floor μ h
    (by linarith only [hp.2]) (delta (noiseVariance μ h)) (delta_bounds _ hs).1 hcap
  exact (gDelta_credit_lower (p μ) (noiseVariance μ h) hp hs).trans hfloor

theorem one_fifth_gate :
    (11 / 10 : ℝ) < (1061 / 1000) + credit (1 / 130) := by norm_num [credit]

theorem original_noiseVariance_lt (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (H C : ℝ) (hm : ContactVariation.PositiveClosedMaximum μ 26 H C)
    (hprev : Extremizer.fixedNSup 25 ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10)
    (hp : p μ ∈ Icc (39 / 100 : ℝ) (2 / 5)) : noiseVariance μ h < (1 : ℝ) / 130 := by
  by_contra hnot
  have hs : (1 : ℝ) / 130 ≤ noiseVariance μ h := le_of_not_gt hnot
  have hs2 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 130) hs 2
  have hs3 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 130) hs 3
  have hc : credit (1 / 130) ≤ credit (noiseVariance μ h) := by
    unfold credit
    nlinarith only [hs, hs2, hs3]
  have hr0 : (1061 : ℝ) / 1000 ≤ P39Reference.rho0 (p μ) :=
    (by norm_num : (1061 : ℝ) / 1000 ≤ 530722777603 / 500000000000).trans (P39Reference.rho0_floor hp)
  have hmom := original_thirdMoment_credit μ h H C hm hprev hC hρ hp
  have hgate := one_fifth_gate
  nlinarith only [hc, hr0, hmom, hgate, hρ]

theorem original_noiseLevel_lt (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (H C : ℝ) (hm : ContactVariation.PositiveClosedMaximum μ 26 H C)
    (hprev : Extremizer.fixedNSup 25 ≤ esseenConstant) (hC : esseenConstant ≤ C)
    (hρ : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10)
    (hp : p μ ∈ Icc (39 / 100 : ℝ) (2 / 5)) : noiseLevel μ h 26 < (1 : ℝ) / 5 := by
  have hs := original_noiseVariance_lt μ h H C hm hprev hC hρ hp
  change 26 * noiseVariance μ h < (1 : ℝ) / 5
  linarith only [hs]

end BerryEsseen.P39CoupledMomentCredit

#print axioms BerryEsseen.P39CoupledMomentCredit.denominator_le_upper
#print axioms BerryEsseen.P39CoupledMomentCredit.geometric_inverse_lower
#print axioms BerryEsseen.P39CoupledMomentCredit.gDelta_credit_lower
#print axioms BerryEsseen.P39CoupledMomentCredit.original_thirdMoment_credit
#print axioms BerryEsseen.P39CoupledMomentCredit.original_noiseVariance_lt
#print axioms BerryEsseen.P39CoupledMomentCredit.original_noiseLevel_lt
