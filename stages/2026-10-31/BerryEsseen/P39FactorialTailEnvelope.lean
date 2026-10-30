module

public import BerryEsseen.FactorialReferencePrice

@[expose] public section

/-! 2026-10-31: two factorial moments replace a finite reference-tail
sum. This file prices the entire stated scalar domain; its source caps,
count variance and threshold are licensed by the original-law frontend.
No probability/noise grid or numerical width optimization is used. -/

noncomputable section

open MeasureTheory Set

namespace BerryEsseen.P39FactorialTailEnvelope

open FactorialReferencePrice QuadraticStopLossFactorials

def cap : ℝ := 9 / 16
def ratio : ℝ := 40 / 39
def etaCap : ℝ := 163 / 1000
def gap0 : ℝ := 4081 / 10000
def gapSlope : ℝ := 9 / 5
def firstFactor : ℝ := etaCap * (25 / 26) * ratio ^ 2 / (2 * cap ^ 4)
def thirdFactor : ℝ := etaCap * (25 * 24 / (4 * 26 ^ 2)) * ratio ^ 3 / cap ^ 4
def quadraticCoefficient : ℝ := firstFactor * gap0 ^ 2
def cubicCoefficient : ℝ := -2 * firstFactor * gap0 * gapSlope + thirdFactor
def quarticCoefficient : ℝ := firstFactor * gapSlope ^ 2

theorem coefficient_gates :
    0 ≤ firstFactor ∧ 0 ≤ quarticCoefficient ∧
      quadraticCoefficient ≤ (7 : ℝ) / 50 ∧
      cubicCoefficient + quarticCoefficient / 5 ≤ -(7 : ℝ) / 25 := by
  norm_num [firstFactor, thirdFactor, quadraticCoefficient, cubicCoefficient,
    quarticCoefficient, etaCap, ratio, cap, gap0, gapSlope]

theorem noise_price_gate (lambda : ℝ) (hl : 0 ≤ lambda) :
    (7 / 50 : ℝ) * lambda ^ 2 - (7 / 25 : ℝ) * lambda ^ 3 - lambda / 600 -
      (803 / 10000 : ℝ) * ((27 / 10 : ℝ) * (lambda / 26) +
        220 * (lambda / 26) ^ 2 + 13000 * (lambda / 26) ^ 3) ≤
      -(67 / 271200 : ℝ) * lambda := by
  have hlin := mul_le_mul_of_nonneg_right
    (by norm_num : (1 / 100 : ℝ) ≤ (803 / 10000) * (27 / 10) / 26 + 1 / 600) hl
  have hquad := mul_le_mul_of_nonneg_right
    (by norm_num : (1 / 40 : ℝ) ≤ (803 / 10000) * 220 / 26 ^ 2) (sq_nonneg lambda)
  have hcub := mul_le_mul_of_nonneg_right
    (by norm_num : (59 / 1000 : ℝ) ≤ (803 / 10000) * 13000 / 26 ^ 3) (pow_nonneg hl 3)
  have hq : (67 / 271200 : ℝ) ≤
      (339 / 1000 : ℝ) * lambda ^ 2 - (23 / 200 : ℝ) * lambda + 1 / 100 := by
    nlinarith only [sq_nonneg (lambda - (115 / 678 : ℝ))]
  have hm := mul_le_mul_of_nonneg_right hq hl
  nlinarith only [hlin, hquad, hcub, hm]

lemma coefficient3_upper (d : ℝ) : coefficient3 d ≤ (1 : ℝ) / 4 := by
  unfold coefficient3
  nlinarith only [sq_nonneg (d - (3 / 2 : ℝ))]

lemma step_square_coefficient2 (B V A w : ℝ) (hB : 0 < B) (hV : 0 ≤ V) :
    step B V ^ 2 * coefficient2 (scaledThreshold B V A w) =
      (2 * step B V - (A - w + V / B)) ^ 2 / 2 := by
  have hs := (step_pos B V hB hV).ne'
  unfold coefficient2 scaledThreshold
  field_simp [hs]

lemma step_square_probability_cube (B V : ℝ) (hB : 0 < B) (hV : 0 ≤ V) :
    step B V ^ 2 * successProbability B V ^ 3 =
      (V / 26) ^ 3 / (B ^ 2 * (B ^ 2 + V / 26)) := by
  have hb : B ≠ 0 := hB.ne'
  have hd : B ^ 2 + V / 26 ≠ 0 := by positivity
  unfold step successProbability
  field_simp [hb, hd]

theorem weighted_Q_le (eta V A lambda : ℝ)
    (he : eta ∈ Icc (0 : ℝ) etaCap) (hl : lambda ∈ Icc (0 : ℝ) (1 / 5))
    (hV : V ∈ Icc (0 : ℝ) (ratio * lambda))
    (hd : scaledThreshold cap V A (1 / 4) ∈ Icc (1 : ℝ) 2)
    (hg : 2 * step cap V - (A - 1 / 4 + V / cap) ≤ gap0 - gapSlope * lambda) :
    eta * StopLossShape.Q (TwoMoment.uniformReferenceSumLaw cap 26 V) A ≤
      (7 / 50 : ℝ) * lambda ^ 2 - (7 / 25 : ℝ) * lambda ^ 3 := by
  have hB : 0 < cap := by norm_num [cap]
  have heta0 : 0 ≤ eta := he.1
  have hs := step_pos cap V hB hV.1
  let d := scaledThreshold cap V A (1 / 4)
  let pi := successProbability cap V
  let gap := 2 * step cap V - (A - 1 / 4 + V / cap)
  let u := gap0 - gapSlope * lambda
  have hgap : 0 ≤ gap := by
    have hh := (div_le_iff₀ hs).mp hd.2
    dsimp only [gap]
    linarith only [hh]
  have hgu : gap ≤ u := hg
  have hu : 0 ≤ u := hgap.trans hgu
  have hgap2 := pow_le_pow_left₀ hgap hgu 2
  have hz : 0 ≤ V / 26 := div_nonneg hV.1 (by norm_num)
  have hden : 0 < cap ^ 2 + V / 26 := by positivity
  have hpi0 : 0 ≤ pi := div_nonneg hz hden.le
  have hpi : pi ≤ ratio * lambda / (26 * cap ^ 2) := by
    have h1 : pi ≤ (V / 26) / cap ^ 2 :=
      div_le_div_of_nonneg_left hz (by positivity) (le_add_of_nonneg_right hz)
    have h2 := div_le_div_of_nonneg_right hV.2 (by positivity : 0 ≤ 26 * cap ^ 2)
    dsimp only [pi, successProbability] at h1
    calc
      _ ≤ (V / 26) / cap ^ 2 := h1
      _ = V / (26 * cap ^ 2) := by ring
      _ ≤ _ := h2
  have hpi2 := pow_le_pow_left₀ hpi0 hpi 2
  have hleft := mul_le_mul he.2 hgap2 (sq_nonneg gap) (by norm_num [etaCap] : 0 ≤ etaCap)
  have hfull := mul_le_mul hleft hpi2 (sq_nonneg pi)
    (mul_nonneg (by norm_num [etaCap] : 0 ≤ etaCap) (sq_nonneg u))
  have hfirst0 := mul_le_mul_of_nonneg_left hfull (by norm_num : (0 : ℝ) ≤ 26 * 25 / 2)
  have hid := step_square_coefficient2 cap V A (1 / 4) hB hV.1
  have hfirst : eta * (step cap V ^ 2 * coefficient2 d) * (26 * 25) * pi ^ 2 ≤
      firstFactor * lambda ^ 2 * u ^ 2 := by
    change eta * (step cap V ^ 2 * coefficient2 (scaledThreshold cap V A (1 / 4))) *
      (26 * 25) * pi ^ 2 ≤ _
    rw [hid]
    dsimp only [gap] at hfirst0
    norm_num only [firstFactor, cap, ratio, etaCap] at hfirst0 ⊢
    nlinarith only [hfirst0]
  have hprod : cap ^ 4 ≤ cap ^ 2 * (cap ^ 2 + V / 26) := by
    nlinarith only [mul_nonneg (sq_nonneg cap) hz]
  have hp3 : step cap V ^ 2 * pi ^ 3 ≤ (ratio * lambda / 26) ^ 3 / cap ^ 4 := by
    change step cap V ^ 2 * successProbability cap V ^ 3 ≤ _
    rw [step_square_probability_cube cap V hB hV.1]
    calc
      _ ≤ (V / 26) ^ 3 / cap ^ 4 :=
        div_le_div_of_nonneg_left (pow_nonneg hz 3) (by positivity) hprod
      _ ≤ _ := div_le_div_of_nonneg_right
        (pow_le_pow_left₀ hz (div_le_div_of_nonneg_right hV.2 (by norm_num : (0 : ℝ) ≤ 26)) 3)
        (by positivity)
  have hc3 := mul_le_mul_of_nonneg_left (coefficient3_upper d)
    (show 0 ≤ eta * step cap V ^ 2 * (26 * 25 * 24) * pi ^ 3 by positivity)
  have hthird1 := mul_le_mul he.2 hp3
    (show 0 ≤ step cap V ^ 2 * pi ^ 3 by positivity)
    (by norm_num [etaCap] : 0 ≤ etaCap)
  have hthird2 := mul_le_mul_of_nonneg_left hthird1
    (by norm_num : (0 : ℝ) ≤ 26 * 25 * 24 / 4)
  have hthird : eta * (step cap V ^ 2 * coefficient3 d) * (26 * 25 * 24) * pi ^ 3 ≤
      thirdFactor * lambda ^ 3 := by
    norm_num only [thirdFactor, cap, ratio, etaCap] at hc3 hthird2 ⊢
    nlinarith only [hc3, hthird2]
  have hq := mul_le_mul_of_nonneg_left (Q_uniform26_le cap V A (1 / 4)
    hB hV.1 (by norm_num) hd) he.1
  have hprice : eta * StopLossShape.Q (TwoMoment.uniformReferenceSumLaw cap 26 V) A ≤
      firstFactor * lambda ^ 2 * u ^ 2 + thirdFactor * lambda ^ 3 := by
    norm_num only [show (4 : ℝ) * (1 / 4) = 1 by norm_num, div_one] at hq
    dsimp only [d, pi] at hfirst hthird
    nlinarith only [hq, hfirst, hthird]
  have h4 : lambda ^ 4 ≤ (1 / 5 : ℝ) * lambda ^ 3 := by
    have hh := mul_le_mul_of_nonneg_right hl.2 (pow_nonneg hl.1 3)
    nlinarith only [hh]
  have hgates := coefficient_gates
  have hk4 := mul_le_mul_of_nonneg_left h4 hgates.2.1
  have hk2 := mul_le_mul_of_nonneg_right hgates.2.2.1 (sq_nonneg lambda)
  have hk3 := mul_le_mul_of_nonneg_right hgates.2.2.2 (pow_nonneg hl.1 3)
  dsimp only [u, quadraticCoefficient, cubicCoefficient, quarticCoefficient] at *
  nlinarith only [hprice, hk4, hk2, hk3]

end BerryEsseen.P39FactorialTailEnvelope

#print axioms BerryEsseen.P39FactorialTailEnvelope.coefficient_gates
#print axioms BerryEsseen.P39FactorialTailEnvelope.weighted_Q_le
