module

public import BerryEsseen.QuadraticStopLossFactorials
public import BerryEsseen.BinomialReferencePrice
public import BerryEsseen.StopLossShape

@[expose] public section

/-! 2026-10-31: a factorial majorant for the true 26-fold reference law.
The two factorial sums are proved polynomial identities for its actual
binomial weights. Zero variance is included throughout. -/

noncomputable section

namespace BerryEsseen.FactorialReferencePrice

open MeasureTheory
open scoped BigOperators
open QuadraticStopLossFactorials

def step (B V : ℝ) : ℝ := B + V / (26 * B)

def successProbability (B V : ℝ) : ℝ := (V / 26) / (B ^ 2 + V / 26)

def scaledThreshold (B V A w : ℝ) : ℝ := (A - w + V / B) / step B V

theorem step_pos (B V : ℝ) (hB : 0 < B) (hV : 0 ≤ V) : 0 < step B V := by
  unfold step
  exact add_pos_of_pos_of_nonneg hB (div_nonneg hV (by positivity))

theorem binomial26_falling2 (p q : ℝ) :
    (∑ j ∈ Finset.range 27,
      ((26 : ℕ).choose j : ℝ) * p ^ j * q ^ (26 - j) * falling2 (j : ℝ)) =
      (26 * 25 : ℝ) * p ^ 2 * (p + q) ^ 24 := by
  norm_num [Finset.sum_range_succ, Nat.choose_eq_descFactorial_div_factorial,
    Nat.descFactorial, Nat.factorial, falling2]
  ring

theorem binomial26_falling3 (p q : ℝ) :
    (∑ j ∈ Finset.range 27,
      ((26 : ℕ).choose j : ℝ) * p ^ j * q ^ (26 - j) * falling3 (j : ℝ)) =
      (26 * 25 * 24 : ℝ) * p ^ 3 * (p + q) ^ 23 := by
  norm_num [Finset.sum_range_succ, Nat.choose_eq_descFactorial_div_factorial,
    Nat.descFactorial, Nat.factorial, falling3]
  ring

/-- The numerator bound is an integral under the actual reference law,
not an assumption about its moments or a substitute distribution. -/
theorem integral_uniform26_le (B V A w : ℝ) (hB : 0 < B) (hV : 0 ≤ V)
    (hd : scaledThreshold B V A w ∈ Set.Icc (1 : ℝ) 2) :
    (∫ x : ℝ, (max (x - A + w) 0) ^ 2 ∂TwoMoment.uniformReferenceSumLaw B 26 V) ≤
      step B V ^ 2 *
        (coefficient2 (scaledThreshold B V A w) * (26 * 25) * successProbability B V ^ 2 +
          coefficient3 (scaledThreshold B V A w) * (26 * 25 * 24) * successProbability B V ^ 3) := by
  let p := successProbability B V
  let q := B ^ 2 / (B ^ 2 + V / 26)
  let W : ℕ → ℝ := fun j => ((26 : ℕ).choose j : ℝ) * p ^ j * q ^ (26 - j)
  let d := scaledThreshold B V A w
  have hz : 0 ≤ V / 26 := div_nonneg hV (by norm_num)
  have hden : 0 < B ^ 2 + V / 26 := add_pos_of_pos_of_nonneg (sq_pos_of_pos hB) hz
  have hp : 0 ≤ p := div_nonneg hz hden.le
  have hq : 0 ≤ q := div_nonneg (sq_nonneg _) hden.le
  have hpq : p + q = 1 := by
    dsimp [p, q, successProbability]
    field_simp [hden.ne']
    ring
  have hs := step_pos B V hB hV
  have hmoment2 : (∑ j ∈ Finset.range 27, W j * falling2 (j : ℝ)) =
      (26 * 25 : ℝ) * p ^ 2 := by
    change (∑ j ∈ Finset.range 27,
      ((26 : ℕ).choose j : ℝ) * p ^ j * q ^ (26 - j) * falling2 (j : ℝ)) = _
    rw [binomial26_falling2, hpq, one_pow, mul_one]
  have hmoment3 : (∑ j ∈ Finset.range 27, W j * falling3 (j : ℝ)) =
      (26 * 25 * 24 : ℝ) * p ^ 3 := by
    change (∑ j ∈ Finset.range 27,
      ((26 : ℕ).choose j : ℝ) * p ^ j * q ^ (26 - j) * falling3 (j : ℝ)) = _
    rw [binomial26_falling3, hpq, one_pow, mul_one]
  have hpoint (j : ℕ) (hj : j ∈ Finset.range 27) :
      (max ((j : ℝ) * B - ((26 - j : ℕ) : ℝ) * (V / 26) / B - A + w) 0) ^ 2 ≤
        step B V ^ 2 * majorant d (j : ℝ) := by
    have hj26 : j ≤ 26 := by have := Finset.mem_range.mp hj; omega
    have hcast : ((26 - j : ℕ) : ℝ) = 26 - (j : ℝ) := by
      rw [Nat.cast_sub hj26]
      norm_num
    have hatom : (j : ℝ) * B - ((26 - j : ℕ) : ℝ) * (V / 26) / B - A + w =
        step B V * ((j : ℝ) - d) := by
      rw [hcast]
      change (j : ℝ) * B - (26 - (j : ℝ)) * (V / 26) / B - A + w =
        step B V * ((j : ℝ) - (A - w + V / B) / step B V)
      rw [mul_sub, mul_div_cancel₀ _ hs.ne']
      unfold step
      field_simp [hB.ne']
      ring
    have hmax : max (step B V * ((j : ℝ) - d)) 0 =
        step B V * max ((j : ℝ) - d) 0 := by
      simpa only [mul_zero] using
        (mul_max_of_nonneg ((j : ℝ) - d) 0 hs.le).symm
    rw [hatom, hmax, mul_pow]
    exact mul_le_mul_of_nonneg_left (squared_positive_part_le j d hd) (sq_nonneg _)
  unfold TwoMoment.uniformReferenceSumLaw
  rw [TwoMoment.finiteIndependentSumLaw_const_eq_convPower]
  simp only [Nat.cast_ofNat]
  rw [TwoMoment.integral_convPower_referenceLaw_eq_binomial_sum B (V / 26) 26
      (fun x => (max (x - A + w) 0) ^ 2) hB hz]
  change (∑ j ∈ Finset.range 27, W j *
    (max ((j : ℝ) * B - ((26 - j : ℕ) : ℝ) * (V / 26) / B - A + w) 0) ^ 2) ≤ _
  calc
    _ ≤ ∑ j ∈ Finset.range 27, W j * (step B V ^ 2 * majorant d (j : ℝ)) := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left (hpoint j hj) (by dsimp [W]; positivity)
    _ = (step B V ^ 2 * coefficient2 d) *
          (∑ j ∈ Finset.range 27, W j * falling2 (j : ℝ)) +
        (step B V ^ 2 * coefficient3 d) *
          (∑ j ∈ Finset.range 27, W j * falling3 (j : ℝ)) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      unfold majorant
      ring
    _ = _ := by
      rw [hmoment2, hmoment3]
      change (step B V ^ 2 * coefficient2 d) * ((26 * 25 : ℝ) * p ^ 2) +
        (step B V ^ 2 * coefficient3 d) * ((26 * 25 * 24 : ℝ) * p ^ 3) =
          step B V ^ 2 * (coefficient2 d * (26 * 25) * p ^ 2 +
            coefficient3 d * (26 * 25 * 24) * p ^ 3)
      ring

/-- A true stop-loss infimum bound, including `V = 0`, at any positive
width whose scaled integer threshold lies in `[1,2]`. -/
theorem Q_uniform26_le (B V A w : ℝ) (hB : 0 < B) (hV : 0 ≤ V) (hw : 0 < w)
    (hd : scaledThreshold B V A w ∈ Set.Icc (1 : ℝ) 2) :
    StopLossShape.Q (TwoMoment.uniformReferenceSumLaw B 26 V) A ≤
      step B V ^ 2 *
        (coefficient2 (scaledThreshold B V A w) * (26 * 25) * successProbability B V ^ 2 +
          coefficient3 (scaledThreshold B V A w) * (26 * 25 * 24) * successProbability B V ^ 3) /
            (4 * w) := by
  exact (StopLossShape.Q_le_price (TwoMoment.uniformReferenceSumLaw B 26 V) A w hw).trans
    (div_le_div_of_nonneg_right (integral_uniform26_le B V A w hB hV hd) (by positivity))

end BerryEsseen.FactorialReferencePrice

#print axioms BerryEsseen.FactorialReferencePrice.binomial26_falling2
#print axioms BerryEsseen.FactorialReferencePrice.binomial26_falling3
#print axioms BerryEsseen.FactorialReferencePrice.integral_uniform26_le
#print axioms BerryEsseen.FactorialReferencePrice.Q_uniform26_le
