module

public import BerryEsseen.ReferenceSumPrice
public import BerryEsseen.PerturbationCDF

@[expose] public section

/-!
The exact finite binomial formula for the true reference price K.
The formula is derived from the actual measure expansion and integration
against its Dirac atoms, rather than used as a replacement definition.
-/

namespace BerryEsseen.TwoMoment

open MeasureTheory
open scoped BigOperators NNReal ENNReal

noncomputable section

/-- The actual convolution power of a two-Dirac mixture, with its
binomial coefficients and sum atoms. The weights need not sum to one. -/
theorem convPower_twoDirac_eq_binomial_measure (lo hi : ℝ) (q p : ℝ≥0) (n : ℕ) :
    MixtureSum.convPower (q • Measure.dirac lo + p • Measure.dirac hi) n =
      ∑ j ∈ Finset.range (n + 1),
        ((n.choose j : ℝ≥0) * p ^ j * q ^ (n - j)) •
          Measure.dirac ((j : ℝ) * hi + ((n - j : ℕ) : ℝ) * lo) := by
  rw [MixtureSum.convPower_mixture]
  apply Finset.sum_congr rfl
  intro j hj
  rw [PerturbationCDF.convPower_dirac, PerturbationCDF.convPower_dirac,
    Measure.dirac_conv_dirac]

/-- Every real test function is integrable under this actual finite
atomic law, including at zero mixture weights. -/
theorem integrable_convPower_twoDirac (lo hi : ℝ) (q p : ℝ≥0) (n : ℕ) (f : ℝ → ℝ) :
    Integrable f (MixtureSum.convPower (q • Measure.dirac lo + p • Measure.dirac hi) n) := by
  rw [convPower_twoDirac_eq_binomial_measure]
  apply integrable_finsetSum_measure.mpr
  intro j hj
  exact (integrable_dirac (by simp)).smul_measure_nnreal

/-- Exact integration against the genuine two-Dirac binomial mixture. -/
theorem integral_convPower_twoDirac (lo hi : ℝ) (q p : ℝ≥0) (n : ℕ) (f : ℝ → ℝ) :
    (∫ x, f x ∂MixtureSum.convPower (q • Measure.dirac lo + p • Measure.dirac hi) n) =
      ∑ j ∈ Finset.range (n + 1),
        (n.choose j : ℝ) * (p : ℝ) ^ j * (q : ℝ) ^ (n - j) *
          f ((j : ℝ) * hi + ((n - j : ℕ) : ℝ) * lo) := by
  rw [convPower_twoDirac_eq_binomial_measure,
    integral_finsetSum_measure (fun j hj =>
      (integrable_dirac (by simp)).smul_measure_nnreal)]
  apply Finset.sum_congr rfl
  intro j hj
  simp [NNReal.smul_def, smul_eq_mul]

/-- General finite-atom integration formula for the actual reference
convolution power. Its variance parameter is exactly the one appearing
in `referenceLaw`, and zero variance is included. -/
theorem integral_convPower_referenceLaw_eq_binomial_sum
    (b z : ℝ) (n : ℕ) (f : ℝ → ℝ) (hb : 0 < b) (hz : 0 ≤ z) :
    (∫ x, f x ∂MixtureSum.convPower (referenceLaw b z) n) =
      ∑ j ∈ Finset.range (n + 1),
        (n.choose j : ℝ) * (z / (b ^ 2 + z)) ^ j *
          (b ^ 2 / (b ^ 2 + z)) ^ (n - j) *
          f ((j : ℝ) * b - ((n - j : ℕ) : ℝ) * z / b) := by
  have hd : 0 < b ^ 2 + z := add_pos_of_pos_of_nonneg (sq_pos_of_pos hb) hz
  have hp : 0 ≤ z / (b ^ 2 + z) := div_nonneg hz hd.le
  have hq : 0 ≤ b ^ 2 / (b ^ 2 + z) := div_nonneg (sq_nonneg _) hd.le
  let p : ℝ≥0 := NNReal.mk (z / (b ^ 2 + z)) hp
  let q : ℝ≥0 := NNReal.mk (b ^ 2 / (b ^ 2 + z)) hq
  have hmix : referenceLaw b z = q • Measure.dirac (-z / b) + p • Measure.dirac b := by
    rw [referenceLaw, ENNReal.ofReal_eq_coe_nnreal hp, ENNReal.ofReal_eq_coe_nnreal hq]
    change p • Measure.dirac b + q • Measure.dirac (-z / b) =
      q • Measure.dirac (-z / b) + p • Measure.dirac b
    exact add_comm _ _
  rw [hmix, integral_convPower_twoDirac]
  apply Finset.sum_congr rfl
  intro j hj
  dsimp only [p, q]
  simp only [NNReal.coe_mk]
  rw [show (j : ℝ) * b + ((n - j : ℕ) : ℝ) * (-z / b) =
      (j : ℝ) * b - ((n - j : ℕ) : ℝ) * z / b by ring]

/-- The exact finite binomial formula for the same true K already
controlled by the finite independent-law comparison. No evaluator is
assumed. The zero-variance law is part of the statement. -/
theorem referenceSumPrice_eq_binomial_sum (b : ℝ) (n : ℕ) (V c : ℝ)
    (hb : 0 < b) (hn : 0 < n) (hV : 0 ≤ V) :
    let z := V / (n : ℝ)
    let p := z / (b ^ 2 + z)
    let q := b ^ 2 / (b ^ 2 + z)
    referenceSumPrice b n V c =
      ∑ j ∈ Finset.range (n + 1),
        (n.choose j : ℝ) * p ^ j * q ^ (n - j) *
          (max ((j : ℝ) * b - ((n - j : ℕ) : ℝ) * z / b - c) 0) ^ 2 := by
  have hz : 0 ≤ V / (n : ℝ) := div_nonneg hV (Nat.cast_pos.mpr hn).le
  dsimp only
  unfold referenceSumPrice uniformReferenceSumLaw
  rw [finiteIndependentSumLaw_const_eq_convPower,
    integral_convPower_referenceLaw_eq_binomial_sum b (V / (n : ℝ)) n
      (fun x => (max (x - c) 0) ^ 2) hb hz]

/-- The empty reference sum is the Dirac mass at zero, independently
of the variance label; no claim that its variance equals `V` is made. -/
theorem referenceSumPrice_empty (b V c : ℝ) :
    referenceSumPrice b 0 V c = (max (-c) 0) ^ 2 := by
  simp [referenceSumPrice, uniformReferenceSumLaw, finiteIndependentSumLaw]

end

end BerryEsseen.TwoMoment

#print axioms BerryEsseen.TwoMoment.convPower_twoDirac_eq_binomial_measure
#print axioms BerryEsseen.TwoMoment.integral_convPower_referenceLaw_eq_binomial_sum
#print axioms BerryEsseen.TwoMoment.referenceSumPrice_eq_binomial_sum
#print axioms BerryEsseen.TwoMoment.referenceSumPrice_empty
