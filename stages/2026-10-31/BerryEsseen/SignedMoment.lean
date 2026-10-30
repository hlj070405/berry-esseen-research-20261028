module

public import BerryEsseen.Target
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

@[expose] public section

/-! 2026-10-28: support-free signed-moment bounds for an actual standardized
real law. Both inequalities are obtained by integrating nonnegative polynomial
witnesses; no support restriction or additional moments are assumed. -/

noncomputable section

open MeasureTheory

namespace BerryEsseen.SignedMoment

def firstAbsoluteMoment (μ : ProbabilityMeasure ℝ) : ℝ :=
  ∫ x, |x| ∂(μ : Measure ℝ)

def signedSecondMoment (μ : ProbabilityMeasure ℝ) : ℝ :=
  ∫ x, x * |x| ∂(μ : Measure ℝ)

lemma integrable_firstAbsoluteMoment (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    Integrable (fun x : ℝ => |x|) (μ : Measure ℝ) := by
  simpa only [Real.norm_eq_abs] using h.integrable_mean.norm

lemma integrable_signedSecondMoment (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    Integrable (fun x : ℝ => x * |x|) (μ : Measure ℝ) := by
  have hmeas : AEStronglyMeasurable (fun x : ℝ => x * |x|) (μ : Measure ℝ) :=
    (continuous_id.mul continuous_abs).aestronglyMeasurable
  apply (integrable_norm_iff hmeas).mp
  have heq : (fun x : ℝ => ‖x * |x|‖) = (fun x : ℝ => x ^ 2) := by
    ext x
    simp only [Real.norm_eq_abs, abs_mul, abs_abs, ← sq, sq_abs]
  rw [heq]
  exact h.integrable_square

/-- The first absolute moment cannot vanish for a law whose second moment is one. -/
theorem firstAbsoluteMoment_pos (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    0 < firstAbsoluteMoment μ := by
  have hnon : 0 ≤ firstAbsoluteMoment μ := integral_nonneg fun x => abs_nonneg x
  by_contra hnot
  have hz : firstAbsoluteMoment μ = 0 := le_antisymm (le_of_not_gt hnot) hnon
  have hae := (integral_eq_zero_iff_of_nonneg (fun x : ℝ => abs_nonneg x)
    (integrable_firstAbsoluteMoment μ h)).mp hz
  have hsquare : (∫ x : ℝ, x ^ 2 ∂(μ : Measure ℝ)) = 0 := by
    calc
      _ = ∫ _ : ℝ, (0 : ℝ) ∂(μ : Measure ℝ) := integral_congr_ae
        (hae.mono fun x hx => by
          have hx0 : x = 0 := abs_eq_zero.mp hx
          simp [hx0])
      _ = 0 := integral_zero _ _
  linarith [h.second_moment_one]

/-- A cubic witness, factored separately on the two half-lines. -/
def cubicWitness (a β x : ℝ) : ℝ :=
  a ^ 2 * |x| ^ 3 + (-2 * a) * x ^ 2 + (-2 * a * β) * (x * |x|) +
    (1 + β ^ 2) * |x| + (2 * β) * x

lemma cubicWitness_nonneg (a β x : ℝ) : 0 ≤ cubicWitness a β x := by
  rcases le_total 0 x with hx | hx
  · have heq : cubicWitness a β x = x * (a * x - 1 - β) ^ 2 := by
      simp only [cubicWitness, abs_of_nonneg hx]
      ring
    rw [heq]
    exact mul_nonneg hx (sq_nonneg _)
  · have heq : cubicWitness a β x = (-x) * (a * (-x) - 1 + β) ^ 2 := by
      simp only [cubicWitness, abs_of_nonpos hx]
      ring
    rw [heq]
    exact mul_nonneg (neg_nonneg.mpr hx) (sq_nonneg _)

lemma integral_cubicWitness (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    (∫ x, cubicWitness (firstAbsoluteMoment μ) (signedSecondMoment μ) x
      ∂(μ : Measure ℝ)) =
    firstAbsoluteMoment μ ^ 2 * thirdAbsoluteMoment μ -
      firstAbsoluteMoment μ * (1 + signedSecondMoment μ ^ 2) := by
  let a := firstAbsoluteMoment μ
  let β := signedSecondMoment μ
  have habs := integrable_firstAbsoluteMoment μ h
  have hsign := integrable_signedSecondMoment μ h
  have hA : Integrable (fun x : ℝ => a ^ 2 * |x| ^ 3) (μ : Measure ℝ) :=
    h.integrable_cube.const_mul _
  have hB : Integrable (fun x : ℝ => (-2 * a) * x ^ 2) (μ : Measure ℝ) :=
    h.integrable_square.const_mul _
  have hC : Integrable (fun x : ℝ => (-2 * a * β) * (x * |x|)) (μ : Measure ℝ) :=
    hsign.const_mul _
  have hD : Integrable (fun x : ℝ => (1 + β ^ 2) * |x|) (μ : Measure ℝ) :=
    habs.const_mul _
  have hE : Integrable (fun x : ℝ => (2 * β) * x) (μ : Measure ℝ) :=
    h.integrable_mean.const_mul _
  have hAB : Integrable (fun x : ℝ => a ^ 2 * |x| ^ 3 + (-2 * a) * x ^ 2)
      (μ : Measure ℝ) := hA.add hB
  have hABC : Integrable (fun x : ℝ => a ^ 2 * |x| ^ 3 + (-2 * a) * x ^ 2 +
      (-2 * a * β) * (x * |x|)) (μ : Measure ℝ) := hAB.add hC
  have hABCD : Integrable (fun x : ℝ => a ^ 2 * |x| ^ 3 + (-2 * a) * x ^ 2 +
      (-2 * a * β) * (x * |x|) + (1 + β ^ 2) * |x|) (μ : Measure ℝ) := hABC.add hD
  change (∫ x, cubicWitness a β x ∂(μ : Measure ℝ)) =
    a ^ 2 * thirdAbsoluteMoment μ - a * (1 + β ^ 2)
  simp only [cubicWitness]
  rw [integral_add hABCD hE, integral_add hABC hD,
    integral_add hAB hC, integral_add hA hB,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_const_mul, h.second_moment_one, h.mean_zero]
  change a ^ 2 * thirdAbsoluteMoment μ + (-2 * a) * 1 + (-2 * a * β) * β +
    (1 + β ^ 2) * a + (2 * β) * 0 = a ^ 2 * thirdAbsoluteMoment μ - a * (1 + β ^ 2)
  ring

/-- The first signed moment bound is obtained from a nonnegative cubic witness. -/
theorem first_mul_third_ge_one_add_signed_sq (μ : ProbabilityMeasure ℝ)
    (h : StandardizedLaw μ) :
    1 + signedSecondMoment μ ^ 2 ≤ firstAbsoluteMoment μ * thirdAbsoluteMoment μ := by
  have ha := firstAbsoluteMoment_pos μ h
  have hnon : 0 ≤ firstAbsoluteMoment μ ^ 2 * thirdAbsoluteMoment μ -
      firstAbsoluteMoment μ * (1 + signedSecondMoment μ ^ 2) := by
    rw [← integral_cubicWitness μ h]
    exact integral_nonneg fun x => cubicWitness_nonneg _ _ x
  have hfactor : 0 ≤ firstAbsoluteMoment μ *
      (firstAbsoluteMoment μ * thirdAbsoluteMoment μ - (1 + signedSecondMoment μ ^ 2)) := by
    nlinarith [hnon]
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left ha).mp hfactor)

/-- Expanded form of `(|x|-a-βx)^2`. -/
def quadraticWitness (a β x : ℝ) : ℝ :=
  (1 + β ^ 2) * x ^ 2 + (-2 * a) * |x| + (-2 * β) * (x * |x|) +
    (2 * a * β) * x + a ^ 2

lemma quadraticWitness_nonneg (a β x : ℝ) : 0 ≤ quadraticWitness a β x := by
  have heq : quadraticWitness a β x = (|x| - a - β * x) ^ 2 := by
    rcases le_total 0 x with hx | hx
    · simp only [quadraticWitness, abs_of_nonneg hx]
      ring
    · simp only [quadraticWitness, abs_of_nonpos hx]
      ring
  rw [heq]
  exact sq_nonneg _

lemma integral_quadraticWitness (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    (∫ x, quadraticWitness (firstAbsoluteMoment μ) (signedSecondMoment μ) x
      ∂(μ : Measure ℝ)) =
    1 - firstAbsoluteMoment μ ^ 2 - signedSecondMoment μ ^ 2 := by
  let a := firstAbsoluteMoment μ
  let β := signedSecondMoment μ
  have habs := integrable_firstAbsoluteMoment μ h
  have hsign := integrable_signedSecondMoment μ h
  have hA : Integrable (fun x : ℝ => (1 + β ^ 2) * x ^ 2) (μ : Measure ℝ) :=
    h.integrable_square.const_mul _
  have hB : Integrable (fun x : ℝ => (-2 * a) * |x|) (μ : Measure ℝ) := habs.const_mul _
  have hC : Integrable (fun x : ℝ => (-2 * β) * (x * |x|)) (μ : Measure ℝ) := hsign.const_mul _
  have hD : Integrable (fun x : ℝ => (2 * a * β) * x) (μ : Measure ℝ) :=
    h.integrable_mean.const_mul _
  have hE : Integrable (fun _ : ℝ => a ^ 2) (μ : Measure ℝ) := integrable_const _
  have hAB : Integrable (fun x : ℝ => (1 + β ^ 2) * x ^ 2 + (-2 * a) * |x|)
      (μ : Measure ℝ) := hA.add hB
  have hABC : Integrable (fun x : ℝ => (1 + β ^ 2) * x ^ 2 + (-2 * a) * |x| +
      (-2 * β) * (x * |x|)) (μ : Measure ℝ) := hAB.add hC
  have hABCD : Integrable (fun x : ℝ => (1 + β ^ 2) * x ^ 2 + (-2 * a) * |x| +
      (-2 * β) * (x * |x|) + (2 * a * β) * x) (μ : Measure ℝ) := hABC.add hD
  change (∫ x, quadraticWitness a β x ∂(μ : Measure ℝ)) = 1 - a ^ 2 - β ^ 2
  simp only [quadraticWitness]
  rw [integral_add hABCD hE, integral_add hABC hD,
    integral_add hAB hC, integral_add hA hB,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
    h.second_moment_one, h.mean_zero]
  simp only [integral_const, probReal_univ, one_smul]
  change (1 + β ^ 2) * 1 + (-2 * a) * a + (-2 * β) * β +
    (2 * a * β) * 0 + a ^ 2 = 1 - a ^ 2 - β ^ 2
  ring

/-- The second signed moment bound is the integral of an actual square. -/
theorem first_sq_add_signed_sq_le_one (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    firstAbsoluteMoment μ ^ 2 + signedSecondMoment μ ^ 2 ≤ 1 := by
  have hnon : 0 ≤ 1 - firstAbsoluteMoment μ ^ 2 - signedSecondMoment μ ^ 2 := by
    rw [← integral_quadraticWitness μ h]
    exact integral_nonneg fun x => quadraticWitness_nonneg _ _ x
  linarith

/-- Polynomial elimination of the first absolute moment, without radicals. -/
theorem signed_sq_polynomial_of_rho_cap (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (R : ℝ) (hcap : thirdAbsoluteMoment μ ≤ R) :
    (1 + signedSecondMoment μ ^ 2) ^ 2 ≤ R ^ 2 * (1 - signedSecondMoment μ ^ 2) := by
  have ha := firstAbsoluteMoment_pos μ h
  have hfirst := first_mul_third_ge_one_add_signed_sq μ h
  have hsecond := first_sq_add_signed_sq_le_one μ h
  have hprod : 1 + signedSecondMoment μ ^ 2 ≤ firstAbsoluteMoment μ * R :=
    hfirst.trans (mul_le_mul_of_nonneg_left hcap (le_of_lt ha))
  have hleft : 0 ≤ 1 + signedSecondMoment μ ^ 2 := by nlinarith [sq_nonneg (signedSecondMoment μ)]
  have hright : 0 ≤ firstAbsoluteMoment μ * R := hleft.trans hprod
  have hsquare := (sq_le_sq₀ hleft hright).mpr hprod
  have hweighted := mul_le_mul_of_nonneg_left hsecond (sq_nonneg R)
  nlinarith [hsquare, hweighted]

/-- A reusable strict rational gate: all numerical work is a polynomial inequality. -/
theorem abs_signed_lt_of_rho_cap (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (R b : ℝ) (hb : 0 ≤ b) (hcap : thirdAbsoluteMoment μ ≤ R)
    (hgate : R ^ 2 * (1 - b ^ 2) < (1 + b ^ 2) ^ 2) :
    |signedSecondMoment μ| < b := by
  have hpoly := signed_sq_polynomial_of_rho_cap μ h R hcap
  by_contra hnot
  have hle : b ≤ |signedSecondMoment μ| := le_of_not_gt hnot
  have hb2 : b ^ 2 ≤ signedSecondMoment μ ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ hb (abs_nonneg (signedSecondMoment μ))).mpr hle
  have hmono : (1 + b ^ 2) ^ 2 ≤ (1 + signedSecondMoment μ ^ 2) ^ 2 :=
    (sq_le_sq₀ (by nlinarith [sq_nonneg b])
      (by nlinarith [sq_nonneg (signedSecondMoment μ)])).mpr (by linarith)
  have hterm : R ^ 2 * (1 - signedSecondMoment μ ^ 2) ≤ R ^ 2 * (1 - b ^ 2) :=
    mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg R)
  linarith

/-- The `ρ ≤ 11/10` support-free signed-moment price. -/
theorem abs_signed_lt_127_500 (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hcap : thirdAbsoluteMoment μ ≤ (11 : ℝ) / 10) :
    |signedSecondMoment μ| < (127 : ℝ) / 500 :=
  abs_signed_lt_of_rho_cap μ h (11 / 10) (127 / 500) (by norm_num) hcap (by norm_num)

/-- The `ρ ≤ 6/5` support-free signed-moment price. -/
theorem abs_signed_lt_44_125 (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hcap : thirdAbsoluteMoment μ ≤ (6 : ℝ) / 5) :
    |signedSecondMoment μ| < (44 : ℝ) / 125 :=
  abs_signed_lt_of_rho_cap μ h (6 / 5) (44 / 125) (by norm_num) hcap (by norm_num)

/-- The `ρ ≤ 7361/4000` support-free signed-moment price. -/
theorem abs_signed_lt_643_1000 (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hcap : thirdAbsoluteMoment μ ≤ (7361 : ℝ) / 4000) :
    |signedSecondMoment μ| < (643 : ℝ) / 1000 :=
  abs_signed_lt_of_rho_cap μ h (7361 / 4000) (643 / 1000) (by norm_num) hcap (by norm_num)

end BerryEsseen.SignedMoment

#print axioms BerryEsseen.SignedMoment.firstAbsoluteMoment_pos
#print axioms BerryEsseen.SignedMoment.first_mul_third_ge_one_add_signed_sq
#print axioms BerryEsseen.SignedMoment.first_sq_add_signed_sq_le_one
#print axioms BerryEsseen.SignedMoment.abs_signed_lt_of_rho_cap
#print axioms BerryEsseen.SignedMoment.abs_signed_lt_127_500
#print axioms BerryEsseen.SignedMoment.abs_signed_lt_44_125
#print axioms BerryEsseen.SignedMoment.abs_signed_lt_643_1000
