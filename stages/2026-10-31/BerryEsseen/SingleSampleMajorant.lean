module

public import BerryEsseen.Target
public import BerryEsseen.TwoMoment

@[expose] public section

/-! Analytic cubic moment majorants for arbitrary standardized laws.
All inequalities are pointwise on the whole real line, with closed cuts.
No support restriction or finite certificate table is used. -/

namespace BerryEsseen.SingleSampleMajorant

open MeasureTheory Set

noncomputable section

def slopeV (b r : ℝ) : ℝ := (2 : ℝ) / 5 * (b + 2 * r)
def slopeU (b r : ℝ) : ℝ := -(2 : ℝ) / 5 * (2 * b * r + r ^ 2)
def meanPrice (b r : ℝ) : ℝ := 1 + slopeV b r + (2 : ℝ) / 5 * b * r ^ 2
def majorant (b r y : ℝ) : ℝ :=
  meanPrice b r + (2 : ℝ) / 5 * |y| ^ 3 + slopeU b r * y + slopeV b r * (y ^ 2 - 1)

theorem majorant_factor (b r y : ℝ) :
    majorant b r y = 1 - (2 : ℝ) / 5 * (y - r) ^ 2 * (y - b) +
      (2 : ℝ) / 5 * (|y| ^ 3 + y ^ 3) := by
  unfold majorant meanPrice slopeU slopeV
  ring

theorem one_le_majorant_of_le (b r y : ℝ) (hy : y ≤ b) : 1 ≤ majorant b r y := by
  have habs : 0 ≤ |y| ^ 3 + y ^ 3 := by
    by_cases hy0 : 0 ≤ y
    · rw [abs_of_nonneg hy0]
      positivity
    · rw [abs_of_nonpos (le_of_not_ge hy0)]
      ring_nf
      exact le_rfl
  have hf := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (y - r)) (sub_nonpos.mpr hy)
  rw [majorant_factor]
  nlinarith only [habs, hf]

theorem base_positive_identity (y : ℝ) (hy : 0 ≤ y) :
    majorant (-13 / 25) (-5 / 8) y =
      (y - 143 / 100) ^ 2 * ((2 : ℝ) / 5 * y + 109 / 250) +
        (51 : ℝ) / 4000 * y + 33967 / 1250000 := by
  unfold majorant meanPrice slopeU slopeV
  rw [abs_of_nonneg hy]
  ring

theorem base_nonneg (y : ℝ) : 0 ≤ majorant (-13 / 25) (-5 / 8) y := by
  by_cases hyb : y ≤ -13 / 25
  · linarith [one_le_majorant_of_le (-13 / 25) (-5 / 8) y hyb]
  by_cases hy : y ≤ 0
  · have hx0 : 0 ≤ y + 5 / 8 := by linarith
    have hx : y + 5 / 8 ≤ (5 : ℝ) / 8 := by linarith
    have hd0 : 0 ≤ y + 13 / 25 := by linarith
    have hd : y + 13 / 25 ≤ (13 : ℝ) / 25 := by linarith
    have hs : (y + 5 / 8) ^ 2 ≤ ((5 : ℝ) / 8) ^ 2 :=
      (sq_le_sq₀ hx0 (by norm_num)).mpr hx
    have hprod := mul_le_mul hs hd hd0 (sq_nonneg ((5 : ℝ) / 8))
    have heq : majorant (-13 / 25) (-5 / 8) y =
        1 - (2 : ℝ) / 5 * (y + 5 / 8) ^ 2 * (y + 13 / 25) := by
      rw [majorant_factor, abs_of_nonpos hy]
      ring
    rw [heq]
    nlinarith only [hprod]
  · have hy0 : 0 ≤ y := le_of_not_ge hy
    rw [base_positive_identity y hy0]
    positivity

theorem negative_family_increment (b y : ℝ) :
    majorant b (-5 / 8) y - majorant (-13 / 25) (-5 / 8) y =
      (2 : ℝ) / 5 * (b + 13 / 25) * (y + 5 / 8) ^ 2 := by
  unfold majorant meanPrice slopeU slopeV
  ring

theorem negative_family_nonneg (b y : ℝ) (hb : -13 / 25 ≤ b) :
    0 ≤ majorant b (-5 / 8) y := by
  have hinc : 0 ≤ majorant b (-5 / 8) y - majorant (-13 / 25) (-5 / 8) y := by
    rw [negative_family_increment]
    exact mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (sq_nonneg _)
  linarith [base_nonneg y]

theorem positive_family_increment (b y : ℝ) (hy : 0 ≤ y) :
    majorant b (-5 / 8 - 3 * b / 10) y - majorant (-13 / 25) (-5 / 8) y =
      13 / 160 + 5 * b / 32 + 3 * b ^ 2 / 20 + 9 * b ^ 3 / 250 +
        (13 / 50 + 7 * b / 20 + 51 * b ^ 2 / 250) * y +
        (26 / 125 + 4 * b / 25) * y ^ 2 := by
  unfold majorant meanPrice slopeU slopeV
  rw [abs_of_nonneg hy]
  ring

theorem positive_family_nonneg (b y : ℝ) (hb : 0 ≤ b) :
    0 ≤ majorant b (-5 / 8 - 3 * b / 10) y := by
  by_cases hy : y ≤ b
  · linarith [one_le_majorant_of_le b (-5 / 8 - 3 * b / 10) y hy]
  have hy0 : 0 ≤ y := hb.trans (le_of_not_ge hy)
  have hinc : 0 ≤ majorant b (-5 / 8 - 3 * b / 10) y -
      majorant (-13 / 25) (-5 / 8) y := by
    rw [positive_family_increment b y hy0]
    positivity
  linarith [base_nonneg y]

theorem integrable_majorant (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ) (b r : ℝ) :
    Integrable (majorant b r) (μ : Measure ℝ) := by
  unfold majorant
  exact (((integrable_const _).add (hμ.integrable_cube.const_mul _)).add
    (hμ.integrable_mean.const_mul _)).add
      ((hμ.integrable_square.sub (integrable_const 1)).const_mul _)

theorem integral_majorant (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ) (b r : ℝ) :
    (∫ y, majorant b r y ∂(μ : Measure ℝ)) = meanPrice b r + (2 : ℝ) / 5 * thirdAbsoluteMoment μ := by
  have hA : Integrable (fun y : ℝ => meanPrice b r + (2 : ℝ) / 5 * |y| ^ 3) (μ : Measure ℝ) :=
    (integrable_const _).add (hμ.integrable_cube.const_mul _)
  have hB : Integrable (fun y : ℝ => slopeU b r * y) (μ : Measure ℝ) :=
    hμ.integrable_mean.const_mul _
  have hC : Integrable (fun y : ℝ => slopeV b r * (y ^ 2 - 1)) (μ : Measure ℝ) := by
    convert (hμ.integrable_square.sub (integrable_const 1)).const_mul (slopeV b r) using 1
  have hAB : Integrable (fun y : ℝ => meanPrice b r + (2 : ℝ) / 5 * |y| ^ 3 + slopeU b r * y)
      (μ : Measure ℝ) := hA.add hB
  unfold majorant
  rw [integral_add hAB hC, integral_add hA hB,
    integral_add (integrable_const _) (hμ.integrable_cube.const_mul _),
    integral_const_mul, integral_const_mul, integral_const_mul,
    integral_sub hμ.integrable_square (integrable_const 1), hμ.mean_zero, hμ.second_moment_one]
  simp [thirdAbsoluteMoment]

/-- Integrating a whole-line majorant preserves every atom at the cut. -/
theorem closedCDF_le_majorant (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (b r : ℝ) (hq : ∀ y, 0 ≤ majorant b r y) :
    (μ : Measure ℝ).real (Iic b) ≤ meanPrice b r + (2 : ℝ) / 5 * thirdAbsoluteMoment μ := by
  rw [← integral_majorant μ hμ b r, ← integral_indicator_one measurableSet_Iic]
  apply integral_mono ((integrable_const (1 : ℝ)).indicator measurableSet_Iic)
    (integrable_majorant μ hμ b r)
  intro y
  by_cases hy : y ∈ Iic b
  · rw [indicator_of_mem hy]
    exact one_le_majorant_of_le b r y hy
  · rw [indicator_of_notMem hy]
    exact hq y

theorem negative_family_CDF (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (b : ℝ) (hb : -13 / 25 ≤ b) :
    (μ : Measure ℝ).real (Iic b) ≤ (1 : ℝ) / 2 + 89 * b / 160 +
      (2 : ℝ) / 5 * thirdAbsoluteMoment μ := by
  have h := closedCDF_le_majorant μ hμ b (-5 / 8) (fun y => negative_family_nonneg b y hb)
  have hp : meanPrice b (-5 / 8) = (1 : ℝ) / 2 + 89 * b / 160 := by
    unfold meanPrice slopeV
    ring
  rwa [hp] at h

theorem positive_family_CDF (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (b : ℝ) (hb : 0 ≤ b) :
    (μ : Measure ℝ).real (Iic b) ≤ (1 : ℝ) / 2 + 253 * b / 800 + 3 * b ^ 2 / 20 + 9 * b ^ 3 / 250 +
      (2 : ℝ) / 5 * thirdAbsoluteMoment μ := by
  have h := closedCDF_le_majorant μ hμ b (-5 / 8 - 3 * b / 10) (fun y => positive_family_nonneg b y hb)
  have hp : meanPrice b (-5 / 8 - 3 * b / 10) =
      (1 : ℝ) / 2 + 253 * b / 800 + 3 * b ^ 2 / 20 + 9 * b ^ 3 / 250 := by
    unfold meanPrice slopeV
    ring
  rwa [hp] at h

/-- A shifted-square majorant proves the closed Cantelli bound for the
same unrestricted standardized law. -/
theorem closedCDF_neg_le_cantelli (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (a : ℝ) (ha : 0 < a) : (μ : Measure ℝ).real (Iic (-a)) ≤ 1 / (1 + a ^ 2) := by
  have hden : 0 < a + 1 / a := add_pos ha (one_div_pos.mpr ha)
  have hI := TwoMoment.integrable_shift_sq (μ : Measure ℝ) (fun y : ℝ => y) (1 / a)
    hμ.integrable_mean hμ.integrable_square
  have hmean := TwoMoment.integral_shift_sq (μ : Measure ℝ) (fun y : ℝ => y) (1 / a)
    hμ.integrable_mean hμ.integrable_square hμ.mean_zero
  rw [hμ.second_moment_one] at hmean
  have hbound : (μ : Measure ℝ).real (Iic (-a)) ≤
      (∫ y, (y - 1 / a) ^ 2 / (a + 1 / a) ^ 2 ∂(μ : Measure ℝ)) := by
    rw [← integral_indicator_one measurableSet_Iic]
    apply integral_mono ((integrable_const (1 : ℝ)).indicator measurableSet_Iic) (hI.div_const _)
    intro y
    by_cases hy : y ∈ Iic (-a)
    · rw [indicator_of_mem hy]
      have hyle : y ≤ -a := hy
      apply (le_div_iff₀ (sq_pos_of_pos hden)).mpr
      have hsq := sq_le_sq₀ hden.le (show 0 ≤ 1 / a - y by linarith [one_div_pos.mpr ha])
      have hx : a + 1 / a ≤ 1 / a - y := by linarith
      nlinarith [(hsq.mpr hx)]
    · rw [indicator_of_notMem hy]
      exact div_nonneg (sq_nonneg _) (sq_nonneg _)
  rw [integral_div, hmean] at hbound
  have heq : (1 + (1 / a) ^ 2) / (a + 1 / a) ^ 2 = 1 / (1 + a ^ 2) := by
    field_simp [ha.ne', hden.ne', (show (1 + a ^ 2 : ℝ) ≠ 0 by positivity)]
    ring
  rwa [heq] at hbound

end

end BerryEsseen.SingleSampleMajorant

#print axioms BerryEsseen.SingleSampleMajorant.closedCDF_le_majorant
#print axioms BerryEsseen.SingleSampleMajorant.closedCDF_neg_le_cantelli
