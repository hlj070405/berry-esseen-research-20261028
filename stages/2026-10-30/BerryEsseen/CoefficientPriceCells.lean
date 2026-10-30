module

public import BerryEsseen.CoefficientRayPrice

@[expose] public section

/-! 2026-10-29: exact cell decomposition and certified cell propagation for
the actual coefficient-ray coarse price. The forcing bound is imposed on
the explicit loss-envelope polynomial. Price nonnegativity and the cell
recurrence are proved from the defining integral, not supplied by a host
recursion or by an unrelated bound on the characteristic-function error. -/

noncomputable section

open MeasureTheory Set
open scoped Interval

namespace BerryEsseen.CoefficientPriceCells

open CoefficientRayPrice

lemma lambda_nonneg (N : ℕ) (hN : 0 < N) (β : ℝ) (hβ : 0 < β) :
    0 ≤ CoarseHighMomentRayPrice.lambda N β := by
  unfold CoarseHighMomentRayPrice.lambda
  exact le_min (div_nonneg hβ.le (sq_nonneg _))
    (div_nonneg (by norm_num) (mul_nonneg (Nat.cast_pos.mpr hN).le hβ.le))

lemma forcing_nonneg (N : ℕ) (hN : 0 < N) (c β u : ℝ) (hβ : 0 < β) (hu : 0 ≤ u) :
    0 ≤ lossEnvelope N c β u *
      (u ^ 2 / 2 + CoarseHighMomentRayPrice.lambda N β * u ^ 3 / 3) := by
  have hl := lambda_nonneg N hN β hβ
  exact mul_nonneg (lossEnvelope_nonneg N c β u) (by positivity)

lemma coarseIntegrand_nonneg (N : ℕ) (hN : 0 < N) (c β u : ℝ)
    (hβ : 0 < β) (hu : 0 ≤ u) : 0 ≤ coarseIntegrand N c β u := by
  have hh := mul_nonneg (Real.exp_nonneg (u ^ 2 / 2))
    (forcing_nonneg N hN c β u hβ hu)
  unfold coarseIntegrand
  convert hh using 1 <;> ring

/-- Nonnegativity belongs to the actual price; it is not an input of the
numerical recurrence. The cubic coefficient c may be any real number. -/
theorem coarsePrice_nonneg (N : ℕ) (hN : 0 < N) (c β t : ℝ)
    (hβ : 0 < β) (ht : 0 ≤ t) : 0 ≤ coarsePrice N c β t := by
  unfold coarsePrice
  exact mul_nonneg (Real.exp_nonneg _) (intervalIntegral.integral_nonneg ht
    (fun u hu => coarseIntegrand_nonneg N hN c β u hβ hu.1))

/-- Exact adjacent-interval split of the defining coarse-price integral.
Continuity proves every integral is defined; no ordering is needed here. -/
theorem coarsePrice_split_integrand (N : ℕ) (c β a b : ℝ) :
    coarsePrice N c β b =
      Real.exp (-((b ^ 2 - a ^ 2) / 2)) * coarsePrice N c β a +
      Real.exp (-(b ^ 2 / 2)) * ∫ u in a..b, coarseIntegrand N c β u := by
  have hs := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    ((continuous_coarseIntegrand N c β).intervalIntegrable 0 a)
    ((continuous_coarseIntegrand N c β).intervalIntegrable a b)
  have he : Real.exp (-((b ^ 2 - a ^ 2) / 2)) * Real.exp (-(a ^ 2 / 2)) =
      Real.exp (-(b ^ 2 / 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold coarsePrice
  rw [← hs, mul_add, ← mul_assoc, he]

/-- Exact variation-of-constants identity, retaining the explicit actual
loss envelope and the polynomial forcing on each cell. -/
theorem coarsePrice_split (N : ℕ) (c β a b : ℝ) :
    coarsePrice N c β b =
      Real.exp (-((b ^ 2 - a ^ 2) / 2)) * coarsePrice N c β a +
      ∫ u in a..b, Real.exp (-((b ^ 2 - u ^ 2) / 2)) *
        (lossEnvelope N c β u *
          (u ^ 2 / 2 + CoarseHighMomentRayPrice.lambda N β * u ^ 3 / 3)) := by
  rw [coarsePrice_split_integrand N c β a b]
  congr 1
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro u _
  unfold coarseIntegrand
  calc
    _ = (Real.exp (-(b ^ 2 / 2)) * Real.exp (u ^ 2 / 2)) *
        (lossEnvelope N c β u *
          (u ^ 2 / 2 + CoarseHighMomentRayPrice.lambda N β * u ^ 3 / 3)) := by ring
    _ = _ := by
      rw [← Real.exp_add]
      congr 1
      congr 1
      ring

private lemma continuous_cellIntegrand (N : ℕ) (c β b : ℝ) :
    Continuous (fun u : ℝ => Real.exp (-((b ^ 2 - u ^ 2) / 2)) *
      (lossEnvelope N c β u *
        (u ^ 2 / 2 + CoarseHighMomentRayPrice.lambda N β * u ^ 3 / 3))) := by
  exact (by fun_prop : Continuous (fun u : ℝ => Real.exp (-((b ^ 2 - u ^ 2) / 2)))).mul
    ((continuous_lossEnvelope N c β).mul (by fun_prop))

lemma forcing_upper_nonneg (N : ℕ) (hN : 0 < N) (c β a b H : ℝ)
    (hβ : 0 < β) (ha : 0 ≤ a) (hab : a ≤ b)
    (hH : ∀ u ∈ Icc a b, lossEnvelope N c β u *
      (u ^ 2 / 2 + CoarseHighMomentRayPrice.lambda N β * u ^ 3 / 3) ≤ H) :
    0 ≤ H :=
  (forcing_nonneg N hN c β a hβ ha).trans (hH a ⟨le_rfl, hab⟩)

/-- One genuine price cell. Its only numerical input is an upper bound on
the explicit forcing at every point of the closed cell. -/
theorem coarsePrice_cell_step (N : ℕ) (hN : 0 < N) (c β a b H : ℝ)
    (hβ : 0 < β) (ha : 0 ≤ a) (hab : a ≤ b)
    (hH : ∀ u ∈ Icc a b, lossEnvelope N c β u *
      (u ^ 2 / 2 + CoarseHighMomentRayPrice.lambda N β * u ^ 3 / 3) ≤ H) :
    coarsePrice N c β b ≤
      Real.exp (-((b ^ 2 - a ^ 2) / 2)) * coarsePrice N c β a + (b - a) * H := by
  have hH0 := forcing_upper_nonneg N hN c β a b H hβ ha hab hH
  have hm := intervalIntegral.integral_mono_on (μ := volume) hab
    ((continuous_cellIntegrand N c β b).intervalIntegrable a b)
    (intervalIntegrable_const (c := H) (a := a) (b := b) (μ := volume))
    (fun u hu => by
      have hu0 : 0 ≤ u := ha.trans hu.1
      have hsq := pow_le_pow_left₀ hu0 hu.2 2
      have he : Real.exp (-((b ^ 2 - u ^ 2) / 2)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by linarith only [hsq])
      calc
        _ ≤ Real.exp (-((b ^ 2 - u ^ 2) / 2)) * H :=
          mul_le_mul_of_nonneg_left (hH u hu) (Real.exp_nonneg _)
        _ ≤ 1 * H := mul_le_mul_of_nonneg_right he hH0
        _ = H := one_mul H)
  rw [intervalIntegral.integral_const, smul_eq_mul] at hm
  rw [coarsePrice_split N c β a b]
  linarith only [hm]

/-- A cell controls its entire interior, including both endpoints. Price
nonnegativity and damping <= 1 are derived from the actual definitions. -/
theorem coarsePrice_cell_inner (N : ℕ) (hN : 0 < N) (c β a b H : ℝ)
    (hβ : 0 < β) (ha : 0 ≤ a) (hab : a ≤ b)
    (hH : ∀ u ∈ Icc a b, lossEnvelope N c β u *
      (u ^ 2 / 2 + CoarseHighMomentRayPrice.lambda N β * u ^ 3 / 3) ≤ H)
    (t : ℝ) (ht : t ∈ Icc a b) :
    coarsePrice N c β t ≤ coarsePrice N c β a + (b - a) * H := by
  have hH0 := forcing_upper_nonneg N hN c β a b H hβ ha hab hH
  have hp0 := coarsePrice_nonneg N hN c β a hβ ha
  have hstep := coarsePrice_cell_step N hN c β a t H hβ ha ht.1
    (fun u hu => hH u ⟨hu.1, hu.2.trans ht.2⟩)
  have hsq := pow_le_pow_left₀ ha ht.1 2
  have he : Real.exp (-((t ^ 2 - a ^ 2) / 2)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith only [hsq])
  have hdecay := mul_le_mul_of_nonneg_right he hp0
  have hwidth := mul_le_mul_of_nonneg_right (sub_le_sub_right ht.2 a) hH0
  nlinarith only [hstep, hdecay, hwidth]

/-- Propagate a certified node value R, using positivity of the exact
exponential multiplier. This is the semantics of an upper-bound recurrence. -/
theorem coarsePrice_cell_step_of_le (N : ℕ) (hN : 0 < N) (c β a b H R : ℝ)
    (hβ : 0 < β) (ha : 0 ≤ a) (hab : a ≤ b)
    (hH : ∀ u ∈ Icc a b, lossEnvelope N c β u *
      (u ^ 2 / 2 + CoarseHighMomentRayPrice.lambda N β * u ^ 3 / 3) ≤ H)
    (hR : coarsePrice N c β a ≤ R) :
    coarsePrice N c β b ≤ Real.exp (-((b ^ 2 - a ^ 2) / 2)) * R + (b - a) * H := by
  apply (coarsePrice_cell_step N hN c β a b H hβ ha hab hH).trans
  have hm := mul_le_mul_of_nonneg_left hR (Real.exp_nonneg (-((b ^ 2 - a ^ 2) / 2)))
  linarith only [hm]

theorem coarsePrice_cell_inner_of_le (N : ℕ) (hN : 0 < N) (c β a b H R : ℝ)
    (hβ : 0 < β) (ha : 0 ≤ a) (hab : a ≤ b)
    (hH : ∀ u ∈ Icc a b, lossEnvelope N c β u *
      (u ^ 2 / 2 + CoarseHighMomentRayPrice.lambda N β * u ^ 3 / 3) ≤ H)
    (hR : coarsePrice N c β a ≤ R) (t : ℝ) (ht : t ∈ Icc a b) :
    coarsePrice N c β t ≤ R + (b - a) * H := by
  have hh := coarsePrice_cell_inner N hN c β a b H hβ ha hab hH t ht
  linarith only [hh, hR]

end BerryEsseen.CoefficientPriceCells

#print axioms BerryEsseen.CoefficientPriceCells.coarsePrice_nonneg
#print axioms BerryEsseen.CoefficientPriceCells.coarsePrice_split
#print axioms BerryEsseen.CoefficientPriceCells.coarsePrice_cell_step
#print axioms BerryEsseen.CoefficientPriceCells.coarsePrice_cell_inner
#print axioms BerryEsseen.CoefficientPriceCells.coarsePrice_cell_step_of_le
#print axioms BerryEsseen.CoefficientPriceCells.coarsePrice_cell_inner_of_le
