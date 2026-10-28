module

public import BerryEsseen.StaircaseIntegral
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
The clipped-square price for the same common residual staircase.
The prefix gate is the original ratio gate from the manuscript. Incoming
jumps retain their closed boundaries, and the phase is any real number.
-/

namespace BerryEsseen.Staircase

open MeasureTheory
open scoped BigOperators

noncomputable section

lemma ratioGate_implies_squarePrice (H a h x : ℝ) (ha : 0 < a) (hh : 0 < h)
    (hgate : H / a ≤ 2 * x / h + x ^ 2 / h ^ 2) :
    a + H ≤ (a / h ^ 2) * (x + h) ^ 2 := by
  have hg := (div_le_iff₀ ha).mp hgate
  have hidentity : (2 * x / h + x ^ 2 / h ^ 2) * a =
      (a / h ^ 2) * (x + h) ^ 2 - a := by
    field_simp [hh.ne']; ring
  rw [hidentity] at hg
  linarith

/-- A price bound at every incoming jump controls the nonnegative phase. -/
theorem incoming_add_le_squarePrice (w : ℕ → ℝ) (a d h y : ℝ) (N : ℕ)
    (ha : 0 ≤ a) (hd : 0 ≤ d) (hh : 0 < h) (hy : 0 ≤ y)
    (hprice : ∀ r : ℕ, 1 ≤ r → r ≤ N →
      a + prefixMass w r ≤ (a / h ^ 2) * ((r : ℝ) * d + h) ^ 2) :
    a + incoming w d y N ≤ (a / h ^ 2) * (y + h) ^ 2 := by
  have hc : 0 ≤ a / h ^ 2 := div_nonneg ha (sq_nonneg h)
  have hcancel : (a / h ^ 2) * h ^ 2 = a :=
    div_mul_cancel₀ a (pow_ne_zero 2 hh.ne')
  induction N with
  | zero =>
      have hsq : h ^ 2 ≤ (y + h) ^ 2 :=
        (sq_le_sq₀ hh.le (by linarith : 0 ≤ y + h)).mpr (by linarith)
      have hm := mul_le_mul_of_nonneg_left hsq hc
      rw [hcancel] at hm
      simpa [incoming] using hm
  | succ N ih =>
      by_cases hlast : ((N + 1 : ℕ) : ℝ) * d ≤ y
      · rw [incoming_eq_prefix_of_last_active w d y (N + 1) hd hlast]
        have hleft : 0 ≤ ((N + 1 : ℕ) : ℝ) * d + h :=
          add_nonneg (mul_nonneg (Nat.cast_nonneg _) hd) hh.le
        have hsq : (((N + 1 : ℕ) : ℝ) * d + h) ^ 2 ≤ (y + h) ^ 2 :=
          (sq_le_sq₀ hleft (by linarith : 0 ≤ y + h)).mpr (by linarith)
        exact (hprice (N + 1) (Nat.succ_pos _) le_rfl).trans
          (mul_le_mul_of_nonneg_left hsq hc)
      · have hprev : a + incoming w d y N ≤ (a / h ^ 2) * (y + h) ^ 2 :=
          ih (fun r hr hrN => hprice r hr (Nat.le_succ_of_le hrN))
        unfold incoming
        rw [Finset.sum_range_succ, ite_eq_right hlast, add_zero]
        exact hprev

/-- The exact clipped-square staircase majorant, including all jump points.
As in the linear majorant, this pointwise implication needs no sign
assumption on the individual incoming weights. -/
theorem signedStaircase_add_le_clippedSquare (w : ℕ → ℝ) (a d h y : ℝ) (N : ℕ)
    (ha : 0 < a) (hd : 0 ≤ d) (hh : 0 < h)
    (hgate : ∀ r : ℕ, 1 ≤ r → r ≤ N → prefixMass w r / a ≤
      2 * (r : ℝ) * d / h + (r : ℝ) ^ 2 * d ^ 2 / h ^ 2) :
    signedStaircase w a d y N + a ≤ (a / h ^ 2) * (max (y + h) 0) ^ 2 := by
  by_cases hy : y < 0
  · simp only [signedStaircase, ite_eq_left hy,
      incoming_eq_zero_of_negative_phase w d y N hd hy, add_zero, neg_add_cancel]
    exact mul_nonneg (div_nonneg ha.le (sq_nonneg h)) (sq_nonneg _)
  · have hynonneg : 0 ≤ y := le_of_not_gt hy
    have hprice : ∀ r : ℕ, 1 ≤ r → r ≤ N →
        a + prefixMass w r ≤ (a / h ^ 2) * ((r : ℝ) * d + h) ^ 2 := by
      intro r hr hrN
      apply ratioGate_implies_squarePrice _ a h ((r : ℝ) * d) ha hh
      simpa only [mul_assoc, mul_pow] using hgate r hr hrN
    have hbound := incoming_add_le_squarePrice w a d h y N ha.le hd hh hynonneg hprice
    simp only [signedStaircase, ite_eq_right hy, neg_zero, zero_add]
    rw [max_eq_left (by linarith : 0 ≤ y + h)]
    linarith

/-- The closed weighted CDF is controlled by the clipped-square price
after dropping only the lower-count losses. -/
theorem coupledCDF_le_clippedSquare (π W : ℕ → ℝ) (k N : ℕ) (Δ h t : ℝ)
    (hπ : ∀ j, 0 ≤ π j) (ha : 0 < π k) (hd : 0 ≤ 1 - Δ) (hh : 0 < h)
    (hcoupling : ∀ r : ℕ, 1 ≤ r → r ≤ N →
      W k - (r : ℝ) * Δ ≤ W (k + r))
    (hgate : ∀ r : ℕ, 1 ≤ r → r ≤ N →
      prefixMass (fun j => π (k + j)) r / π k ≤
        2 * (r : ℝ) * (1 - Δ) / h + (r : ℝ) ^ 2 * (1 - Δ) ^ 2 / h ^ 2) :
    weightedClosedCDF π W (k + N) ((k : ℝ) + t) ≤ lowerMass π k - π k +
      (π k / h ^ 2) * (max (t + h - W k) 0) ^ 2 := by
  have hstep := coupledCDF_deviation_le_staircase π W k N Δ t hπ hcoupling
  have hbound := signedStaircase_add_le_clippedSquare (fun r => π (k + r)) (π k)
    (1 - Δ) h (t - W k) N ha hd hh hgate
  have hphase : t - W k + h = t + h - W k := by ring
  rw [hphase] at hbound
  linarith

lemma clippedSquare_le_two_squares (c u : ℝ) :
    (max (c - u) 0) ^ 2 ≤ 2 * c ^ 2 + 2 * u ^ 2 := by
  by_cases hz : 0 ≤ c - u
  · rw [max_eq_left hz]
    nlinarith [sq_nonneg (c + u)]
  · rw [max_eq_right (le_of_not_ge hz)]
    nlinarith [sq_nonneg c, sq_nonneg u]

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A measurable residual with a finite second moment has an integrable
shifted squared positive part, on every finite measure space. -/
theorem integrable_clippedSquare_of_integrable_sq (μ : Measure Ω) [IsFiniteMeasure μ]
    (W : Ω → ℝ) (c : ℝ) (hW : Measurable W)
    (hSq : Integrable (fun ω => (W ω) ^ 2) μ) :
    Integrable (fun ω => (max (c - W ω) 0) ^ 2) μ := by
  have hdom : Integrable (fun ω => 2 * c ^ 2 + 2 * (W ω) ^ 2) μ :=
    (integrable_const (2 * c ^ 2)).add (hSq.const_mul 2)
  have hm : Measurable (fun ω => (max (c - W ω) 0) ^ 2) :=
    ((measurable_const.sub hW).max measurable_const).pow_const 2
  apply hdom.mono' hm.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact clippedSquare_le_two_squares c (W ω))

/-- The clipped-square bound on an arbitrary probability space.
Its hypotheses require the actual second moment to be integrable; no
finite-support assumption on the residual laws is made. -/
theorem coupledMixtureCDF_le_clippedSquare (μ : Measure Ω) [IsProbabilityMeasure μ]
    (π : ℕ → ℝ) (W : ℕ → Ω → ℝ) (k N : ℕ) (Δ h t : ℝ)
    (hπ : ∀ j, 0 ≤ π j) (ha : 0 < π k) (hd : 0 ≤ 1 - Δ) (hh : 0 < h)
    (hclosed : ∀ j : ℕ, j ≤ k + N →
      MeasurableSet {ω | (j : ℝ) + W j ω ≤ (k : ℝ) + t})
    (hWk : Measurable (W k)) (hSq : Integrable (fun ω => (W k ω) ^ 2) μ)
    (hcoupling : ∀ᵐ ω ∂μ, ∀ r : ℕ, 1 ≤ r → r ≤ N →
      W k ω - (r : ℝ) * Δ ≤ W (k + r) ω)
    (hgate : ∀ r : ℕ, 1 ≤ r → r ≤ N →
      prefixMass (fun j => π (k + j)) r / π k ≤
        2 * (r : ℝ) * (1 - Δ) / h + (r : ℝ) ^ 2 * (1 - Δ) ^ 2 / h ^ 2) :
    closedMixtureCDF μ π W (k + N) ((k : ℝ) + t) ≤ lowerMass π k - π k +
      (π k / h ^ 2) * (∫ ω, (max (t + h - W k ω) 0) ^ 2 ∂μ) := by
  have hclip := integrable_clippedSquare_of_integrable_sq μ (W k) (t + h) hWk hSq
  have hprice : Integrable (fun ω =>
      (π k / h ^ 2) * (max (t + h - W k ω) 0) ^ 2) μ :=
    hclip.const_mul (π k / h ^ 2)
  have hrhs : Integrable (fun ω => lowerMass π k - π k +
      (π k / h ^ 2) * (max (t + h - W k ω) 0) ^ 2) μ :=
    (integrable_const (lowerMass π k - π k)).add hprice
  have hae : (fun ω => weightedClosedCDF π (fun j => W j ω) (k + N) ((k : ℝ) + t))
      ≤ᵐ[μ] (fun ω => lowerMass π k - π k +
        (π k / h ^ 2) * (max (t + h - W k ω) 0) ^ 2) :=
    hcoupling.mono (fun ω hc => coupledCDF_le_clippedSquare π (fun j => W j ω)
      k N Δ h t hπ ha hd hh hc hgate)
  have hint := integral_mono_ae
    (integrable_weightedClosedCDF μ π W (k + N) ((k : ℝ) + t) hclosed) hrhs hae
  have hidentity :
      (∫ ω, lowerMass π k - π k +
        (π k / h ^ 2) * (max (t + h - W k ω) 0) ^ 2 ∂μ) = lowerMass π k - π k +
      (π k / h ^ 2) * (∫ ω, (max (t + h - W k ω) 0) ^ 2 ∂μ) := by
    rw [integral_add (integrable_const (lowerMass π k - π k)) hprice,
      integral_const_mul]
    simp only [integral_const, probReal_univ, one_smul]
  calc
    closedMixtureCDF μ π W (k + N) ((k : ℝ) + t) =
        ∫ ω, weightedClosedCDF π (fun j => W j ω) (k + N) ((k : ℝ) + t) ∂μ :=
      (integral_weightedClosedCDF μ π W (k + N) ((k : ℝ) + t) hclosed).symm
    _ ≤ _ := hint
    _ = _ := hidentity

end

end BerryEsseen.Staircase

#print axioms BerryEsseen.Staircase.signedStaircase_add_le_clippedSquare
#print axioms BerryEsseen.Staircase.coupledCDF_le_clippedSquare
#print axioms BerryEsseen.Staircase.coupledMixtureCDF_le_clippedSquare
