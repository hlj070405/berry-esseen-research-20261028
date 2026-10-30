module

public import BerryEsseen.CoefficientRayPrice
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

@[expose] public section

/-! 2026-10-29: endpoint arithmetic controls the entire frequency cell.
A cubic with nonnegative cubic coefficient has no interior maximum on
the nonnegative half-line. The resulting cell bounds apply to the actual
coefficient envelope and its loss; no finite sampling assumption is used. -/

noncomputable section

open Set

namespace BerryEsseen.CubicCellEnvelope

open CoefficientRayPrice

def cubic (A B t : ℝ) : ℝ := -A * t ^ 2 + B * t ^ 3

lemma cubic_hasDerivAt (A B t : ℝ) :
    HasDerivAt (cubic A B) (t * (3 * B * t - 2 * A)) t := by
  unfold cubic
  convert (((hasDerivAt_id' t).fun_pow 2).const_mul (-A)).add
    (((hasDerivAt_id' t).fun_pow 3).const_mul B) using 1
  ring

theorem cubic_le_endpoint_max (A B a b t : ℝ) (hB : 0 ≤ B)
    (ha : 0 ≤ a) (hat : a ≤ t) (htb : t ≤ b) :
    cubic A B t ≤ max (cubic A B a) (cubic A B b) := by
  have hc : Continuous (cubic A B) := by unfold cubic; fun_prop
  by_cases hd : 3 * B * t ≤ 2 * A
  · have hm : AntitoneOn (cubic A B) (Icc a t) := by
      apply antitoneOn_of_hasDerivWithinAt_nonpos (f' := fun u => u * (3 * B * u - 2 * A))
        (convex_Icc a t) hc.continuousOn
      · intro u _
        exact (cubic_hasDerivAt A B u).hasDerivWithinAt
      · intro u hu
        rw [interior_Icc] at hu
        have hu0 : 0 ≤ u := ha.trans hu.1.le
        have hup := mul_le_mul_of_nonneg_left hu.2.le (by positivity : 0 ≤ 3 * B)
        exact mul_nonpos_of_nonneg_of_nonpos hu0 (by linarith only [hup, hd])
    exact (hm ⟨le_rfl, hat⟩ ⟨hat, le_rfl⟩ hat).trans (le_max_left _ _)
  · have hm : MonotoneOn (cubic A B) (Icc t b) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun u => u * (3 * B * u - 2 * A))
        (convex_Icc t b) hc.continuousOn
      · intro u _
        exact (cubic_hasDerivAt A B u).hasDerivWithinAt
      · intro u hu
        rw [interior_Icc] at hu
        have hu0 : 0 ≤ u := ha.trans (hat.trans hu.1.le)
        have hup := mul_le_mul_of_nonneg_left hu.1.le (by positivity : 0 ≤ 3 * B)
        exact mul_nonneg hu0 (by linarith only [hup, not_le.mp hd])
    exact (hm ⟨le_rfl, htb⟩ ⟨htb, le_rfl⟩ htb).trans (le_max_right _ _)

theorem exponent_le_endpoint_max (c A B β a b t : ℝ)
    (hc : 0 ≤ c) (hB : 0 ≤ B) (hβ : 0 ≤ β)
    (ha : 0 ≤ a) (hat : a ≤ t) (htb : t ≤ b) :
    exponent c A B β t ≤ max (exponent c A B β a) (exponent c A B β b) := by
  have ht : 0 ≤ t := ha.trans hat
  have hb : 0 ≤ b := ht.trans htb
  simpa only [exponent, abs_of_nonneg ht, abs_of_nonneg ha, abs_of_nonneg hb, cubic] using
    cubic_le_endpoint_max A (B * c * β) a b t (by positivity) ha hat htb

def cellExponent (c β a b : ℝ) : ℝ :=
  min 0 (min
    (max (exponent c (1 / 2) (1 / 10) β a) (exponent c (1 / 2) (1 / 10) β b))
    (min
      (max (exponent c ClassicalCosineCubic.a ClassicalCosineCubic.b β a)
        (exponent c ClassicalCosineCubic.a ClassicalCosineCubic.b β b))
      (max (exponent c ClassicalRationalCosine.a ClassicalRationalCosine.b β a)
        (exponent c ClassicalRationalCosine.a ClassicalRationalCosine.b β b))))

lemma cellExponent_nonpos (c β a b : ℝ) : cellExponent c β a b ≤ 0 := min_le_left _ _

private lemma exp_min (x y : ℝ) : Real.exp (min x y) = min (Real.exp x) (Real.exp y) := by
  rcases le_total x y with h | h
  · rw [min_eq_left h, min_eq_left (Real.exp_le_exp.mpr h)]
  · rw [min_eq_right h, min_eq_right (Real.exp_le_exp.mpr h)]

theorem envelope_le_exp_cell (c β a b t : ℝ) (hc : 0 ≤ c) (hβ : 0 ≤ β)
    (ha : 0 ≤ a) (hat : a ≤ t) (htb : t ≤ b) :
    envelope c β t ≤ Real.exp (cellExponent c β a b) := by
  have h0 := exponent_le_endpoint_max c (1 / 2) (1 / 10) β a b t hc (by norm_num) hβ ha hat htb
  have h1 := exponent_le_endpoint_max c ClassicalCosineCubic.a ClassicalCosineCubic.b β a b t
    hc ClassicalCosineCubic.b_nonneg hβ ha hat htb
  have h2 := exponent_le_endpoint_max c ClassicalRationalCosine.a ClassicalRationalCosine.b β a b t
    hc ClassicalRationalCosine.b_nonneg hβ ha hat htb
  unfold envelope cellExponent
  simp only [exp_min, Real.exp_zero]
  exact min_le_min le_rfl (min_le_min (Real.exp_le_exp.mpr h0)
    (min_le_min (Real.exp_le_exp.mpr h1) (Real.exp_le_exp.mpr h2)))

theorem lossEnvelope_le_exp_cell (N : ℕ) (hN : 0 < N) (c β a b t α : ℝ)
    (hc : 0 ≤ c) (hβ : 0 ≤ β) (ha : 0 ≤ a) (hat : a ≤ t) (htb : t ≤ b)
    (hα : α ≤ 1 - HighMomentRayDamping.loss N β) :
    lossEnvelope N c β t ≤ Real.exp (α * cellExponent c β a b) := by
  have he : 0 ≤ 1 - HighMomentRayDamping.loss N β :=
    sub_nonneg.mpr (HighMomentRayDamping.loss_le_one N hN β)
  have h0 := mul_le_mul_of_nonneg_left
    (exponent_le_endpoint_max c (1 / 2) (1 / 10) β a b t hc (by norm_num) hβ ha hat htb) he
  have h1 := mul_le_mul_of_nonneg_left
    (exponent_le_endpoint_max c ClassicalCosineCubic.a ClassicalCosineCubic.b β a b t
      hc ClassicalCosineCubic.b_nonneg hβ ha hat htb) he
  have h2 := mul_le_mul_of_nonneg_left
    (exponent_le_endpoint_max c ClassicalRationalCosine.a ClassicalRationalCosine.b β a b t
      hc ClassicalRationalCosine.b_nonneg hβ ha hat htb) he
  have hraw : lossEnvelope N c β t ≤
      Real.exp ((1 - HighMomentRayDamping.loss N β) * cellExponent c β a b) := by
    unfold lossEnvelope cellExponent
    rw [mul_min_of_nonneg _ _ he, mul_zero,
      mul_min_of_nonneg _ _ he, mul_min_of_nonneg _ _ he]
    simp only [exp_min, Real.exp_zero]
    exact min_le_min le_rfl (min_le_min (Real.exp_le_exp.mpr h0)
      (min_le_min (Real.exp_le_exp.mpr h1) (Real.exp_le_exp.mpr h2)))
  apply hraw.trans
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right hα (cellExponent_nonpos c β a b))

/-- A rounded cell exponent may replace the exact endpoint expression.
This is the nonnegative power used in the second Prawitz integral. -/
theorem envelope_le_of_cell_upper (c β a b t M : ℝ) (hc : 0 ≤ c) (hβ : 0 ≤ β)
    (ha : 0 ≤ a) (hat : a ≤ t) (htb : t ≤ b)
    (hM : cellExponent c β a b ≤ M) : envelope c β t ≤ Real.exp M :=
  (envelope_le_exp_cell c β a b t hc hβ ha hat htb).trans (Real.exp_le_exp.mpr hM)

/-- The actual forcing is controlled on the entire cell by rounded
exponent and lambda bounds. These are numeric gates, not sampled values. -/
theorem forcing_le_of_cell_upper (N : ℕ) (hN : 0 < N) (c β a b t α M L : ℝ)
    (hc : 0 ≤ c) (hβ : 0 ≤ β) (ha : 0 ≤ a) (hat : a ≤ t) (htb : t ≤ b)
    (hα0 : 0 ≤ α) (hα : α ≤ 1 - HighMomentRayDamping.loss N β)
    (hM : cellExponent c β a b ≤ M) (hL : CoarseHighMomentRayPrice.lambda N β ≤ L) :
    lossEnvelope N c β t * (t ^ 2 / 2 + CoarseHighMomentRayPrice.lambda N β * t ^ 3 / 3) ≤
      Real.exp (α * M) * (b ^ 2 / 2 + L * b ^ 3 / 3) := by
  have ht0 := ha.trans hat
  have hLam : 0 ≤ CoarseHighMomentRayPrice.lambda N β := by
    unfold CoarseHighMomentRayPrice.lambda
    positivity
  have hL0 := hLam.trans hL
  have henv := (lossEnvelope_le_exp_cell N hN c β a b t α hc hβ ha hat htb hα).trans
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hM hα0))
  have h2 := pow_le_pow_left₀ ht0 htb 2
  have h3 := pow_le_pow_left₀ ht0 htb 3
  have hm := mul_le_mul hL h3 (pow_nonneg ht0 3) hL0
  have hp : t ^ 2 / 2 + CoarseHighMomentRayPrice.lambda N β * t ^ 3 / 3 ≤
      b ^ 2 / 2 + L * b ^ 3 / 3 := by linarith only [h2, hm]
  exact mul_le_mul henv hp (by positivity) (Real.exp_nonneg _)

end BerryEsseen.CubicCellEnvelope

#print axioms BerryEsseen.CubicCellEnvelope.cubic_le_endpoint_max
#print axioms BerryEsseen.CubicCellEnvelope.envelope_le_exp_cell
#print axioms BerryEsseen.CubicCellEnvelope.lossEnvelope_le_exp_cell
#print axioms BerryEsseen.CubicCellEnvelope.forcing_le_of_cell_upper
