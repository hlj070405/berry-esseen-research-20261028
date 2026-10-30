module

public import BerryEsseen.IidSmoothingPrice

@[expose] public section

/-! 2026-10-29: local restart identities and cell bounds for the same
actual normalized iid characteristic-function error. The proof restarts
the existing complex integrating-factor function on each cell. It never
differentiates a norm or restarts a global integral price. A modulus q is
used only where it is explicitly licensed by the original law's CF. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Interval Topology

namespace BerryEsseen.IidErrorCells

open IidSmoothingPrice SquareBiasFourier

def actualError (μ : ProbabilityMeasure ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  charFun (μ : Measure ℝ) (t / Real.sqrt n) ^ n - (Real.exp (-(t ^ 2 / 2)) : ℂ)

def radius (μ : ProbabilityMeasure ℝ) (n : ℕ) (t : ℝ) : ℝ := ‖actualError μ n t‖

def normalizedResidual (μ : ProbabilityMeasure ℝ) (n : ℕ) (u : ℝ) : ℂ :=
  (Real.sqrt n : ℂ) * charFun (μ : Measure ℝ) (u / Real.sqrt n) ^ (n - 1) *
    firstResidual μ (u / Real.sqrt n)

def cellResidual (μ : ProbabilityMeasure ℝ) (n : ℕ) (b u : ℝ) : ℂ :=
  (Real.exp (-((b ^ 2 - u ^ 2) / 2)) : ℂ) * normalizedResidual μ n u

lemma radius_nonneg (μ : ProbabilityMeasure ℝ) (n : ℕ) (t : ℝ) : 0 ≤ radius μ n t :=
  norm_nonneg _

private lemma normalized_square (n : ℕ) (hn : 0 < n) (t : ℝ) :
    (n : ℝ) * ((t / Real.sqrt n) ^ 2 / 2) = t ^ 2 / 2 := by
  rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  field_simp [(Nat.cast_pos.mpr hn : (0 : ℝ) < n).ne']

private lemma scaledFactor_normalized (n : ℕ) (hn : 0 < n) (t : ℝ) :
    scaledFactor n (t / Real.sqrt n) = (Real.exp (t ^ 2 / 2) : ℂ) := by
  unfold scaledFactor
  rw [normalized_square n hn t]

private lemma scaledGaussian_normalized (n : ℕ) (hn : 0 < n) (t : ℝ) :
    scaledGaussian n (t / Real.sqrt n) = (Real.exp (-(t ^ 2 / 2)) : ℂ) := by
  unfold scaledGaussian
  rw [normalized_square n hn t]

/-- The old integrating factor is restarted on an arbitrary raw cell.
The left endpoint is its actual complex CF discrepancy. -/
theorem raw_restart_identity (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (hn : 0 < n) (a b : ℝ) :
    charFun (μ : Measure ℝ) b ^ n - scaledGaussian n b =
      (scaledGaussian n b * scaledFactor n a) *
        (charFun (μ : Measure ℝ) a ^ n - scaledGaussian n a) +
      scaledGaussian n b * ∫ u in a..b, residual μ n u := by
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => hasDerivAt_transformed μ h n hn u)
    ((continuous_residual μ h n).intervalIntegrable a b)
  rw [hFTC]
  unfold transformed
  have ha := scaledGaussian_mul_factor n a
  have hb := scaledGaussian_mul_factor n b
  calc
    _ = scaledGaussian n b * (scaledFactor n b * charFun (μ : Measure ℝ) b ^ n) -
        scaledGaussian n b * (scaledGaussian n a * scaledFactor n a) := by
      rw [ha, mul_one, ← mul_assoc, hb, one_mul]
    _ = _ := by ring

private lemma scaled_residual_eq (μ : ProbabilityMeasure ℝ) (n : ℕ) (hn : 0 < n) (u : ℝ) :
    (Real.sqrt (n : ℝ))⁻¹ • residual μ n (u / Real.sqrt n) =
      (Real.exp (u ^ 2 / 2) : ℂ) * normalizedResidual μ n u := by
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  have hsc : (Real.sqrt (n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hs2 : (Real.sqrt (n : ℝ) : ℂ) ^ 2 = (n : ℂ) := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg n)
  rw [Complex.real_smul]
  unfold IidSmoothingPrice.residual normalizedResidual scaledFactor
  rw [normalized_square n hn u]
  push_cast
  rw [← hs2]
  field_simp [hsc]

/-- Exact normalized-frequency restart, including the true Jacobian and
the same-law first residual. There is no norm differentiability assumption. -/
theorem normalized_restart_identity (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (hn : 0 < n) (a b : ℝ) :
    actualError μ n b = (Real.exp (-((b ^ 2 - a ^ 2) / 2)) : ℂ) * actualError μ n a +
      ∫ u in a..b, cellResidual μ n b u := by
  have hsub := intervalIntegral.inv_smul_integral_comp_div
    (a := a) (b := b) (residual μ n) (Real.sqrt (n : ℝ))
  have hI : (∫ u in a / Real.sqrt n..b / Real.sqrt n, residual μ n u) =
      ∫ u in a..b, (Real.exp (u ^ 2 / 2) : ℂ) * normalizedResidual μ n u := by
    rw [← hsub, ← intervalIntegral.integral_smul]
    apply intervalIntegral.integral_congr
    intro u _
    exact scaled_residual_eq μ n hn u
  have hraw := raw_restart_identity μ h n hn (a / Real.sqrt n) (b / Real.sqrt n)
  rw [scaledGaussian_normalized n hn b, scaledGaussian_normalized n hn a,
    scaledFactor_normalized n hn a, hI] at hraw
  change actualError μ n b =
    ((Real.exp (-(b ^ 2 / 2)) : ℂ) * (Real.exp (a ^ 2 / 2) : ℂ)) * actualError μ n a +
      (Real.exp (-(b ^ 2 / 2)) : ℂ) *
        ∫ u in a..b, (Real.exp (u ^ 2 / 2) : ℂ) * normalizedResidual μ n u at hraw
  have hd : (Real.exp (-(b ^ 2 / 2)) : ℂ) * (Real.exp (a ^ 2 / 2) : ℂ) =
      (Real.exp (-((b ^ 2 - a ^ 2) / 2)) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 1
    congr 1
    ring
  rw [hd] at hraw
  apply hraw.trans
  congr 1
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro u _
  dsimp only
  unfold cellResidual
  rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
  congr 1
  congr 1
  congr 1
  ring

/-- The residual forcing is bounded using only an explicitly licensed
pointwise modulus of this original law's CF. q need not be continuous. -/
theorem norm_normalizedResidual_le (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (hn : 0 < n) (q : ℝ → ℝ) (u : ℝ) (hu : 0 ≤ u)
    (hq : ‖charFun (μ : Measure ℝ) (u / Real.sqrt n)‖ ≤ q (u / Real.sqrt n)) :
    ‖normalizedResidual μ n u‖ ≤ Real.sqrt n * q (u / Real.sqrt n) ^ (n - 1) *
      sinePrimitive μ (u / Real.sqrt n) := by
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  have hpow := pow_le_pow_left₀ (norm_nonneg _) hq (n - 1)
  have hr := norm_firstResidual_le_sinePrimitive μ h (u / Real.sqrt n) (div_nonneg hu hs.le)
  unfold normalizedResidual
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs, norm_pow]
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left hpow hs.le
  · exact hr
  · exact norm_nonneg _
  · exact mul_nonneg hs.le (pow_nonneg ((norm_nonneg _).trans hq) _)

lemma forcing_upper_nonneg (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (hn : 0 < n) (q : ℝ → ℝ) (a b H : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hq : ∀ t ∈ Icc a b, ‖charFun (μ : Measure ℝ) (t / Real.sqrt n)‖ ≤ q (t / Real.sqrt n))
    (hH : ∀ t ∈ Icc a b, Real.sqrt n * q (t / Real.sqrt n) ^ (n - 1) *
      sinePrimitive μ (t / Real.sqrt n) ≤ H) : 0 ≤ H :=
  (norm_nonneg (normalizedResidual μ n a)).trans
    ((norm_normalizedResidual_le μ h n hn q a ha (hq a ⟨le_rfl, hab⟩)).trans
      (hH a ⟨le_rfl, hab⟩))

lemma norm_cellResidual_le (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (hn : 0 < n) (q : ℝ → ℝ) (a b H : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hq : ∀ t ∈ Icc a b, ‖charFun (μ : Measure ℝ) (t / Real.sqrt n)‖ ≤ q (t / Real.sqrt n))
    (hH : ∀ t ∈ Icc a b, Real.sqrt n * q (t / Real.sqrt n) ^ (n - 1) *
      sinePrimitive μ (t / Real.sqrt n) ≤ H)
    (u : ℝ) (hu : u ∈ Icc a b) : ‖cellResidual μ n b u‖ ≤ H := by
  have hH0 := forcing_upper_nonneg μ h n hn q a b H ha hab hq hH
  have hu0 : 0 ≤ u := ha.trans hu.1
  have hr := (norm_normalizedResidual_le μ h n hn q u hu0 (hq u hu)).trans (hH u hu)
  have hsq := pow_le_pow_left₀ hu0 hu.2 2
  have he : Real.exp (-((b ^ 2 - u ^ 2) / 2)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith only [hsq])
  unfold cellResidual
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp (-((b ^ 2 - u ^ 2) / 2)) * H :=
      mul_le_mul_of_nonneg_left hr (Real.exp_nonneg _)
    _ ≤ 1 * H := mul_le_mul_of_nonneg_right he hH0
    _ = H := one_mul H

/-- Local endpoint propagation for the actual normalized CF error.
The only envelope hypothesis is its stated same-law pointwise license. -/
theorem radius_cell_step (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (hn : 0 < n) (q : ℝ → ℝ) (a b H : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hq : ∀ t ∈ Icc a b, ‖charFun (μ : Measure ℝ) (t / Real.sqrt n)‖ ≤ q (t / Real.sqrt n))
    (hH : ∀ t ∈ Icc a b, Real.sqrt n * q (t / Real.sqrt n) ^ (n - 1) *
      sinePrimitive μ (t / Real.sqrt n) ≤ H) :
    radius μ n b ≤ Real.exp (-((b ^ 2 - a ^ 2) / 2)) * radius μ n a + (b - a) * H := by
  have hint : ‖∫ u in a..b, cellResidual μ n b u‖ ≤ (b - a) * H := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := cellResidual μ n b) (a := a) (b := b) (C := H) (fun u hu => by
        rw [uIoc_of_le hab] at hu
        exact norm_cellResidual_le μ h n hn q a b H ha hab hq hH u ⟨hu.1.le, hu.2⟩)
    rw [abs_of_nonneg (sub_nonneg.mpr hab)] at hh
    nlinarith only [hh]
  unfold radius
  rw [normalized_restart_identity μ h n hn a b]
  apply (norm_add_le _ _).trans
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  linarith only [hint]

theorem radius_cell_inner (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (hn : 0 < n) (q : ℝ → ℝ) (a b H : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hq : ∀ t ∈ Icc a b, ‖charFun (μ : Measure ℝ) (t / Real.sqrt n)‖ ≤ q (t / Real.sqrt n))
    (hH : ∀ t ∈ Icc a b, Real.sqrt n * q (t / Real.sqrt n) ^ (n - 1) *
      sinePrimitive μ (t / Real.sqrt n) ≤ H)
    (t : ℝ) (ht : t ∈ Icc a b) : radius μ n t ≤ radius μ n a + (b - a) * H := by
  have hH0 := forcing_upper_nonneg μ h n hn q a b H ha hab hq hH
  have hs := radius_cell_step μ h n hn q a t H ha ht.1
    (fun u hu => hq u ⟨hu.1, hu.2.trans ht.2⟩)
    (fun u hu => hH u ⟨hu.1, hu.2.trans ht.2⟩)
  have hsq := pow_le_pow_left₀ ha ht.1 2
  have he : Real.exp (-((t ^ 2 - a ^ 2) / 2)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith only [hsq])
  have hd := mul_le_mul_of_nonneg_right he (radius_nonneg μ n a)
  have hw := mul_le_mul_of_nonneg_right (sub_le_sub_right ht.2 a) hH0
  nlinarith only [hs, hd, hw]

/-- Any proved upper bound on the same actual endpoint radius may be
restarted here, including the minimum of Taylor and triangle bounds. -/
theorem radius_cell_step_of_le (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (hn : 0 < n) (q : ℝ → ℝ) (a b H R : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hq : ∀ t ∈ Icc a b, ‖charFun (μ : Measure ℝ) (t / Real.sqrt n)‖ ≤ q (t / Real.sqrt n))
    (hH : ∀ t ∈ Icc a b, Real.sqrt n * q (t / Real.sqrt n) ^ (n - 1) *
      sinePrimitive μ (t / Real.sqrt n) ≤ H)
    (hR : radius μ n a ≤ R) :
    radius μ n b ≤ Real.exp (-((b ^ 2 - a ^ 2) / 2)) * R + (b - a) * H := by
  apply (radius_cell_step μ h n hn q a b H ha hab hq hH).trans
  have hh := mul_le_mul_of_nonneg_left hR (Real.exp_nonneg (-((b ^ 2 - a ^ 2) / 2)))
  linarith only [hh]

theorem radius_cell_inner_of_le (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (hn : 0 < n) (q : ℝ → ℝ) (a b H R : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hq : ∀ t ∈ Icc a b, ‖charFun (μ : Measure ℝ) (t / Real.sqrt n)‖ ≤ q (t / Real.sqrt n))
    (hH : ∀ t ∈ Icc a b, Real.sqrt n * q (t / Real.sqrt n) ^ (n - 1) *
      sinePrimitive μ (t / Real.sqrt n) ≤ H)
    (hR : radius μ n a ≤ R) (t : ℝ) (ht : t ∈ Icc a b) :
    radius μ n t ≤ R + (b - a) * H := by
  have hh := radius_cell_inner μ h n hn q a b H ha hab hq hH t ht
  linarith only [hh, hR]

end BerryEsseen.IidErrorCells

#print axioms BerryEsseen.IidErrorCells.raw_restart_identity
#print axioms BerryEsseen.IidErrorCells.normalized_restart_identity
#print axioms BerryEsseen.IidErrorCells.radius_cell_step
#print axioms BerryEsseen.IidErrorCells.radius_cell_inner
#print axioms BerryEsseen.IidErrorCells.radius_cell_step_of_le
#print axioms BerryEsseen.IidErrorCells.radius_cell_inner_of_le
