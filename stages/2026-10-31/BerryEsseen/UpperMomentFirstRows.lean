module

public import BerryEsseen.UpperMomentSpectralCells

@[expose] public section

/-! 2026-10-30: integral-row semantics for the absolute first comparison
integrand in pure spectral coordinates. Regular rows use the true global
R and closed-cell forcing, with an almost-everywhere kernel bound. The
first row is controlled by a continuous polynomial after the kernel's
1/v factor cancels. No kernel endpoint value is inferred from a limit. -/

noncomputable section

open MeasureTheory Set
open scoped Interval

namespace BerryEsseen.UpperMomentFirstRows

open UpperMomentSpectralCells (R forcing)
open UpperMomentSpectrumPrice (d)

abbrev kernel (V v : ℝ) : ℝ := RaySpectralCurvature.spectralKernelWeight V v

def firstIntegrand (U : ℝ) (G : ℝ → ℝ) (V s v : ℝ) : ℝ := kernel V v * R U G s v

lemma measurable_kernel (V : ℝ) : Measurable (kernel V) := by
  have heq : kernel V = RaySpectralCurvature.secondSpectralIntegrand V 0 := by
    funext v
    simp only [kernel, RaySpectralCurvature.secondSpectralIntegrand, RaySpectralCurvature.powerExp,
      Real.log_zero, mul_zero, zero_mul, sub_zero, Real.exp_zero, mul_one]
  rw [heq]
  exact RaySpectralCurvature.measurable_secondSpectralIntegrand V 0

lemma measurable_firstIntegrand (U : ℝ) (G : ℝ → ℝ) (hG : Continuous G) (V s : ℝ) :
    Measurable (firstIntegrand U G V s) :=
  (measurable_kernel V).mul (UpperMomentSpectralCells.continuous_R U G hG s).measurable

lemma firstIntegrand_nonneg (U : ℝ) (G : ℝ → ℝ) (V s v : ℝ)
    (hU : 0 < U) (hs : 0 ≤ s) (hv : 0 ≤ v) : 0 ≤ firstIntegrand U G V s v :=
  mul_nonneg (norm_nonneg _) (UpperMomentSpectralCells.R_nonneg U G s v hU hs hv)

lemma kernel_le_ae_of_Ioo (V a b K : ℝ) (hK : ∀ v ∈ Ioo a b, kernel V v ≤ K) :
    ∀ᵐ v ∂volume.restrict (Icc a b), kernel V v ≤ K := by
  filter_upwards [ae_restrict_mem measurableSet_Icc,
    ae_restrict_of_ae (volume.ae_ne a), ae_restrict_of_ae (volume.ae_ne b)] with v hv hva hvb
  exact hK v ⟨lt_of_le_of_ne hv.1 (Ne.symm hva), lt_of_le_of_ne hv.2 hvb⟩

/-- The kernel bound is only almost everywhere on the closed cell, so
the totalized endpoint values impose no extra numerical obligations. -/
theorem cell_integrand_le_ae (U : ℝ) (G : ℝ → ℝ) (hG : Continuous G)
    (V s a b H Ra K : ℝ) (hU : 0 < U) (hs : 0 < s) (ha : 0 ≤ a) (hab : a ≤ b)
    (hH : ∀ w ∈ Icc a b, forcing U G s w ≤ H) (hRa0 : 0 ≤ Ra) (hRa : R U G s a ≤ Ra)
    (hK0 : 0 ≤ K) (hK : ∀ᵐ v ∂volume.restrict (Icc a b), kernel V v ≤ K) :
    ∀ᵐ v ∂volume.restrict (Icc a b), firstIntegrand U G V s v ≤ K * (Ra + (b - a) * H) := by
  have hH0 := UpperMomentSpectralCells.forcing_upper_nonneg U G s a b H hU hs.le ha hab hH
  filter_upwards [ae_restrict_mem measurableSet_Icc, hK] with v hv hk
  have hR := UpperMomentSpectralCells.R_cell_inner_of_le U G hG s a b H Ra
    hU hs ha hab hH hRa0 hRa v hv
  have hw := mul_le_mul_of_nonneg_right (sub_le_sub_right hv.2 a) hH0
  have hR' : R U G s v ≤ Ra + (b - a) * H := by linarith only [hR, hw]
  exact mul_le_mul hk hR' (UpperMomentSpectralCells.R_nonneg U G s v hU hs.le (ha.trans hv.1)) hK0

/-- The very same row bound proves genuine integrability. No default-zero
branch of the real integral is used in the subsequent row inequality. -/
theorem cell_intervalIntegrable (U : ℝ) (G : ℝ → ℝ) (hG : Continuous G)
    (V s a b H Ra K : ℝ) (hU : 0 < U) (hs : 0 < s) (ha : 0 ≤ a) (hab : a ≤ b)
    (hH : ∀ w ∈ Icc a b, forcing U G s w ≤ H) (hRa0 : 0 ≤ Ra) (hRa : R U G s a ≤ Ra)
    (hK0 : 0 ≤ K) (hK : ∀ᵐ v ∂volume.restrict (Icc a b), kernel V v ≤ K) :
    IntervalIntegrable (firstIntegrand U G V s) volume a b := by
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
  have hc : Continuous (fun _ : ℝ => K * (Ra + (b - a) * H)) := continuous_const
  apply hc.integrableOn_Icc.mono' (measurable_firstIntegrand U G hG V s).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Icc,
    cell_integrand_le_ae U G hG V s a b H Ra K hU hs ha hab hH hRa0 hRa hK0 hK] with v hv hh
  simpa only [Real.norm_eq_abs,
    abs_of_nonneg (firstIntegrand_nonneg U G V s v hU hs.le (ha.trans hv.1))] using hh

/-- Reusable real row license for any later exact integer upper-row gate. -/
theorem cell_integral_le (U : ℝ) (G : ℝ → ℝ) (hG : Continuous G)
    (V s a b H Ra K : ℝ) (hU : 0 < U) (hs : 0 < s) (ha : 0 ≤ a) (hab : a ≤ b)
    (hH : ∀ w ∈ Icc a b, forcing U G s w ≤ H) (hRa0 : 0 ≤ Ra) (hRa : R U G s a ≤ Ra)
    (hK0 : 0 ≤ K) (hK : ∀ᵐ v ∂volume.restrict (Icc a b), kernel V v ≤ K) :
    (∫ v in a..b, firstIntegrand U G V s v) ≤ (b - a) * K * (Ra + (b - a) * H) := by
  have hi := intervalIntegral.integral_mono_ae_restrict hab
    (cell_intervalIntegrable U G hG V s a b H Ra K hU hs ha hab hH hRa0 hRa hK0 hK)
    (intervalIntegrable_const (c := K * (Ra + (b - a) * H)) (a := a) (b := b) (μ := volume))
    (cell_integrand_le_ae U G hG V s a b H Ra K hU hs ha hab hH hRa0 hRa hK0 hK)
  simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_assoc] using hi

theorem cell_integral_le_row (U : ℝ) (G : ℝ → ℝ) (hG : Continuous G)
    (V s a b H Ra K row : ℝ) (hU : 0 < U) (hs : 0 < s) (ha : 0 ≤ a) (hab : a ≤ b)
    (hH : ∀ w ∈ Icc a b, forcing U G s w ≤ H) (hRa0 : 0 ≤ Ra) (hRa : R U G s a ≤ Ra)
    (hK0 : 0 ≤ K) (hK : ∀ᵐ v ∂volume.restrict (Icc a b), kernel V v ≤ K)
    (hrow : (b - a) * K * (Ra + (b - a) * H) ≤ row) :
    (∫ v in a..b, firstIntegrand U G V s v) ≤ row :=
  (cell_integral_le U G hG V s a b H Ra K hU hs ha hab hH hRa0 hRa hK0 hK).trans hrow

def firstMajorant (U V s v : ℝ) : ℝ :=
  s * ((V / (12 * Real.pi)) * v ^ 2 +
    (1 / 12 + V * d U / (24 * Real.pi)) * v ^ 3 + (d U / 24) * v ^ 4)

lemma continuous_firstMajorant (U V s : ℝ) : Continuous (firstMajorant U V s) := by
  unfold firstMajorant
  fun_prop

/-- This bound is required only at positive v. Cancellation makes its
polynomial majorant continuous at zero, independently of kernel totalization. -/
theorem firstIntegrand_le_majorant (U : ℝ) (G : ℝ → ℝ) (hG : Continuous G)
    (hG0 : ∀ w, G w ≤ 0) (V s v : ℝ) (hU : 0 < U) (hV : 0 < V)
    (hds : d U ≤ s) (hv : 0 < v) (hvV : v ≤ V) :
    firstIntegrand U G V s v ≤ firstMajorant U V s v := by
  have hs : 0 ≤ s := (by unfold d; positivity : 0 ≤ d U).trans hds
  have hk := RaySpectralCurvature.spectralKernelWeight_le V v hV hv hvV
  have hr := UpperMomentSpectralCells.R_le_first_polynomial U G hG hG0 s v hU hds hv.le
  have hr0 := UpperMomentSpectralCells.R_nonneg U G s v hU hs hv.le
  have hk0 : 0 ≤ V / (2 * Real.pi) / v + 1 / 2 := by positivity
  apply (mul_le_mul hk hr hr0 hk0).trans_eq
  unfold firstMajorant
  field_simp [hv.ne', Real.pi_ne_zero]
  ring

/-- Genuine integrability across the first endpoint follows from the
continuous polynomial bound on Ioc, where every frequency is positive. -/
theorem first_intervalIntegrable (U : ℝ) (G : ℝ → ℝ) (hG : Continuous G)
    (hG0 : ∀ w, G w ≤ 0) (V s A : ℝ) (hU : 0 < U) (hV : 0 < V)
    (hds : d U ≤ s) (hA : 0 ≤ A) (hAV : A ≤ V) :
    IntervalIntegrable (firstIntegrand U G V s) volume 0 A := by
  have hs : 0 ≤ s := (by unfold d; positivity : 0 ≤ d U).trans hds
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hA).mpr
  apply ((continuous_firstMajorant U V s).intervalIntegrable 0 A).1.mono'
    (measurable_firstIntegrand U G hG V s).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
  simpa only [Real.norm_eq_abs, abs_of_nonneg (firstIntegrand_nonneg U G V s v hU hs hv.1.le)] using
    firstIntegrand_le_majorant U G hG hG0 V s v hU hV hds hv.1 (hv.2.trans hAV)

theorem firstMajorant_integral (U V s h : ℝ) :
    (∫ v in (0 : ℝ)..h, firstMajorant U V s v) =
      s * (h ^ 4 / 48 + d U * h ^ 5 / 120 + V * h ^ 3 / (36 * Real.pi) +
        V * d U * h ^ 4 / (96 * Real.pi)) := by
  have h2 : IntervalIntegrable (fun v : ℝ => (V / (12 * Real.pi)) * v ^ 2) volume 0 h :=
    (by fun_prop : Continuous (fun v : ℝ => (V / (12 * Real.pi)) * v ^ 2)).intervalIntegrable 0 h
  have h3 : IntervalIntegrable (fun v : ℝ =>
      (1 / 12 + V * d U / (24 * Real.pi)) * v ^ 3) volume 0 h :=
    (by fun_prop : Continuous (fun v : ℝ =>
      (1 / 12 + V * d U / (24 * Real.pi)) * v ^ 3)).intervalIntegrable 0 h
  have h4 : IntervalIntegrable (fun v : ℝ => (d U / 24) * v ^ 4) volume 0 h :=
    (by fun_prop : Continuous (fun v : ℝ => (d U / 24) * v ^ 4)).intervalIntegrable 0 h
  unfold firstMajorant
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add (h2.add h3) h4,
    intervalIntegral.integral_add h2 h3]
  congr 1
  simp only [intervalIntegral.integral_const_mul, integral_pow]
  norm_num
  ring

/-- The complete analytic first row for the absolute integrand k(v)R(v).
For h<=A<=V the sole band premise here is obtained by transitivity. -/
theorem first_cell_integral_le (U : ℝ) (G : ℝ → ℝ) (hG : Continuous G)
    (hG0 : ∀ w, G w ≤ 0) (V s h : ℝ) (hU : 0 < U) (hV : 0 < V)
    (hds : d U ≤ s) (hh : 0 ≤ h) (hhV : h ≤ V) :
    (∫ v in (0 : ℝ)..h, firstIntegrand U G V s v) ≤
      s * (h ^ 4 / 48 + d U * h ^ 5 / 120 + V * h ^ 3 / (36 * Real.pi) +
        V * d U * h ^ 4 / (96 * Real.pi)) := by
  have hi := intervalIntegral.integral_mono_on_of_le_Ioo hh
    (first_intervalIntegrable U G hG hG0 V s h hU hV hds hh hhV)
    ((continuous_firstMajorant U V s).intervalIntegrable 0 h)
    (fun v hv => firstIntegrand_le_majorant U G hG hG0 V s v hU hV hds hv.1 (hv.2.le.trans hhV))
  exact hi.trans_eq (firstMajorant_integral U V s h)

end BerryEsseen.UpperMomentFirstRows

#print axioms BerryEsseen.UpperMomentFirstRows.cell_intervalIntegrable
#print axioms BerryEsseen.UpperMomentFirstRows.cell_integral_le
#print axioms BerryEsseen.UpperMomentFirstRows.cell_integral_le_row
#print axioms BerryEsseen.UpperMomentFirstRows.firstIntegrand_le_majorant
#print axioms BerryEsseen.UpperMomentFirstRows.first_intervalIntegrable
#print axioms BerryEsseen.UpperMomentFirstRows.firstMajorant_integral
#print axioms BerryEsseen.UpperMomentFirstRows.first_cell_integral_le
