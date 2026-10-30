module

public import BerryEsseen.UpperMomentSpectrumPrice

@[expose] public section

/-! 2026-10-30: exact spectral-coordinate cell semantics of the global
upper-moment comparison price. R is the defining comparison integral,
not the actual CF error. Its forcing and Gaussian transport give the
closed-cell recurrence without square-root coordinate conversions. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped Interval

namespace BerryEsseen.UpperMomentSpectralCells

open UpperMomentSpectrumPrice (d W)

def integrand (U : ℝ) (G : ℝ → ℝ) (s w : ℝ) : ℝ :=
  Real.exp (s * w ^ 2 / 2 + (s - d U) * G w) * W U w

def R (U : ℝ) (G : ℝ → ℝ) (s v : ℝ) : ℝ :=
  s * Real.exp (-s * v ^ 2 / 2) * ∫ w in (0 : ℝ)..v, integrand U G s w

def forcing (U : ℝ) (G : ℝ → ℝ) (s w : ℝ) : ℝ :=
  s * Real.exp ((s - d U) * G w) * W U w

def cellIntegrand (U : ℝ) (G : ℝ → ℝ) (s v w : ℝ) : ℝ :=
  Real.exp (-s * (v ^ 2 - w ^ 2) / 2) * forcing U G s w

lemma continuous_integrand (U : ℝ) (G : ℝ → ℝ) (hG : Continuous G) (s : ℝ) :
    Continuous (integrand U G s) := by
  exact (by fun_prop : Continuous (fun w => Real.exp (s * w ^ 2 / 2 + (s - d U) * G w))).mul
    (UpperMomentSpectrumPrice.continuous_W U)

lemma continuous_forcing (U : ℝ) (G : ℝ → ℝ) (hG : Continuous G) (s : ℝ) :
    Continuous (forcing U G s) := by
  exact (by fun_prop : Continuous (fun w => s * Real.exp ((s - d U) * G w))).mul
    (UpperMomentSpectrumPrice.continuous_W U)

lemma continuous_cellIntegrand (U : ℝ) (G : ℝ → ℝ) (hG : Continuous G) (s v : ℝ) :
    Continuous (cellIntegrand U G s v) :=
  (by fun_prop : Continuous (fun w => Real.exp (-s * (v ^ 2 - w ^ 2) / 2))).mul
    (continuous_forcing U G hG s)

theorem continuous_R (U : ℝ) (G : ℝ → ℝ) (hG : Continuous G) (s : ℝ) :
    Continuous (R U G s) :=
  (by fun_prop : Continuous (fun v => s * Real.exp (-s * v ^ 2 / 2))).mul
    (intervalIntegral.continuous_primitive
      (fun a b => (continuous_integrand U G hG s).intervalIntegrable a b) 0)

@[simp] theorem R_zero (U : ℝ) (G : ℝ → ℝ) (s : ℝ) : R U G s 0 = 0 := by simp [R]

lemma forcing_nonneg (U : ℝ) (G : ℝ → ℝ) (s w : ℝ)
    (hU : 0 < U) (hs : 0 ≤ s) (hw : 0 ≤ w) : 0 ≤ forcing U G s w := by
  exact mul_nonneg (mul_nonneg hs (Real.exp_nonneg _))
    (UpperMomentSpectrumPrice.W_nonneg U w hU hw)

theorem R_nonneg (U : ℝ) (G : ℝ → ℝ) (s v : ℝ)
    (hU : 0 < U) (hs : 0 ≤ s) (hv : 0 ≤ v) : 0 ≤ R U G s v := by
  apply mul_nonneg (mul_nonneg hs (Real.exp_nonneg _))
  apply intervalIntegral.integral_nonneg hv
  intro w hw
  exact mul_nonneg (Real.exp_nonneg _) (UpperMomentSpectrumPrice.W_nonneg U w hU hw.1)

lemma cellIntegrand_eq (U : ℝ) (G : ℝ → ℝ) (s v w : ℝ) :
    cellIntegrand U G s v w =
      s * Real.exp (-s * (v ^ 2 - w ^ 2) / 2 + (s - d U) * G w) * W U w := by
  unfold cellIntegrand forcing
  rw [Real.exp_add]
  ring

/-- The same comparison integral, with transport and true forcing explicit. -/
theorem R_eq_integral (U : ℝ) (G : ℝ → ℝ) (s v : ℝ) :
    R U G s v = ∫ w in (0 : ℝ)..v, cellIntegrand U G s v w := by
  unfold R
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro w _
  rw [cellIntegrand_eq]
  unfold integrand
  rw [show -s * (v ^ 2 - w ^ 2) / 2 + (s - d U) * G w =
    -s * v ^ 2 / 2 + (s * w ^ 2 / 2 + (s - d U) * G w) by ring, Real.exp_add]
  ring

/-- The spectral slice is sqrt(s) times the absolute comparison R. -/
theorem firstSlice_eq_sqrt_mul_R (U : ℝ) (G : ℝ → ℝ) (s v : ℝ) (hs : 0 < s) :
    UpperMomentSpectrumPrice.firstSlice U G s v = Real.sqrt s * R U G s v := by
  have hp : s ^ (3 / 2 : ℝ) = Real.sqrt s * s := by
    rw [show (3 / 2 : ℝ) = (1 / 2 : ℝ) + 1 by norm_num,
      Real.rpow_add_one hs.ne', ← Real.sqrt_eq_rpow]
  rw [R_eq_integral, ← intervalIntegral.integral_const_mul]
  unfold UpperMomentSpectrumPrice.firstSlice
  apply intervalIntegral.integral_congr
  intro w _
  dsimp only
  rw [UpperMomentSpectrumPrice.core, hp, cellIntegrand_eq]
  ring

/-- This identifies R with the existing global comparison price. -/
theorem R_eq_beta_mul_physicalPrice (U β : ℝ) (G : ℝ → ℝ) (v : ℝ) (hβ : 0 < β) :
    R U G (1 / β ^ 2) v = β * UpperMomentSpectrumPrice.physicalPrice U β G (v / β) := by
  have hs : (0 : ℝ) < 1 / β ^ 2 := by positivity
  have hroot : Real.sqrt (1 / β ^ 2) = 1 / β := by
    rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one,
      Real.sqrt_sq_eq_abs, abs_of_pos hβ]
  rw [UpperMomentSpectrumPrice.physicalPrice_spectral_eq U β G v hβ,
    firstSlice_eq_sqrt_mul_R U G _ v hs, hroot]
  field_simp [hβ.ne']

/-- Exact adjacent-interval split, with no frequency ordering needed. -/
theorem R_split_integrand (U : ℝ) (G : ℝ → ℝ) (hG : Continuous G) (s a b : ℝ) :
    R U G s b = Real.exp (-s * (b ^ 2 - a ^ 2) / 2) * R U G s a +
      s * Real.exp (-s * b ^ 2 / 2) * ∫ w in a..b, integrand U G s w := by
  have hi := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    ((continuous_integrand U G hG s).intervalIntegrable 0 a)
    ((continuous_integrand U G hG s).intervalIntegrable a b)
  have he : Real.exp (-s * (b ^ 2 - a ^ 2) / 2) * Real.exp (-s * a ^ 2 / 2) =
      Real.exp (-s * b ^ 2 / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold R
  rw [← hi, mul_add]
  congr 1
  symm
  calc
    _ = s * (Real.exp (-s * (b ^ 2 - a ^ 2) / 2) * Real.exp (-s * a ^ 2 / 2)) *
        ∫ w in (0 : ℝ)..a, integrand U G s w := by ring
    _ = _ := by rw [he]

theorem R_split (U : ℝ) (G : ℝ → ℝ) (hG : Continuous G) (s a b : ℝ) :
    R U G s b = Real.exp (-s * (b ^ 2 - a ^ 2) / 2) * R U G s a +
      ∫ w in a..b, cellIntegrand U G s b w := by
  rw [R_split_integrand U G hG s a b]
  congr 1
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro w _
  rw [cellIntegrand_eq]
  unfold integrand
  rw [show -s * (b ^ 2 - w ^ 2) / 2 + (s - d U) * G w =
    -s * b ^ 2 / 2 + (s * w ^ 2 / 2 + (s - d U) * G w) by ring, Real.exp_add]
  ring

lemma forcing_upper_nonneg (U : ℝ) (G : ℝ → ℝ) (s a b H : ℝ)
    (hU : 0 < U) (hs : 0 ≤ s) (ha : 0 ≤ a) (hab : a ≤ b)
    (hH : ∀ w ∈ Icc a b, forcing U G s w ≤ H) : 0 ≤ H :=
  (forcing_nonneg U G s a hU hs ha).trans (hH a ⟨le_rfl, hab⟩)

/-- A closed-cell forcing bound propagates the defining global price. -/
theorem R_cell_step (U : ℝ) (G : ℝ → ℝ) (hG : Continuous G) (s a b H : ℝ)
    (hU : 0 < U) (hs : 0 < s) (ha : 0 ≤ a) (hab : a ≤ b)
    (hH : ∀ w ∈ Icc a b, forcing U G s w ≤ H) :
    R U G s b ≤ Real.exp (-s * (b ^ 2 - a ^ 2) / 2) * R U G s a + (b - a) * H := by
  have hH0 := forcing_upper_nonneg U G s a b H hU hs.le ha hab hH
  have hi := intervalIntegral.integral_mono_on (μ := volume) hab
    ((continuous_cellIntegrand U G hG s b).intervalIntegrable a b)
    (intervalIntegrable_const (c := H) (a := a) (b := b) (μ := volume))
    (fun w hw => by
      have hsq := pow_le_pow_left₀ (ha.trans hw.1) hw.2 2
      have he : Real.exp (-s * (b ^ 2 - w ^ 2) / 2) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith only [mul_nonneg hs.le (sub_nonneg.mpr hsq)])
      calc
        _ ≤ Real.exp (-s * (b ^ 2 - w ^ 2) / 2) * H :=
          mul_le_mul_of_nonneg_left (hH w hw) (Real.exp_nonneg _)
        _ ≤ 1 * H := mul_le_mul_of_nonneg_right he hH0
        _ = H := one_mul H)
  rw [intervalIntegral.integral_const, smul_eq_mul] at hi
  rw [R_split U G hG s a b]
  linarith only [hi]

/-- The interior uses its actual prefix width v-a, including both endpoints. -/
theorem R_cell_inner (U : ℝ) (G : ℝ → ℝ) (hG : Continuous G) (s a b H : ℝ)
    (hU : 0 < U) (hs : 0 < s) (ha : 0 ≤ a) (_hab : a ≤ b)
    (hH : ∀ w ∈ Icc a b, forcing U G s w ≤ H) (v : ℝ) (hv : v ∈ Icc a b) :
    R U G s v ≤ R U G s a + (v - a) * H := by
  have hstep := R_cell_step U G hG s a v H hU hs ha hv.1
    (fun w hw => hH w ⟨hw.1, hw.2.trans hv.2⟩)
  have hsq := pow_le_pow_left₀ ha hv.1 2
  have he : Real.exp (-s * (v ^ 2 - a ^ 2) / 2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith only [mul_nonneg hs.le (sub_nonneg.mpr hsq)])
  have hd := mul_le_mul_of_nonneg_right he (R_nonneg U G s a hU hs.le ha)
  nlinarith only [hstep, hd]

theorem R_cell_step_of_le (U : ℝ) (G : ℝ → ℝ) (hG : Continuous G) (s a b H Ra : ℝ)
    (hU : 0 < U) (hs : 0 < s) (ha : 0 ≤ a) (hab : a ≤ b)
    (hH : ∀ w ∈ Icc a b, forcing U G s w ≤ H) (_hRa0 : 0 ≤ Ra) (hRa : R U G s a ≤ Ra) :
    R U G s b ≤ Real.exp (-s * (b ^ 2 - a ^ 2) / 2) * Ra + (b - a) * H := by
  apply (R_cell_step U G hG s a b H hU hs ha hab hH).trans
  exact add_le_add (mul_le_mul_of_nonneg_left hRa (Real.exp_nonneg _)) le_rfl

theorem R_cell_inner_of_le (U : ℝ) (G : ℝ → ℝ) (hG : Continuous G) (s a b H Ra : ℝ)
    (hU : 0 < U) (hs : 0 < s) (ha : 0 ≤ a) (_hab : a ≤ b)
    (hH : ∀ w ∈ Icc a b, forcing U G s w ≤ H) (hRa0 : 0 ≤ Ra) (hRa : R U G s a ≤ Ra)
    (v : ℝ) (hv : v ∈ Icc a b) : R U G s v ≤ Ra + (v - a) * H := by
  have hstep := R_cell_step_of_le U G hG s a v H Ra hU hs ha hv.1
    (fun w hw => hH w ⟨hw.1, hw.2.trans hv.2⟩) hRa0 hRa
  have hsq := pow_le_pow_left₀ ha hv.1 2
  have he : Real.exp (-s * (v ^ 2 - a ^ 2) / 2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith only [mul_nonneg hs.le (sub_nonneg.mpr hsq)])
  have hd := mul_le_mul_of_nonneg_right he hRa0
  nlinarith only [hstep, hd]

/-- The true integral gives the analytic first-cell bound. -/
theorem R_le_first_polynomial (U : ℝ) (G : ℝ → ℝ) (hG : Continuous G)
    (hG0 : ∀ w, G w ≤ 0) (s v : ℝ) (hU : 0 < U) (hds : d U ≤ s) (hv : 0 ≤ v) :
    R U G s v ≤ s * (v ^ 3 / 6 + d U * v ^ 4 / 12) := by
  have hs : 0 ≤ s := (by unfold d; positivity : 0 ≤ d U).trans hds
  have hp : Continuous (fun w : ℝ => (s / 2) * w ^ 2 + (s * d U / 3) * w ^ 3) := by fun_prop
  have hi := intervalIntegral.integral_mono_on (μ := volume) hv
    ((continuous_cellIntegrand U G hG s v).intervalIntegrable 0 v) (hp.intervalIntegrable 0 v)
    (fun w hw => by
      have hsq := pow_le_pow_left₀ hw.1 hw.2 2
      have ha : -s * (v ^ 2 - w ^ 2) / 2 + (s - d U) * G w ≤ 0 := by
        have h1 := mul_nonneg hs (sub_nonneg.mpr hsq)
        have h2 := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hds) (hG0 w)
        nlinarith only [h1, h2]
      have he := Real.exp_le_one_iff.mpr ha
      have hW := UpperMomentSpectrumPrice.W_le U w hU hw.1
      have hW0 := UpperMomentSpectrumPrice.W_nonneg U w hU hw.1
      rw [cellIntegrand_eq]
      calc
        _ ≤ s * 1 * W U w := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left he hs) hW0
        _ ≤ s * (w ^ 2 / 2 + d U * w ^ 3 / 3) := by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hW hs
        _ = _ := by ring)
  rw [R_eq_integral]
  apply hi.trans_eq
  rw [intervalIntegral.integral_add
    ((by fun_prop : Continuous (fun w : ℝ => (s / 2) * w ^ 2)).intervalIntegrable 0 v)
    ((by fun_prop : Continuous (fun w : ℝ => (s * d U / 3) * w ^ 3)).intervalIntegrable 0 v),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_pow, integral_pow]
  norm_num
  ring

/-- The actual law's error is below R, while R remains the global
comparison integral for the fixed upper moment. -/
theorem normalized_error_le_R (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (U : ℝ) (hU : 0 < U) (hρ : thirdAbsoluteMoment μ ≤ U) (n : ℕ) (hn : 0 < n)
    (t : ℝ) (ht : 0 ≤ t) :
    ‖charFun (μ : Measure ℝ) (t / Real.sqrt n) ^ n - (Real.exp (-(t ^ 2 / 2)) : ℂ)‖ ≤
      R U (UpperMomentDamping.G U U) (UpperMomentDamping.sScale U n)
        (UpperMomentDamping.betaScale U n * t) := by
  have hβ := UpperMomentSpectrumPrice.betaScale_pos U n hU hn
  have hh := (div_le_iff₀ hβ).mp
    (UpperMomentSpectrumPrice.normalized_error_div_scale_le_price μ hμ U hU hρ n hn t ht)
  have he : R U (UpperMomentDamping.G U U) (UpperMomentDamping.sScale U n)
      (UpperMomentDamping.betaScale U n * t) = UpperMomentDamping.betaScale U n *
        UpperMomentSpectrumPrice.physicalPrice U (UpperMomentDamping.betaScale U n)
          (UpperMomentDamping.G U U) t := by
    rw [UpperMomentDamping.sScale_eq_inv_betaScale_sq U n hU hn,
      R_eq_beta_mul_physicalPrice U _ _ _ hβ]
    congr 2
    field_simp [hβ.ne']
  rw [he]
  simpa only [mul_comm] using hh

end BerryEsseen.UpperMomentSpectralCells

#print axioms BerryEsseen.UpperMomentSpectralCells.firstSlice_eq_sqrt_mul_R
#print axioms BerryEsseen.UpperMomentSpectralCells.R_eq_beta_mul_physicalPrice
#print axioms BerryEsseen.UpperMomentSpectralCells.R_zero
#print axioms BerryEsseen.UpperMomentSpectralCells.continuous_R
#print axioms BerryEsseen.UpperMomentSpectralCells.R_nonneg
#print axioms BerryEsseen.UpperMomentSpectralCells.R_split
#print axioms BerryEsseen.UpperMomentSpectralCells.R_cell_step
#print axioms BerryEsseen.UpperMomentSpectralCells.R_cell_inner
#print axioms BerryEsseen.UpperMomentSpectralCells.R_cell_step_of_le
#print axioms BerryEsseen.UpperMomentSpectralCells.R_cell_inner_of_le
#print axioms BerryEsseen.UpperMomentSpectralCells.R_le_first_polynomial
#print axioms BerryEsseen.UpperMomentSpectralCells.normalized_error_le_R
