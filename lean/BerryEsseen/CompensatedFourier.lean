module

public import BerryEsseen.GaussianTailPrices
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-! 2026-10-28: the absolutely convergent compensated scalar Fourier payoff.
A nonnegative Laplace/Gamma product is proved integrable via Tonelli's norm
criterion before any Bochner Fubini interchange is used. -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace BerryEsseen.CompensatedFourier

def payoff (y t : ℝ) : ℝ := (t * y - Real.sin (t * y)) / t ^ 3

def laplaceKernel (y t s : ℝ) : ℝ :=
  (s ^ 2 / 2) * Real.exp (-(s * t)) * (t * y - Real.sin (t * y))

def rationalPrice (y s : ℝ) : ℝ := y ^ 3 / (2 * (s ^ 2 + y ^ 2))

lemma integrable_t_exp_neg (s : ℝ) (hs : 0 < s) :
    IntegrableOn (fun t : ℝ => t * Real.exp (-(s * t))) (Ioi 0) := by
  simpa only [Real.rpow_one, neg_mul] using
    (integrableOn_rpow_mul_exp_neg_mul_rpow (s := (1 : ℝ)) (p := (1 : ℝ)) (b := s)
      (by norm_num) (by norm_num) hs)

lemma integral_t_exp_neg (s : ℝ) (hs : 0 < s) :
    (∫ t in Ioi 0, t * Real.exp (-(s * t))) = 1 / s ^ 2 := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (2 : ℝ)) (r := s) (by norm_num) hs
  have hg : Real.Gamma (2 : ℝ) = 1 := by norm_num
  simpa only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.rpow_ofNat,
    hg, mul_one, div_pow, one_pow] using h

lemma complex_exp_im (s y t : ℝ) :
    (Complex.exp ((-(s : ℂ) + (y : ℂ) * Complex.I) * (t : ℂ))).im =
      Real.exp (-(s * t)) * Real.sin (t * y) := by
  simp [Complex.exp_im, Complex.mul_re, Complex.mul_im, mul_comm]

lemma integrable_exp_sin (s y : ℝ) (hs : 0 < s) :
    IntegrableOn (fun t : ℝ => Real.exp (-(s * t)) * Real.sin (t * y)) (Ioi 0) := by
  have hc : (-(s : ℂ) + (y : ℂ) * Complex.I).re < 0 := by simp; linarith
  have h : IntegrableOn
      (fun t : ℝ => (Complex.exp ((-(s : ℂ) + (y : ℂ) * Complex.I) * (t : ℂ))).im) (Ioi 0) :=
    (integrableOn_exp_mul_complex_Ioi hc 0).im
  exact h.congr (Filter.Eventually.of_forall (complex_exp_im s y))

/-- An absolutely convergent Laplace-sine integral, obtained from the official complex exponential primitive. -/
lemma integral_exp_sin (s y : ℝ) (hs : 0 < s) :
    (∫ t in Ioi 0, Real.exp (-(s * t)) * Real.sin (t * y)) = y / (s ^ 2 + y ^ 2) := by
  let a : ℂ := -(s : ℂ) + (y : ℂ) * Complex.I
  have hre : a.re = -s := by simp [a]
  have him : a.im = y := by simp [a]
  have hc : a.re < 0 := by rw [hre]; linarith
  have hi := integrableOn_exp_mul_complex_Ioi hc 0
  calc
    (∫ t in Ioi 0, Real.exp (-(s * t)) * Real.sin (t * y)) =
        ∫ t : ℝ in Ioi 0, (Complex.exp (a * (t : ℂ))).im := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun t => (complex_exp_im s y t).symm
    _ = (∫ t : ℝ in Ioi 0, Complex.exp (a * (t : ℂ))).im := integral_im hi
    _ = _ := by
      rw [integral_exp_mul_complex_Ioi hc 0]
      simp [Complex.div_im, Complex.normSq_apply, hre, him]
      ring

lemma laplaceKernel_expand (y t s : ℝ) :
    laplaceKernel y t s = (s ^ 2 / 2) *
      (y * (t * Real.exp (-(s * t))) - Real.exp (-(s * t)) * Real.sin (t * y)) := by
  unfold laplaceKernel
  ring

lemma integrable_laplace_section (y s : ℝ) (hs : 0 < s) :
    IntegrableOn (fun t : ℝ => laplaceKernel y t s) (Ioi 0) := by
  have heq : (fun t : ℝ => laplaceKernel y t s) = (fun t : ℝ => (s ^ 2 / 2) *
      (y * (t * Real.exp (-(s * t))) - Real.exp (-(s * t)) * Real.sin (t * y))) :=
    funext fun t => laplaceKernel_expand y t s
  rw [heq]
  exact (((integrable_t_exp_neg s hs).const_mul y).sub (integrable_exp_sin s y hs)).const_mul _

lemma integral_laplace_section (y s : ℝ) (hs : 0 < s) :
    (∫ t in Ioi 0, laplaceKernel y t s) = rationalPrice y s := by
  have hA : IntegrableOn (fun t : ℝ => y * (t * Real.exp (-(s * t)))) (Ioi 0) :=
    (integrable_t_exp_neg s hs).const_mul _
  have hB := integrable_exp_sin s y hs
  have heq : (fun t : ℝ => laplaceKernel y t s) = (fun t : ℝ => (s ^ 2 / 2) *
      (y * (t * Real.exp (-(s * t))) - Real.exp (-(s * t)) * Real.sin (t * y))) :=
    funext fun t => laplaceKernel_expand y t s
  rw [heq, integral_const_mul, integral_sub hA hB, integral_const_mul,
    integral_t_exp_neg s hs, integral_exp_sin s y hs]
  have hd : s ^ 2 + y ^ 2 ≠ 0 := ne_of_gt (by nlinarith [sq_nonneg y, sq_pos_of_pos hs])
  unfold rationalPrice
  field_simp [ne_of_gt hs, hd]; ring

lemma rationalPrice_eq_scaled (y s : ℝ) (hy : y ≠ 0) :
    rationalPrice y s = (y / 2) * (1 + ((1 / y) * s) ^ 2)⁻¹ := by
  unfold rationalPrice
  have hd : s ^ 2 + y ^ 2 ≠ 0 := ne_of_gt (by nlinarith [sq_nonneg s, sq_pos_of_ne_zero hy])
  field_simp [hy, hd]; ring

lemma integrable_rationalPrice (y : ℝ) (hy : 0 < y) : Integrable (rationalPrice y) := by
  have h := (integrable_inv_one_add_mul_sq (b := (1 / y)) (one_div_ne_zero (ne_of_gt hy))).const_mul (y / 2)
  exact h.congr (Filter.Eventually.of_forall fun s => (rationalPrice_eq_scaled y s (ne_of_gt hy)).symm)

lemma integral_rationalPrice (y : ℝ) (hy : 0 < y) :
    (∫ s in Ioi 0, rationalPrice y s) = Real.pi * y ^ 2 / 4 := by
  have heq : rationalPrice y = (fun s : ℝ => (y / 2) * (1 + ((1 / y) * s) ^ 2)⁻¹) :=
    funext fun s => rationalPrice_eq_scaled y s (ne_of_gt hy)
  rw [heq, integral_const_mul, integral_comp_mul_left_Ioi
    (fun s : ℝ => (1 + s ^ 2)⁻¹) 0 (one_div_pos.mpr hy)]
  simp only [one_div, inv_inv, mul_zero, integral_Ioi_inv_one_add_sq, Real.arctan_zero, sub_zero, smul_eq_mul]
  ring

end BerryEsseen.CompensatedFourier

#print axioms BerryEsseen.CompensatedFourier.integral_exp_sin
#print axioms BerryEsseen.CompensatedFourier.integral_laplace_section
#print axioms BerryEsseen.CompensatedFourier.integral_rationalPrice

namespace BerryEsseen.CompensatedFourier

abbrev positiveLebesgue : Measure ℝ := volume.restrict (Ioi 0)

lemma laplaceKernel_nonneg (y t s : ℝ) (hy : 0 ≤ y) (ht : 0 ≤ t) :
    0 ≤ laplaceKernel y t s := by
  unfold laplaceKernel
  apply mul_nonneg
  · exact mul_nonneg (div_nonneg (sq_nonneg s) (by norm_num)) (Real.exp_pos _).le
  · exact sub_nonneg.mpr (Real.sin_le (mul_nonneg ht hy))

lemma gamma_section_eq (y t : ℝ) : (fun s : ℝ => laplaceKernel y t s) =
    (fun s : ℝ => (t * y - Real.sin (t * y)) / 2 * (s ^ 2 * Real.exp (-(t * s)))) := by
  ext s
  unfold laplaceKernel
  rw [mul_comm s t]
  ring

lemma integrable_gamma_section (y t : ℝ) (ht : 0 < t) :
    IntegrableOn (fun s : ℝ => laplaceKernel y t s) (Ioi 0) := by
  rw [gamma_section_eq]
  exact (GaussianTailPrices.integrable_sq_exp_neg t ht).const_mul _

lemma integral_gamma_section (y t : ℝ) (ht : 0 < t) :
    (∫ s in Ioi 0, laplaceKernel y t s) = payoff y t := by
  rw [gamma_section_eq, integral_const_mul, GaussianTailPrices.integral_sq_exp_neg t ht]
  unfold payoff
  ring

/-- Tonelli's norm criterion first proves actual product integrability from the finite
Laplace/arctangent price. The original Fourier payoff is not an integrability hypothesis. -/
theorem integrable_laplace_product (y : ℝ) (hy : 0 < y) :
    Integrable (fun p : ℝ × ℝ => laplaceKernel y p.1 p.2)
      (positiveLebesgue.prod positiveLebesgue) := by
  have hc : Continuous (fun p : ℝ × ℝ => laplaceKernel y p.1 p.2) := by
    unfold laplaceKernel
    fun_prop
  apply (integrable_prod_iff' hc.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact integrable_laplace_section y s hs
  · have heq : (fun s : ℝ => ∫ t : ℝ, ‖laplaceKernel y t s‖ ∂positiveLebesgue) =ᵐ[positiveLebesgue]
        rationalPrice y := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      calc
        (∫ t : ℝ, ‖laplaceKernel y t s‖ ∂positiveLebesgue) =
            ∫ t : ℝ, laplaceKernel y t s ∂positiveLebesgue := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          exact Real.norm_of_nonneg (laplaceKernel_nonneg y t s hy.le ht.le)
        _ = rationalPrice y s := integral_laplace_section y s hs
    exact (integrable_rationalPrice y hy).integrableOn.congr heq.symm

/-- Original compensated payoff integrability is a consequence of the proved product integrability. -/
theorem integrable_payoff_pos (y : ℝ) (hy : 0 < y) : IntegrableOn (payoff y) (Ioi 0) := by
  have h := (integrable_laplace_product y hy).integral_prod_left
  apply h.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact integral_gamma_section y t ht

/-- The positive-y scalar identity, with Fubini applied only after absolute integrability. -/
theorem integral_payoff_pos (y : ℝ) (hy : 0 < y) :
    (∫ t in Ioi 0, payoff y t) = Real.pi * y ^ 2 / 4 := by
  have hswap := integral_integral_swap (μ := positiveLebesgue) (ν := positiveLebesgue)
    (f := fun t s : ℝ => laplaceKernel y t s) (integrable_laplace_product y hy)
  calc
    (∫ t in Ioi 0, payoff y t) =
        ∫ t : ℝ, (∫ s : ℝ, laplaceKernel y t s ∂positiveLebesgue) ∂positiveLebesgue := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact (integral_gamma_section y t ht).symm
    _ = ∫ s : ℝ, (∫ t : ℝ, laplaceKernel y t s ∂positiveLebesgue) ∂positiveLebesgue := hswap
    _ = ∫ s in Ioi 0, rationalPrice y s := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact integral_laplace_section y s hs
    _ = _ := integral_rationalPrice y hy

lemma payoff_neg (y t : ℝ) : payoff (-y) t = -payoff y t := by
  unfold payoff
  rw [mul_neg, Real.sin_neg]
  ring

/-- The original Lebesgue integrand is absolutely integrable for every real y. -/
theorem integrable_payoff (y : ℝ) : IntegrableOn (payoff y) (Ioi 0) := by
  rcases lt_trichotomy y 0 with hy | hy | hy
  · have h : IntegrableOn (fun t : ℝ => -payoff (-y) t) (Ioi 0) := (integrable_payoff_pos (-y) (neg_pos.mpr hy)).neg
    exact h.congr (Filter.Eventually.of_forall fun t => by dsimp only; rw [payoff_neg, neg_neg])
  · subst y
    have heq : payoff 0 = (fun _ : ℝ => (0 : ℝ)) := by ext t; simp [payoff]
    rw [heq]
    change Integrable (fun _ : ℝ => (0 : ℝ)) (volume.restrict (Ioi (0 : ℝ)))
    exact integrable_zero ℝ ℝ (volume.restrict (Ioi (0 : ℝ)))
  · exact integrable_payoff_pos y hy

/-- The real compensated scalar Fourier payoff; no conditional sinc integral is used. -/
theorem integral_compensated_fourier (y : ℝ) :
    (∫ t in Ioi 0, (t * y - Real.sin (t * y)) / t ^ 3) = Real.pi * y * |y| / 4 := by
  change (∫ t in Ioi 0, payoff y t) = _
  rcases lt_trichotomy y 0 with hy | hy | hy
  · have heq : payoff y = (fun t : ℝ => -payoff (-y) t) := by
      ext t
      rw [payoff_neg, neg_neg]
    rw [heq, integral_neg, integral_payoff_pos (-y) (neg_pos.mpr hy), abs_of_neg hy]
    ring
  · subst y
    simp [payoff]
  · rw [integral_payoff_pos y hy, abs_of_pos hy]
    ring

theorem integrable_abs_compensated_fourier (y : ℝ) :
    IntegrableOn (fun t : ℝ => |(t * y - Real.sin (t * y)) / t ^ 3|) (Ioi 0) := by
  change Integrable (fun t : ℝ => |(t * y - Real.sin (t * y)) / t ^ 3|) (volume.restrict (Ioi 0))
  simpa only [payoff, Real.norm_eq_abs] using (integrable_payoff y).norm

end BerryEsseen.CompensatedFourier

#print axioms BerryEsseen.CompensatedFourier.integrable_laplace_product
#print axioms BerryEsseen.CompensatedFourier.integrable_payoff
#print axioms BerryEsseen.CompensatedFourier.integrable_abs_compensated_fourier
#print axioms BerryEsseen.CompensatedFourier.integral_compensated_fourier

namespace BerryEsseen.CompensatedFourier

lemma payoff_nonneg (y t : ℝ) (hy : 0 ≤ y) (ht : 0 ≤ t) : 0 ≤ payoff y t :=
  div_nonneg (sub_nonneg.mpr (Real.sin_le (mul_nonneg ht hy))) (pow_nonneg ht 3)

/-- The absolute scalar price, useful for subsequent moment-based Fubini arguments. -/
theorem integral_abs_compensated_fourier (y : ℝ) :
    (∫ t in Ioi 0, |(t * y - Real.sin (t * y)) / t ^ 3|) = Real.pi * y ^ 2 / 4 := by
  have heq : (fun t : ℝ => |payoff y t|) =ᵐ[positiveLebesgue] (fun t : ℝ => payoff |y| t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    by_cases hy : 0 ≤ y
    · rw [abs_of_nonneg hy, abs_of_nonneg (payoff_nonneg y t hy ht.le)]
    · have hpos : 0 ≤ payoff (-y) t := payoff_nonneg (-y) t (by linarith) ht.le
      have hodd : payoff y t = -payoff (-y) t := by rw [payoff_neg, neg_neg]
      rw [abs_of_neg (lt_of_not_ge hy), hodd, abs_neg, abs_of_nonneg hpos]
  calc
    (∫ t in Ioi 0, |(t * y - Real.sin (t * y)) / t ^ 3|) = ∫ t in Ioi 0, payoff |y| t :=
      integral_congr_ae heq
    _ = Real.pi * |y| * abs (abs y) / 4 := integral_compensated_fourier |y|
    _ = Real.pi * |y| ^ 2 / 4 := by rw [abs_abs]; ring
    _ = _ := by rw [sq_abs]

end BerryEsseen.CompensatedFourier

#print axioms BerryEsseen.CompensatedFourier.integral_abs_compensated_fourier
