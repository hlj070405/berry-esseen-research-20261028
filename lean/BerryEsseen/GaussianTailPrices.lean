module

public import BerryEsseen.GaussianMills
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Tactic.FieldSimp

@[expose] public section

/-!
Actual Gaussian integral prices used for the negative part of the Peano
kernel. All improper-integral comparisons below include integrability
proofs. No finite grid or support restriction is used.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace BerryEsseen.GaussianTailPrices

open GaussianTools GaussianMills

lemma integrable_band_price (x : ℝ) :
    Integrable (fun t : ℝ => (x - t / 2) * phi t) := by
  have hfun : (fun t : ℝ => (x - t / 2) * phi t) =
      (fun t : ℝ => x * phi t - (1 / 2 : ℝ) * (t * phi t)) := by
    funext t
    ring
  rw [hfun]
  exact (integrable_phi.const_mul x).sub (integrable_mul_phi.const_mul (1 / 2 : ℝ))

lemma integral_band_formula (x a b : ℝ) (hab : a ≤ b) :
    (∫ t in Ioc a b, (x - t / 2) * phi t) =
      x * (tail a - tail b) - (phi a - phi b) / 2 := by
  have h0 := intervalIntegral.integral_Ioi_sub_Ioi (a := a) (b := b)
    integrable_phi.integrableOn hab
  rw [intervalIntegral.integral_of_le hab, integral_phi_Ioi, integral_phi_Ioi] at h0
  have hphi : (∫ t in Ioc a b, phi t) = tail a - tail b := by
    simpa only [tail] using h0.symm
  have h1 := intervalIntegral.integral_Ioi_sub_Ioi (a := a) (b := b)
    integrable_mul_phi.integrableOn hab
  rw [intervalIntegral.integral_of_le hab, integral_mul_phi_Ioi,
    integral_mul_phi_Ioi] at h1
  have hmoment : (∫ t in Ioc a b, t * phi t) = phi a - phi b := h1.symm
  have hfun : (fun t : ℝ => (x - t / 2) * phi t) =
      (fun t : ℝ => x * phi t - (1 / 2 : ℝ) * (t * phi t)) := by
    funext t
    ring
  rw [hfun, integral_sub (integrable_phi.const_mul x).integrableOn
    (integrable_mul_phi.const_mul (1 / 2 : ℝ)).integrableOn,
    integral_const_mul, integral_const_mul, hphi, hmoment]
  ring

/-- The finite-band Gaussian price, for every real `x ≥ 2`. -/
theorem band_price_le (x : ℝ) (hx : 2 ≤ x) :
    (∫ t in Ioc (x / 2) (2 * x), (x - t / 2) * phi t) ≤
      (3 / 2 : ℝ) * phi (x / 2) + (1 / 2 : ℝ) * phi (2 * x) := by
  have ha : 0 < x / 2 := by linarith
  have hab : x / 2 ≤ 2 * x := by linarith
  have hm := (le_div_iff₀ ha).mp (tail_le_phi_div (x / 2) ha)
  have hn := mul_nonneg (show 0 ≤ x by linarith) (tail_nonneg (2 * x))
  rw [integral_band_formula x (x / 2) (2 * x) hab]
  nlinarith

/-- Moving right from `x` admits an exponential envelope for the actual
Gaussian density. The omitted factor is `exp (-u²/2) ≤ 1`. -/
lemma phi_add_le_exp (x u : ℝ) :
    phi (x + u) ≤ phi x * Real.exp (-x * u) := by
  have hidentity : phi (x + u) = phi x * Real.exp (-x * u - u ^ 2 / 2) := by
    rw [phi_formula, phi_formula, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [hidentity]
  apply mul_le_mul_of_nonneg_left _ (phi_nonneg x)
  exact Real.exp_le_exp.mpr (by nlinarith [sq_nonneg u])

lemma phi_le_shiftExp (x t : ℝ) :
    phi t ≤ phi x * Real.exp (-x * (t - x)) := by
  have heq : x + (t - x) = t := by ring
  simpa only [heq] using phi_add_le_exp x (t - x)

lemma integrable_sq_exp_neg (x : ℝ) (hx : 0 < x) :
    IntegrableOn (fun u : ℝ => u ^ 2 * Real.exp (-(x * u))) (Ioi 0) := by
  simpa only [Real.rpow_two, Real.rpow_one, neg_mul] using
    (integrableOn_rpow_mul_exp_neg_mul_rpow (s := (2 : ℝ)) (p := (1 : ℝ)) (b := x)
      (by norm_num) (by norm_num) hx)

lemma integral_sq_exp_neg (x : ℝ) (hx : 0 < x) :
    (∫ u : ℝ in Ioi 0, u ^ 2 * Real.exp (-(x * u))) = 2 / x ^ 3 := by
  have hg := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (3 : ℝ)) (r := x)
    (by norm_num) hx
  have hgamma : Real.Gamma (3 : ℝ) = 2 := by norm_num
  have hformula : (∫ u : ℝ in Ioi 0, u ^ 2 * Real.exp (-(x * u))) =
      (1 / x) ^ (3 : ℕ) * 2 := by
    simpa only [show (3 : ℝ) - 1 = 2 by norm_num, Real.rpow_two,
      Real.rpow_ofNat, hgamma] using hg
  rw [hformula, div_pow, one_pow]
  ring

lemma subRight_preimage_Ioi_zero (x : ℝ) :
    (fun t : ℝ => t - x) ⁻¹' Ioi 0 = Ioi x := by
  ext t
  simp only [mem_preimage, mem_Ioi]
  constructor <;> intro h <;> linarith

lemma integrable_sq_exp_shifted (x : ℝ) (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => (t - x) ^ 2 * Real.exp (-(x * (t - x)))) (Ioi x) := by
  have h := (measurableEmbedding_subRight x).integrableOn_map_iff
    (f := fun u : ℝ => u ^ 2 * Real.exp (-(x * u))) (μ := volume) (s := Ioi 0)
  rw [map_sub_right_eq_self, subRight_preimage_Ioi_zero] at h
  exact h.mp (integrable_sq_exp_neg x hx)

lemma integral_sq_exp_shifted (x : ℝ) (hx : 0 < x) :
    (∫ t : ℝ in Ioi x, (t - x) ^ 2 * Real.exp (-(x * (t - x)))) = 2 / x ^ 3 := by
  have h := (measurableEmbedding_subRight x).setIntegral_map (μ := volume)
    (fun u : ℝ => u ^ 2 * Real.exp (-(x * u))) (Ioi 0)
  rw [map_sub_right_eq_self, subRight_preimage_Ioi_zero] at h
  exact h.symm.trans (integral_sq_exp_neg x hx)

lemma tail_sq_pointwise_le (x t : ℝ) (hx : 0 < x) (ht : x ≤ t) :
    (t - x) ^ 2 * tail t ≤
      (phi x / x) * ((t - x) ^ 2 * Real.exp (-(x * (t - x)))) := by
  have htpos : 0 < t := lt_of_lt_of_le hx ht
  have hm := (le_div_iff₀ htpos).mp (tail_le_phi_div t htpos)
  have hmono := mul_le_mul_of_nonneg_left ht (tail_nonneg t)
  have hp := phi_le_shiftExp x t
  simp only [neg_mul] at hp
  have htail : tail t ≤ (phi x * Real.exp (-(x * (t - x)))) / x :=
    (le_div_iff₀ hx).mpr (by linarith)
  calc
    _ ≤ (t - x) ^ 2 * ((phi x * Real.exp (-(x * (t - x)))) / x) :=
      mul_le_mul_of_nonneg_left htail (sq_nonneg _)
    _ = _ := by ring

lemma continuous_tail : Continuous tail := by
  unfold tail
  exact continuous_const.sub
    (continuous_iff_continuousAt.mpr fun t => (hasDerivAt_Phi t).continuousAt)

/-- The original squared-tail integrand is genuinely integrable. -/
theorem integrable_tail_sq_price (x : ℝ) (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => (t - x) ^ 2 * tail t) (Ioi x) := by
  have hr : IntegrableOn (fun t : ℝ =>
      (phi x / x) * ((t - x) ^ 2 * Real.exp (-(x * (t - x))))) (Ioi x) :=
    (integrable_sq_exp_shifted x hx).const_mul (phi x / x)
  have hc : Continuous (fun t : ℝ => (t - x) ^ 2 * tail t) :=
    ((continuous_id.sub continuous_const).pow 2).mul continuous_tail
  apply hr.mono' hc.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (tail_nonneg t))]
  exact tail_sq_pointwise_le x t hx (le_of_lt ht)

/-- The improper squared-tail price, for every real `x ≥ 2`. -/
theorem half_tail_sq_price_le (x : ℝ) (hx : 2 ≤ x) :
    (1 / 2 : ℝ) * (∫ t in Ioi x, (t - x) ^ 2 * tail t) ≤ phi x / x ^ 4 := by
  have hxpos : 0 < x := by linarith
  have hr : IntegrableOn (fun t : ℝ =>
      (phi x / x) * ((t - x) ^ 2 * Real.exp (-(x * (t - x))))) (Ioi x) :=
    (integrable_sq_exp_shifted x hxpos).const_mul (phi x / x)
  have hle : (∫ t in Ioi x, (t - x) ^ 2 * tail t) ≤
      ∫ t in Ioi x, (phi x / x) *
        ((t - x) ^ 2 * Real.exp (-(x * (t - x)))) := by
    apply integral_mono_ae (integrable_tail_sq_price x hxpos) hr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact tail_sq_pointwise_le x t hxpos (le_of_lt ht)
  rw [integral_const_mul, integral_sq_exp_shifted x hxpos] at hle
  calc
    _ ≤ (1 / 2 : ℝ) * ((phi x / x) * (2 / x ^ 3)) :=
      mul_le_mul_of_nonneg_left hle (by norm_num)
    _ = _ := by field_simp [hxpos.ne']

end BerryEsseen.GaussianTailPrices

#print axioms BerryEsseen.GaussianTailPrices.band_price_le
#print axioms BerryEsseen.GaussianTailPrices.integrable_tail_sq_price
#print axioms BerryEsseen.GaussianTailPrices.half_tail_sq_price_le
