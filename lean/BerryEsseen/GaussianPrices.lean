module

public import BerryEsseen.GaussianTools
public import BerryEsseen.GaussianMills
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section

/-! 2026-10-28: strict rational prices for the actual Gaussian density and CDF.
The exponential certificates use fixed finite partial sums; interval comparisons
use the actual CDF integral and the fundamental theorem of calculus. -/

noncomputable section

open MeasureTheory Set
open scoped BigOperators Topology

namespace BerryEsseen.GaussianPrices

open GaussianTools GaussianMills

lemma phi_zero_eq : phi 0 = 1 / Real.sqrt (2 * Real.pi) := by
  simp [phi_formula, one_div]

/-- A strict rational lower density price, using the official upper bound on pi. -/
theorem phi_zero_gt_39_100 : (39 : ℝ) / 100 < phi 0 := by
  have hr : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hs := Real.sq_sqrt (show 0 ≤ 2 * Real.pi by positivity)
  have hp := Real.pi_lt_d2
  have hu : Real.sqrt (2 * Real.pi) < (100 : ℝ) / 39 := by nlinarith
  rw [phi_zero_eq]
  apply (lt_div_iff₀ hr).mpr
  nlinarith

/-- A strict rational upper density price, using the official lower bound on pi. -/
theorem phi_zero_lt_2_5 : phi 0 < (2 : ℝ) / 5 := by
  have hr : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hs := Real.sq_sqrt (show 0 ≤ 2 * Real.pi by positivity)
  have hp := Real.pi_gt_d2
  have hl : (5 : ℝ) / 2 < Real.sqrt (2 * Real.pi) := by nlinarith
  rw [phi_zero_eq]
  apply (div_lt_iff₀ hr).mpr
  nlinarith

lemma phi_eq_phi_zero_mul_exp (t : ℝ) :
    phi t = phi 0 * Real.exp (-(t ^ 2 / 2)) := by
  rw [phi_formula, phi_zero_eq, one_div]
  congr 1
  congr 1
  ring

lemma phi_eq_phi_zero_div_exp (t : ℝ) :
    phi t = phi 0 / Real.exp (t ^ 2 / 2) := by
  rw [phi_eq_phi_zero_mul_exp, Real.exp_neg]
  simp only [div_eq_mul_inv]

/-- Convert a finite positive-exponential certificate to a strict actual-density price. -/
lemma phi_lt_of_exp_lower (t b L : ℝ) (hb : 0 ≤ b)
    (hExp : L ≤ Real.exp (t ^ 2 / 2)) (hprice : (2 : ℝ) / 5 ≤ b * L) : phi t < b := by
  rw [phi_eq_phi_zero_div_exp]
  apply (div_lt_iff₀ (Real.exp_pos _)).mpr
  calc
    phi 0 < (2 : ℝ) / 5 := phi_zero_lt_2_5
    _ ≤ b * L := hprice
    _ ≤ b * Real.exp (t ^ 2 / 2) := mul_le_mul_of_nonneg_left hExp hb

/-- The certificate uses terms 0 through 3 of exp(1/2). -/
theorem phi_one_lt_49_200 : phi 1 < (49 : ℝ) / 200 := by
  apply phi_lt_of_exp_lower 1 (49 / 200) (80 / 49) (by norm_num) ?_ (by norm_num)
  have h := Real.sum_le_exp_of_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ)) 4
  have hc : (80 : ℝ) / 49 ≤ ∑ i ∈ Finset.range 4, (1 / 2 : ℝ) ^ i / (i.factorial : ℝ) := by
    norm_num [Finset.sum_range_succ]
  convert hc.trans h using 1; norm_num

/-- The certificate uses terms 0 through 6 of exp(2). -/
theorem phi_two_lt_11_200 : phi 2 < (11 : ℝ) / 200 := by
  apply phi_lt_of_exp_lower 2 (11 / 200) (80 / 11) (by norm_num) ?_ (by norm_num)
  have h := Real.sum_le_exp_of_nonneg (by norm_num : 0 ≤ (2 : ℝ)) 7
  have hc : (80 : ℝ) / 11 ≤ ∑ i ∈ Finset.range 7, (2 : ℝ) ^ i / (i.factorial : ℝ) := by
    norm_num [Finset.sum_range_succ]
  convert hc.trans h using 1; norm_num

/-- The certificate uses terms 0 through 12 of exp(8). -/
theorem phi_four_lt_3_20000 : phi 4 < (3 : ℝ) / 20000 := by
  apply phi_lt_of_exp_lower 4 (3 / 20000) (8000 / 3) (by norm_num) ?_ (by norm_num)
  have h := Real.sum_le_exp_of_nonneg (by norm_num : 0 ≤ (8 : ℝ)) 13
  have hc : (8000 : ℝ) / 3 ≤ ∑ i ∈ Finset.range 13, (8 : ℝ) ^ i / (i.factorial : ℝ) := by
    norm_num [Finset.sum_range_succ]
  convert hc.trans h using 1; norm_num

/-- The quadratic upper bound holds on the whole nonnegative half-line. -/
theorem exp_neg_le_quadratic (u : ℝ) (hu : 0 ≤ u) :
    Real.exp (-u) ≤ 1 - u + u ^ 2 / 2 := by
  let F : ℝ → ℝ := fun v => 1 - v + v ^ 2 / 2 - Real.exp (-v)
  have hd : ∀ v, HasDerivAt F (-1 + v + Real.exp (-v)) v := by
    intro v
    change HasDerivAt (fun z : ℝ => 1 - z + z ^ 2 / 2 - Real.exp (-z)) _ v
    convert (((hasDerivAt_const v (1 : ℝ)).fun_sub (hasDerivAt_id' v)).fun_add
      (((hasDerivAt_id' v).fun_pow 2).div_const 2)).fun_sub
      ((hasDerivAt_id' v).fun_neg.exp) using 1
    ring
  have hm : Monotone F := monotone_of_hasDerivAt_nonneg hd (by
    intro v
    change 0 ≤ -1 + v + Real.exp (-v)
    linarith [Real.one_sub_le_exp_neg v])
  have hz : F 0 = 0 := by simp [F]
  have hnon : 0 ≤ F u := by rw [← hz]; exact hm hu
  dsimp only [F] at hnon
  linarith

/-- The lower quadratic density comparison includes both endpoints of [0,1]. -/
theorem phi_lower_on_unit (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (39 : ℝ) / 100 * (1 - t ^ 2 / 2) ≤ phi t := by
  have hpoly : 0 ≤ 1 - t ^ 2 / 2 := by
    have hsq := mul_nonneg ht0 (show 0 ≤ 1 - t by linarith)
    nlinarith
  rw [phi_eq_phi_zero_mul_exp]
  calc
    (39 : ℝ) / 100 * (1 - t ^ 2 / 2) ≤ phi 0 * (1 - t ^ 2 / 2) :=
      mul_le_mul_of_nonneg_right phi_zero_gt_39_100.le hpoly
    _ ≤ phi 0 * Real.exp (-(t ^ 2 / 2)) :=
      mul_le_mul_of_nonneg_left (Real.one_sub_le_exp_neg _) (phi_nonneg 0)

/-- The quartic upper comparison in fact holds for every real t. -/
theorem phi_le_quartic (t : ℝ) :
    phi t ≤ (2 : ℝ) / 5 * (1 - t ^ 2 / 2 + t ^ 4 / 8) := by
  rw [phi_eq_phi_zero_mul_exp]
  calc
    phi 0 * Real.exp (-(t ^ 2 / 2)) ≤ (2 : ℝ) / 5 * Real.exp (-(t ^ 2 / 2)) :=
      mul_le_mul_of_nonneg_right phi_zero_lt_2_5.le (Real.exp_pos _).le
    _ ≤ (2 : ℝ) / 5 * (1 - t ^ 2 / 2 + (t ^ 2 / 2) ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left (exp_neg_le_quadratic _ (div_nonneg (sq_nonneg t) (by norm_num))) (by norm_num)
    _ = _ := by ring

/-- The actual closed Gaussian CDF takes value one half at zero. -/
theorem Phi_zero : Phi 0 = (1 : ℝ) / 2 := by
  have h := Phi_neg (0 : ℝ)
  simp only [neg_zero, tail] at h
  linarith

/-- The density lower bound is integrated using the actual CDF and FTC, on closed [0,1]. -/
theorem Phi_lower_on_unit (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 : ℝ) / 2 + (39 : ℝ) / 100 * (t - t ^ 3 / 6) ≤ Phi t := by
  have hc : Continuous (fun u : ℝ => (39 : ℝ) / 100 * (1 - u ^ 2 / 2)) := by fun_prop
  have hp : ∀ u : ℝ, HasDerivAt (fun v : ℝ => (39 : ℝ) / 100 * (v - v ^ 3 / 6))
      ((39 : ℝ) / 100 * (1 - u ^ 2 / 2)) u := by
    intro u
    convert ((hasDerivAt_id' u).fun_sub (((hasDerivAt_id' u).fun_pow 3).div_const 6)).const_mul
      ((39 : ℝ) / 100) using 1
    ring
  have hInt : (∫ u in (0 : ℝ)..t, (39 : ℝ) / 100 * (1 - u ^ 2 / 2)) =
      (39 : ℝ) / 100 * (t - t ^ 3 / 6) := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hp u) (hc.intervalIntegrable 0 t)]
    norm_num
  have hmono := intervalIntegral.integral_mono_on (μ := volume) ht0 (hc.intervalIntegrable 0 t)
    (continuous_phi.intervalIntegrable 0 t) (fun u hu => phi_lower_on_unit u hu.1 (hu.2.trans ht1))
  rw [hInt] at hmono
  rw [Phi_eq_const_add_intervalIntegral, Phi_zero]
  linarith

theorem Phi_one_ge_33_40 : (33 : ℝ) / 40 ≤ Phi 1 := by
  have h := Phi_lower_on_unit 1 (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

end BerryEsseen.GaussianPrices

#print axioms BerryEsseen.GaussianPrices.phi_zero_gt_39_100
#print axioms BerryEsseen.GaussianPrices.phi_zero_lt_2_5
#print axioms BerryEsseen.GaussianPrices.phi_one_lt_49_200
#print axioms BerryEsseen.GaussianPrices.phi_two_lt_11_200
#print axioms BerryEsseen.GaussianPrices.phi_four_lt_3_20000
#print axioms BerryEsseen.GaussianPrices.exp_neg_le_quadratic
#print axioms BerryEsseen.GaussianPrices.phi_lower_on_unit
#print axioms BerryEsseen.GaussianPrices.phi_le_quartic
#print axioms BerryEsseen.GaussianPrices.Phi_zero
#print axioms BerryEsseen.GaussianPrices.Phi_lower_on_unit
#print axioms BerryEsseen.GaussianPrices.Phi_one_ge_33_40


