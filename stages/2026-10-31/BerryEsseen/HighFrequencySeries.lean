module

public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

/-! 2026-10-28: the manuscript's S3 and S5 prices are finite twenty-term
expressions controlling their actual infinite series. The omitted terms begin
at j=21, and their bounds are genuine improper integrals from x=20. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators

namespace BerryEsseen.HighFrequencySeries

def powerKernel (p : ℕ) (w x : ℝ) : ℝ := 1 / (x - w) ^ p

/-- Natural index m represents the original integer j=m+1. -/
def seriesTerm (p : ℕ) (w : ℝ) (m : ℕ) : ℝ := powerKernel p w ((m : ℝ) + 1)

def S3 : ℝ := (∑ m ∈ Finset.range 20, seriesTerm 3 0 m) + 1 / 800

def S5 (w : ℝ) : ℝ :=
  (∑ m ∈ Finset.range 20, seriesTerm 5 w m) + 1 / (4 * (20 - w) ^ 4)

lemma powerKernel_nonneg (p : ℕ) (w x : ℝ) (hx : w < x) : 0 ≤ powerKernel p w x := by
  unfold powerKernel
  positivity

lemma antitoneOn_powerKernel (p : ℕ) (w a : ℝ) (ha : w < a) :
    AntitoneOn (powerKernel p w) (Ici a) := by
  intro x hx y hy hxy
  unfold powerKernel
  apply one_div_le_one_div_of_le (pow_pos (by linarith [mem_Ici.mp hx] : 0 < x - w) p)
  exact pow_le_pow_left₀ (by linarith [mem_Ici.mp hx] : 0 ≤ x - w) (sub_le_sub_right hxy w) p

lemma powerKernel_eq_rpow (p : ℕ) (w x : ℝ) (hx : w < x) :
    powerKernel p w x = (x - w) ^ (-(p : ℝ)) := by
  rw [Real.rpow_neg (by linarith : 0 ≤ x - w), Real.rpow_natCast]
  simp only [powerKernel, one_div]

lemma integrableOn_powerKernel (p : ℕ) (hp : 1 < p) (w a : ℝ) (ha : w < a) :
    IntegrableOn (powerKernel p w) (Ioi a) := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp
  have hi := integrableOn_add_rpow_Ioi_of_lt (a := -(p : ℝ)) (c := a) (m := -w)
    (by linarith) (by linarith)
  apply hi.congr_fun _ measurableSet_Ioi
  intro x hx
  simpa only [sub_eq_add_neg] using (powerKernel_eq_rpow p w x (ha.trans hx)).symm

/-- A translated real-power integral, evaluated by the actual improper FTC. -/
lemma integral_shifted_rpow (r w a : ℝ) (hr : r < -1) (ha : w < a) :
    (∫ x in Ioi a, (x - w) ^ r) = -(a - w) ^ (r + 1) / (r + 1) := by
  have hd : ∀ x ∈ Ici a, HasDerivAt
      (fun t : ℝ => (t - w) ^ (r + 1) / (r + 1)) ((x - w) ^ r) x := by
    intro x hx
    convert! (((hasDerivAt_id x).sub_const w).rpow_const _).div_const _ using 1
    · simp [show r + 1 ≠ 0 by linarith, mul_comm]
    left
    linarith [mem_Ici.mp hx, id_eq x]
  have hi : IntegrableOn (fun x : ℝ => (x - w) ^ r) (Ioi a) := by
    simpa only [sub_eq_add_neg] using
      (integrableOn_add_rpow_Ioi_of_lt (a := r) (c := a) (m := -w) hr (by linarith))
  have ht : Tendsto (fun t : ℝ => (t - w) ^ (r + 1) / (r + 1)) atTop (𝓝 0) := by
    have hpow : Tendsto (fun t : ℝ => (t - w) ^ (r + 1)) atTop (𝓝 0) := by
      have h := (tendsto_rpow_neg_atTop (by linarith : 0 < -(r + 1))).comp
        (tendsto_atTop_add_const_right atTop (-w) tendsto_id)
      simpa only [Function.comp_def, id_eq, neg_neg, sub_eq_add_neg] using h
    simpa only [zero_div] using hpow.div_const (r + 1)
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' hd hi ht
  simpa only [zero_sub, neg_div] using h

lemma integral_powerKernel_three (w a : ℝ) (ha : w < a) :
    (∫ x in Ioi a, powerKernel 3 w x) = 1 / (2 * (a - w) ^ 2) := by
  have heq : (∫ x in Ioi a, powerKernel 3 w x) = ∫ x in Ioi a, (x - w) ^ (-(3 : ℝ)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    exact powerKernel_eq_rpow 3 w x (ha.trans hx)
  rw [heq, integral_shifted_rpow _ _ _ (by norm_num) ha]
  norm_num only [show -(3 : ℝ) + 1 = -(2 : ℝ) by norm_num]
  rw [Real.rpow_neg (by linarith : 0 ≤ a - w), Real.rpow_two]
  field_simp [sub_ne_zero.mpr (ne_of_gt ha)]

lemma integral_powerKernel_five (w a : ℝ) (ha : w < a) :
    (∫ x in Ioi a, powerKernel 5 w x) = 1 / (4 * (a - w) ^ 4) := by
  have heq : (∫ x in Ioi a, powerKernel 5 w x) = ∫ x in Ioi a, (x - w) ^ (-(5 : ℝ)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    exact powerKernel_eq_rpow 5 w x (ha.trans hx)
  rw [heq, integral_shifted_rpow _ _ _ (by norm_num) ha]
  norm_num only [show -(5 : ℝ) + 1 = -(4 : ℝ) by norm_num]
  rw [Real.rpow_neg (by linarith : 0 ≤ a - w), Real.rpow_ofNat]
  field_simp [sub_ne_zero.mpr (ne_of_gt ha)]

/-- The integral test proves convergence of the full naturally indexed series. -/
lemma summable_seriesTerm (p : ℕ) (hp : 1 < p) (w : ℝ) (hw : w < 20) :
    Summable (seriesTerm p w) := by
  have hw' : w - 1 < 19 := by linarith
  have hs : Summable (fun n : ℕ => powerKernel p (w - 1) (n : ℝ)) :=
    (antitoneOn_powerKernel p (w - 1) 19 hw').summable_of_integrableOn_Ioi
      (integrableOn_powerKernel p hp (w - 1) 19 hw')
      (fun x hx => powerKernel_nonneg p (w - 1) x (hw'.trans hx))
  apply hs.congr
  intro n
  unfold seriesTerm powerKernel
  rw [show (n : ℝ) - (w - 1) = (n : ℝ) + 1 - w by ring]

/-- The first omitted natural index is m=20, hence the first original j is 21. -/
lemma series_tail_le_integral (p : ℕ) (hp : 1 < p) (w : ℝ) (hw : w < 20) :
    (∑' m : ℕ, seriesTerm p w (m + 20)) ≤ ∫ x in Ioi (20 : ℝ), powerKernel p w x := by
  have h := (antitoneOn_powerKernel p w 20 hw).tsum_comp_add_le_integral 20
    (integrableOn_powerKernel p hp w 20 hw)
    (fun x hx => powerKernel_nonneg p w x (hw.trans hx))
  simpa only [seriesTerm, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, add_assoc] using h

lemma seriesTerm_three_nonneg (m : ℕ) : 0 ≤ seriesTerm 3 0 m := by
  apply powerKernel_nonneg
  positivity

lemma seriesTerm_five_nonneg (w : ℝ) (hw : w ≤ 1 / 4) (m : ℕ) :
    0 ≤ seriesTerm 5 w m := by
  apply powerKernel_nonneg
  have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  linarith

lemma summable_series_three : Summable (seriesTerm 3 0) :=
  summable_seriesTerm 3 (by norm_num) 0 (by norm_num)

lemma summable_series_five (w : ℝ) (_hw0 : 0 < w) (hw : w ≤ 1 / 4) :
    Summable (seriesTerm 5 w) :=
  summable_seriesTerm 5 (by norm_num) w (by linarith)

lemma tsum_series_three_nonneg : 0 ≤ ∑' m : ℕ, seriesTerm 3 0 m :=
  tsum_nonneg seriesTerm_three_nonneg

lemma tsum_series_five_nonneg (w : ℝ) (hw : w ≤ 1 / 4) :
    0 ≤ ∑' m : ℕ, seriesTerm 5 w m :=
  tsum_nonneg (seriesTerm_five_nonneg w hw)

lemma S3_nonneg : 0 ≤ S3 := by
  unfold S3
  exact add_nonneg (Finset.sum_nonneg (fun m _ => seriesTerm_three_nonneg m)) (by norm_num)

lemma S5_nonneg (w : ℝ) (hw : w ≤ 1 / 4) : 0 ≤ S5 w := by
  unfold S5
  exact add_nonneg (Finset.sum_nonneg (fun m _ => seriesTerm_five_nonneg w hw m)) (by positivity)

theorem series_three_le_S3 : (∑' m : ℕ, seriesTerm 3 0 m) ≤ S3 := by
  have ht := series_tail_le_integral 3 (by norm_num) 0 (by norm_num)
  rw [integral_powerKernel_three 0 20 (by norm_num)] at ht
  norm_num at ht
  rw [← summable_series_three.sum_add_tsum_nat_add 20]
  exact add_le_add le_rfl ht

theorem series_five_le_S5 (w : ℝ) (hw0 : 0 < w) (hw : w ≤ 1 / 4) :
    (∑' m : ℕ, seriesTerm 5 w m) ≤ S5 w := by
  have ht := series_tail_le_integral 5 (by norm_num) w (by linarith)
  rw [integral_powerKernel_five w 20 (by linarith)] at ht
  rw [← (summable_series_five w hw0 hw).sum_add_tsum_nat_add 20]
  exact add_le_add le_rfl ht

end BerryEsseen.HighFrequencySeries

#print axioms BerryEsseen.HighFrequencySeries.integral_powerKernel_three
#print axioms BerryEsseen.HighFrequencySeries.integral_powerKernel_five
#print axioms BerryEsseen.HighFrequencySeries.summable_series_three
#print axioms BerryEsseen.HighFrequencySeries.summable_series_five
#print axioms BerryEsseen.HighFrequencySeries.series_three_le_S3
#print axioms BerryEsseen.HighFrequencySeries.series_five_le_S5
