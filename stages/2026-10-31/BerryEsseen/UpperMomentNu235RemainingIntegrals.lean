module

public import BerryEsseen.UpperMomentN47ScalarSemantics
public import BerryEsseen.UpperMomentN47KernelTables
public import BerryEsseen.UpperMomentNu235Checks
public import BerryEsseen.UpperMomentSharedSpectrum
public import BerryEsseen.UpperMomentAbsoluteProfile

@[expose] public section

/-! 2026-10-30: connect the new real ν=235/4 endpoint second and third Int18 rows to
the genuine pure-v integrals. Kernel bounds are used only on open cells;
the interval-integral theorem removes their exceptional endpoints.
The fixed real endpoint only chooses s; it is not an iid sample count. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

noncomputable section

namespace BerryEsseen.UpperMomentNu235RemainingIntegrals

open MeasureTheory Set
open scoped Interval BigOperators
open FixedPointEnclosure FixedPointArithmetic FixedPointUpperMomentExp
open FixedFourierConstants (scale scale_positive)
open UpperMomentN47ScalarSemantics (U d v1 v2)
open UpperMomentNu235Data UpperMomentNu235Checks UpperMomentN47KernelTables


def s : ℝ := 940000000 / 54184321
lemma s_pos : 0 < s := by norm_num [s]
lemma s_eq_nu_mul_d : s = (235 / 4 : ℝ) * d := by
  norm_num [s, UpperMomentN47ScalarSemantics.d, UpperMomentN47ScalarSemantics.U]

def compactValue (z : ℤ) : ℝ := (z : ℝ) / 10 ^ 18
def Q2 (j : ℕ) : ℤ := Q218.getD j 0
def E3 (j : ℕ) : ℤ := E318.getD j 0
def row2Upper (j : ℕ) : ℤ := row218.getD j 0
def row3Upper (j : ℕ) : ℤ := row318.getD j 0

lemma val_lift18 (z : ℤ) :
    FixedPointUpperMomentRate.val (lift18 z) = compactValue z := by
  norm_num [FixedPointUpperMomentRate.val, qval, lift18,
    UpperMomentNu235Data.factor, compactValue, FixedFourierConstants.scale]
  ring

private lemma allZip_sound {α β : Type*} (xs : List α) (ys : List β)
    (da : α) (db : β) (check : α → β → Bool)
    (h : (xs.zip ys).all (fun p => check p.1 p.2) = true)
    (j : ℕ) (hx : j < xs.length) (hy : j < ys.length) :
    check (xs.getD j da) (ys.getD j db) = true := by
  have hj : j < (xs.zip ys).length := by simp only [List.length_zip]; omega
  have hh := (List.all_eq_true.mp h) _ (List.getElem_mem hj)
  simpa only [List.getElem_zip, List.getD_eq_getElem xs da hx,
    List.getD_eq_getElem ys db hy] using hh

private lemma allZip3_sound (xs ys zs : List ℤ) (check : ℤ → ℤ → ℤ → Bool)
    (h : ((xs.zip ys).zip zs).all (fun p => check p.1.1 p.1.2 p.2) = true)
    (j : ℕ) (hx : j < xs.length) (hy : j < ys.length) (hz : j < zs.length) :
    check (xs.getD j 0) (ys.getD j 0) (zs.getD j 0) = true := by
  have hj : j < ((xs.zip ys).zip zs).length := by simp only [List.length_zip]; omega
  have hh := (List.all_eq_true.mp h) _ (List.getElem_mem hj)
  simpa only [List.getElem_zip, List.getD_eq_getElem xs 0 hx,
    List.getD_eq_getElem ys 0 hy, List.getD_eq_getElem zs 0 hz] using hh

private lemma indexedAll_sound (xs : List ℤ) (check : ℕ → ℤ → Bool)
    (h : xs.zipIdx.all (fun p => check p.2 p.1) = true) (j : ℕ) (hj : j < xs.length) :
    check j (xs.getD j 0) = true := by
  have hh := (List.forall_mem_zipIdx'.mp (List.all_eq_true.mp h)) j hj
  simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj,
    Option.getD_some] using hh

theorem power_row_checked (j : ℕ) (hj : j < 1024) :
    powerCheck sb (lift18 (UpperMomentN47ScalarSemantics.secondRow j).G)
      (lift18 (Q2 j)) = true := by
  apply allZip_sound UpperMomentN47ScalarData.T2data Q218
    UpperMomentN47ScalarSemantics.secondDefault 0
    (fun r q => powerCheck sb (lift18 r.G) (lift18 q))
    second_power_table_checked j
  · simpa only [UpperMomentN47ScalarData.T2data_length] using hj
  · simpa only [Q218_length] using hj

theorem product2_row_checked (j : ℕ) (hj : j < 1024) :
    productCheck dt2 (lift18 (kernel2Upper j)) (lift18 (Q2 j))
      (lift18 (row2Upper j)) = true := by
  apply allZip3_sound UpperMomentN47KernelWitnesses.kernel218 Q218 row218
    (fun k q r => productCheck dt2 (lift18 k) (lift18 q) (lift18 r))
    second_table_checked j
  · simpa only [UpperMomentN47KernelWitnesses.kernel218_length] using hj
  · simpa only [Q218_length] using hj
  · simpa only [row218_length] using hj

theorem gaussian_row_checked (j : ℕ) (hj : j < 1024) :
    gaussianCheck sb (firstGridBox j) (lift18 (E3 j)) = true := by
  apply indexedAll_sound E318
    (fun j e => gaussianCheck sb (firstGridBox j) (lift18 e))
    gaussian_table_checked j
  simpa only [E318_length] using hj

theorem product3_row_checked (j : ℕ) (hj : j < 1024) :
    productCheck dt1 (lift18 (correctionUpper j)) (lift18 (E3 j))
      (lift18 (row3Upper j)) = true := by
  apply allZip3_sound UpperMomentN47KernelWitnesses.correction18 E318 row318
    (fun k e r => productCheck dt1 (lift18 k) (lift18 e) (lift18 r))
    third_table_checked j
  · simpa only [UpperMomentN47KernelWitnesses.correction18_length] using hj
  · simpa only [E318_length] using hj
  · simpa only [row318_length] using hj

lemma contains_s : Contains scale sb s := by
  simpa only [sb, s, Int.cast_ofNat] using
    rat_contains scale scale_positive 940000000 54184321 (by decide)

lemma contains_dt1 : Contains scale dt1 (1 / 1280 : ℝ) := by
  simpa only [dt1, Int.cast_one, Int.cast_ofNat] using
    rat_contains scale scale_positive 1 1280 (by decide)

lemma contains_dt2 : Contains scale dt2 (1 / 320 : ℝ) := by
  simpa only [dt2, Int.cast_one, Int.cast_ofNat] using
    rat_contains scale scale_positive 1 320 (by decide)

lemma contains_firstGrid (j : ℕ) : Contains scale (firstGridBox j) (v1 j) := by
  simpa only [firstGridBox, firstLeft, UpperMomentN47ScalarSemantics.v1,
    Int.cast_natCast, Int.cast_ofNat] using
    rat_contains scale scale_positive (j : ℤ) 1280 (by decide)

theorem actual_power_cell_le (j : ℕ) (hj : j < 1024) {v : ℝ}
    (hv : v ∈ Icc (v2 j) (v2 (j + 1))) :
    Real.exp (s * UpperMomentDamping.G U U v) ≤ compactValue (Q2 j) := by
  have hc : powerCheck sb
      (UpperMomentN47ScalarChecks.lift18 (UpperMomentN47ScalarSemantics.secondRow j).G)
      (lift18 (Q2 j)) = true := by
    simpa only [UpperMomentN47ScalarChecks.lift18, lift18, UpperMomentNu235Data.factor]
      using power_row_checked j hj
  have hh := UpperMomentSharedSpectrum.actual_power_cell_le j hj contains_s hv hc
  simpa only [val_lift18] using hh

theorem actual_gaussian_cell_le (j : ℕ) (hj : j < 1024) {v : ℝ}
    (hv : v1 j ≤ v) :
    Real.exp (-s * v ^ 2 / 2) ≤ compactValue (E3 j) := by
  simpa only [val_lift18] using gaussianCheck_sound contains_s
    (contains_firstGrid j) hv (gaussian_row_checked j hj)

lemma v1_mono {j k : ℕ} (hjk : j ≤ k) : v1 j ≤ v1 k := by
  unfold UpperMomentN47ScalarSemantics.v1
  exact div_le_div_of_nonneg_right (by exact_mod_cast hjk) (by norm_num)

lemma v2_mono {j k : ℕ} (hjk : j ≤ k) : v2 j ≤ v2 k := by
  unfold UpperMomentN47ScalarSemantics.v2
  exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.add_le_add_left hjk 256)
    (by norm_num)

lemma v1_zero : v1 0 = 0 := by norm_num [UpperMomentN47ScalarSemantics.v1]
lemma v1_last : v1 1024 = 4 / 5 := by norm_num [UpperMomentN47ScalarSemantics.v1]
lemma v2_zero : v2 0 = 4 / 5 := by norm_num [UpperMomentN47ScalarSemantics.v2]
lemma v2_last : v2 1024 = 4 := by norm_num [UpperMomentN47ScalarSemantics.v2]

lemma firstGrid_ratio (j : ℕ) : v1 j / 4 = z1 j := by
  simp only [UpperMomentN47ScalarSemantics.v1, z1, p1, q,
    Int.cast_mul, Int.cast_natCast, Int.cast_ofNat]
  ring

lemma secondGrid_ratio (j : ℕ) : v2 j / 4 = z2 j := by
  simp only [UpperMomentN47ScalarSemantics.v2, z2, p2, q,
    Nat.cast_add, Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_ofNat]
  ring

lemma first_open_ratio {j : ℕ} {v : ℝ} (hv : v ∈ Ioo (v1 j) (v1 (j + 1))) :
    v / 4 ∈ Ioo (z1 j) (z1 (j + 1)) := by
  rw [← firstGrid_ratio j, ← firstGrid_ratio (j + 1)]
  exact ⟨div_lt_div_of_pos_right hv.1 (by norm_num),
    div_lt_div_of_pos_right hv.2 (by norm_num)⟩

lemma second_open_ratio {j : ℕ} {v : ℝ} (hv : v ∈ Ioo (v2 j) (v2 (j + 1))) :
    v / 4 ∈ Ioo (z2 j) (z2 (j + 1)) := by
  rw [← secondGrid_ratio j, ← secondGrid_ratio (j + 1)]
  exact ⟨div_lt_div_of_pos_right hv.1 (by norm_num),
    div_lt_div_of_pos_right hv.2 (by norm_num)⟩

theorem actual_second_cell_le (j : ℕ) (hj : j < 1024) {v : ℝ}
    (hv : v ∈ Ioo (v2 j) (v2 (j + 1))) :
    UpperMomentAbsoluteProfile.second (UpperMomentDamping.G U U) 4 s v ≤
      compactValue (kernel2Upper j) * compactValue (Q2 j) := by
  have hk : RaySpectralCurvature.spectralKernelWeight 4 v ≤
      compactValue (kernel2Upper j) := by
    have hh := actual_kernel2_cell_le j hj (second_open_ratio hv)
    norm_num [RaySpectralCurvature.spectralKernelWeight, compactValue, Sc,
      UpperMomentN47KernelWitnesses.compactScale] at hh ⊢
    exact hh
  have he := actual_power_cell_le j hj ⟨hv.1.le, hv.2.le⟩
  exact mul_le_mul hk he (Real.exp_nonneg _) ((norm_nonneg _).trans hk)

theorem actual_third_cell_le (j : ℕ) (hj : j < 1024) {v : ℝ}
    (hv : v ∈ Ioo (v1 j) (v1 (j + 1))) :
    UpperMomentAbsoluteProfile.third 4 s v ≤
      compactValue (correctionUpper j) * compactValue (E3 j) := by
  have hk : RaySpectralCurvature.spectralCorrectionWeight 4 v ≤
      compactValue (correctionUpper j) := by
    have hh := actual_correction_cell_le j hj (first_open_ratio hv)
    norm_num [RaySpectralCurvature.spectralCorrectionWeight, compactValue, Sc,
      UpperMomentN47KernelWitnesses.compactScale] at hh ⊢
    exact hh
  have he := actual_gaussian_cell_le j hj hv.1.le
  exact mul_le_mul hk he (Real.exp_nonneg _) ((norm_nonneg _).trans hk)

theorem profile_integrable : UpperMomentAbsoluteProfile.ProfileIntegrable
    U (UpperMomentDamping.G U U) (4 / 5) 4 s := by
  apply UpperMomentAbsoluteProfile.profileIntegrable U UpperMomentN47ScalarSemantics.U_pos
    _ (UpperMomentDamping.continuous_G U U) (UpperMomentDamping.G_nonpos U U)
    (4 / 5) 4 s (by norm_num) (by norm_num) s_pos
  norm_num [UpperMomentSpectrumPrice.d, UpperMomentN47ScalarSemantics.U,
    s]

lemma second_integrable : IntervalIntegrable
    (UpperMomentAbsoluteProfile.second (UpperMomentDamping.G U U) 4 s) volume (4 / 5) 4 :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr profile_integrable.second

lemma third_integrable : IntervalIntegrable
    (UpperMomentAbsoluteProfile.third 4 s) volume 0 (4 / 5) :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr profile_integrable.third

lemma second_cell_integrable (j : ℕ) (hj : j < 1024) : IntervalIntegrable
    (UpperMomentAbsoluteProfile.second (UpperMomentDamping.G U U) 4 s) volume
    (v2 j) (v2 (j + 1)) := by
  apply second_integrable.mono_set
  rw [uIcc_of_le (v2_mono (Nat.le_succ j)), uIcc_of_le (by norm_num : (4 / 5 : ℝ) ≤ 4)]
  apply Icc_subset_Icc
  · rw [← v2_zero]; exact v2_mono (Nat.zero_le j)
  · rw [← v2_last]; exact v2_mono (by omega)

lemma third_cell_integrable (j : ℕ) (hj : j < 1024) : IntervalIntegrable
    (UpperMomentAbsoluteProfile.third 4 s) volume (v1 j) (v1 (j + 1)) := by
  apply third_integrable.mono_set
  rw [uIcc_of_le (v1_mono (Nat.le_succ j)), uIcc_of_le (by norm_num : (0 : ℝ) ≤ 4 / 5)]
  apply Icc_subset_Icc
  · exact UpperMomentN47ScalarSemantics.v1_nonneg j
  · rw [← v1_last]; exact v1_mono (by omega)

private lemma integral_le_row {f : ℝ → ℝ} {a b dt : ℝ} {Dt : Box} {k e row : ℤ}
    (hab : a ≤ b) (hint : IntervalIntegrable f volume a b)
    (hdt : Contains scale Dt dt) (hwidth : b - a = dt)
    (hcheck : productCheck Dt (lift18 k) (lift18 e) (lift18 row) = true)
    (hbound : ∀ v ∈ Ioo a b, f v ≤ compactValue k * compactValue e) :
    (∫ v in a..b, f v) ≤ compactValue row := by
  have hm := intervalIntegral.integral_mono_on_of_le_Ioo hab hint
    (intervalIntegrable_const (c := compactValue k * compactValue e)
      (a := a) (b := b) (μ := volume)) hbound
  rw [intervalIntegral.integral_const, smul_eq_mul] at hm
  have hp := productCheck_sound hdt hcheck
  simp only [val_lift18] at hp
  calc
    _ ≤ (b - a) * (compactValue k * compactValue e) := hm
    _ = dt * compactValue k * compactValue e := by rw [hwidth]; ring
    _ ≤ compactValue row := hp

theorem actual_second_cell_integral_le (j : ℕ) (hj : j < 1024) :
    (∫ v in v2 j..v2 (j + 1),
      UpperMomentAbsoluteProfile.second (UpperMomentDamping.G U U) 4 s v) ≤
        compactValue (row2Upper j) :=
  integral_le_row (v2_mono (Nat.le_succ j)) (second_cell_integrable j hj)
    contains_dt2 (UpperMomentN47ScalarSemantics.v2_width j)
    (product2_row_checked j hj) (fun _ hv => actual_second_cell_le j hj hv)

theorem actual_third_cell_integral_le (j : ℕ) (hj : j < 1024) :
    (∫ v in v1 j..v1 (j + 1), UpperMomentAbsoluteProfile.third 4 s v) ≤
      compactValue (row3Upper j) :=
  integral_le_row (v1_mono (Nat.le_succ j)) (third_cell_integrable j hj)
    contains_dt1 (UpperMomentN47ScalarSemantics.v1_width j)
    (product3_row_checked j hj) (fun _ hv => actual_third_cell_le j hj hv)

private lemma list_sum_as_range (xs : List ℤ) :
    (∑ j ∈ Finset.range xs.length, (xs.getD j 0 : ℝ)) = (xs.sum : ℝ) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simpa [Finset.sum_range_succ', add_comm] using
      congrArg (fun y : ℝ => (x : ℝ) + y) ih

lemma compact_sum_as_range (xs : List ℤ) :
    (∑ j ∈ Finset.range xs.length, compactValue (xs.getD j 0)) =
      (xs.sum : ℝ) / 10 ^ 18 := by
  simp only [compactValue, ← Finset.sum_div]
  rw [list_sum_as_range]

theorem actual_second_interval_integral_le_rows :
    (∫ v in (4 / 5 : ℝ)..4,
      UpperMomentAbsoluteProfile.second (UpperMomentDamping.G U U) 4 s v) ≤
        (row218.sum : ℝ) / 10 ^ 18 := by
  have hs := intervalIntegral.sum_integral_adjacent_intervals
    (fun j hj => second_cell_integrable j hj)
  rw [v2_zero, v2_last] at hs
  rw [← hs]
  calc
    _ ≤ ∑ j ∈ Finset.range 1024, compactValue (row2Upper j) := by
      apply Finset.sum_le_sum
      intro j hj
      exact actual_second_cell_integral_le j (Finset.mem_range.mp hj)
    _ = _ := by
      rw [← compact_sum_as_range row218, row218_length]
      rfl

theorem actual_third_interval_integral_le_rows :
    (∫ v in (0 : ℝ)..(4 / 5), UpperMomentAbsoluteProfile.third 4 s v) ≤
      (row318.sum : ℝ) / 10 ^ 18 := by
  have hs := intervalIntegral.sum_integral_adjacent_intervals
    (fun j hj => third_cell_integrable j hj)
  rw [v1_zero, v1_last] at hs
  rw [← hs]
  calc
    _ ≤ ∑ j ∈ Finset.range 1024, compactValue (row3Upper j) := by
      apply Finset.sum_le_sum
      intro j hj
      exact actual_third_cell_integral_le j (Finset.mem_range.mp hj)
    _ = _ := by
      rw [← compact_sum_as_range row318, row318_length]
      rfl

/-- The actual second Ioc integral, including the final cell whose kernel
license is only open at v=4. The endpoint is removed by Lebesgue integration. -/
theorem actual_second_integral_le_rows :
    (∫ v in Ioc (4 / 5 : ℝ) 4,
      UpperMomentAbsoluteProfile.second (UpperMomentDamping.G U U) 4 s v) ≤
        (row218.sum : ℝ) / 10 ^ 18 := by
  simpa only [intervalIntegral.integral_of_le (by norm_num : (4 / 5 : ℝ) ≤ 4)] using
    actual_second_interval_integral_le_rows

/-- The true correction integral uses the same capped correction witnesses
and Gaussian bounds on every open cell. -/
theorem actual_third_integral_le_rows :
    (∫ v in Ioc (0 : ℝ) (4 / 5), UpperMomentAbsoluteProfile.third 4 s v) ≤
      (row318.sum : ℝ) / 10 ^ 18 := by
  simpa only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 4 / 5)] using
    actual_third_interval_integral_le_rows

end BerryEsseen.UpperMomentNu235RemainingIntegrals

#print axioms BerryEsseen.UpperMomentNu235RemainingIntegrals.actual_power_cell_le
#print axioms BerryEsseen.UpperMomentNu235RemainingIntegrals.actual_gaussian_cell_le
#print axioms BerryEsseen.UpperMomentNu235RemainingIntegrals.actual_second_integral_le_rows
#print axioms BerryEsseen.UpperMomentNu235RemainingIntegrals.actual_third_integral_le_rows
