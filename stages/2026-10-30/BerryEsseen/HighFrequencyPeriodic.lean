module

public import BerryEsseen.HighFrequencyCells
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

@[expose] public section

/-! 2026-10-28: the entire nonzero periodic region. The countable core union
and its complement partition x>1/2. This is a fixed-distance calculation,
not an average over a probability-law event; the zero cell is separate. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators Interval
open BerryEsseen.HighFrequencyCells

namespace BerryEsseen.HighFrequencyPeriodic

def center (k : ℕ) : ℝ := (k : ℝ) + 1
def coreCell (w : ℝ) (k : ℕ) : Set ℝ := Icc (center k - w) (center k + w)
def coreUnion (w : ℝ) : Set ℝ := ⋃ k : ℕ, coreCell w k
def wings (w : ℝ) : Set ℝ := Ioi (1 / 2 : ℝ) \ coreUnion w
def inverseCube (x : ℝ) : ℝ := 1 / x ^ 3
def periodicIntegrand (q x : ℝ) : ℝ := Real.exp (-q * Real.sin (Real.pi * x) ^ 2) / x ^ 3
def cubicSeries : ℝ := ∑' k : ℕ, 1 / center k ^ 3
def fifthSeries (w : ℝ) : ℝ := ∑' k : ℕ, 1 / (center k - w) ^ 5

lemma center_ge_one (k : ℕ) : 1 ≤ center k := by unfold center; exact le_add_of_nonneg_left (Nat.cast_nonneg k)

lemma summable_cubic : Summable (fun k : ℕ => 1 / center k ^ 3) := by
  have hs : Summable (fun k : ℕ => 1 / (k : ℝ) ^ 3) := Real.summable_one_div_nat_pow.mpr (by decide)
  simpa only [Function.comp_def, center, Nat.cast_add, Nat.cast_one, Nat.succ_eq_add_one] using
    hs.comp_injective Nat.succ_injective

lemma summable_fifth (w : ℝ) (hwcap : w ≤ 1 / 4) :
    Summable (fun k : ℕ => 1 / (center k - w) ^ 5) := by
  have hs := (Real.summable_one_div_nat_add_rpow (1 - w) (5 : ℝ)).mpr (by norm_num)
  refine hs.congr fun k => ?_
  have hp : 0 < (k : ℝ) + (1 - w) := by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ (k : ℝ))]
  rw [abs_of_pos hp, Real.rpow_ofNat]
  unfold center
  congr 2
  ring

lemma integrableOn_inverseCube (b : ℝ) (hb : 0 < b) : IntegrableOn inverseCube (Ioi b) := by
  have hi := integrableOn_Ioi_rpow_of_lt (a := (-3 : ℝ)) (by norm_num) hb
  refine hi.congr_fun (fun x hx => ?_) measurableSet_Ioi
  have hx0 : 0 ≤ x := (hb.trans hx).le
  simp only [inverseCube, Real.rpow_neg hx0, Real.rpow_ofNat, one_div]

lemma integral_inverseCube (b : ℝ) (hb : 0 < b) :
    (∫ x in Ioi b, inverseCube x) = 1 / (2 * b ^ 2) := by
  calc
    _ = ∫ x in Ioi b, x ^ (-3 : ℝ) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      have hx0 : 0 ≤ x := (hb.trans hx).le
      simp only [inverseCube, Real.rpow_neg hx0, Real.rpow_ofNat, one_div]
    _ = _ := by
      rw [integral_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) hb]
      norm_num only [show (-3 : ℝ) + 1 = -2 by norm_num]
      rw [Real.rpow_neg hb.le, Real.rpow_two]
      ring

lemma periodicIntegrand_nonneg (q x : ℝ) (hx : 0 ≤ x) : 0 ≤ periodicIntegrand q x := by
  unfold periodicIntegrand
  positivity

lemma periodicIntegrand_le_inverseCube (q x : ℝ) (hq : 0 ≤ q) (hx : 0 ≤ x) :
    periodicIntegrand q x ≤ inverseCube x := by
  unfold periodicIntegrand inverseCube
  apply div_le_div_of_nonneg_right _ (pow_nonneg hx 3)
  apply Real.exp_le_one_iff.mpr
  nlinarith [mul_nonneg hq (sq_nonneg (Real.sin (Real.pi * x)))]

lemma integrableOn_periodicIntegrand (q b : ℝ) (hq : 0 ≤ q) (hb : 0 < b) :
    IntegrableOn (periodicIntegrand q) (Ioi b) := by
  have hm : Measurable (periodicIntegrand q) := by unfold periodicIntegrand; fun_prop
  apply (integrableOn_inverseCube b hb).mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : 0 ≤ x := (hb.trans hx).le
  rw [Real.norm_eq_abs, abs_of_nonneg (periodicIntegrand_nonneg q x hx0)]
  exact periodicIntegrand_le_inverseCube q x hq hx0

lemma measurableSet_coreUnion (w : ℝ) : MeasurableSet (coreUnion w) :=
  MeasurableSet.iUnion fun _ => measurableSet_Icc

lemma coreUnion_subset (w : ℝ) (hwcap : w ≤ 1 / 4) : coreUnion w ⊆ Ioi (1 / 2 : ℝ) := by
  intro x hx
  rcases mem_iUnion.mp hx with ⟨k, hk⟩
  dsimp only [coreCell] at hk
  have hc := center_ge_one k
  change 1 / 2 < x
  linarith [hk.1]

lemma coreCells_pairwise_disjoint (w : ℝ) (hwcap : w ≤ 1 / 4) :
    Pairwise (fun k l => Disjoint (coreCell w k) (coreCell w l)) := by
  intro k l hkl
  apply disjoint_left.mpr
  intro x hk hl
  dsimp only [coreCell, center] at hk hl
  rcases lt_or_gt_of_ne hkl with hlt | hgt
  · have hstep : (k : ℝ) + 1 ≤ l := by exact_mod_cast Nat.succ_le_of_lt hlt
    linarith [hk.2, hl.1]
  · have hstep : (l : ℝ) + 1 ≤ k := by exact_mod_cast Nat.succ_le_of_lt hgt
    linarith [hl.2, hk.1]

lemma sin_sq_shift (k : ℕ) (v : ℝ) :
    Real.sin (Real.pi * (center k + v)) ^ 2 = Real.sin (Real.pi * v) ^ 2 := by
  have heq : Real.pi * (center k + v) = Real.pi * v + (k + 1 : ℕ) * Real.pi := by
    unfold center
    push_cast
    ring
  rw [heq, Real.sin_add_nat_mul_pi, mul_pow]
  have hs : ((-1 : ℝ) ^ (k + 1)) ^ 2 = 1 := by
    rw [← sq_abs, abs_neg_one_pow]
    norm_num
  rw [hs, one_mul]

lemma integral_coreCell_shift (q w : ℝ) (k : ℕ) (hw : 0 ≤ w) :
    (∫ x in coreCell w k, periodicIntegrand q x) =
      ∫ v in Icc (-w) w, Real.exp (-q * Real.sin (Real.pi * v) ^ 2) / (center k + v) ^ 3 := by
  have heq : (fun v => periodicIntegrand q (center k + v)) =
      (fun v => Real.exp (-q * Real.sin (Real.pi * v) ^ 2) / (center k + v) ^ 3) := by
    ext v
    unfold periodicIntegrand
    rw [sin_sq_shift]
  unfold coreCell
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith : center k - w ≤ center k + w)]
  have htranslate := intervalIntegral.integral_comp_add_left (f := periodicIntegrand q)
    (a := -w) (b := w) (center k)
  rw [show center k + (-w) = center k - w by ring] at htranslate
  rw [← htranslate]
  rw [heq]
  rw [intervalIntegral.integral_of_le (by linarith : -w ≤ w), ← integral_Icc_eq_integral_Ioc]

lemma coreCell_cost (q w : ℝ) (k : ℕ) (hq : 0 < q) (hw : 0 < w) (hwcap : w ≤ 1 / 4) :
    (∫ x in coreCell w k, periodicIntegrand q x) ≤
      Real.sqrt (Real.pi / (q * sineSlope w ^ 2)) *
        (1 / center k ^ 3 + (3 / (q * sineSlope w ^ 2)) / (center k - w) ^ 5) := by
  have hh := sineSlope_pos w hw.le hwcap
  have hr : 0 < q * sineSlope w ^ 2 := mul_pos hq (sq_pos_of_pos hh)
  have hj := center_ge_one k
  have hiG := (nonzero_cell_cost (center k) (q * sineSlope w ^ 2) w hj hr hw hwcap)
  have hiS : IntegrableOn
      (fun v => Real.exp (-q * Real.sin (Real.pi * v) ^ 2) / (center k + v) ^ 3) (Icc (-w) w) := by
    apply ContinuousOn.integrableOn_Icc
    apply (by fun_prop : ContinuousOn
      (fun v : ℝ => Real.exp (-q * Real.sin (Real.pi * v) ^ 2)) (Icc (-w) w)).div (by fun_prop)
    intro v hv
    exact pow_ne_zero 3 (ne_of_gt (by linarith [hv.1] : 0 < center k + v))
  rw [integral_coreCell_shift q w k hw.le]
  calc
    _ ≤ ∫ v in Icc (-w) w, cellIntegrand (center k) (q * sineSlope w ^ 2) v := by
      apply setIntegral_mono_on hiS hiG.1 measurableSet_Icc
      intro v hv
      have hvabs : |v| ≤ w := abs_le.mpr hv
      have hb := core_sine_bound w v hw hwcap hvabs
      have hsq := (sq_le_sq₀ (mul_nonneg hh.le (abs_nonneg v)) (abs_nonneg _)).mpr hb
      have hmul := mul_le_mul_of_nonneg_left hsq hq.le
      have he : -q * Real.sin (Real.pi * v) ^ 2 ≤ -(q * sineSlope w ^ 2 * v ^ 2) := by
        simp only [mul_pow, sq_abs] at hmul
        nlinarith only [hmul]
      exact div_le_div_of_nonneg_right (Real.exp_le_exp.mpr he)
        (pow_nonneg (by linarith [hv.1] : 0 ≤ center k + v) 3)
    _ ≤ _ := hiG.2

/-- Actual summation over the measurable disjoint infinite core union. -/
theorem coreUnion_cost (q w : ℝ) (hq : 0 < q) (hw : 0 < w) (hwcap : w ≤ 1 / 4) :
    IntegrableOn (periodicIntegrand q) (coreUnion w) ∧
      (∫ x in coreUnion w, periodicIntegrand q x) ≤
        Real.sqrt (Real.pi / (q * sineSlope w ^ 2)) *
          (cubicSeries + (3 / (q * sineSlope w ^ 2)) * fifthSeries w) := by
  have hi := (integrableOn_periodicIntegrand q (1 / 2) hq.le (by norm_num)).mono_set (coreUnion_subset w hwcap)
  have hsI := (hasSum_integral_iUnion (fun k => (measurableSet_Icc : MeasurableSet (coreCell w k)))
    (coreCells_pairwise_disjoint w hwcap) hi).summable
  have h3 := summable_cubic
  have h5 := summable_fifth w hwcap
  have hsP := (h3.add (h5.mul_left (3 / (q * sineSlope w ^ 2)))).mul_left
    (Real.sqrt (Real.pi / (q * sineSlope w ^ 2)))
  have hsP' : Summable (fun k : ℕ => Real.sqrt (Real.pi / (q * sineSlope w ^ 2)) *
      (1 / center k ^ 3 + (3 / (q * sineSlope w ^ 2)) / (center k - w) ^ 5)) := by
    simpa only [mul_one_div] using hsP
  refine ⟨hi, ?_⟩
  change (∫ x in ⋃ k : ℕ, Icc (center k - w) (center k + w), periodicIntegrand q x) ≤ _
  rw [integral_iUnion (fun k => (measurableSet_Icc : MeasurableSet (coreCell w k)))
    (coreCells_pairwise_disjoint w hwcap) hi]
  have hsum := Summable.tsum_le_tsum (fun k => coreCell_cost q w k hq hw hwcap) hsI hsP'
  have hnorm : (∑' k : ℕ, Real.sqrt (Real.pi / (q * sineSlope w ^ 2)) *
      (1 / center k ^ 3 + (3 / (q * sineSlope w ^ 2)) / (center k - w) ^ 5)) =
      Real.sqrt (Real.pi / (q * sineSlope w ^ 2)) *
        (cubicSeries + (3 / (q * sineSlope w ^ 2)) * fifthSeries w) := by
    rw [tsum_mul_left]
    congr 1
    have hterms : (fun k : ℕ => 1 / center k ^ 3 +
        (3 / (q * sineSlope w ^ 2)) / (center k - w) ^ 5) =
        (fun k : ℕ => 1 / center k ^ 3 +
        (3 / (q * sineSlope w ^ 2)) * (1 / (center k - w) ^ 5)) := by
      funext k
      ring
    rw [hterms, (h3.tsum_add (h5.mul_left (3 / (q * sineSlope w ^ 2)))), tsum_mul_left]
    rfl
  exact hsum.trans_eq hnorm

/-- Every point of x>1/2 has an actual nearest positive integer center. -/
lemma exists_nearest_center (x : ℝ) (hx : 1 / 2 < x) :
    ∃ k : ℕ, |x - center k| ≤ 1 / 2 := by
  let m : ℕ := Nat.floor (x + 1 / 2)
  have hm : 1 ≤ m := Nat.le_floor (by
    simpa only [Nat.cast_one] using (show (1 : ℝ) ≤ x + 1 / 2 by linarith))
  have hmEq : m - 1 + 1 = m := Nat.sub_add_cancel hm
  have hc : center (m - 1) = (m : ℝ) := by unfold center; exact_mod_cast hmEq
  have hlo : (m : ℝ) ≤ x + 1 / 2 := Nat.floor_le (by linarith : 0 ≤ x + 1 / 2)
  have hhi : x + 1 / 2 < (m : ℝ) + 1 := Nat.lt_floor_add_one _
  refine ⟨m - 1, ?_⟩
  rw [hc]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

lemma wing_sine_sq (w x : ℝ) (hw : 0 < w) (hwcap : w ≤ 1 / 4) (hx : x ∈ wings w) :
    sineSlope w ^ 2 * w ^ 2 ≤ Real.sin (Real.pi * x) ^ 2 := by
  rcases exists_nearest_center x hx.1 with ⟨k, hk⟩
  have hl : w ≤ |x - center k| := by
    by_contra h
    have hab := abs_lt.mp (lt_of_not_ge h)
    apply hx.2
    exact mem_iUnion.mpr ⟨k, ⟨by linarith [hab.1], by linarith [hab.2]⟩⟩
  have hh := sineSlope_pos w hw.le hwcap
  have hb := wing_sine_bound w (x - center k) hw hwcap hl hk
  have hsq := (sq_le_sq₀ (mul_nonneg hh.le hw.le) (abs_nonneg _)).mpr hb
  rw [sq_abs] at hsq
  have hs := sin_sq_shift k (x - center k)
  rw [show center k + (x - center k) = x by ring] at hs
  rw [← hs] at hsq
  nlinarith only [hsq]

/-- Wings are charged once against the total inverse-cube mass, not once per cell. -/
theorem wings_cost (q w : ℝ) (hq : 0 < q) (hw : 0 < w) (hwcap : w ≤ 1 / 4) :
    IntegrableOn (periodicIntegrand q) (wings w) ∧
      (∫ x in wings w, periodicIntegrand q x) ≤ 2 * Real.exp (-q * sineSlope w ^ 2 * w ^ 2) := by
  have hiAll := integrableOn_periodicIntegrand q (1 / 2) hq.le (by norm_num)
  have hi : IntegrableOn (periodicIntegrand q) (wings w) := hiAll.mono_set sdiff_subset
  let C := Real.exp (-q * sineSlope w ^ 2 * w ^ 2)
  have hC : 0 ≤ C := (Real.exp_pos _).le
  have hMajor : IntegrableOn (fun x => C * inverseCube x) (Ioi (1 / 2 : ℝ)) :=
    (integrableOn_inverseCube (1 / 2) (by norm_num)).const_mul C
  have hM := hMajor.mono_set (show wings w ⊆ Ioi (1 / 2 : ℝ) from sdiff_subset)
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ x in wings w, C * inverseCube x := by
      apply setIntegral_mono_on hi hM (measurableSet_Ioi.diff (measurableSet_coreUnion w))
      intro x hx
      have hs := mul_le_mul_of_nonneg_left (wing_sine_sq w x hw hwcap hx) hq.le
      have he : -q * Real.sin (Real.pi * x) ^ 2 ≤ -q * sineSlope w ^ 2 * w ^ 2 := by nlinarith only [hs]
      have hxhalf : (1 / 2 : ℝ) < x := hx.1
      have hx0 : 0 ≤ x := by linarith
      have hdiv := div_le_div_of_nonneg_right (Real.exp_le_exp.mpr he)
        (pow_nonneg hx0 3)
      simpa only [periodicIntegrand, inverseCube, mul_one_div] using hdiv
    _ ≤ ∫ x in Ioi (1 / 2 : ℝ), C * inverseCube x := by
      apply setIntegral_mono_set hMajor
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        have hxhalf : (1 / 2 : ℝ) < x := hx
        have hx0 : 0 ≤ x := by linarith
        exact mul_nonneg hC (div_nonneg zero_le_one (pow_nonneg hx0 3))
      · exact Eventually.of_forall fun _ hx => hx.1
    _ = 2 * C := by rw [integral_const_mul, integral_inverseCube (1 / 2) (by norm_num)]; norm_num; ring

/-- The complete nonzero periodic region x>1/2, with genuine L¹ and convergent series. -/
theorem nonzero_region_cost (q w : ℝ) (hq : 0 < q) (hw : 0 < w) (hwcap : w ≤ 1 / 4) :
    IntegrableOn (periodicIntegrand q) (Ioi (1 / 2 : ℝ)) ∧
      (∫ x in Ioi (1 / 2 : ℝ), periodicIntegrand q x) ≤
        Real.sqrt (Real.pi / (q * sineSlope w ^ 2)) *
          (cubicSeries + (3 / (q * sineSlope w ^ 2)) * fifthSeries w) +
          2 * Real.exp (-q * sineSlope w ^ 2 * w ^ 2) := by
  have hi := integrableOn_periodicIntegrand q (1 / 2) hq.le (by norm_num)
  have hc := coreUnion_cost q w hq hw hwcap
  have hwg := wings_cost q w hq hw hwcap
  have hsplit := setIntegral_sdiff (measurableSet_coreUnion w) hi (coreUnion_subset w hwcap)
  refine ⟨hi, ?_⟩
  change (∫ x in wings w, periodicIntegrand q x) = _ at hsplit
  linarith [hc.2, hwg.2]

def frequencyScale (D : ℝ) : ℝ := D / (2 * Real.pi)
def fixedDistanceIntegrand (n : ℕ) (a D t : ℝ) : ℝ :=
  Real.exp (-(n : ℝ) * a * Real.sin (t * D / 2) ^ 2) / t ^ 3

lemma frequencyScale_pos (D : ℝ) (hD : 0 < D) : 0 < frequencyScale D :=
  div_pos hD (mul_pos (by norm_num) Real.pi_pos)

lemma frequencyScale_threshold (D : ℝ) (hD : 0 < D) :
    frequencyScale D * (Real.pi / D) = 1 / 2 := by
  unfold frequencyScale
  field_simp [ne_of_gt hD, Real.pi_ne_zero]

lemma fixedDistanceIntegrand_scale (n : ℕ) (a D t : ℝ) (hD : 0 < D) :
    fixedDistanceIntegrand n a D t = frequencyScale D ^ 3 *
      periodicIntegrand ((n : ℝ) * a) (frequencyScale D * t) := by
  have hβ := frequencyScale_pos D hD
  have harg : Real.pi * (frequencyScale D * t) = t * D / 2 := by
    unfold frequencyScale
    field_simp [Real.pi_ne_zero]
  unfold fixedDistanceIntegrand periodicIntegrand
  rw [harg]
  simp only [neg_mul]
  symm
  rw [← mul_div_assoc, mul_pow]
  exact mul_div_mul_left _ _ (pow_ne_zero 3 (ne_of_gt hβ))

/-- The true frequency substitution and its D²/(4π²) inverse-cube Jacobian. -/
lemma fixedDistance_integral_scale (n : ℕ) (a D : ℝ) (hD : 0 < D) :
    (∫ t in Ioi (Real.pi / D), fixedDistanceIntegrand n a D t) =
      frequencyScale D ^ 2 * (∫ x in Ioi (1 / 2 : ℝ), periodicIntegrand ((n : ℝ) * a) x) := by
  have hβ := frequencyScale_pos D hD
  have heq : fixedDistanceIntegrand n a D = (fun t => frequencyScale D ^ 3 *
      periodicIntegrand ((n : ℝ) * a) (frequencyScale D * t)) :=
    funext fun t => fixedDistanceIntegrand_scale n a D t hD
  rw [heq, integral_const_mul, integral_comp_mul_left_Ioi _ _ hβ,
    frequencyScale_threshold D hD, smul_eq_mul]
  field_simp [ne_of_gt hβ]

lemma pi_three_halves : Real.pi ^ (3 / 2 : ℝ) = Real.pi * Real.sqrt Real.pi := by
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add Real.pi_pos,
    Real.rpow_one, ← Real.sqrt_eq_rpow]

lemma fixedDistance_core_coefficient (n : ℕ) (hn : 0 < n) (a D h : ℝ)
    (ha : 0 < a) (hh : 0 < h) :
    Real.sqrt n * frequencyScale D ^ 2 * Real.sqrt (Real.pi / ((n : ℝ) * a * h ^ 2)) =
      D ^ 2 / (4 * Real.pi ^ (3 / 2 : ℝ) * h * Real.sqrt a) := by
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  rw [Real.sqrt_div Real.pi_nonneg, Real.sqrt_mul (mul_nonneg hnR.le ha.le),
    Real.sqrt_mul hnR.le, Real.sqrt_sq_eq_abs, abs_of_pos hh, pi_three_halves]
  unfold frequencyScale
  field_simp [ne_of_gt (Real.sqrt_pos.mpr hnR), ne_of_gt (Real.sqrt_pos.mpr ha),
    ne_of_gt hh, Real.pi_ne_zero, ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)]
  ring_nf
  norm_num [Real.sq_sqrt Real.pi_nonneg]

lemma fixedDistance_wing_coefficient (n : ℕ) (D : ℝ) :
    Real.sqrt n * frequencyScale D ^ 2 * 2 = D ^ 2 * Real.sqrt n / (2 * Real.pi ^ 2) := by
  unfold frequencyScale
  field_simp [Real.pi_ne_zero]

/-- The entire nonzero-cell tail t>π/D, retaining the original two prices.
No claim about the zero cell or conditional averaging is made here. -/
theorem fixedDistance_nonzero_tail (n : ℕ) (hn : 0 < n) (a D w : ℝ)
    (ha : 0 < a) (hD : 0 < D) (hw : 0 < w) (hwcap : w ≤ 1 / 4) :
    IntegrableOn (fixedDistanceIntegrand n a D) (Ioi (Real.pi / D)) ∧
      Real.sqrt n * (∫ t in Ioi (Real.pi / D), fixedDistanceIntegrand n a D t) ≤
        D ^ 2 / (4 * Real.pi ^ (3 / 2 : ℝ) * sineSlope w * Real.sqrt a) *
          (cubicSeries + (3 / ((n : ℝ) * a * sineSlope w ^ 2)) * fifthSeries w) +
        D ^ 2 * Real.sqrt n / (2 * Real.pi ^ 2) *
          Real.exp (-((n : ℝ) * a) * sineSlope w ^ 2 * w ^ 2) := by
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hdim := nonzero_region_cost ((n : ℝ) * a) w (mul_pos hnR ha) hw hwcap
  have hβ := frequencyScale_pos D hD
  have hcomp : IntegrableOn
      (fun t => periodicIntegrand ((n : ℝ) * a) (frequencyScale D * t)) (Ioi (Real.pi / D)) := by
    apply (integrableOn_Ioi_comp_mul_left_iff _ _ hβ).mpr
    simpa only [frequencyScale_threshold D hD] using hdim.1
  have hi : IntegrableOn (fixedDistanceIntegrand n a D) (Ioi (Real.pi / D)) := by
    have heq : fixedDistanceIntegrand n a D = (fun t => frequencyScale D ^ 3 *
        periodicIntegrand ((n : ℝ) * a) (frequencyScale D * t)) :=
      funext fun t => fixedDistanceIntegrand_scale n a D t hD
    rw [heq]
    exact hcomp.const_mul _
  refine ⟨hi, ?_⟩
  rw [fixedDistance_integral_scale n a D hD]
  have hbound := mul_le_mul_of_nonneg_left hdim.2
    (mul_nonneg (Real.sqrt_nonneg (n : ℝ)) (sq_nonneg (frequencyScale D)))
  have hcoeff := fixedDistance_core_coefficient n hn a D (sineSlope w) ha (sineSlope_pos w hw.le hwcap)
  have hwcoeff := fixedDistance_wing_coefficient n D
  calc
    _ = (Real.sqrt n * frequencyScale D ^ 2) *
        (∫ x in Ioi (1 / 2 : ℝ), periodicIntegrand ((n : ℝ) * a) x) := by ring
    _ ≤ (Real.sqrt n * frequencyScale D ^ 2) *
        (Real.sqrt (Real.pi / ((n : ℝ) * a * sineSlope w ^ 2)) *
          (cubicSeries + (3 / ((n : ℝ) * a * sineSlope w ^ 2)) * fifthSeries w) +
          2 * Real.exp (-((n : ℝ) * a) * sineSlope w ^ 2 * w ^ 2)) := hbound
    _ = _ := by
      calc
        _ = (Real.sqrt n * frequencyScale D ^ 2 *
            Real.sqrt (Real.pi / ((n : ℝ) * a * sineSlope w ^ 2))) *
              (cubicSeries + (3 / ((n : ℝ) * a * sineSlope w ^ 2)) * fifthSeries w) +
            (Real.sqrt n * frequencyScale D ^ 2 * 2) *
              Real.exp (-((n : ℝ) * a) * sineSlope w ^ 2 * w ^ 2) := by ring
        _ = _ := by rw [hcoeff, hwcoeff]

end BerryEsseen.HighFrequencyPeriodic

#print axioms BerryEsseen.HighFrequencyPeriodic.summable_cubic
#print axioms BerryEsseen.HighFrequencyPeriodic.summable_fifth
#print axioms BerryEsseen.HighFrequencyPeriodic.coreUnion_cost
#print axioms BerryEsseen.HighFrequencyPeriodic.wings_cost
#print axioms BerryEsseen.HighFrequencyPeriodic.nonzero_region_cost
#print axioms BerryEsseen.HighFrequencyPeriodic.fixedDistance_integral_scale
#print axioms BerryEsseen.HighFrequencyPeriodic.fixedDistance_nonzero_tail
