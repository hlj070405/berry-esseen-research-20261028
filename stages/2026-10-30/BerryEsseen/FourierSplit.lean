module

public import BerryEsseen.LowFrequencyCancellation
public import BerryEsseen.HighFrequencyDamping
public import BerryEsseen.HighFrequencyComparator
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

@[expose] public section

/-! 2026-10-28: the actual Fourier remainder across the original low/high
split. The CF, Gaussian-cubic comparator and phase are identified literally.
The Gaussian comparator is retained on the entire high ray, and all signed
and absolute integral comparisons have actual L1 proofs. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter

namespace BerryEsseen.FourierSplit

open CharacteristicExpansion

theorem gaussianComparator_eq_actualComparator (μ : ProbabilityMeasure ℝ) (n : ℕ) (t : ℝ) :
    LowFrequencyLeading.gaussianComparator μ n t = HighFrequencyComparator.actualComparator μ n t := by
  rw [LowFrequencyLeading.gaussianComparator_eq_original,
    HighFrequencyComparator.actualComparator_eq_original]
  rw [show gamma μ = FourierRemainder.thirdMoment μ from rfl]
  congr 1
  push_cast
  ring

theorem actualV_eq_actualDifference (μ : ProbabilityMeasure ℝ) (n : ℕ) (t : ℝ) :
    LowFrequencyLeading.actualV μ n t = charFun (μ : Measure ℝ) t ^ n -
      HighFrequencyComparator.actualComparator μ n t := by
  unfold LowFrequencyLeading.actualV
  rw [gaussianComparator_eq_actualComparator]

/-- Exact original phase and comparator, with no reflection of H or gamma. -/
theorem originalIntegrand_eq_low_signed (μ : ProbabilityMeasure ℝ) (n : ℕ) (H t : ℝ) :
    FourierRemainder.originalIntegrand μ n H t =
      (pureExp (-(H * t)) * LowFrequencyLeading.actualV μ n t).im / t ^ 3 := by
  rw [HighFrequencyComparator.originalIntegrand_eq,
    ← LowFrequencyLeading.phase_eq_original, ← actualV_eq_actualDifference]

theorem original_abs_eq_lowIntegrand (μ : ProbabilityMeasure ℝ) (n : ℕ) (H t : ℝ)
    (ht : 0 < t) :
    |FourierRemainder.originalIntegrand μ n H t| = LowFrequencyLeading.lowIntegrand μ n H t := by
  rw [originalIntegrand_eq_low_signed, abs_div, abs_of_pos (pow_pos ht 3)]
  rfl

/-- The actual norm quotient, independent of the unit-modulus phase. -/
def highIntegrand (μ : ProbabilityMeasure ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  ‖LowFrequencyLeading.actualV μ n t‖ / t ^ 3

def Iinf (μ : ProbabilityMeasure ℝ) (n : ℕ) : ℝ :=
  ∫ t in Ioi (1 / 2 : ℝ), highIntegrand μ n t

theorem measurable_highIntegrand (μ : ProbabilityMeasure ℝ) (n : ℕ) :
    Measurable (highIntegrand μ n) := by
  have hf := LowFrequencyError.measurable_actual_charFun μ
  unfold highIntegrand LowFrequencyLeading.actualV LowFrequencyLeading.gaussianComparator
  fun_prop

theorem highIntegrand_nonneg (μ : ProbabilityMeasure ℝ) (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ highIntegrand μ n t := div_nonneg (norm_nonneg _) (pow_nonneg ht 3)

theorem original_abs_le_highIntegrand (μ : ProbabilityMeasure ℝ) (n : ℕ) (H t : ℝ)
    (ht : 0 < t) : |FourierRemainder.originalIntegrand μ n H t| ≤ highIntegrand μ n t := by
  rw [original_abs_eq_lowIntegrand μ n H t ht]
  unfold LowFrequencyLeading.lowIntegrand highIntegrand
  apply div_le_div_of_nonneg_right _ (pow_nonneg ht.le 3)
  calc
    _ ≤ ‖pureExp (-(H * t)) * LowFrequencyLeading.actualV μ n t‖ := Complex.abs_im_le_norm _
    _ = _ := by rw [norm_mul, norm_pureExp, one_mul]

theorem highIntegrand_le_cf_add_comparator (μ : ProbabilityMeasure ℝ) (n : ℕ) (t : ℝ)
    (ht : 0 < t) :
    highIntegrand μ n t ≤ HighFrequencyDamping.initialIntegrand μ n t +
      HighFrequencyComparator.comparatorQuotient μ n t := by
  unfold highIntegrand
  rw [actualV_eq_actualDifference]
  calc
    _ ≤ (‖charFun (μ : Measure ℝ) t ^ n‖ +
        ‖HighFrequencyComparator.actualComparator μ n t‖) / t ^ 3 :=
      div_le_div_of_nonneg_right (norm_sub_le _ _) (pow_nonneg ht.le 3)
    _ = _ := by rw [add_div]; rfl

/-- The non-Gaussian high-ray majorant has its own genuine L1 proof. -/
theorem integrableOn_inverse_cube_ray (b : ℝ) (hb : 0 < b) :
    IntegrableOn (fun t : ℝ => 1 / t ^ 3) (Ioi b) := by
  have hi := integrableOn_Ioi_rpow_of_lt (a := (-3 : ℝ)) (by norm_num) hb
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Real.rpow_neg (hb.trans ht).le, Real.rpow_ofNat]
  simp only [one_div]

theorem integrableOn_cfQuotient_ray (μ : ProbabilityMeasure ℝ) (n : ℕ) (b : ℝ) (hb : 0 < b) :
    IntegrableOn (HighFrequencyDamping.initialIntegrand μ n) (Ioi b) := by
  apply (integrableOn_inverse_cube_ray b hb).mono'
    (HighFrequencyDamping.measurable_initialIntegrand μ n).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 < t := hb.trans ht
  have hnorm : ‖charFun (μ : Measure ℝ) t ^ n‖ ≤ 1 := by
    rw [norm_pow]
    simpa only [one_pow] using
      pow_le_pow_left₀ (norm_nonneg _) (norm_charFun_le_one (μ := (μ : Measure ℝ)) t) n
  rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ HighFrequencyDamping.initialIntegrand μ n t from
    div_nonneg (norm_nonneg _) (pow_nonneg ht0.le 3))]
  exact div_le_div_of_nonneg_right hnorm (pow_nonneg ht0.le 3)

/-- Independent L1 of the true high difference quotient, before integration
of the triangle inequality. Both comparator terms remain present. -/
theorem integrableOn_highIntegrand (μ : ProbabilityMeasure ℝ) (n : ℕ) (hn : 0 < n) :
    IntegrableOn (highIntegrand μ n) (Ioi (1 / 2 : ℝ)) := by
  have hi := (integrableOn_cfQuotient_ray μ n (1 / 2) (by norm_num)).add
    (HighFrequencyComparator.integrableOn_comparatorQuotient μ n hn)
  apply hi.mono' (measurable_highIntegrand μ n).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 < t := lt_trans (by norm_num) ht
  rw [Real.norm_eq_abs, abs_of_nonneg (highIntegrand_nonneg μ n t ht0.le)]
  exact highIntegrand_le_cf_add_comparator μ n t ht0

theorem integrableOn_actualV_div_cube (μ : ProbabilityMeasure ℝ) (n : ℕ) (hn : 0 < n) :
    IntegrableOn (fun t : ℝ => LowFrequencyLeading.actualV μ n t / (t : ℂ) ^ 3)
      (Ioi (1 / 2 : ℝ)) := by
  have hf := LowFrequencyError.measurable_actual_charFun μ
  have hm : Measurable (fun t : ℝ => LowFrequencyLeading.actualV μ n t / (t : ℂ) ^ 3) := by
    unfold LowFrequencyLeading.actualV LowFrequencyLeading.gaussianComparator
    fun_prop
  apply (integrable_norm_iff hm.aestronglyMeasurable).mp
  apply (integrableOn_highIntegrand μ n hn).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 < t := lt_trans (by norm_num) ht
  simp only [highIntegrand, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]

theorem integrableOn_lowIntegrand (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (n : ℕ) (hn : 0 < n) (H : ℝ) :
    IntegrableOn (LowFrequencyLeading.lowIntegrand μ n H) (Ioc (0 : ℝ) (1 / 2)) := by
  have hAbs : IntegrableOn (fun t : ℝ => |FourierRemainder.originalIntegrand μ n H t|) (Ioi 0) :=
    (FourierRemainder.integrable_originalIntegrand μ hμ n hn H).abs
  have hi := hAbs.mono_set (show Ioc (0 : ℝ) (1 / 2) ⊆ Ioi 0 from fun _ ht => ht.1)
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact original_abs_eq_lowIntegrand μ n H t ht.1

/-- Adding the value at zero changes no Lebesgue integral. -/
theorem I0_eq_closed_interval (μ : ProbabilityMeasure ℝ) (n : ℕ) (H : ℝ) :
    LowFrequencyLeading.I0 μ n H =
      ∫ t in Icc (0 : ℝ) (1 / 2), LowFrequencyLeading.lowIntegrand μ n H t := by
  exact integral_Icc_eq_integral_Ioc.symm

/-- Original E_n is bounded by its actual low imaginary quotient and the
actual high norm quotient on their complete original domains. -/
theorem value_le_low_high (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (n : ℕ) (hn : 0 < n) (H : ℝ) :
    |FourierRemainder.value μ n H| ≤ (2 / Real.pi) *
      (Real.sqrt n * LowFrequencyLeading.I0 μ n H + Real.sqrt n * Iinf μ n) := by
  have hAbs : IntegrableOn (fun t : ℝ => |FourierRemainder.originalIntegrand μ n H t|) (Ioi 0) :=
    (FourierRemainder.integrable_originalIntegrand μ hμ n hn H).abs
  have hLow := hAbs.mono_set (show Ioc (0 : ℝ) (1 / 2) ⊆ Ioi 0 from fun _ ht => ht.1)
  have hHigh := hAbs.mono_set (Ioi_subset_Ioi_iff.mpr (by norm_num : (0 : ℝ) ≤ 1 / 2))
  have hsplit := setIntegral_union (s := Ioc (0 : ℝ) (1 / 2)) (t := Ioi (1 / 2 : ℝ))
    Ioc_disjoint_Ioi_same measurableSet_Ioi hLow hHigh
  rw [Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hsplit
  have hloweq : (∫ t in Ioc (0 : ℝ) (1 / 2), |FourierRemainder.originalIntegrand μ n H t|) =
      LowFrequencyLeading.I0 μ n H := by
    unfold LowFrequencyLeading.I0
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact original_abs_eq_lowIntegrand μ n H t ht.1
  have hhighle : (∫ t in Ioi (1 / 2 : ℝ), |FourierRemainder.originalIntegrand μ n H t|) ≤
      Iinf μ n := by
    apply integral_mono_ae hHigh (integrableOn_highIntegrand μ n hn)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact original_abs_le_highIntegrand μ n H t (lt_trans (by norm_num) ht)
  have hb : |∫ t in Ioi (0 : ℝ), FourierRemainder.originalIntegrand μ n H t| ≤
      LowFrequencyLeading.I0 μ n H + Iinf μ n := by
    apply abs_integral_le_integral_abs.trans
    rw [hsplit, hloweq]
    exact add_le_add le_rfl hhighle
  have hp : 0 ≤ 2 * Real.sqrt (n : ℝ) / Real.pi := by positivity
  calc
    _ = (2 * Real.sqrt n / Real.pi) *
        |∫ t in Ioi (0 : ℝ), FourierRemainder.originalIntegrand μ n H t| := by
      rw [FourierRemainder.value, abs_mul, abs_of_nonneg hp]
    _ ≤ (2 * Real.sqrt n / Real.pi) * (LowFrequencyLeading.I0 μ n H + Iinf μ n) :=
      mul_le_mul_of_nonneg_left hb hp
    _ = _ := by ring

theorem cf_integral_split (μ : ProbabilityMeasure ℝ) (n : ℕ) :
    (∫ t in Ioi (1 / 2 : ℝ), HighFrequencyDamping.initialIntegrand μ n t) =
      (∫ t in Icc (1 / 2 : ℝ) HighFrequencyDamping.cutoff,
        HighFrequencyDamping.initialIntegrand μ n t) +
      ∫ t in Ioi HighFrequencyDamping.cutoff, HighFrequencyDamping.initialIntegrand μ n t := by
  have hi := integrableOn_cfQuotient_ray μ n (1 / 2) (by norm_num)
  have hmid := hi.mono_set (show Ioc (1 / 2 : ℝ) HighFrequencyDamping.cutoff ⊆ Ioi (1 / 2) from
    fun _ ht => ht.1)
  have htail := hi.mono_set (Ioi_subset_Ioi_iff.mpr
    (by norm_num [HighFrequencyDamping.cutoff] : (1 / 2 : ℝ) ≤ HighFrequencyDamping.cutoff))
  have hs := setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hmid htail
  rw [Ioc_union_Ioi_eq_Ioi (by norm_num [HighFrequencyDamping.cutoff] :
    (1 / 2 : ℝ) ≤ HighFrequencyDamping.cutoff)] at hs
  rw [integral_Icc_eq_integral_Ioc]
  exact hs

/-- Only the CF is split at .9; the comparator keeps its whole (.5,infinity) ray. -/
theorem Iinf_le_cf_split_add_comparator (μ : ProbabilityMeasure ℝ) (n : ℕ) (hn : 0 < n) :
    Iinf μ n ≤
      (∫ t in Icc (1 / 2 : ℝ) HighFrequencyDamping.cutoff,
        HighFrequencyDamping.initialIntegrand μ n t) +
      (∫ t in Ioi HighFrequencyDamping.cutoff, HighFrequencyDamping.initialIntegrand μ n t) +
      ∫ t in Ioi (1 / 2 : ℝ), HighFrequencyComparator.comparatorQuotient μ n t := by
  have hcf := integrableOn_cfQuotient_ray μ n (1 / 2) (by norm_num)
  have hcomp := HighFrequencyComparator.integrableOn_comparatorQuotient μ n hn
  calc
    _ ≤ ∫ t in Ioi (1 / 2 : ℝ),
        (HighFrequencyDamping.initialIntegrand μ n t +
          HighFrequencyComparator.comparatorQuotient μ n t) := by
      apply integral_mono_ae (integrableOn_highIntegrand μ n hn) (hcf.add hcomp)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact highIntegrand_le_cf_add_comparator μ n t (lt_trans (by norm_num) ht)
    _ = _ := by rw [integral_add hcf hcomp, cf_integral_split]

def KF (n : ℕ) (L0 L2 middlePrice tailPrice compPrice : ℝ) : ℝ :=
  (2 / Real.pi) * (L0 + L2 / Real.sqrt n + middlePrice + tailPrice + compPrice)

def sF (LH : ℝ) : ℝ := 2 * LH / Real.pi

/-- Every price hypothesis is attached to its displayed genuine integral.
This interface assembles certificates; it does not calculate their prices. -/
theorem value_le_affine_envelope (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (n : ℕ) (hn : 0 < n) (H L0 LH L2 middlePrice tailPrice compPrice : ℝ)
    (hlow : Real.sqrt n * LowFrequencyLeading.I0 μ n H ≤ L0 + LH * |H| + L2 / Real.sqrt n)
    (hmiddle : Real.sqrt n * (∫ t in Icc (1 / 2 : ℝ) HighFrequencyDamping.cutoff,
      HighFrequencyDamping.initialIntegrand μ n t) ≤ middlePrice)
    (htail : Real.sqrt n * (∫ t in Ioi HighFrequencyDamping.cutoff,
      HighFrequencyDamping.initialIntegrand μ n t) ≤ tailPrice)
    (hcomp : Real.sqrt n * (∫ t in Ioi (1 / 2 : ℝ),
      HighFrequencyComparator.comparatorQuotient μ n t) ≤ compPrice) :
    |FourierRemainder.value μ n H| ≤ KF n L0 L2 middlePrice tailPrice compPrice + sF LH * |H| := by
  have hhigh : Real.sqrt n * Iinf μ n ≤ middlePrice + tailPrice + compPrice := by
    calc
      _ ≤ Real.sqrt n *
          ((∫ t in Icc (1 / 2 : ℝ) HighFrequencyDamping.cutoff,
            HighFrequencyDamping.initialIntegrand μ n t) +
          (∫ t in Ioi HighFrequencyDamping.cutoff, HighFrequencyDamping.initialIntegrand μ n t) +
          ∫ t in Ioi (1 / 2 : ℝ), HighFrequencyComparator.comparatorQuotient μ n t) :=
        mul_le_mul_of_nonneg_left (Iinf_le_cf_split_add_comparator μ n hn) (Real.sqrt_nonneg _)
      _ = Real.sqrt n * (∫ t in Icc (1 / 2 : ℝ) HighFrequencyDamping.cutoff,
          HighFrequencyDamping.initialIntegrand μ n t) +
          Real.sqrt n * (∫ t in Ioi HighFrequencyDamping.cutoff,
            HighFrequencyDamping.initialIntegrand μ n t) +
          Real.sqrt n * (∫ t in Ioi (1 / 2 : ℝ),
            HighFrequencyComparator.comparatorQuotient μ n t) := by ring
      _ ≤ _ := add_le_add (add_le_add hmiddle htail) hcomp
  calc
    _ ≤ (2 / Real.pi) * (Real.sqrt n * LowFrequencyLeading.I0 μ n H + Real.sqrt n * Iinf μ n) :=
      value_le_low_high μ hμ n hn H
    _ ≤ (2 / Real.pi) * ((L0 + LH * |H| + L2 / Real.sqrt n) +
        (middlePrice + tailPrice + compPrice)) :=
      mul_le_mul_of_nonneg_left (add_le_add hlow hhigh) (by positivity)
    _ = _ := by unfold KF sF; ring

def dampingPrice (n : ℕ) (M : ℝ) : ℝ :=
  2 * Real.sqrt n * Real.exp (-(n : ℝ) * HighFrequencyDamping.dampingRate M)

def comparatorPrice (n : ℕ) (g : ℝ) : ℝ :=
  Real.sqrt n * Real.exp (-(n : ℝ) / 8) *
    (2 * RationalGaussianTail.Lambda ((n : ℝ) / 8) + g / 3)

/-- The already proved middle-CF and whole-comparator prices are actually
applied here. The remaining high-CF tail certificate stays explicit. -/
theorem value_le_affine_with_high_prices (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (h4 : Integrable (fun x : ℝ => x ^ 4) (μ : Measure ℝ))
    (n : ℕ) (hn : 0 < n) (H L0 LH L2 M g tailPrice : ℝ)
    (hlow : Real.sqrt n * LowFrequencyLeading.I0 μ n H ≤ L0 + LH * |H| + L2 / Real.sqrt n)
    (hM4 : moment μ 4 ≤ M) (hMupper : M ≤ 111 / 10) (hg : |gamma μ| ≤ g)
    (htail : Real.sqrt n * (∫ t in Ioi HighFrequencyDamping.cutoff,
      HighFrequencyDamping.initialIntegrand μ n t) ≤ tailPrice) :
    |FourierRemainder.value μ n H| ≤
      KF n L0 L2 (dampingPrice n M) tailPrice (comparatorPrice n g) + sF LH * |H| := by
  have hmiddle := (HighFrequencyDamping.initial_segment_cost μ hμ h4 n hn M hM4 hMupper).2
  have hcomp := HighFrequencyComparator.gaussian_comparator_price μ n hn g hg
  exact value_le_affine_envelope μ hμ n hn H L0 LH L2 (dampingPrice n M) tailPrice
    (comparatorPrice n g) hlow hmiddle htail hcomp

/-- Direct original triangle wiring, preserving n>2, every actual moment
cap and the original unreflected H. The high-CF tail remains a real price input. -/
theorem value_le_triangle_envelope (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (h6 : Integrable (fun x : ℝ => |x| ^ 6) (μ : Measure ℝ)) (n : ℕ) (hn : 2 < n)
    (H g M M6bar aStar Z Iu tailPrice : ℝ) (hg : |gamma μ| ≤ g) (hgcap : g ≤ 37 / 20)
    (hM4 : moment μ 4 ≤ M) (hMupper : M ≤ 111 / 10) (hM6 : sixthMoment μ ≤ M6bar)
    (ha : |quarticCoeff μ| ≤ aStar) (hZ : |fifthCoeff μ| ≤ Z)
    (hIu : LowFrequencyLeading.gaussianMass ≤ Iu)
    (htail : Real.sqrt n * (∫ t in Ioi HighFrequencyDamping.cutoff,
      HighFrequencyDamping.initialIntegrand μ n t) ≤ tailPrice) :
    |FourierRemainder.value μ n H| ≤
      KF n (LowFrequencyLeading.triangleL0 n g aStar Z Iu)
        (LowFrequencyError.coefficientL2 n M g M6bar aStar Z)
        (dampingPrice n M) tailPrice (comparatorPrice n g) +
      sF (LowFrequencyLeading.triangleLH n g aStar Iu) * |H| := by
  have hlow := (LowFrequencyLeading.low_frequency_triangle μ hμ h6 n hn H g M M6bar aStar Z Iu
    hg hgcap hM4 hMupper hM6 ha hZ hIu).2
  exact value_le_affine_with_high_prices μ hμ
    (integrable_moment_of_sixth μ h6 4 (by norm_num)) n (by omega) H _ _ _ M g tailPrice
      hlow hM4 hMupper hg htail

/-- Direct original paired-cancellation wiring. Jstar is certified against
the actual signed c5 of this same law and is never treated as an evaluated price. -/
theorem value_le_paired_envelope (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (h6 : Integrable (fun x : ℝ => |x| ^ 6) (μ : Measure ℝ)) (n : ℕ) (hn : 2 < n)
    (H g M M6bar aStar Z Iu Jstar tailPrice : ℝ) (hg : |gamma μ| ≤ g) (hgcap : g ≤ 37 / 20)
    (hM4 : moment μ 4 ≤ M) (hMupper : M ≤ 111 / 10) (hM6 : sixthMoment μ ≤ M6bar)
    (ha : |quarticCoeff μ| ≤ aStar) (hZ : |fifthCoeff μ| ≤ Z)
    (hIu : LowFrequencyLeading.gaussianMass ≤ Iu)
    (hJ : LowFrequencyCancellation.J (fifthCoeff μ) (LowFrequencyCancellation.actualC5 μ) ≤ Jstar)
    (htail : Real.sqrt n * (∫ t in Ioi HighFrequencyDamping.cutoff,
      HighFrequencyDamping.initialIntegrand μ n t) ≤ tailPrice) :
    |FourierRemainder.value μ n H| ≤
      KF n (LowFrequencyCancellation.pairedL0 n g aStar Z Iu Jstar)
        (LowFrequencyError.coefficientL2 n M g M6bar aStar Z)
        (dampingPrice n M) tailPrice (comparatorPrice n g) +
      sF (LowFrequencyCancellation.pairedLH n g aStar Z Iu) * |H| := by
  have hlow := (LowFrequencyCancellation.low_frequency_paired μ hμ h6 n hn H g M M6bar aStar Z Iu Jstar
    hg hgcap hM4 hMupper hM6 ha hZ hIu hJ).2
  exact value_le_affine_with_high_prices μ hμ
    (integrable_moment_of_sixth μ h6 4 (by norm_num)) n (by omega) H _ _ _ M g tailPrice
      hlow hM4 hMupper hg htail

end BerryEsseen.FourierSplit

#print axioms BerryEsseen.FourierSplit.gaussianComparator_eq_actualComparator
#print axioms BerryEsseen.FourierSplit.integrableOn_highIntegrand
#print axioms BerryEsseen.FourierSplit.integrableOn_actualV_div_cube
#print axioms BerryEsseen.FourierSplit.value_le_low_high
#print axioms BerryEsseen.FourierSplit.value_le_affine_envelope
#print axioms BerryEsseen.FourierSplit.value_le_triangle_envelope
#print axioms BerryEsseen.FourierSplit.value_le_paired_envelope
