module

public import BerryEsseen.HighFrequencyPeriodic
public import BerryEsseen.HighFrequencySeries
public import BerryEsseen.HighFrequencyZeroCell

@[expose] public section

/-! 2026-10-28: complete fixed-distance high-frequency tail synthesis.
Only the first two prices carry D². This module does not perform the
subsequent averaging over the actual conditional product-event law. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators Interval
open BerryEsseen.HighFrequencyCells BerryEsseen.HighFrequencyPeriodic
open BerryEsseen.HighFrequencySeries
open BerryEsseen.HighFrequencyZeroCell

namespace BerryEsseen.HighFrequencyDistance

def nonzeroPrice (n : ℕ) (a D w : ℝ) : ℝ :=
  D ^ 2 / (4 * Real.pi ^ (3 / 2 : ℝ) * sineSlope w * Real.sqrt a) *
    (S3 + (3 / ((n : ℝ) * a * sineSlope w ^ 2)) * S5 w) +
  D ^ 2 * Real.sqrt n / (2 * Real.pi ^ 2) *
    Real.exp (-((n : ℝ) * a) * sineSlope w ^ 2 * w ^ 2)

/-- The D² coefficient exported for later actual conditional second-moment averaging. -/
def nonzeroSlope (n : ℕ) (a w : ℝ) : ℝ :=
  (S3 + (3 / ((n : ℝ) * a * sineSlope w ^ 2)) * S5 w) /
    (4 * Real.pi ^ (3 / 2 : ℝ) * sineSlope w * Real.sqrt a) +
  Real.sqrt n / (2 * Real.pi ^ 2) *
    Real.exp (-((n : ℝ) * a) * sineSlope w ^ 2 * w ^ 2)

lemma nonzeroPrice_eq_sq_mul (n : ℕ) (a D w : ℝ) :
    nonzeroPrice n a D w = D ^ 2 * nonzeroSlope n a w := by
  unfold nonzeroPrice nonzeroSlope
  ring

lemma nonzeroSlope_nonneg (n : ℕ) (a w : ℝ) (ha : 0 < a)
    (hw : 0 < w) (hwcap : w ≤ 1 / 4) : 0 ≤ nonzeroSlope n a w := by
  have hh := sineSlope_pos w hw.le hwcap
  have hS3 := S3_nonneg
  have hS5 := S5_nonneg w hwcap
  unfold nonzeroSlope
  positivity

lemma cubicSeries_le : cubicSeries ≤ S3 := by
  simpa only [cubicSeries, HighFrequencyPeriodic.center, seriesTerm, powerKernel, sub_zero] using series_three_le_S3

lemma fifthSeries_le (w : ℝ) (hw : 0 < w) (hwcap : w ≤ 1 / 4) : fifthSeries w ≤ S5 w := by
  simpa only [fifthSeries, HighFrequencyPeriodic.center, seriesTerm, powerKernel] using series_five_le_S5 w hw hwcap

/-- The true nonzero-region integral with the original finite twenty-term prices. -/
theorem nonzero_tail_finite_price (n : ℕ) (hn : 0 < n) (a D w : ℝ)
    (ha : 0 < a) (hD : 0 < D) (hw : 0 < w) (hwcap : w ≤ 1 / 4) :
    IntegrableOn (fixedDistanceIntegrand n a D) (Ioi (Real.pi / D)) ∧
      Real.sqrt n * (∫ t in Ioi (Real.pi / D), fixedDistanceIntegrand n a D t) ≤
        nonzeroPrice n a D w := by
  have hraw := fixedDistance_nonzero_tail n hn a D w ha hD hw hwcap
  have hh := sineSlope_pos w hw.le hwcap
  have hrate : 0 ≤ 3 / ((n : ℝ) * a * sineSlope w ^ 2) := by positivity
  have hinner := add_le_add cubicSeries_le (mul_le_mul_of_nonneg_left (fifthSeries_le w hw hwcap) hrate)
  have hpref : 0 ≤ D ^ 2 / (4 * Real.pi ^ (3 / 2 : ℝ) * sineSlope w * Real.sqrt a) := by positivity
  have houter := mul_le_mul_of_nonneg_left hinner hpref
  refine ⟨hraw.1, hraw.2.trans ?_⟩
  exact add_le_add houter le_rfl

lemma fixedDistanceIntegrand_nonneg (n : ℕ) (a D t : ℝ) (ht : 0 ≤ t) :
    0 ≤ fixedDistanceIntegrand n a D t := fixedDistance_nonneg n a D t ht

/-- The whole exact t⁻³ quotient is L¹ on every positive lower tail. -/
theorem integrableOn_fixedDistance_tail (n : ℕ) (a D b : ℝ) (ha : 0 ≤ a) (hb : 0 < b) :
    IntegrableOn (fixedDistanceIntegrand n a D) (Ioi b) :=
  integrableOn_fixedDistance_Ioi n a D b ha hb

/-- Exact closed-zero/open-nonzero partition, extending the nonzero part below
b only through a nonnegative integral. Endpoints are retained in the zero part. -/
lemma tail_le_zero_plus_nonzero (n : ℕ) (hn : 0 < n) (a D b w : ℝ)
    (ha : 0 < a) (hD : 0 < D) (hb : 0 < b) (hw : 0 < w) (hwcap : w ≤ 1 / 4) :
    Real.sqrt n * (∫ t in Ioi b, fixedDistanceIntegrand n a D t) ≤
      Real.sqrt n * (∫ t in Ioi b ∩ Iic (Real.pi / D), fixedDistanceIntegrand n a D t) +
        nonzeroPrice n a D w := by
  have hi := integrableOn_fixedDistance_tail n a D b ha.le hb
  have hNZ := nonzero_tail_finite_price n hn a D w ha hD hw hwcap
  have hsplit := integral_inter_add_sdiff (measurableSet_Iic : MeasurableSet (Iic (Real.pi / D))) hi
  have hsets : Ioi b \ Iic (Real.pi / D) = Ioi b ∩ Ioi (Real.pi / D) := by
    ext t
    simp
  rw [hsets] at hsplit
  have hcut : 0 < Real.pi / D := div_pos Real.pi_pos hD
  have hExtend : (∫ t in Ioi b ∩ Ioi (Real.pi / D), fixedDistanceIntegrand n a D t) ≤
      ∫ t in Ioi (Real.pi / D), fixedDistanceIntegrand n a D t := by
    apply setIntegral_mono_set hNZ.1
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact fixedDistanceIntegrand_nonneg n a D t (hcut.trans ht).le
    · exact Eventually.of_forall fun _ ht => ht.2
  calc
    _ = Real.sqrt n * (∫ t in Ioi b ∩ Iic (Real.pi / D), fixedDistanceIntegrand n a D t) +
        Real.sqrt n * (∫ t in Ioi b ∩ Ioi (Real.pi / D), fixedDistanceIntegrand n a D t) := by
      rw [← hsplit]
      ring
    _ ≤ Real.sqrt n * (∫ t in Ioi b ∩ Iic (Real.pi / D), fixedDistanceIntegrand n a D t) +
        Real.sqrt n * (∫ t in Ioi (Real.pi / D), fixedDistanceIntegrand n a D t) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hExtend (Real.sqrt_nonneg (n : ℝ)))
    _ ≤ _ := add_le_add le_rfl hNZ.2

def basicPrice (n : ℕ) (a D d b w : ℝ) : ℝ :=
  nonzeroPrice n a D w + Zbasic n a d b + wingPrice n a b

def improvedPrice (n : ℕ) (a D d b w : ℝ) : ℝ :=
  nonzeroPrice n a D w + Zimproved n a d b + wingPrice n a b

def minimumPrice (n : ℕ) (a D d b w : ℝ) : ℝ :=
  nonzeroPrice n a D w + min (Zbasic n a d b) (Zimproved n a d b) + wingPrice n a b

lemma basicPrice_eq_affine (n : ℕ) (a D d b w : ℝ) :
    basicPrice n a D d b w = D ^ 2 * nonzeroSlope n a w + Zbasic n a d b + wingPrice n a b := by
  rw [basicPrice, nonzeroPrice_eq_sq_mul]

lemma improvedPrice_eq_affine (n : ℕ) (a D d b w : ℝ) :
    improvedPrice n a D d b w = D ^ 2 * nonzeroSlope n a w + Zimproved n a d b + wingPrice n a b := by
  rw [improvedPrice, nonzeroPrice_eq_sq_mul]

lemma minimumPrice_eq_affine (n : ℕ) (a D d b w : ℝ) :
    minimumPrice n a D d b w = D ^ 2 * nonzeroSlope n a w +
      min (Zbasic n a d b) (Zimproved n a d b) + wingPrice n a b := by
  rw [minimumPrice, nonzeroPrice_eq_sq_mul]

/-- The complete fixed-D Ioi b tail with the original basic zero-cell price.
In particular b=9/10 needs no additional restriction on D. -/
theorem fixedDistance_tail_basic (n : ℕ) (hn : 0 < n) (a D d b w : ℝ)
    (ha : 0 < a) (hd : 0 < d) (hDd : d ≤ D) (hb : 0 < b)
    (hw : 0 < w) (hwcap : w ≤ 1 / 4) :
    IntegrableOn (fixedDistanceIntegrand n a D) (Ioi b) ∧
      Real.sqrt n * (∫ t in Ioi b, fixedDistanceIntegrand n a D t) ≤ basicPrice n a D d b w := by
  have hp := tail_le_zero_plus_nonzero n hn a D b w ha (hd.trans_le hDd) hb hw hwcap
  have hz := (fixedDistance_zero_tail_basic n hn a D d b ha hd hDd hb).2
  have hz' : Real.sqrt n * (∫ t in Ioi b ∩ Iic (Real.pi / D), fixedDistanceIntegrand n a D t) ≤
      Zbasic n a d b + wingPrice n a b := by
    simpa only [zeroTail, zeroDomain] using hz
  refine ⟨integrableOn_fixedDistance_tail n a D b ha.le hb, ?_⟩
  unfold basicPrice
  linarith

/-- The complete fixed-D tail with the rational Gaussian zero-cell improvement. -/
theorem fixedDistance_tail_improved (n : ℕ) (hn : 0 < n) (a D d b w : ℝ)
    (ha : 0 < a) (hd : 0 < d) (hDd : d ≤ D) (hb : 0 < b)
    (hw : 0 < w) (hwcap : w ≤ 1 / 4) :
    IntegrableOn (fixedDistanceIntegrand n a D) (Ioi b) ∧
      Real.sqrt n * (∫ t in Ioi b, fixedDistanceIntegrand n a D t) ≤ improvedPrice n a D d b w := by
  have hp := tail_le_zero_plus_nonzero n hn a D b w ha (hd.trans_le hDd) hb hw hwcap
  have hz := (fixedDistance_zero_tail_improved n hn a D d b ha hd hDd hb).2
  have hz' : Real.sqrt n * (∫ t in Ioi b ∩ Iic (Real.pi / D), fixedDistanceIntegrand n a D t) ≤
      Zimproved n a d b + wingPrice n a b := by
    simpa only [zeroTail, zeroDomain] using hz
  refine ⟨integrableOn_fixedDistance_tail n a D b ha.le hb, ?_⟩
  unfold improvedPrice
  linarith

/-- The two proved zero-cell alternatives can be minimized for the same fixed D. -/
theorem fixedDistance_tail_min (n : ℕ) (hn : 0 < n) (a D d b w : ℝ)
    (ha : 0 < a) (hd : 0 < d) (hDd : d ≤ D) (hb : 0 < b)
    (hw : 0 < w) (hwcap : w ≤ 1 / 4) :
    IntegrableOn (fixedDistanceIntegrand n a D) (Ioi b) ∧
      Real.sqrt n * (∫ t in Ioi b, fixedDistanceIntegrand n a D t) ≤ minimumPrice n a D d b w := by
  have hp := tail_le_zero_plus_nonzero n hn a D b w ha (hd.trans_le hDd) hb hw hwcap
  have hz := (fixedDistance_zero_tail_min n hn a D d b ha hd hDd hb).2
  have hz' : Real.sqrt n * (∫ t in Ioi b ∩ Iic (Real.pi / D), fixedDistanceIntegrand n a D t) ≤
      min (Zbasic n a d b) (Zimproved n a d b) + wingPrice n a b := by
    simpa only [zeroTail, zeroDomain] using hz
  refine ⟨integrableOn_fixedDistance_tail n a D b ha.le hb, ?_⟩
  unfold minimumPrice
  linarith

end BerryEsseen.HighFrequencyDistance

#print axioms BerryEsseen.HighFrequencyDistance.nonzero_tail_finite_price
#print axioms BerryEsseen.HighFrequencyDistance.integrableOn_fixedDistance_tail
#print axioms BerryEsseen.HighFrequencyDistance.tail_le_zero_plus_nonzero
#print axioms BerryEsseen.HighFrequencyDistance.fixedDistance_tail_basic
#print axioms BerryEsseen.HighFrequencyDistance.fixedDistance_tail_improved
#print axioms BerryEsseen.HighFrequencyDistance.fixedDistance_tail_min
