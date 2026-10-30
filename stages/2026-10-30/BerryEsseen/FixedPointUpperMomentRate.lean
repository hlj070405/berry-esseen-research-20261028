module

public import BerryEsseen.FixedPointCubic
public import BerryEsseen.FixedPointCellCheck
public import BerryEsseen.UpperMomentSpectrumPrice
public import BerryEsseen.FixedPointTrig

@[expose] public section

/-! 2026-10-30: executable one-sided candidates for the fixed U spectrum,
the complete sine forcing and Gaussian cell transport. Extracted candidates
are exact rational upper points; none encloses the unknown original value.
All square roots are checked by polynomial or upper-square integer gates. -/

open MeasureTheory Set
open scoped Interval

namespace BerryEsseen.FixedPointUpperMomentRate

open FixedPointEnclosure FixedPointArithmetic
open FixedFourierConstants (scale scale_positive)
open FixedPointUpper (point point_contains)

abbrev val (z : ℤ) : ℝ := (qval scale z : ℝ)

lemma val_mono {a b : ℤ} (h : a ≤ b) : val a ≤ val b := by
  exact_mod_cast qval_mono scale_positive h

lemma val_nonneg {z : ℤ} (h : 0 ≤ z) : 0 ≤ val z := FixedPointUpper.qval_nonneg scale_positive h

lemma val_nonpos {z : ℤ} (h : z ≤ 0) : val z ≤ 0 := by
  simpa only [val, qval, Int.cast_zero, Rat.cast_zero, zero_div] using val_mono h

lemma pos_of_lo {I : Box} {x : ℝ} (hx : Contains scale I x) (h : 0 < I.lo) : 0 < x := by
  have hp : (0 : ℝ) < val I.lo := by
    simp only [val, qval, Rat.cast_div, Rat.cast_intCast]
    exact div_pos (by exact_mod_cast h) (by exact_mod_cast scale_positive)
  exact hp.trans_le hx.1

def constBox (z : ℤ) : Box := rat scale scale_positive z 1 (by decide)

theorem constBox_contains (z : ℤ) : Contains scale (constBox z) (z : ℝ) := by
  simpa only [constBox, Int.cast_one, div_one] using rat_contains scale scale_positive z 1 (by decide)

def cubeBox (I : Box) : Box := mul scale scale_positive (sq scale scale_positive I) I

theorem cubeBox_contains {I : Box} {x : ℝ} (hx : Contains scale I x) :
    Contains scale (cubeBox I) (x ^ 3) := by
  convert mul_contains scale_positive (sq_contains scale_positive hx) hx using 1
  · rfl
  · ring

def invU (U : Box) (hU : 0 < U.lo) : Box := invPos scale scale_positive U hU
def dBox (U : Box) (hU : 0 < U.lo) : Box := sq scale scale_positive (invU U hU)
def cBox (U : Box) (hU : 0 < U.lo) : Box := add (constBox 1) (invU U hU)

theorem dBox_contains {U : Box} (hU : 0 < U.lo) {u : ℝ} (hu : Contains scale U u) :
    Contains scale (dBox U hU) (UpperMomentSpectrumPrice.d u) := by
  have hh := sq_contains scale_positive (invPos_contains scale_positive hU hu)
  simpa only [dBox, invU, UpperMomentSpectrumPrice.d, inv_pow, one_div] using hh

theorem cBox_contains {U : Box} (hU : 0 < U.lo) {u : ℝ} (hu : Contains scale U u) :
    Contains scale (cBox U hU) ((u + 1) / u) := by
  have hh := add_contains scale_positive (constBox_contains 1) (invPos_contains scale_positive hU hu)
  convert hh using 1
  · rfl
  · have hp := pos_of_lo hu hU
    push_cast
    field_simp [hp.ne']

/-- The nested root is controlled without evaluating a square root. -/
theorem gammaCap_le_of_polynomial (U g : ℝ) (hU : 0 ≤ U) (hg : 0 ≤ g)
    (hT : 0 ≤ 2 * g ^ 2 - U ^ 2 + 4)
    (hP : U ^ 2 * (U ^ 2 + 8) ≤ (2 * g ^ 2 - U ^ 2 + 4) ^ 2) :
    UpperMomentDamping.gammaCap U ≤ g := by
  have he : (U * Real.sqrt (U ^ 2 + 8)) ^ 2 = U ^ 2 * (U ^ 2 + 8) := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  have hs : U * Real.sqrt (U ^ 2 + 8) ≤ 2 * g ^ 2 - U ^ 2 + 4 :=
    (sq_le_sq₀ (mul_nonneg hU (Real.sqrt_nonneg _)) hT).mp (he ▸ hP)
  unfold UpperMomentDamping.gammaCap
  apply (Real.sqrt_le_left hg).mpr
  linarith only [hs]

def gammaTBox (U : Box) (g : ℤ) : Box :=
  add (sub (mul scale scale_positive (constBox 2) (sq scale scale_positive (point g)))
    (sq scale scale_positive U)) (constBox 4)

def gammaRBox (U : Box) : Box :=
  mul scale scale_positive (sq scale scale_positive U)
    (add (sq scale scale_positive U) (constBox 8))

theorem gammaTBox_contains {U : Box} {u : ℝ} (hu : Contains scale U u) (g : ℤ) :
    Contains scale (gammaTBox U g) (2 * val g ^ 2 - u ^ 2 + 4) := by
  simpa only [gammaTBox, Int.cast_ofNat] using
    add_contains scale_positive (sub_contains scale_positive
      (mul_contains scale_positive (constBox_contains 2)
        (sq_contains scale_positive (point_contains scale g))) (sq_contains scale_positive hu))
      (constBox_contains 4)

theorem gammaRBox_contains {U : Box} {u : ℝ} (hu : Contains scale U u) :
    Contains scale (gammaRBox U) (u ^ 2 * (u ^ 2 + 8)) := by
  simpa only [gammaRBox, Int.cast_ofNat] using
    mul_contains scale_positive (sq_contains scale_positive hu)
      (add_contains scale_positive (sq_contains scale_positive hu) (constBox_contains 8))

def gammaCheck (U : Box) (g : ℤ) : Bool :=
  decide (0 ≤ U.lo ∧ 0 ≤ g ∧ 0 ≤ (gammaTBox U g).lo ∧
    (gammaRBox U).hi ≤ (sq scale scale_positive (gammaTBox U g)).lo)

theorem gammaCheck_sound {U : Box} {u : ℝ} {g : ℤ} (hu : Contains scale U u)
    (hc : gammaCheck U g = true) : UpperMomentDamping.gammaCap u ≤ val g := by
  have hg := of_decide_eq_true hc
  have ht := gammaTBox_contains hu g
  have hr := gammaRBox_contains hu
  have ht2 := sq_contains scale_positive ht
  apply gammaCap_le_of_polynomial u (val g) ((val_nonneg hg.1).trans hu.1)
    (val_nonneg hg.2.1) ((val_nonneg hg.2.2.1).trans ht.1)
  exact hr.2.trans ((val_mono hg.2.2.2).trans ht2.1)

/-- All three old raw cubics are bounded directly, before any exponential. -/
theorem old_raw_le_cell (c a b v : ℝ) (hc : 0 ≤ c) (ha : 0 ≤ a) (hv : v ∈ Icc a b) :
    CoefficientRaySpectral.spectralExponent c v ≤ CubicCellEnvelope.cellExponent c 1 a b := by
  have h0 := CubicCellEnvelope.exponent_le_endpoint_max c (1 / 2) (1 / 10) 1 a b v hc (by norm_num) (by norm_num) ha hv.1 hv.2
  have h1 := CubicCellEnvelope.exponent_le_endpoint_max c ClassicalCosineCubic.a ClassicalCosineCubic.b 1 a b v hc ClassicalCosineCubic.b_nonneg (by norm_num) ha hv.1 hv.2
  have h2 := CubicCellEnvelope.exponent_le_endpoint_max c ClassicalRationalCosine.a ClassicalRationalCosine.b 1 a b v hc ClassicalRationalCosine.b_nonneg (by norm_num) ha hv.1 hv.2
  exact min_le_min le_rfl (min_le_min h0 (min_le_min h1 h2))

def invPiBox : Box := invPos scale scale_positive FixedFourierConstants.piBox (by decide)
def fourthABox : Box := divInt (add
  (mul scale scale_positive (constBox 4) (sq scale scale_positive invPiBox))
  (mul scale scale_positive (constBox 2) invPiBox)) 3 (by decide)
def fourthBBox : Box := add
  (divInt (mul scale scale_positive (constBox 16) (cubeBox invPiBox)) 27 (by decide))
  (divInt (mul scale scale_positive (constBox 4) (sq scale scale_positive invPiBox)) 9 (by decide))

theorem invPiBox_contains : Contains scale invPiBox Real.pi⁻¹ :=
  invPos_contains scale_positive (by decide) FixedFourierConstants.contains_pi

theorem fourthABox_contains : Contains scale fourthABox ClassicalThreeHalvesCosine.a := by
  have hh := divInt_contains scale_positive (by decide : (0 : ℤ) < 3)
    (add_contains scale_positive
      (mul_contains scale_positive (constBox_contains 4) (sq_contains scale_positive invPiBox_contains))
      (mul_contains scale_positive (constBox_contains 2) invPiBox_contains))
  convert hh using 1
  · rfl
  · unfold ClassicalThreeHalvesCosine.a
    push_cast
    field_simp [Real.pi_ne_zero]

theorem fourthBBox_contains : Contains scale fourthBBox ClassicalThreeHalvesCosine.b := by
  have hh := add_contains scale_positive
    (divInt_contains scale_positive (by decide : (0 : ℤ) < 27)
      (mul_contains scale_positive (constBox_contains 16) (cubeBox_contains invPiBox_contains)))
    (divInt_contains scale_positive (by decide : (0 : ℤ) < 9)
      (mul_contains scale_positive (constBox_contains 4) (sq_contains scale_positive invPiBox_contains)))
  convert hh using 1
  · rfl
  · unfold ClassicalThreeHalvesCosine.b
    push_cast
    field_simp [Real.pi_ne_zero]

def rawM4Box (C L R : Box) : Box :=
  minBox (FixedPointCubic.cellExponentBox C FixedFourierConstants.oneBox L R)
    (FixedPointCubic.endpointMaxBox C FixedFourierConstants.oneBox L R fourthABox fourthBBox)

theorem raw_g4_le_upper {C L R : Box} {c a b v : ℝ}
    (hC : Contains scale C c) (hL : Contains scale L a) (hR : Contains scale R b)
    (hc : 0 ≤ c) (ha : 0 ≤ a) (hv : v ∈ Icc a b) :
    UpperMomentDamping.g4 c v ≤ val (rawM4Box C L R).hi := by
  have hb := ha.trans (hv.1.trans hv.2)
  have hOld := FixedPointCubic.cellExponentBox_contains hC FixedFourierConstants.contains_one hL hR ha hb
  have hFourth := FixedPointCubic.endpointMaxBox_contains hC FixedFourierConstants.contains_one hL hR fourthABox_contains fourthBBox_contains ha hb
  have hBox := minBox_contains scale_positive hOld hFourth
  have hp := CubicCellEnvelope.exponent_le_endpoint_max c ClassicalThreeHalvesCosine.a ClassicalThreeHalvesCosine.b 1 a b v hc ClassicalThreeHalvesCosine.b_nonneg (by norm_num) ha hv.1 hv.2
  exact (min_le_min (old_raw_le_cell c a b v hc ha hv) hp).trans hBox.2

/-- The second-order correction is increasing on the nonpositive ray. -/
theorem damped_mono (k x y : ℝ) (hk : 0 ≤ k) (hxy : x ≤ y) (hy : y ≤ 0) :
    x - k * x ^ 2 ≤ y - k * y ^ 2 := by
  have hs : y ^ 2 ≤ x ^ 2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hs hk
  linarith only [hxy, hm]

def refSqBox (U V : Box) (g : ℤ) (hU : 0 < U.lo) : Box :=
  add (sq scale scale_positive (sub (sq scale scale_positive U)
      (divInt (sq scale scale_positive V) 2 (by decide))))
    (sq scale scale_positive (divInt
      (mul scale scale_positive (divPos scale scale_positive (point g) U hU) (cubeBox V)) 16 (by decide)))

theorem refSqBox_contains {U V : Box} (hU : 0 < U.lo) {u v : ℝ}
    (hu : Contains scale U u) (hv : Contains scale V v) (g : ℤ) :
    Contains scale (refSqBox U V g hU) (‖UpperMomentDamping.reference u (val g) v‖ ^ 2) := by
  have hre := sub_contains scale_positive (sq_contains scale_positive hu)
    (divInt_contains scale_positive (by decide : (0 : ℤ) < 2) (sq_contains scale_positive hv))
  have him := divInt_contains scale_positive (by decide : (0 : ℤ) < 16)
    (mul_contains scale_positive
      (divPos_contains scale_positive hU (point_contains scale g) hu) (cubeBox_contains hv))
  have hh := add_contains scale_positive (sq_contains scale_positive hre) (sq_contains scale_positive him)
  convert hh using 1
  · rfl
  · rw [UpperMomentDamping.reference_norm_sq]
    push_cast
    ring

theorem reference_norm_mono (U g₀ g v : ℝ) (hU : 0 < U) (hg₀ : 0 ≤ g₀) (hg : g₀ ≤ g) :
    ‖UpperMomentDamping.reference U g₀ v‖ ≤ ‖UpperMomentDamping.reference U g v‖ := by
  have hdiv := div_le_div_of_nonneg_right hg hU.le
  have hs := pow_le_pow_left₀ (div_nonneg hg₀ hU.le) hdiv 2
  have hm := mul_le_mul_of_nonneg_right hs (show 0 ≤ v ^ 6 / 256 by positivity)
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [UpperMomentDamping.reference_norm_sq, UpperMomentDamping.reference_norm_sq]
  nlinarith only [hm]

theorem reference_le_candidate {U V : Box} (hU : 0 < U.lo) {u v : ℝ} {g norm : ℤ}
    (hu : Contains scale U u) (hv : Contains scale V v)
    (hg : UpperMomentDamping.gammaCap u ≤ val g)
    (hgate : FixedPointUpper.UpperSquareGate scale (refSqBox U V g hU) norm) :
    ‖UpperMomentDamping.reference u (UpperMomentDamping.gammaCap u) v‖ ≤ val norm := by
  have hh := FixedPointUpper.sqrt_le_upper scale_positive (refSqBox_contains hU hu hv g) hgate
  have hn : ‖UpperMomentDamping.reference u (val g) v‖ ≤ val norm := by
    simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)] using hh
  exact (reference_norm_mono u _ _ v (pos_of_lo hu hU) (Real.sqrt_nonneg _) hg).trans hn

def rawMRBox (U V : Box) (norm : ℤ) : Box :=
  minBox FixedPointCubic.zeroBox
    (sub (add (divInt (mul scale scale_positive (constBox 5) (cubeBox V)) 48 (by decide))
      (point norm)) (sq scale scale_positive U))

theorem rawMRBox_contains {U V : Box} {u v : ℝ}
    (hu : Contains scale U u) (hv : Contains scale V v) (norm : ℤ) :
    Contains scale (rawMRBox U V norm) (min 0 (5 * v ^ 3 / 48 + val norm - u ^ 2)) := by
  simpa only [rawMRBox, Int.cast_ofNat] using minBox_contains scale_positive
    (FixedPointCubic.zeroBox_contains scale)
    (sub_contains scale_positive (add_contains scale_positive
      (divInt_contains scale_positive (by decide : (0 : ℤ) < 48)
        (mul_contains scale_positive (constBox_contains 5) (cubeBox_contains hv)))
      (point_contains scale norm)) (sq_contains scale_positive hu))

theorem raw_h_le_upper {U V : Box} (hU : 0 < U.lo) {u v : ℝ} {g norm : ℤ}
    (hu : Contains scale U u) (hv : Contains scale V v) (hv0 : 0 ≤ v)
    (hg : UpperMomentDamping.gammaCap u ≤ val g)
    (hnorm : FixedPointUpper.UpperSquareGate scale (refSqBox U V g hU) norm) :
    UpperMomentDamping.h u u (UpperMomentDamping.gammaCap u) v ≤ val (rawMRBox U V norm).hi := by
  have hp := pos_of_lo hu hU
  have hn := reference_le_candidate hU hu hv hg hnorm
  have hh : UpperMomentDamping.H u u (UpperMomentDamping.gammaCap u) v ≤
      5 * v ^ 3 / 48 + val norm - u ^ 2 := by
    unfold UpperMomentDamping.H
    rw [div_self hp.ne', abs_of_nonneg hv0]
    linarith only [hn]
  exact (min_le_min le_rfl hh).trans (rawMRBox_contains hu hv norm).2

def correctedGBox (U : Box) (hU : 0 < U.lo) (m4 mr : ℤ) : Box :=
  minBox
    (sub (point m4) (mul scale scale_positive (dBox U hU) (sq scale scale_positive (point m4))))
    (sub (point mr) (divInt (mul scale scale_positive (dBox U hU) (sq scale scale_positive (point mr))) 2 (by decide)))

theorem correctedGBox_contains {U : Box} (hU : 0 < U.lo) {u : ℝ}
    (hu : Contains scale U u) (m4 mr : ℤ) :
    Contains scale (correctedGBox U hU m4 mr)
      (min (val m4 - val m4 ^ 2 / u ^ 2) (val mr - val mr ^ 2 / (2 * u ^ 2))) := by
  have hd := dBox_contains hU hu
  have h4 := sub_contains scale_positive (point_contains scale m4)
    (mul_contains scale_positive hd (sq_contains scale_positive (point_contains scale m4)))
  have hr := sub_contains scale_positive (point_contains scale mr)
    (divInt_contains scale_positive (by decide : (0 : ℤ) < 2)
      (mul_contains scale_positive hd (sq_contains scale_positive (point_contains scale mr))))
  convert minBox_contains scale_positive h4 hr using 1
  · rfl
  · unfold UpperMomentSpectrumPrice.d
    push_cast
    congr 1 <;> ring

theorem G_le_of_raw (U v m4 mr : ℝ)
    (h4 : UpperMomentDamping.g4 ((U + 1) / U) v ≤ m4) (hm4 : m4 ≤ 0)
    (hr : UpperMomentDamping.h U U (UpperMomentDamping.gammaCap U) v ≤ mr) (hmr : mr ≤ 0) :
    UpperMomentDamping.G U U v ≤ min (m4 - m4 ^ 2 / U ^ 2) (mr - mr ^ 2 / (2 * U ^ 2)) := by
  have h4' := damped_mono (1 / U ^ 2) _ _ (by positivity) h4 hm4
  have hr' := damped_mono (1 / (2 * U ^ 2)) _ _ (by positivity) hr hmr
  have h4'' : UpperMomentDamping.g4 ((U + 1) / U) v -
      UpperMomentDamping.g4 ((U + 1) / U) v ^ 2 / U ^ 2 ≤ m4 - m4 ^ 2 / U ^ 2 := by
    simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm] using h4'
  have hr'' : UpperMomentDamping.h U U (UpperMomentDamping.gammaCap U) v -
      UpperMomentDamping.h U U (UpperMomentDamping.gammaCap U) v ^ 2 / (2 * U ^ 2) ≤
        mr - mr ^ 2 / (2 * U ^ 2) := by
    simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm] using hr'
  unfold UpperMomentDamping.G UpperMomentDamping.spectrum
  exact min_le_min h4'' hr''

/-- Every candidate is independently checked. In particular, raw candidates
are used as exact upper points only after the whole-cell raw checks. -/
def rateCheck (U L R : Box) (g norm m4 mr G : ℤ) : Bool :=
  if hU : 0 < U.lo then
    gammaCheck U g && decide (0 ≤ L.lo ∧ L.hi ≤ R.lo ∧ m4 ≤ 0 ∧ mr ≤ 0 ∧ G ≤ 0 ∧
      FixedPointUpper.UpperSquareGate scale (refSqBox U (FixedPointExp.hull L R) g hU) norm ∧
      (rawM4Box (cBox U hU) L R).hi ≤ m4 ∧
      (rawMRBox U (FixedPointExp.hull L R) norm).hi ≤ mr ∧
      (correctedGBox U hU m4 mr).hi ≤ G)
  else false

theorem rateCheck_sound {U L R : Box} {u a b v : ℝ} {g norm m4 mr G : ℤ}
    (hu : Contains scale U u) (ha : Contains scale L a) (hb : Contains scale R b)
    (hv : v ∈ Icc a b) (hc : rateCheck U L R g norm m4 mr G = true) :
    UpperMomentDamping.G u u v ≤ val G := by
  unfold rateCheck at hc
  split_ifs at hc with hU
  · have hchecks := Bool.and_eq_true_iff.mp hc
    have hγ := gammaCheck_sound hu hchecks.1
    rcases of_decide_eq_true hchecks.2 with ⟨hL0, _hLR, hm4, hmr, _hG, hnorm, h4, hr, hcorr⟩
    have hu0 := pos_of_lo hu hU
    have ha0 := (val_nonneg hL0).trans ha.1
    have hV := FixedPointExp.hull_contains_between scale_positive ha hb hv.1 hv.2
    have hc0 : 0 ≤ (u + 1) / u := by positivity
    have hraw4 := (raw_g4_le_upper (cBox_contains hU hu) ha hb hc0 ha0 hv).trans (val_mono h4)
    have hrawr := (raw_h_le_upper hU hu hV (ha0.trans hv.1) hγ hnorm).trans (val_mono hr)
    exact (G_le_of_raw u v (val m4) (val mr) hraw4 (val_nonpos hm4) hrawr (val_nonpos hmr)).trans
      ((correctedGBox_contains hU hu m4 mr).2.trans (val_mono hcorr))

lemma sine_kernel_nonneg (U v : ℝ) (hU : 0 < U) (hv : 0 ≤ v) :
    0 ≤ FiniteRhoSinePrice.kernel U v := by
  have h1 : 0 ≤ Real.sin (min (U * v / 2) (Real.pi / 2)) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (le_min (by positivity) (by positivity))
      ((min_le_right _ _).trans (by linarith [Real.pi_pos]))
  have h2 : 0 ≤ Real.sin (min v (Real.pi / 2)) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (le_min hv (by positivity))
      ((min_le_right _ _).trans (by linarith [Real.pi_pos]))
  unfold FiniteRhoSinePrice.kernel FiniteRhoSinePrice.firstKernel FiniteRhoSinePrice.secondKernel
  positivity

theorem W_mono (U a b : ℝ) (hU : 0 < U) (ha : 0 ≤ a) (hab : a ≤ b) :
    UpperMomentSpectrumPrice.W U a ≤ UpperMomentSpectrumPrice.W U b := by
  apply mul_le_mul_of_nonneg_left _ hU.le
  apply intervalIntegral.integral_mono_interval (μ := volume) (by rfl)
    (div_nonneg ha hU.le) (div_le_div_of_nonneg_right hab hU.le)
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    exact sine_kernel_nonneg U v hU hv.1.le
  · exact (FiniteRhoSinePrice.continuous_kernel U).intervalIntegrable 0 (b / U)

theorem W_eq_inactive (U v : ℝ) (hU : 0 < U) (hv : 0 ≤ v)
    (hvpi : v ≤ Real.pi) (hvU : v / U ≤ Real.pi / 2) :
    UpperMomentSpectrumPrice.W U v =
      8 * Real.sin (v / 4) ^ 2 + U * Real.sin (v / U) - v * Real.cos (v / U) := by
  unfold UpperMomentSpectrumPrice.W
  rw [FiniteRhoSinePrice.H_eq_closedForm U _ hU (div_nonneg hv hU.le)]
  unfold FiniteRhoSinePrice.closedForm FiniteRhoSinePrice.firstCut FiniteRhoSinePrice.secondCut
  rw [min_eq_left (div_le_div_of_nonneg_right hvpi hU.le), min_eq_left hvU]
  have he : U * (v / U) / 4 = v / 4 := by field_simp [hU.ne']
  rw [he]
  simp only [sub_self, mul_zero, zero_div, add_zero]
  field_simp [hU.ne']

def quarterBox (R : Box) : Box := divInt R 4 (by decide)
def ratioBox (U R : Box) (hU : 0 < U.lo) : Box := divPos scale scale_positive R U hU

def wrightBox (U R : Box) (hU : 0 < U.lo) : Box :=
  sub (add
    (mul scale scale_positive (constBox 8)
      (sq scale scale_positive (FixedPointTrig.sinBox scale scale_positive (quarterBox R))))
    (mul scale scale_positive U
      (FixedPointTrig.sinBox scale scale_positive (ratioBox U R hU))))
    (mul scale scale_positive R
      (FixedPointTrig.cosBox scale scale_positive (ratioBox U R hU)))

def wrightCheck (U R : Box) (W : ℤ) : Bool :=
  if hU : 0 < U.lo then
    decide (0 ≤ R.lo ∧ R.hi ≤ FixedFourierConstants.piBox.lo ∧
      (ratioBox U R hU).hi ≤ (divInt FixedFourierConstants.piBox 2 (by decide)).lo ∧
      0 ≤ (quarterBox R).lo ∧ (quarterBox R).hi ≤ scale ∧
      0 ≤ (ratioBox U R hU).lo ∧ (ratioBox U R hU).hi ≤ scale ∧
      0 ≤ W ∧ (wrightBox U R hU).hi ≤ W)
  else false

theorem wrightCheck_sound {U R : Box} {u b : ℝ} {W : ℤ}
    (hu : Contains scale U u) (hb : Contains scale R b) (hc : wrightCheck U R W = true) :
    UpperMomentSpectrumPrice.W u b ≤ val W := by
  unfold wrightCheck at hc
  split_ifs at hc with hU
  · rcases of_decide_eq_true hc with ⟨hR0, hpi, hhalf, hq0, hq1, hr0, hr1, _hW, hval⟩
    have hu0 := pos_of_lo hu hU
    have hb0 := (val_nonneg hR0).trans hb.1
    have hq : Contains scale (quarterBox R) (b / 4) := by
      simpa only [quarterBox, Int.cast_ofNat] using divInt_contains scale_positive (by decide : (0 : ℤ) < 4) hb
    have hr : Contains scale (ratioBox U R hU) (b / u) := divPos_contains scale_positive hU hb hu
    have hsinQ := FixedPointTrig.sinBox_contains scale_positive hq hq0 hq1
    have hsinR := FixedPointTrig.sinBox_contains scale_positive hr hr0 hr1
    have hcosR := FixedPointTrig.cosBox_contains scale_positive hr hr0 hr1
    have hbox := sub_contains scale_positive
      (add_contains scale_positive
        (mul_contains scale_positive (constBox_contains 8) (sq_contains scale_positive hsinQ))
        (mul_contains scale_positive hu hsinR)) (mul_contains scale_positive hb hcosR)
    have hbpi : b ≤ Real.pi := hb.2.trans ((val_mono hpi).trans FixedFourierConstants.contains_pi.1)
    have hhalfbox := divInt_contains scale_positive (by decide : (0 : ℤ) < 2) FixedFourierConstants.contains_pi
    have hcap : b / u ≤ Real.pi / 2 := hr.2.trans ((val_mono hhalf).trans (by simpa only [Int.cast_ofNat] using hhalfbox.1))
    rw [W_eq_inactive u b hu0 hb0 hbpi hcap]
    exact hbox.2.trans (val_mono hval)

abbrev expDen (X : Box) : Box := FixedPointCellForcing.expDen X 8
abbrev expPositive (X : Box) (hden : 0 < (expDen X).lo) : Box :=
  FixedPointCellForcing.expPositive X 8 hden

def expCheck (X : Box) (candidate : ℤ) : Bool :=
  if 0 ≤ X.lo then
    if hden : 0 < (expDen X).lo then
      if hpos : 0 < (expPositive X hden).lo then
        decide (0 ≤ candidate ∧ FixedPointUpper.expUpper scale scale_positive X 8 hden hpos ≤ candidate)
      else false
    else false
  else false

theorem expCheck_sound {X : Box} {x : ℝ} {candidate : ℤ}
    (hx : Contains scale X x) (hc : expCheck X candidate = true) :
    Real.exp (-x) ≤ val candidate := by
  unfold expCheck at hc
  split_ifs at hc with hX0 hden hpos
  · have hg := of_decide_eq_true hc
    exact (FixedPointUpper.exp_neg_le_upper scale_positive hx ((val_nonneg hX0).trans hx.1)
      8 hden hpos).trans (val_mono hg.2)

def forcingInputBox (U S : Box) (hU : 0 < U.lo) (G : ℤ) : Box :=
  neg (mul scale scale_positive (sub S (dBox U hU)) (point G))

theorem forcingInputBox_contains {U S : Box} (hU : 0 < U.lo) {u s : ℝ}
    (hu : Contains scale U u) (hs : Contains scale S s) (G : ℤ) :
    Contains scale (forcingInputBox U S hU G) (-((s - UpperMomentSpectrumPrice.d u) * val G)) :=
  neg_contains scale_positive (mul_contains scale_positive
    (sub_contains scale_positive hs (dBox_contains hU hu)) (point_contains scale G))

def forcingProductBox (S : Box) (P W : ℤ) : Box :=
  mul scale scale_positive S (mul scale scale_positive (point P) (point W))

theorem forcingProductBox_contains {S : Box} {s : ℝ} (hs : Contains scale S s) (P W : ℤ) :
    Contains scale (forcingProductBox S P W) (s * (val P * val W)) :=
  mul_contains scale_positive hs (mul_contains scale_positive (point_contains scale P) (point_contains scale W))

def forcingCheck (U S : Box) (G W P H : ℤ) : Bool :=
  if hU : 0 < U.lo then
    expCheck (forcingInputBox U S hU G) P && decide
      (0 ≤ S.lo ∧ 0 ≤ (sub S (dBox U hU)).lo ∧ G ≤ 0 ∧ 0 ≤ W ∧ 0 ≤ P ∧ 0 ≤ H ∧
        (forcingProductBox S P W).hi ≤ H)
  else false

theorem forcingCheck_sound {U S : Box} {u s v : ℝ} {G W P H : ℤ}
    (hu : Contains scale U u) (hs : Contains scale S s) (hv : 0 ≤ v)
    (hG : UpperMomentDamping.G u u v ≤ val G) (hW : UpperMomentSpectrumPrice.W u v ≤ val W)
    (hc : forcingCheck U S G W P H = true) :
    s * Real.exp ((s - UpperMomentSpectrumPrice.d u) * UpperMomentDamping.G u u v) *
      UpperMomentSpectrumPrice.W u v ≤ val H := by
  unfold forcingCheck at hc
  split_ifs at hc with hU
  · have hchecks := Bool.and_eq_true_iff.mp hc
    rcases of_decide_eq_true hchecks.2 with ⟨hS0, hdiff0, _hG0, _hW0, hP0, _hH0, hprod⟩
    have hu0 := pos_of_lo hu hU
    have hs0 := (val_nonneg hS0).trans hs.1
    have hdiff := sub_contains scale_positive hs (dBox_contains hU hu)
    have hdiff' := (val_nonneg hdiff0).trans hdiff.1
    have he := expCheck_sound (forcingInputBox_contains hU hu hs G) hchecks.1
    rw [neg_neg] at he
    have hexp := (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hG hdiff')).trans he
    have hmul := mul_le_mul hexp hW (UpperMomentSpectrumPrice.W_nonneg u v hu0 hv) (val_nonneg hP0)
    have hmul' := mul_le_mul_of_nonneg_left hmul hs0
    have hright := (forcingProductBox_contains hs P W).2.trans (val_mono hprod)
    have hbound : s * Real.exp ((s - UpperMomentSpectrumPrice.d u) * UpperMomentDamping.G u u v) *
        UpperMomentSpectrumPrice.W u v ≤ s * (val P * val W) := by
      simpa only [mul_assoc] using hmul'
    exact hbound.trans hright

def forcingCellCheck (U S L R : Box) (g norm m4 mr G W P H : ℤ) : Bool :=
  (rateCheck U L R g norm m4 mr G && wrightCheck U R W) && forcingCheck U S G W P H

/-- The terminal whole-cell forcing theorem has no free spectral or
forcing upper premise: all candidates are licensed by executable gates. -/
theorem forcingCellCheck_sound {U S L R : Box} {u s a b v : ℝ} {g norm m4 mr G W P H : ℤ}
    (hu : Contains scale U u) (hs : Contains scale S s)
    (ha : Contains scale L a) (hb : Contains scale R b) (hv : v ∈ Icc a b)
    (hc : forcingCellCheck U S L R g norm m4 mr G W P H = true) :
    s * Real.exp ((s - UpperMomentSpectrumPrice.d u) * UpperMomentDamping.G u u v) *
      UpperMomentSpectrumPrice.W u v ≤ val H := by
  have hchecks := Bool.and_eq_true_iff.mp hc
  have hleft := Bool.and_eq_true_iff.mp hchecks.1
  have hG := rateCheck_sound hu ha hb hv hleft.1
  have hW := wrightCheck_sound hu hb hleft.2
  have hrate := hleft.1
  unfold rateCheck at hrate
  split_ifs at hrate with hU
  · have hg := Bool.and_eq_true_iff.mp hrate
    have hL0 := (of_decide_eq_true hg.2).1
    have hv0 := ((val_nonneg hL0).trans ha.1).trans hv.1
    have hWmono := W_mono u v b (pos_of_lo hu hU) hv0 hv.2
    exact forcingCheck_sound hu hs hv0 hG (hWmono.trans hW) hchecks.2

def decayInputBox (S L R : Box) : Box :=
  mul scale scale_positive S
    (divInt (sub (sq scale scale_positive R) (sq scale scale_positive L)) 2 (by decide))

theorem decayInputBox_contains {S L R : Box} {s a b : ℝ}
    (hs : Contains scale S s) (ha : Contains scale L a) (hb : Contains scale R b) :
    Contains scale (decayInputBox S L R) (s * ((b ^ 2 - a ^ 2) / 2)) := by
  simpa only [decayInputBox, Int.cast_ofNat] using mul_contains scale_positive hs
    (divInt_contains scale_positive (by decide : (0 : ℤ) < 2)
      (sub_contains scale_positive (sq_contains scale_positive hb) (sq_contains scale_positive ha)))

def decayCheck (S L R : Box) (D : ℤ) : Bool :=
  decide (0 ≤ S.lo ∧ 0 ≤ L.lo ∧ L.hi ≤ R.lo ∧ D ≤ scale) && expCheck (decayInputBox S L R) D

theorem decayCheck_sound {S L R : Box} {s a b : ℝ} {D : ℤ}
    (hs : Contains scale S s) (ha : Contains scale L a) (hb : Contains scale R b)
    (hc : decayCheck S L R D = true) :
    Real.exp (-s * (b ^ 2 - a ^ 2) / 2) ≤ val D := by
  have hh := expCheck_sound (decayInputBox_contains hs ha hb) (Bool.and_eq_true_iff.mp hc).2
  convert hh using 1
  congr 1
  ring

end BerryEsseen.FixedPointUpperMomentRate

#print axioms BerryEsseen.FixedPointUpperMomentRate.gammaCheck_sound
#print axioms BerryEsseen.FixedPointUpperMomentRate.fourthABox_contains
#print axioms BerryEsseen.FixedPointUpperMomentRate.fourthBBox_contains
#print axioms BerryEsseen.FixedPointUpperMomentRate.rateCheck_sound
#print axioms BerryEsseen.FixedPointUpperMomentRate.W_mono
#print axioms BerryEsseen.FixedPointUpperMomentRate.W_eq_inactive
#print axioms BerryEsseen.FixedPointUpperMomentRate.wrightCheck_sound
#print axioms BerryEsseen.FixedPointUpperMomentRate.expCheck_sound
#print axioms BerryEsseen.FixedPointUpperMomentRate.forcingCellCheck_sound
#print axioms BerryEsseen.FixedPointUpperMomentRate.decayCheck_sound

