module

public import BerryEsseen.FixedPointArithmetic
public import BerryEsseen.FixedFourierConstants
public import BerryEsseen.CubicCellEnvelope

@[expose] public section

/-! 2026-10-29: executable fixed-point enclosures for the three actual
cubic characteristic-function exponents. Endpoint maxima and their minimum
with zero retain Contains semantics. Their upper endpoints control the
entire closed nonnegative frequency cell by CubicCellEnvelope, rather than
by a finite sample. Exponential bounds below stop at the actual Real.exp;
no exponential numerical oracle or generic expression evaluator is used. -/

namespace BerryEsseen.FixedPointCubic

open FixedPointEnclosure FixedPointArithmetic
open FixedFourierConstants (scale scale_positive thetaABox thetaBBox)

/-- The frozen I arithmetic order: -A*t² + (((B*c)*beta)*(t²*t)).
The cube uses one square and one multiplication, with no generic power. -/
def exponentBox (S : ℤ) (hS : 0 < S) (C Beta T A B : Box) : Box :=
  let T2 := sq S hS T
  add (neg (mul S hS A T2))
    (mul S hS (mul S hS (mul S hS B C) Beta) (mul S hS T2 T))

/-- The absolute frequency in the actual exponent is removed only with
the explicit nonnegative-frequency qualification. -/
theorem exponentBox_contains {S : ℤ} (hS : 0 < S) {C Beta T A B : Box}
    {c beta t a b : ℝ} (hC : Contains S C c) (hBeta : Contains S Beta beta)
    (hT : Contains S T t) (hA : Contains S A a) (hB : Contains S B b)
    (ht : 0 ≤ t) :
    Contains S (exponentBox S hS C Beta T A B)
      (CoefficientRayPrice.exponent c a b beta t) := by
  have h2 := sq_contains hS hT
  have h3 := mul_contains hS h2 hT
  have hquad := neg_contains hS (mul_contains hS hA h2)
  have hcubic := mul_contains hS (mul_contains hS (mul_contains hS hB hC) hBeta) h3
  have h := add_contains hS hquad hcubic
  convert h using 1
  · rfl
  · unfold CoefficientRayPrice.exponent
    rw [abs_of_nonneg ht]
    ring

/-- Maximum implemented using only the frozen negation and minimum. -/
def maxBox (I J : Box) : Box := neg (minBox (neg I) (neg J))

theorem maxBox_contains {S : ℤ} (hS : 0 < S) {I J : Box} {x y : ℝ}
    (hI : Contains S I x) (hJ : Contains S J y) :
    Contains S (maxBox I J) (max x y) := by
  have h := neg_contains hS (minBox_contains hS (neg_contains hS hI) (neg_contains hS hJ))
  have heq : -min (-x) (-y) = max x y := by
    rcases le_total x y with hxy | hyx
    · rw [min_eq_right (neg_le_neg hxy), max_eq_right hxy, neg_neg]
    · rw [min_eq_left (neg_le_neg hyx), max_eq_left hyx, neg_neg]
  simpa only [maxBox, heq] using h

def zeroBox : Box := ⟨0, 0, le_rfl⟩

theorem zeroBox_contains (S : ℤ) : Contains S zeroBox (0 : ℝ) := by
  simp [Contains, zeroBox, qval]

def halfBox : Box := rat scale scale_positive 1 2 (by decide)
def tenthBox : Box := rat scale scale_positive 1 10 (by decide)
def hundredthBox : Box := rat scale scale_positive 1 100 (by decide)
def oneOver625Box : Box := rat scale scale_positive 1 625 (by decide)

theorem halfBox_contains : Contains scale halfBox (1 / 2 : ℝ) := by
  simpa only [halfBox, Int.cast_one, Int.cast_ofNat] using
    rat_contains scale scale_positive 1 2 (by decide)

theorem tenthBox_contains : Contains scale tenthBox (1 / 10 : ℝ) := by
  simpa only [tenthBox, Int.cast_one, Int.cast_ofNat] using
    rat_contains scale scale_positive 1 10 (by decide)

theorem hundredthBox_contains : Contains scale hundredthBox (1 / 100 : ℝ) := by
  simpa only [hundredthBox, Int.cast_one, Int.cast_ofNat] using
    rat_contains scale scale_positive 1 100 (by decide)

theorem oneOver625Box_contains : Contains scale oneOver625Box (1 / 625 : ℝ) := by
  simpa only [oneOver625Box, Int.cast_one, Int.cast_ofNat] using
    rat_contains scale scale_positive 1 625 (by decide)

def endpointMaxBox (C Beta L R A B : Box) : Box :=
  maxBox (exponentBox scale scale_positive C Beta L A B)
    (exponentBox scale scale_positive C Beta R A B)

theorem endpointMaxBox_contains {C Beta L R A B : Box} {c beta l r a b : ℝ}
    (hC : Contains scale C c) (hBeta : Contains scale Beta beta)
    (hL : Contains scale L l) (hR : Contains scale R r)
    (hA : Contains scale A a) (hB : Contains scale B b)
    (hl : 0 ≤ l) (hr : 0 ≤ r) :
    Contains scale (endpointMaxBox C Beta L R A B)
      (max (CoefficientRayPrice.exponent c a b beta l)
        (CoefficientRayPrice.exponent c a b beta r)) :=
  maxBox_contains scale_positive
    (exponentBox_contains scale_positive hC hBeta hL hA hB hl)
    (exponentBox_contains scale_positive hC hBeta hR hA hB hr)

/-- The same min/max expression as the real cellExponent, using the
three original coefficient pairs and the actual frozen theta enclosures. -/
def cellExponentBox (C Beta L R : Box) : Box :=
  minBox zeroBox (minBox
    (endpointMaxBox C Beta L R halfBox tenthBox)
    (minBox (endpointMaxBox C Beta L R thetaABox thetaBBox)
      (endpointMaxBox C Beta L R hundredthBox oneOver625Box)))

theorem cellExponentBox_contains {C Beta L R : Box} {c beta l r : ℝ}
    (hC : Contains scale C c) (hBeta : Contains scale Beta beta)
    (hL : Contains scale L l) (hR : Contains scale R r)
    (hl : 0 ≤ l) (hr : 0 ≤ r) :
    Contains scale (cellExponentBox C Beta L R)
      (CubicCellEnvelope.cellExponent c beta l r) := by
  have h0 := endpointMaxBox_contains hC hBeta hL hR halfBox_contains tenthBox_contains hl hr
  have htheta := endpointMaxBox_contains hC hBeta hL hR
    FixedFourierConstants.contains_thetaA FixedFourierConstants.contains_thetaB hl hr
  have hrat := endpointMaxBox_contains hC hBeta hL hR
    hundredthBox_contains oneOver625Box_contains hl hr
  simpa only [cellExponentBox, CubicCellEnvelope.cellExponent,
    ClassicalRationalCosine.a, ClassicalRationalCosine.b] using
    minBox_contains scale_positive (zeroBox_contains scale)
      (minBox_contains scale_positive h0 (minBox_contains scale_positive htheta hrat))

/-- The integer upper endpoint is nonpositive by construction, without a
floating-point check or a sign premise on the enclosed exponent. -/
theorem cellExponentBox_hi_nonpos (C Beta L R : Box) :
    (cellExponentBox C Beta L R).hi ≤ 0 :=
  min_le_left 0 _

theorem cellExponent_le_upper {C Beta L R : Box} {c beta l r : ℝ}
    (hC : Contains scale C c) (hBeta : Contains scale Beta beta)
    (hL : Contains scale L l) (hR : Contains scale R r)
    (hl : 0 ≤ l) (hr : 0 ≤ r) :
    CubicCellEnvelope.cellExponent c beta l r ≤
      ((cellExponentBox C Beta L R).hi : ℝ) / scale := by
  exact ((contains_iff_real _ _ _).mp (cellExponentBox_contains hC hBeta hL hR hl hr)).2

/-- One integer cell bound controls every real frequency in the closed
cell, with the original coefficient and moment sign qualifications. -/
theorem envelope_le_exp_upper {C Beta L R : Box} {c beta l r t : ℝ}
    (hC : Contains scale C c) (hBeta : Contains scale Beta beta)
    (hL : Contains scale L l) (hR : Contains scale R r)
    (hc : 0 ≤ c) (hbeta : 0 ≤ beta) (hl : 0 ≤ l) (ht : t ∈ Set.Icc l r) :
    CoefficientRayPrice.envelope c beta t ≤
      Real.exp (((cellExponentBox C Beta L R).hi : ℝ) / scale) :=
  CubicCellEnvelope.envelope_le_of_cell_upper c beta l r t _ hc hbeta hl ht.1 ht.2
    (cellExponent_le_upper hC hBeta hL hR hl (hl.trans (ht.1.trans ht.2)))

/-- The loss factor's lower endpoint is licensed by its Contains proof;
the only extra sign gate is the decidable integer comparison 0 <= lo.
The direction is essential because the exact cellExponent is nonpositive. -/
theorem lossEnvelope_le_exp_upper (N : ℕ) (hN : 0 < N)
    {C Beta L R Alpha : Box} {c beta l r t : ℝ}
    (hC : Contains scale C c) (hBeta : Contains scale Beta beta)
    (hL : Contains scale L l) (hR : Contains scale R r)
    (hAlpha : Contains scale Alpha (1 - HighMomentRayDamping.loss N beta))
    (hAlpha0 : 0 ≤ Alpha.lo)
    (hc : 0 ≤ c) (hbeta : 0 ≤ beta) (hl : 0 ≤ l) (ht : t ∈ Set.Icc l r) :
    CoefficientRayPrice.lossEnvelope N c beta t ≤
      Real.exp (((Alpha.lo : ℝ) / scale) *
        (((cellExponentBox C Beta L R).hi : ℝ) / scale)) := by
  have halpha := ((contains_iff_real _ _ _).mp hAlpha).1
  have halpha0 : 0 ≤ (Alpha.lo : ℝ) / scale :=
    div_nonneg (by exact_mod_cast hAlpha0) (by exact_mod_cast scale_positive.le)
  have hM := cellExponent_le_upper hC hBeta hL hR hl (hl.trans (ht.1.trans ht.2))
  exact (CubicCellEnvelope.lossEnvelope_le_exp_cell N hN c beta l r t
    ((Alpha.lo : ℝ) / scale) hc hbeta hl ht.1 ht.2 halpha).trans
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hM halpha0))

end BerryEsseen.FixedPointCubic

#print axioms BerryEsseen.FixedPointCubic.exponentBox_contains
#print axioms BerryEsseen.FixedPointCubic.cellExponentBox_contains
#print axioms BerryEsseen.FixedPointCubic.envelope_le_exp_upper
#print axioms BerryEsseen.FixedPointCubic.lossEnvelope_le_exp_upper
