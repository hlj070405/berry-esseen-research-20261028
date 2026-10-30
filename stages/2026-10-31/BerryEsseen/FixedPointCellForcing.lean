module

public import BerryEsseen.FixedPointCubic
public import BerryEsseen.FixedPointUpper

@[expose] public section

/-! 2026-10-29: executable integer upper prices for a whole frequency cell.
The loss exponent uses the exact rational values of Alpha.lo and the cubic
upper endpoint, rather than singleton enclosures of the original unknowns.
The exponential primitive is the proved clipped/Taylor/reciprocal routine;
its two remaining premises are explicit integer lower-endpoint comparisons.
Forcing retains the actual right endpoint b and actual lambda. -/

namespace BerryEsseen.FixedPointCellForcing

open FixedPointEnclosure FixedPointArithmetic
open FixedFourierConstants (scale scale_positive)
open FixedPointUpper (point point_contains)

/-- The two aliases expose precisely the integer expressions checked by
the caller of FixedPointUpper.expUpper. -/
abbrev expDen (X : Box) (m : ℕ) : Box :=
  FixedPointExp.tailDen scale scale_positive
    (FixedPointExp.reduced (FixedPointUpper.clipped32 scale scale_positive X)) m

abbrev expPositive (X : Box) (m : ℕ) (hden : 0 < (expDen X m).lo) : Box :=
  FixedPointExp.expPositive scale scale_positive
    (FixedPointUpper.clipped32 scale scale_positive X) m hden

def lossInputBox (C Beta L R Alpha : Box) : Box :=
  neg (mul scale scale_positive (point Alpha.lo)
    (point (FixedPointCubic.cellExponentBox C Beta L R).hi))

theorem lossInputBox_contains (C Beta L R Alpha : Box) :
    Contains scale (lossInputBox C Beta L R Alpha)
      (-(((Alpha.lo : ℝ) / scale) *
        (((FixedPointCubic.cellExponentBox C Beta L R).hi : ℝ) / scale))) := by
  simpa only [lossInputBox, qval, Rat.cast_div, Rat.cast_intCast] using
    neg_contains scale_positive (mul_contains scale_positive
      (point_contains scale Alpha.lo)
      (point_contains scale (FixedPointCubic.cellExponentBox C Beta L R).hi))

theorem lossInput_nonneg (C Beta L R Alpha : Box) (hAlpha0 : 0 ≤ Alpha.lo) :
    0 ≤ -(((Alpha.lo : ℝ) / scale) *
      (((FixedPointCubic.cellExponentBox C Beta L R).hi : ℝ) / scale)) := by
  have hA : 0 ≤ (Alpha.lo : ℝ) / scale :=
    div_nonneg (by exact_mod_cast hAlpha0) (by exact_mod_cast scale_positive.le)
  have hM : ((FixedPointCubic.cellExponentBox C Beta L R).hi : ℝ) / scale ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg
      (by exact_mod_cast FixedPointCubic.cellExponentBox_hi_nonpos C Beta L R)
      (by exact_mod_cast scale_positive.le)
  exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos hA hM)

def lossUpper (C Beta L R Alpha : Box) (m : ℕ)
    (hden : 0 < (expDen (lossInputBox C Beta L R Alpha) m).lo)
    (hpos : 0 < (expPositive (lossInputBox C Beta L R Alpha) m hden).lo) : ℤ :=
  FixedPointUpper.expUpper scale scale_positive (lossInputBox C Beta L R Alpha) m hden hpos

/-- Every frequency in the closed cell is controlled by the computed
integer exp upper; no real exponential upper is an input premise. -/
theorem lossEnvelope_le_upper (N : ℕ) (hN : 0 < N)
    {C Beta L R Alpha : Box} {c beta a b u : ℝ}
    (hC : Contains scale C c) (hBeta : Contains scale Beta beta)
    (hL : Contains scale L a) (hR : Contains scale R b)
    (hAlpha : Contains scale Alpha (1 - HighMomentRayDamping.loss N beta))
    (hAlpha0 : 0 ≤ Alpha.lo) (hc : 0 ≤ c) (hbeta : 0 < beta)
    (ha : 0 ≤ a) (_hab : a ≤ b) (hu : u ∈ Set.Icc a b) (m : ℕ)
    (hden : 0 < (expDen (lossInputBox C Beta L R Alpha) m).lo)
    (hpos : 0 < (expPositive (lossInputBox C Beta L R Alpha) m hden).lo) :
    CoefficientRayPrice.lossEnvelope N c beta u ≤
      (qval scale (lossUpper C Beta L R Alpha m hden hpos) : ℝ) := by
  have hcell := FixedPointCubic.lossEnvelope_le_exp_upper N hN hC hBeta hL hR
    hAlpha hAlpha0 hc hbeta.le ha hu
  have hexp := FixedPointUpper.exp_neg_le_upper scale_positive
    (lossInputBox_contains C Beta L R Alpha) (lossInput_nonneg C Beta L R Alpha hAlpha0)
    m hden hpos
  have hnum : Real.exp (((Alpha.lo : ℝ) / scale) *
      (((FixedPointCubic.cellExponentBox C Beta L R).hi : ℝ) / scale)) ≤
      (qval scale (lossUpper C Beta L R Alpha m hden hpos) : ℝ) := by
    simpa only [neg_neg, lossUpper] using hexp
  exact hcell.trans hnum

/-- The actual polynomial factor at the actual right endpoint, using the
frozen square-then-multiply cube and division operation order. -/
def forcingBox (upper : ℤ) (Lambda R : Box) : Box :=
  let R2 := sq scale scale_positive R
  mul scale scale_positive (point upper)
    (add (divInt R2 2 (by decide))
      (divInt (mul scale scale_positive Lambda (mul scale scale_positive R2 R)) 3 (by decide)))

theorem forcingBox_contains {Lambda R : Box} {lambda b : ℝ}
    (hLambda : Contains scale Lambda lambda) (hR : Contains scale R b) (upper : ℤ) :
    Contains scale (forcingBox upper Lambda R)
      ((qval scale upper : ℝ) * (b ^ 2 / 2 + lambda * b ^ 3 / 3)) := by
  have h2 := sq_contains scale_positive hR
  have h3 : Contains scale (mul scale scale_positive (sq scale scale_positive R) R) (b ^ 3) := by
    convert mul_contains scale_positive h2 hR using 1; ring
  have hquad := divInt_contains scale_positive (by decide : (0 : ℤ) < 2) h2
  have hcubic := divInt_contains scale_positive (by decide : (0 : ℤ) < 3)
    (mul_contains scale_positive hLambda h3)
  simpa only [forcingBox, Int.cast_ofNat] using
    mul_contains scale_positive (point_contains scale upper) (add_contains scale_positive hquad hcubic)

/-- The same integer forcing price controls the whole closed cell.
Only the actual b is used in the monotonicity step, not R.hi/scale. -/
theorem forcing_le_upper (N : ℕ) (hN : 0 < N)
    {C Beta L R Alpha Lambda : Box} {c beta a b u : ℝ}
    (hC : Contains scale C c) (hBeta : Contains scale Beta beta)
    (hL : Contains scale L a) (hR : Contains scale R b)
    (hAlpha : Contains scale Alpha (1 - HighMomentRayDamping.loss N beta))
    (hAlpha0 : 0 ≤ Alpha.lo)
    (hLambda : Contains scale Lambda (CoarseHighMomentRayPrice.lambda N beta))
    (hc : 0 ≤ c) (hbeta : 0 < beta) (ha : 0 ≤ a) (hab : a ≤ b)
    (hu : u ∈ Set.Icc a b) (m : ℕ)
    (hden : 0 < (expDen (lossInputBox C Beta L R Alpha) m).lo)
    (hpos : 0 < (expPositive (lossInputBox C Beta L R Alpha) m hden).lo) :
    CoefficientRayPrice.lossEnvelope N c beta u *
        (u ^ 2 / 2 + CoarseHighMomentRayPrice.lambda N beta * u ^ 3 / 3) ≤
      ((forcingBox (lossUpper C Beta L R Alpha m hden hpos) Lambda R).hi : ℝ) / scale := by
  have henv := lossEnvelope_le_upper N hN hC hBeta hL hR hAlpha hAlpha0
    hc hbeta ha hab hu m hden hpos
  have hU0 := (CoefficientRayPrice.lossEnvelope_nonneg N c beta u).trans henv
  have hu0 : 0 ≤ u := ha.trans hu.1
  have hb0 : 0 ≤ b := ha.trans hab
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hLambda0 : 0 ≤ CoarseHighMomentRayPrice.lambda N beta := by
    unfold CoarseHighMomentRayPrice.lambda
    positivity
  have h2 := pow_le_pow_left₀ hu0 hu.2 2
  have h3 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hu0 hu.2 3) hLambda0
  have hpoly : u ^ 2 / 2 + CoarseHighMomentRayPrice.lambda N beta * u ^ 3 / 3 ≤
      b ^ 2 / 2 + CoarseHighMomentRayPrice.lambda N beta * b ^ 3 / 3 := by
    linarith only [h2, h3]
  have hfactor0 : 0 ≤ u ^ 2 / 2 + CoarseHighMomentRayPrice.lambda N beta * u ^ 3 / 3 := by
    positivity
  have hproduct := mul_le_mul henv hpoly hfactor0 hU0
  exact hproduct.trans (((contains_iff_real _ _ _).mp
    (forcingBox_contains hLambda hR (lossUpper C Beta L R Alpha m hden hpos))).2)

def decayInputBox (L R : Box) : Box :=
  divInt (sub (sq scale scale_positive R) (sq scale scale_positive L)) 2 (by decide)

theorem decayInputBox_contains {L R : Box} {a b : ℝ}
    (hL : Contains scale L a) (hR : Contains scale R b) :
    Contains scale (decayInputBox L R) ((b ^ 2 - a ^ 2) / 2) := by
  simpa only [decayInputBox, Int.cast_ofNat] using
    divInt_contains scale_positive (by decide : (0 : ℤ) < 2)
      (sub_contains scale_positive (sq_contains scale_positive hR) (sq_contains scale_positive hL))

def decayUpper (L R : Box) (m : ℕ)
    (hden : 0 < (expDen (decayInputBox L R) m).lo)
    (hpos : 0 < (expPositive (decayInputBox L R) m hden).lo) : ℤ :=
  FixedPointUpper.expUpper scale scale_positive (decayInputBox L R) m hden hpos

/-- Computed upper for the true Gaussian attenuation between consecutive
cell endpoints, including coincident endpoints. -/
theorem decay_step_le_upper {L R : Box} {a b : ℝ}
    (hL : Contains scale L a) (hR : Contains scale R b)
    (ha : 0 ≤ a) (hab : a ≤ b) (m : ℕ)
    (hden : 0 < (expDen (decayInputBox L R) m).lo)
    (hpos : 0 < (expPositive (decayInputBox L R) m hden).lo) :
    Real.exp (-((b ^ 2 - a ^ 2) / 2)) ≤
      (qval scale (decayUpper L R m hden hpos) : ℝ) := by
  have hdelta : 0 ≤ (b ^ 2 - a ^ 2) / 2 :=
    div_nonneg (sub_nonneg.mpr (pow_le_pow_left₀ ha hab 2)) (by norm_num)
  exact FixedPointUpper.exp_neg_le_upper scale_positive (decayInputBox_contains hL hR)
    hdelta m hden hpos

end BerryEsseen.FixedPointCellForcing

#print axioms BerryEsseen.FixedPointCellForcing.lossEnvelope_le_upper
#print axioms BerryEsseen.FixedPointCellForcing.forcing_le_upper
#print axioms BerryEsseen.FixedPointCellForcing.decay_step_le_upper
