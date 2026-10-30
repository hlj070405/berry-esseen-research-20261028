module

public import BerryEsseen.FixedPointCellForcing

@[expose] public section

/-! 2026-10-29: pure-integer Bool acceptance for whole-cell forcing and
Gaussian step decay, at scale 10^40 and Taylor degree eight. Every failed
integer positivity comparison returns false; no fallback is accepted.
Soundness retains the actual common real parameters and all qualifications. -/

namespace BerryEsseen.FixedPointCellCheck

open FixedPointEnclosure FixedPointArithmetic FixedPointCellForcing
open FixedFourierConstants (scale scale_positive)

def forcingCheck (C Beta L R Alpha Lambda : Box) (candidate : ℤ) : Bool :=
  if 0 ≤ Alpha.lo then
    if hden : 0 < (expDen (lossInputBox C Beta L R Alpha) 8).lo then
      if hpos : 0 < (expPositive (lossInputBox C Beta L R Alpha) 8 hden).lo then
        decide ((forcingBox (lossUpper C Beta L R Alpha 8 hden hpos) Lambda R).hi ≤ candidate)
      else false
    else false
  else false

def decayCheck (L R : Box) (candidate : ℤ) : Bool :=
  if hden : 0 < (expDen (decayInputBox L R) 8).lo then
    if hpos : 0 < (expPositive (decayInputBox L R) 8 hden).lo then
      decide (decayUpper L R 8 hden hpos ≤ candidate)
    else false
  else false

theorem forcingCheck_sound (N : ℕ) (hN : 0 < N)
    {C Beta L R Alpha Lambda : Box} {c beta a b u : ℝ} {candidate : ℤ}
    (hC : Contains scale C c) (hBeta : Contains scale Beta beta)
    (hL : Contains scale L a) (hR : Contains scale R b)
    (hAlpha : Contains scale Alpha (1 - HighMomentRayDamping.loss N beta))
    (hLambda : Contains scale Lambda (CoarseHighMomentRayPrice.lambda N beta))
    (hc : 0 ≤ c) (hbeta : 0 < beta) (ha : 0 ≤ a) (hab : a ≤ b)
    (hu : u ∈ Set.Icc a b)
    (hcheck : forcingCheck C Beta L R Alpha Lambda candidate = true) :
    CoefficientRayPrice.lossEnvelope N c beta u *
        (u ^ 2 / 2 + CoarseHighMomentRayPrice.lambda N beta * u ^ 3 / 3) ≤
      (qval scale candidate : ℝ) := by
  unfold forcingCheck at hcheck
  split_ifs at hcheck with hAlpha0 hden hpos
  · have hgate := of_decide_eq_true hcheck
    have hreal := forcing_le_upper N hN hC hBeta hL hR hAlpha hAlpha0 hLambda
      hc hbeta ha hab hu 8 hden hpos
    have hreal' : CoefficientRayPrice.lossEnvelope N c beta u *
        (u ^ 2 / 2 + CoarseHighMomentRayPrice.lambda N beta * u ^ 3 / 3) ≤
        (qval scale (forcingBox (lossUpper C Beta L R Alpha 8 hden hpos) Lambda R).hi : ℝ) := by
      simpa only [qval, Rat.cast_div, Rat.cast_intCast] using hreal
    exact hreal'.trans (by exact_mod_cast qval_mono scale_positive hgate)

theorem decayCheck_sound {L R : Box} {a b : ℝ} {candidate : ℤ}
    (hL : Contains scale L a) (hR : Contains scale R b) (ha : 0 ≤ a) (hab : a ≤ b)
    (hcheck : decayCheck L R candidate = true) :
    Real.exp (-((b ^ 2 - a ^ 2) / 2)) ≤ (qval scale candidate : ℝ) := by
  unfold decayCheck at hcheck
  split_ifs at hcheck with hden hpos
  · have hgate := of_decide_eq_true hcheck
    exact (decay_step_le_upper hL hR ha hab 8 hden hpos).trans
      (by exact_mod_cast qval_mono scale_positive hgate)

/-- Exact negated rational value of the already rounded cubic upper.
This is not a singleton enclosure of the unknown actual exponent. -/
def envelopeInputBox (C Beta A B : Box) : Box :=
  neg (FixedPointUpper.point (FixedPointCubic.cellExponentBox C Beta A B).hi)

theorem envelopeInputBox_contains (C Beta A B : Box) :
    Contains scale (envelopeInputBox C Beta A B)
      (-(qval scale (FixedPointCubic.cellExponentBox C Beta A B).hi : ℝ)) :=
  neg_contains scale_positive
    (FixedPointUpper.point_contains scale (FixedPointCubic.cellExponentBox C Beta A B).hi)

theorem envelopeInput_nonneg (C Beta A B : Box) :
    0 ≤ -(qval scale (FixedPointCubic.cellExponentBox C Beta A B).hi : ℝ) := by
  simp only [qval, Rat.cast_div, Rat.cast_intCast]
  exact neg_nonneg.mpr (div_nonpos_of_nonpos_of_nonneg
    (by exact_mod_cast FixedPointCubic.cellExponentBox_hi_nonpos C Beta A B)
    (by exact_mod_cast scale_positive.le))

def envelopeUpper (C Beta A B : Box) (m : ℕ)
    (hden : 0 < (expDen (envelopeInputBox C Beta A B) m).lo)
    (hpos : 0 < (expPositive (envelopeInputBox C Beta A B) m hden).lo) : ℤ :=
  FixedPointUpper.expUpper scale scale_positive (envelopeInputBox C Beta A B) m hden hpos

/-- The computed upper controls the actual second-integral envelope on
the whole closed frequency cell. The three maxima and min0 are inherited
from the proved cellExponentBox; truncation at 32 is supplied by expUpper. -/
theorem envelope_le_upper {C Beta A B : Box} {c beta a b t : ℝ}
    (hC : Contains scale C c) (hBeta : Contains scale Beta beta)
    (hA : Contains scale A a) (hB : Contains scale B b)
    (hc : 0 ≤ c) (hbeta : 0 ≤ beta) (ha : 0 ≤ a) (_hab : a ≤ b)
    (ht : t ∈ Set.Icc a b) (m : ℕ)
    (hden : 0 < (expDen (envelopeInputBox C Beta A B) m).lo)
    (hpos : 0 < (expPositive (envelopeInputBox C Beta A B) m hden).lo) :
    CoefficientRayPrice.envelope c beta t ≤
      (qval scale (envelopeUpper C Beta A B m hden hpos) : ℝ) := by
  have hcell := FixedPointCubic.envelope_le_exp_upper hC hBeta hA hB hc hbeta ha ht
  have hcell' : CoefficientRayPrice.envelope c beta t ≤
      Real.exp (qval scale (FixedPointCubic.cellExponentBox C Beta A B).hi : ℝ) := by
    simpa only [qval, Rat.cast_div, Rat.cast_intCast] using hcell
  have hexp := FixedPointUpper.exp_neg_le_upper scale_positive
    (envelopeInputBox_contains C Beta A B) (envelopeInput_nonneg C Beta A B) m hden hpos
  exact hcell'.trans (by simpa only [neg_neg, envelopeUpper] using hexp)

def gaussianInputBox (A : Box) : Box := divInt (sq scale scale_positive A) 2 (by decide)

theorem gaussianInputBox_contains {A : Box} {a : ℝ} (hA : Contains scale A a) :
    Contains scale (gaussianInputBox A) (a ^ 2 / 2) := by
  simpa only [gaussianInputBox, Int.cast_ofNat] using
    divInt_contains scale_positive (by decide : (0 : ℤ) < 2) (sq_contains scale_positive hA)

def gaussianUpper (A : Box) (m : ℕ)
    (hden : 0 < (expDen (gaussianInputBox A) m).lo)
    (hpos : 0 < (expPositive (gaussianInputBox A) m hden).lo) : ℤ :=
  FixedPointUpper.expUpper scale scale_positive (gaussianInputBox A) m hden hpos

/-- A left endpoint controls the actual Gaussian on the entire ray t>=a>=0. -/
theorem gaussian_le_upper {A : Box} {a t : ℝ} (hA : Contains scale A a)
    (ha : 0 ≤ a) (hat : a ≤ t) (m : ℕ)
    (hden : 0 < (expDen (gaussianInputBox A) m).lo)
    (hpos : 0 < (expPositive (gaussianInputBox A) m hden).lo) :
    Real.exp (-(t ^ 2 / 2)) ≤ (qval scale (gaussianUpper A m hden hpos) : ℝ) := by
  have hsq := pow_le_pow_left₀ ha hat 2
  have hmono : Real.exp (-(t ^ 2 / 2)) ≤ Real.exp (-(a ^ 2 / 2)) :=
    Real.exp_le_exp.mpr (by linarith only [hsq])
  exact hmono.trans (FixedPointUpper.exp_neg_le_upper scale_positive
    (gaussianInputBox_contains hA) (by positivity) m hden hpos)

/-- S is an explicit computational argument; this checker supports the
existing certified scale40 constants and rejects every other scale. -/
def envelopeCheck (S : ℤ) (m : ℕ) (C Beta A B : Box) (candidate : ℤ) : Bool :=
  if S = scale then
    if hden : 0 < (expDen (envelopeInputBox C Beta A B) m).lo then
      if hpos : 0 < (expPositive (envelopeInputBox C Beta A B) m hden).lo then
        decide (envelopeUpper C Beta A B m hden hpos ≤ candidate)
      else false
    else false
  else false

def gaussianCheck (S : ℤ) (m : ℕ) (A : Box) (candidate : ℤ) : Bool :=
  if S = scale then
    if hden : 0 < (expDen (gaussianInputBox A) m).lo then
      if hpos : 0 < (expPositive (gaussianInputBox A) m hden).lo then
        decide (gaussianUpper A m hden hpos ≤ candidate)
      else false
    else false
  else false

theorem envelopeCheck_sound {S : ℤ} {m : ℕ} {C Beta A B : Box}
    {c beta a b t : ℝ} {candidate : ℤ}
    (hC : Contains S C c) (hBeta : Contains S Beta beta)
    (hA : Contains S A a) (hB : Contains S B b)
    (hc : 0 ≤ c) (hbeta : 0 ≤ beta) (ha : 0 ≤ a) (hab : a ≤ b)
    (ht : t ∈ Set.Icc a b)
    (hcheck : envelopeCheck S m C Beta A B candidate = true) :
    CoefficientRayPrice.envelope c beta t ≤ (qval S candidate : ℝ) := by
  unfold envelopeCheck at hcheck
  split_ifs at hcheck with hscale hden hpos
  · subst S
    have hgate := of_decide_eq_true hcheck
    exact (envelope_le_upper hC hBeta hA hB hc hbeta ha hab ht m hden hpos).trans
      (by exact_mod_cast qval_mono scale_positive hgate)

theorem gaussianCheck_sound {S : ℤ} {m : ℕ} {A : Box} {a t : ℝ} {candidate : ℤ}
    (hA : Contains S A a) (ha : 0 ≤ a) (hat : a ≤ t)
    (hcheck : gaussianCheck S m A candidate = true) :
    Real.exp (-(t ^ 2 / 2)) ≤ (qval S candidate : ℝ) := by
  unfold gaussianCheck at hcheck
  split_ifs at hcheck with hscale hden hpos
  · subst S
    have hgate := of_decide_eq_true hcheck
    exact (gaussian_le_upper hA ha hat m hden hpos).trans
      (by exact_mod_cast qval_mono scale_positive hgate)

end BerryEsseen.FixedPointCellCheck

#print axioms BerryEsseen.FixedPointCellCheck.forcingCheck_sound
#print axioms BerryEsseen.FixedPointCellCheck.decayCheck_sound
#print axioms BerryEsseen.FixedPointCellCheck.envelope_le_upper
#print axioms BerryEsseen.FixedPointCellCheck.gaussian_le_upper
#print axioms BerryEsseen.FixedPointCellCheck.envelopeCheck_sound
#print axioms BerryEsseen.FixedPointCellCheck.gaussianCheck_sound
