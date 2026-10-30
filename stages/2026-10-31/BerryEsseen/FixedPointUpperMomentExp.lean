module

public import BerryEsseen.FixedPointUpperMomentRate

@[expose] public section

/-! 2026-10-30: executable exponential and row gates in pure spectral
coordinates. The same actual G is supplied by rateCheck_sound; positive
point witnesses represent only their chosen rational upper values. -/

open Set

namespace BerryEsseen.FixedPointUpperMomentExp

open FixedPointEnclosure FixedPointArithmetic
open FixedFourierConstants (scale scale_positive)
open FixedPointUpper (point point_contains)
open FixedPointUpperMomentRate (val val_mono val_nonneg expCheck expCheck_sound)

def powerInputBox (S : Box) (G : ℤ) : Box :=
  neg (mul scale scale_positive S (point G))

def powerCheck (S : Box) (G Q : ℤ) : Bool :=
  decide (0 ≤ S.lo) && expCheck (powerInputBox S G) Q

theorem powerCheck_sound {S : Box} {s g : ℝ} {G Q : ℤ}
    (hs : Contains scale S s) (hg : g ≤ val G)
    (hc : powerCheck S G Q = true) : Real.exp (s * g) ≤ val Q := by
  have hh := Bool.and_eq_true_iff.mp hc
  have hs0 := (val_nonneg (of_decide_eq_true hh.1)).trans hs.1
  have hinput : Contains scale (powerInputBox S G) (-(s * val G)) :=
    neg_contains scale_positive
      (mul_contains scale_positive hs (point_contains scale G))
  have he := expCheck_sound hinput hh.2
  rw [neg_neg] at he
  exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hg hs0)).trans he

def powerCellCheck (U S L R : Box) (g norm m4 mr G Q : ℤ) : Bool :=
  FixedPointUpperMomentRate.rateCheck U L R g norm m4 mr G && powerCheck S G Q

theorem powerCellCheck_sound {U S L R : Box} {u s a b v : ℝ}
    {g norm m4 mr G Q : ℤ}
    (hu : Contains scale U u) (hs : Contains scale S s)
    (ha : Contains scale L a) (hb : Contains scale R b) (hv : v ∈ Icc a b)
    (hc : powerCellCheck U S L R g norm m4 mr G Q = true) :
    Real.exp (s * UpperMomentDamping.G u u v) ≤ val Q := by
  have hh := Bool.and_eq_true_iff.mp hc
  exact powerCheck_sound hs
    (FixedPointUpperMomentRate.rateCheck_sound hu ha hb hv hh.1) hh.2

def gaussianInputBox (S L : Box) : Box :=
  divInt (mul scale scale_positive S (sq scale scale_positive L)) 2 (by decide)

def gaussianCheck (S L : Box) (E : ℤ) : Bool :=
  decide (0 ≤ S.lo ∧ 0 ≤ L.lo) && expCheck (gaussianInputBox S L) E

theorem gaussianCheck_sound {S L : Box} {s a v : ℝ} {E : ℤ}
    (hs : Contains scale S s) (ha : Contains scale L a) (hav : a ≤ v)
    (hc : gaussianCheck S L E = true) : Real.exp (-s * v ^ 2 / 2) ≤ val E := by
  have hh := Bool.and_eq_true_iff.mp hc
  have hnn := of_decide_eq_true hh.1
  have hs0 := (val_nonneg hnn.1).trans hs.1
  have ha0 := (val_nonneg hnn.2).trans ha.1
  have hsq := pow_le_pow_left₀ ha0 hav 2
  have hinput : Contains scale (gaussianInputBox S L) (s * a ^ 2 / 2) := by
    simpa only [gaussianInputBox, Int.cast_ofNat] using
      divInt_contains scale_positive (by decide : (0 : ℤ) < 2)
        (mul_contains scale_positive hs (sq_contains scale_positive ha))
  have he := expCheck_sound hinput hh.2
  have hp : -s * v ^ 2 / 2 ≤ -(s * a ^ 2 / 2) := by
    nlinarith only [mul_le_mul_of_nonneg_left hsq hs0]
  exact (Real.exp_le_exp.mpr hp).trans he

def productBox (Dt : Box) (K E : ℤ) : Box :=
  mul scale scale_positive (mul scale scale_positive Dt (point K)) (point E)

def productCheck (Dt : Box) (K E row : ℤ) : Bool :=
  decide ((productBox Dt K E).hi ≤ row)

theorem productCheck_sound {Dt : Box} {dt : ℝ} {K E row : ℤ}
    (hdt : Contains scale Dt dt) (hc : productCheck Dt K E row = true) :
    dt * val K * val E ≤ val row := by
  have hb := mul_contains scale_positive
    (mul_contains scale_positive hdt (point_contains scale K)) (point_contains scale E)
  exact hb.2.trans (val_mono (of_decide_eq_true hc))

def firstRowBox (Dt : Box) (K R H : ℤ) : Box :=
  mul scale scale_positive (mul scale scale_positive Dt (point K))
    (add (point R) (mul scale scale_positive Dt (point H)))

def firstRowCheck (Dt : Box) (K R H row : ℤ) : Bool :=
  decide ((firstRowBox Dt K R H).hi ≤ row)

theorem firstRowCheck_sound {Dt : Box} {dt : ℝ} {K R H row : ℤ}
    (hdt : Contains scale Dt dt) (hc : firstRowCheck Dt K R H row = true) :
    dt * val K * (val R + dt * val H) ≤ val row := by
  have hb := mul_contains scale_positive
    (mul_contains scale_positive hdt (point_contains scale K))
    (add_contains scale_positive (point_contains scale R)
      (mul_contains scale_positive hdt (point_contains scale H)))
  exact hb.2.trans (val_mono (of_decide_eq_true hc))

end BerryEsseen.FixedPointUpperMomentExp

#print axioms BerryEsseen.FixedPointUpperMomentExp.powerCellCheck_sound
#print axioms BerryEsseen.FixedPointUpperMomentExp.gaussianCheck_sound
#print axioms BerryEsseen.FixedPointUpperMomentExp.productCheck_sound
#print axioms BerryEsseen.FixedPointUpperMomentExp.firstRowCheck_sound
