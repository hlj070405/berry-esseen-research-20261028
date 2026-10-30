module

public import BerryEsseen.FixedPointUpperMomentRate

@[expose] public section

/-! 2026-10-30: rational W majorant for scalar gates.  This uses the existing
global W_le theorem and retains the same G/forcing comparison price. -/

noncomputable section

open Set

namespace BerryEsseen.FixedPointUpperMomentCoarseW

open FixedPointEnclosure FixedPointArithmetic FixedPointUpperMomentRate
open FixedFourierConstants (scale scale_positive)

def coarseWBox (U R : Box) (hU : 0 < U.lo) : Box :=
  add (divInt (sq scale scale_positive R) 2 (by decide))
    (divInt (mul scale scale_positive (dBox U hU) (cubeBox R)) 3 (by decide))

theorem coarseWBox_contains {U R : Box} (hU : 0 < U.lo) {u b : ℝ}
    (hu : Contains scale U u) (hb : Contains scale R b) :
    Contains scale (coarseWBox U R hU)
      (b ^ 2 / 2 + UpperMomentSpectrumPrice.d u * b ^ 3 / 3) := by
  simpa only [coarseWBox, Int.cast_ofNat] using
    add_contains scale_positive
      (divInt_contains scale_positive (by decide : (0 : ℤ) < 2) (sq_contains scale_positive hb))
      (divInt_contains scale_positive (by decide : (0 : ℤ) < 3)
        (mul_contains scale_positive (dBox_contains hU hu) (cubeBox_contains hb)))

def coarseWCheck (U R : Box) (W : ℤ) : Bool :=
  if hU : 0 < U.lo then
    decide (0 ≤ R.lo ∧ 0 ≤ W ∧ (coarseWBox U R hU).hi ≤ W)
  else false

theorem coarseWCheck_sound {U R : Box} {u b : ℝ} {W : ℤ}
    (hu : Contains scale U u) (hb : Contains scale R b)
    (hc : coarseWCheck U R W = true) : UpperMomentSpectrumPrice.W u b ≤ val W := by
  unfold coarseWCheck at hc
  split_ifs at hc with hU
  · rcases of_decide_eq_true hc with ⟨hb0, _hW0, hW⟩
    have hb0' := (val_nonneg hb0).trans hb.1
    exact (UpperMomentSpectrumPrice.W_le u b (pos_of_lo hu hU) hb0').trans
      ((coarseWBox_contains hU hu hb).2.trans (val_mono hW))

def coarseForcingCellCheck (U S L R : Box) (g norm m4 mr G W P H : ℤ) : Bool :=
  (rateCheck U L R g norm m4 mr G && coarseWCheck U R W) && forcingCheck U S G W P H

theorem coarseForcingCellCheck_sound {U S L R : Box} {u s a b v : ℝ}
    {g norm m4 mr G W P H : ℤ}
    (hu : Contains scale U u) (hs : Contains scale S s)
    (ha : Contains scale L a) (hb : Contains scale R b) (hv : v ∈ Icc a b)
    (hc : coarseForcingCellCheck U S L R g norm m4 mr G W P H = true) :
    s * Real.exp ((s - UpperMomentSpectrumPrice.d u) * UpperMomentDamping.G u u v) *
      UpperMomentSpectrumPrice.W u v ≤ val H := by
  have hchecks := Bool.and_eq_true_iff.mp hc
  have hleft := Bool.and_eq_true_iff.mp hchecks.1
  have hG := rateCheck_sound hu ha hb hv hleft.1
  have hW := coarseWCheck_sound hu hb hleft.2
  have hrate := hleft.1
  unfold rateCheck at hrate
  split_ifs at hrate with hU
  · have hg := Bool.and_eq_true_iff.mp hrate
    have hL0 := (of_decide_eq_true hg.2).1
    have hv0 := ((val_nonneg hL0).trans ha.1).trans hv.1
    exact forcingCheck_sound hu hs hv0 hG
      ((W_mono u v b (pos_of_lo hu hU) hv0 hv.2).trans hW) hchecks.2

end BerryEsseen.FixedPointUpperMomentCoarseW

#print axioms BerryEsseen.FixedPointUpperMomentCoarseW.coarseWCheck_sound
#print axioms BerryEsseen.FixedPointUpperMomentCoarseW.coarseForcingCellCheck_sound
