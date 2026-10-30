module

public import BerryEsseen.PhaseInterpolation
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-! 2026-10-29: a uniform endpoint chord for positive power-exponential
kernels. The exponential rate cancels in logarithmic interpolation.
The same endpoint weights and factor can therefore be integrated against
arbitrary nonnegative weights, without differentiating those integrals. -/

noncomputable section

open Real Set

namespace BerryEsseen.PowerExponentialEndpoint

lemma log_quadratic_convex (a b : ℝ) (ha : 0 < a) :
    ConvexOn ℝ (Icc a b) (fun x => Real.log x + (1 / a ^ 2) * x ^ 2 / 2) := by
  let gp : ℝ → ℝ := fun x => 1 / x + (1 / a ^ 2) * x
  let gpp : ℝ → ℝ := fun x => -(1 / x ^ 2) + 1 / a ^ 2
  have hlog : ContinuousOn Real.log (Icc a b) := by
    intro x hx
    exact (Real.continuousAt_log (ha.trans_le hx.1).ne').continuousWithinAt
  apply convexOn_of_hasDerivWithinAt2_nonneg (f' := gp) (f'' := gpp) (convex_Icc _ _)
    (hlog.add ((by fun_prop : Continuous (fun x : ℝ => (1 / a ^ 2) * x ^ 2 / 2)).continuousOn))
  · intro x hx
    have hx' : x ∈ Icc a b := interior_subset hx
    have hx0 : 0 < x := ha.trans_le hx'.1
    have hd := (Real.hasDerivAt_log hx0.ne').add
      ((((hasDerivAt_id' x).fun_pow 2).const_mul (1 / a ^ 2)).div_const 2)
    apply HasDerivAt.hasDerivWithinAt
    convert hd using 1
    dsimp [gp]
    simp only [one_div]
    ring
  · intro x hx
    have hx' : x ∈ Icc a b := interior_subset hx
    have hx0 : 0 < x := ha.trans_le hx'.1
    have hd := ((hasDerivAt_const x (1 : ℝ)).fun_div (hasDerivAt_id' x) hx0.ne').add
      ((hasDerivAt_id' x).const_mul (1 / a ^ 2))
    apply HasDerivAt.hasDerivWithinAt
    convert hd using 1
    dsimp [gpp]
    ring
  · intro x hx
    have hx' : x ∈ Icc a b := interior_subset hx
    have hx0 : 0 < x := ha.trans_le hx'.1
    have hs : a ^ 2 ≤ x ^ 2 := (sq_le_sq₀ ha.le hx0.le).mpr hx'.1
    have hh := one_div_le_one_div_of_le (sq_pos_of_pos ha) hs
    dsimp [gpp]
    linarith only [hh]

theorem log_chord_gap (a b s : ℝ) (ha : 0 < a) (hab : a < b) (hs : s ∈ Icc a b) :
    Real.log s ≤ (b - s) / (b - a) * Real.log a +
      (s - a) / (b - a) * Real.log b + (b - a) ^ 2 / (8 * a ^ 2) := by
  have h := PhaseInterpolation.semiconvex_chord Real.log a b (1 / a ^ 2)
    (Real.log a) (Real.log b) (s - a) hab (log_quadratic_convex a b ha)
    le_rfl le_rfl (sub_nonneg.mpr hs.1) (by linarith only [hs.2])
  have hshift : a + (s - a) = s := by ring
  rw [hshift] at h
  have hgeom : (s - a) * (b - s) ≤ (b - a) ^ 2 / 4 := by
    nlinarith [sq_nonneg (s - (a + b) / 2)]
  have hM := mul_le_mul_of_nonneg_left hgeom
    (show 0 ≤ (1 / a ^ 2) / 2 by positivity)
  have hM' : (1 / a ^ 2) / 2 * (s - a) * (b - a - (s - a)) ≤
      (b - a) ^ 2 / (8 * a ^ 2) := by
    calc
      _ = (1 / a ^ 2) / 2 * ((s - a) * (b - s)) := by ring
      _ ≤ (1 / a ^ 2) / 2 * ((b - a) ^ 2 / 4) := hM
      _ = _ := by field_simp [ha.ne']; ring
  have hlin : Real.log a + (Real.log b - Real.log a) / (b - a) * (s - a) =
      (b - s) / (b - a) * Real.log a + (s - a) / (b - a) * Real.log b := by
    field_simp [sub_pos.mpr hab |>.ne']
    ring
  rw [hlin] at h
  linarith only [h, hM']

lemma powerExp_eq (x p R : ℝ) (hx : 0 < x) :
    x ^ p * Real.exp (-R * x) = Real.exp (p * Real.log x - R * x) := by
  rw [Real.rpow_def_of_pos hx, ← Real.exp_add]
  congr 1
  ring

/-- The factor and interpolation weights are independent of the rate R
and of p within [0,r]. This is the key to positive integral mixtures. -/
theorem powerExp_le_endpoint_mixture (a b s p R r : ℝ)
    (ha : 0 < a) (hab : a < b) (hs : s ∈ Icc a b) (hp0 : 0 ≤ p) (hpr : p ≤ r) :
    s ^ p * Real.exp (-R * s) ≤
      Real.exp (r * ((b - a) ^ 2 / (8 * a ^ 2))) *
        ((b - s) / (b - a) * (a ^ p * Real.exp (-R * a)) +
          (s - a) / (b - a) * (b ^ p * Real.exp (-R * b))) := by
  let w0 := (b - s) / (b - a)
  let w1 := (s - a) / (b - a)
  let D := (b - a) ^ 2 / (8 * a ^ 2)
  have hH : 0 < b - a := sub_pos.mpr hab
  have hw0 : 0 ≤ w0 := div_nonneg (sub_nonneg.mpr hs.2) hH.le
  have hw1 : 0 ≤ w1 := div_nonneg (sub_nonneg.mpr hs.1) hH.le
  have hsum : w0 + w1 = 1 := by dsimp [w0, w1]; field_simp [hH.ne']; ring
  have hpoint : s = w0 * a + w1 * b := by dsimp [w0, w1]; field_simp [hH.ne']; ring
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hlog := mul_le_mul_of_nonneg_left (log_chord_gap a b s ha hab hs) hp0
  have hpd := mul_le_mul_of_nonneg_right hpr hD
  let A := p * Real.log a - R * a
  let B := p * Real.log b - R * b
  have hC : p * Real.log s - R * s ≤ w0 * A + w1 * B + r * D := by
    have heq : p * (w0 * Real.log a + w1 * Real.log b + D) - R * s =
        w0 * A + w1 * B + p * D := by rw [hpoint]; dsimp [A, B]; ring
    change p * Real.log s ≤ p * (w0 * Real.log a + w1 * Real.log b + D) at hlog
    have hh : p * Real.log s - R * s ≤
        p * (w0 * Real.log a + w1 * Real.log b + D) - R * s := by linarith only [hlog]
    rw [heq] at hh
    linarith only [hh, hpd]
  have hJ := convexOn_exp.2 (mem_univ A) (mem_univ B) hw0 hw1 hsum
  change Real.exp (w0 * A + w1 * B) ≤ w0 * Real.exp A + w1 * Real.exp B at hJ
  rw [powerExp_eq s p R (ha.trans_le hs.1), powerExp_eq a p R ha,
    powerExp_eq b p R (ha.trans hab)]
  calc
    _ ≤ Real.exp (w0 * A + w1 * B + r * D) := Real.exp_le_exp.mpr hC
    _ = Real.exp (r * D) * Real.exp (w0 * A + w1 * B) := by rw [Real.exp_add]; ring
    _ ≤ Real.exp (r * D) * (w0 * Real.exp A + w1 * Real.exp B) :=
      mul_le_mul_of_nonneg_left hJ (Real.exp_pos _).le

end BerryEsseen.PowerExponentialEndpoint

#print axioms BerryEsseen.PowerExponentialEndpoint.log_chord_gap
#print axioms BerryEsseen.PowerExponentialEndpoint.powerExp_le_endpoint_mixture
