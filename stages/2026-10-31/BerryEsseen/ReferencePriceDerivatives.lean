module

public import BerryEsseen.BinomialReferencePrice
public import BerryEsseen.GaussianPeano
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Slope

@[expose] public section

/-!
Continuous first derivatives of the actual finite reference price.
The squared positive part is proved C1 at its knot as well as away
from it. The exact binomial identity then transports this regularity
to K; the native variance derivative bounds use the proved increment
inequality for that same actual expectation.
-/

namespace BerryEsseen.TwoMoment

open MeasureTheory Filter Set
open scoped BigOperators Topology ContDiff

noncomputable section

/-- The quadratic hinge has its native derivative also at the knot.
The strict sides reuse the established GaussianPeano local identities. -/
theorem hasDerivAt_hinge_zero (u : ℝ) :
    HasDerivAt (GaussianPeano.hinge 0) (GaussianPeano.hingeSlope 0 u) u := by
  rcases lt_trichotomy u 0 with hu | rfl | hu
  · have h := (hasDerivAt_const u (0 : ℝ)).congr_of_eventuallyEq
      (GaussianPeano.hinge_eventuallyEq_zero 0 u hu)
    simpa only [GaussianPeano.hingeSlope, sub_zero, max_eq_right hu.le] using h
  · simp only [GaussianPeano.hingeSlope, sub_self, max_self]
    apply hasDerivAt_iff_tendsto_slope.mpr
    have hslope : slope (GaussianPeano.hinge 0) 0 = (fun v : ℝ => max v 0 / 2) := by
      funext v
      rw [slope_def_field]
      simp only [GaussianPeano.hinge, sub_zero, sub_self, max_self,
        zero_pow (by decide : 2 ≠ 0), zero_div]
      by_cases hv : v ≤ 0
      · simp [max_eq_right hv]
      · have hv' : 0 < v := lt_of_not_ge hv
        rw [max_eq_left hv'.le]
        field_simp [hv'.ne']
    rw [hslope]
    have hc : Continuous (fun v : ℝ => max v 0 / 2) := by fun_prop
    have hc0 : ContinuousAt (fun v : ℝ => max v 0 / 2) 0 := hc.continuousAt
    have ht : Tendsto (fun v : ℝ => max v 0 / 2) (𝓝 (0 : ℝ)) (𝓝 0) := by
      simpa using hc0.tendsto
    exact ht.mono_left nhdsWithin_le_nhds
  · have h := (GaussianPeano.hasDerivAt_shift_square 0 u).congr_of_eventuallyEq
      (GaussianPeano.hinge_eventuallyEq_poly 0 u hu)
    simpa only [GaussianPeano.hingeSlope, sub_zero, max_eq_left hu.le] using h

/-- Continuous native first derivatives imply C1 for the hinge globally. -/
theorem contDiff_one_hinge_zero : ContDiff ℝ 1 (GaussianPeano.hinge 0) := by
  apply contDiff_one_iff_deriv.mpr
  constructor
  · exact fun u => (hasDerivAt_hinge_zero u).differentiableAt
  · have hd : deriv (GaussianPeano.hinge 0) = GaussianPeano.hingeSlope 0 :=
      funext (fun u => (hasDerivAt_hinge_zero u).deriv)
    rw [hd]
    unfold GaussianPeano.hingeSlope
    fun_prop

/-- The squared positive part is C1 across its activation point. -/
theorem contDiff_one_squarePositivePart : ContDiff ℝ 1 (fun x : ℝ => (max x 0) ^ 2) := by
  have h := (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => (2 : ℝ))).mul contDiff_one_hinge_zero
  convert h using 1
  funext x
  simp only [GaussianPeano.hinge, sub_zero]
  ring

/-- C1 regularity of the same true reference expectation on positive
variance, including every value at which any atom is activated. -/
theorem referenceSumPrice_contDiffOn (b : ℝ) (n : ℕ) (c : ℝ)
    (hb : 0 < b) (hn : 0 < n) :
    ContDiffOn ℝ 1 (fun V : ℝ => referenceSumPrice b n V c) (Ioi 0) := by
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hz : ContDiffOn ℝ 1 (fun V : ℝ => V / (n : ℝ)) (Ioi 0) :=
    (contDiffOn_id : ContDiffOn ℝ 1 (fun V : ℝ => V) (Ioi 0)).div_const _
  have hb2 : ContDiffOn ℝ 1 (fun _ : ℝ => b ^ 2) (Ioi 0) := contDiffOn_const
  have hden : ContDiffOn ℝ 1 (fun V : ℝ => b ^ 2 + V / (n : ℝ)) (Ioi 0) := hb2.add hz
  have hden0 : ∀ V ∈ Ioi (0 : ℝ), b ^ 2 + V / (n : ℝ) ≠ 0 := by
    intro V hV
    exact (add_pos (sq_pos_of_pos hb) (div_pos hV hnR)).ne'
  have hp : ContDiffOn ℝ 1
      (fun V : ℝ => (V / (n : ℝ)) / (b ^ 2 + V / (n : ℝ))) (Ioi 0) := by
    convert hz.div hden hden0 using 1
  have hq : ContDiffOn ℝ 1
      (fun V : ℝ => b ^ 2 / (b ^ 2 + V / (n : ℝ))) (Ioi 0) := by
    convert hb2.div hden hden0 using 1
  have hsum : ContDiffOn ℝ 1 (fun V : ℝ =>
      ∑ j ∈ Finset.range (n + 1),
        (n.choose j : ℝ) * ((V / (n : ℝ)) / (b ^ 2 + V / (n : ℝ))) ^ j *
          (b ^ 2 / (b ^ 2 + V / (n : ℝ))) ^ (n - j) *
          (max ((j : ℝ) * b - ((n - j : ℕ) : ℝ) * (V / (n : ℝ)) / b - c) 0) ^ 2)
      (Ioi 0) := by
    apply ContDiffOn.sum
    intro j hj
    have hnj : ContDiffOn ℝ 1 (fun _ : ℝ => ((n - j : ℕ) : ℝ)) (Ioi 0) := contDiffOn_const
    have hjb : ContDiffOn ℝ 1 (fun _ : ℝ => (j : ℝ) * b) (Ioi 0) := contDiffOn_const
    have hatom : ContDiffOn ℝ 1
        (fun V : ℝ => (j : ℝ) * b - ((n - j : ℕ) : ℝ) * (V / (n : ℝ)) / b - c) (Ioi 0) :=
      (hjb.sub ((hnj.mul hz).div_const b)).sub contDiffOn_const
    have htrunc := contDiff_one_squarePositivePart.fun_comp_contDiffOn hatom
    have hchoose : ContDiffOn ℝ 1 (fun _ : ℝ => (n.choose j : ℝ)) (Ioi 0) := contDiffOn_const
    exact ((hchoose.mul (hp.pow j)).mul (hq.pow (n - j))).mul htrunc
  apply hsum.congr
  intro V hV
  exact referenceSumPrice_eq_binomial_sum b n V c hb hn hV.le

theorem referenceSumPrice_differentiableAt (b : ℝ) (n : ℕ) (V c : ℝ)
    (hb : 0 < b) (hn : 0 < n) (hV : 0 < V) :
    DifferentiableAt ℝ (fun W : ℝ => referenceSumPrice b n W c) V :=
  ((referenceSumPrice_contDiffOn b n c hb hn).contDiffAt (isOpen_Ioi.mem_nhds hV)).differentiableAt_one

theorem referenceSumPrice_continuousOn_deriv (b : ℝ) (n : ℕ) (c : ℝ)
    (hb : 0 < b) (hn : 0 < n) :
    ContinuousOn (deriv (fun V : ℝ => referenceSumPrice b n V c)) (Ioi 0) :=
  (referenceSumPrice_contDiffOn b n c hb hn).continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl

/-- The actual native derivative of K in total variance lies in [0,1].
Differentiability is established above, not supplied as an assumption. -/
theorem referenceSumPrice_deriv_bounds (b : ℝ) (n : ℕ) (V c : ℝ)
    (hb : 0 < b) (hn : 0 < n) (hV : 0 < V) :
    0 ≤ deriv (fun W : ℝ => referenceSumPrice b n W c) V ∧
      deriv (fun W : ℝ => referenceSumPrice b n W c) V ≤ 1 := by
  have hmono : MonotoneOn (fun W : ℝ => referenceSumPrice b n W c) (Ioi 0) := by
    intro x hx y hy hxy
    exact sub_nonneg.mp (referenceSumPrice_variance_increment b n x y c hb hn hx.le hxy).1
  have hrem : MonotoneOn (fun W : ℝ => W - referenceSumPrice b n W c) (Ioi 0) := by
    intro x hx y hy hxy
    have h := (referenceSumPrice_variance_increment b n x y c hb hn hx.le hxy).2
    linarith
  have hnonneg : 0 ≤ derivWithin (fun W : ℝ => referenceSumPrice b n W c) (Ioi 0) V :=
    hmono.derivWithin_nonneg
  rw [derivWithin_of_isOpen isOpen_Ioi hV] at hnonneg
  have hrem_nonneg : 0 ≤ derivWithin (fun W : ℝ => W - referenceSumPrice b n W c) (Ioi 0) V :=
    hrem.derivWithin_nonneg
  have hD := (referenceSumPrice_differentiableAt b n V c hb hn hV).hasDerivAt
  have hremD : HasDerivAt (fun W : ℝ => W - referenceSumPrice b n W c)
      (1 - deriv (fun W : ℝ => referenceSumPrice b n W c) V) V := by
    convert (hasDerivAt_id' V).sub hD using 1
  rw [derivWithin_of_isOpen isOpen_Ioi hV, hremD.deriv] at hrem_nonneg
  exact ⟨hnonneg, by linarith⟩

end

end BerryEsseen.TwoMoment

#print axioms BerryEsseen.TwoMoment.hasDerivAt_hinge_zero
#print axioms BerryEsseen.TwoMoment.contDiff_one_squarePositivePart
#print axioms BerryEsseen.TwoMoment.referenceSumPrice_contDiffOn
#print axioms BerryEsseen.TwoMoment.referenceSumPrice_deriv_bounds
