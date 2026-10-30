module

public import BerryEsseen.SupportContact
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Tactic.FieldSimp

@[expose] public section

/-! 2026-10-28: the actual contact majorant used in the conserved-resource
identity. The tail law is H minus the genuine (n-1)-fold iid sum. Closed
events retain threshold atoms; differentiability is only asserted for the
explicit majorant, never for the original distribution function. -/

noncomputable section

open MeasureTheory Set

namespace BerryEsseen.ContactPolynomial

def predecessorTailLaw (μ : ProbabilityMeasure ℝ) (n : ℕ) (H : ℝ) :
    ProbabilityMeasure ℝ :=
  ⟨(MixtureSum.iidSumLaw (μ : Measure ℝ) (n - 1)).map
    (fun y : ℝ => H - y), inferInstance⟩

theorem predecessorTailLaw_closedTail (μ : ProbabilityMeasure ℝ)
    (n : ℕ) (H x : ℝ) :
    (predecessorTailLaw μ n H : Measure ℝ).real (Ici x) =
      (MixtureSum.iidSumLaw (μ : Measure ℝ) (n - 1)).real (Iic (H - x)) := by
  change ((MixtureSum.iidSumLaw (μ : Measure ℝ) (n - 1)).map
    (fun y : ℝ => H - y)).real (Ici x) = _
  rw [map_measureReal_apply (by fun_prop) measurableSet_Ici]
  congr 1
  ext y
  change x ≤ H - y ↔ y ≤ H - x
  constructor <;> intro h <;> linarith

def majorant (μ : ProbabilityMeasure ℝ) (n : ℕ) (H C x : ℝ) : ℝ :=
  (MixtureSum.iidSumLaw (μ : Measure ℝ) n).real (Iic H) -
    GaussianTools.phi (H / Real.sqrt n) / n *
      (Real.sqrt n * x + (H / Real.sqrt n) / 2 * (x ^ 2 - 1)) +
    C / ((n : ℝ) * Real.sqrt n) * ContactVariation.momentSlope μ x

def majorantSlope (μ : ProbabilityMeasure ℝ) (n : ℕ) (H C x : ℝ) : ℝ :=
  -(GaussianTools.phi (H / Real.sqrt n) / n) *
      (Real.sqrt n + (H / Real.sqrt n) * x) +
    C / ((n : ℝ) * Real.sqrt n) *
      (3 * x * |x| - 3 * thirdAbsoluteMoment μ * x -
        3 * SignedMoment.signedSecondMoment μ)

theorem hasDerivAt_momentSlope (μ : ProbabilityMeasure ℝ) (x : ℝ) :
    HasDerivAt (ContactVariation.momentSlope μ)
      (3 * x * |x| - 3 * thirdAbsoluteMoment μ * x -
        3 * SignedMoment.signedSecondMoment μ) x := by
  have hd := (((PerturbationMoment.hasDerivAt_abs_cube x).sub
    (((hasDerivAt_id x).fun_pow 2).const_mul
      ((3 / 2 : ℝ) * thirdAbsoluteMoment μ))).sub
    ((hasDerivAt_id x).const_mul (3 * SignedMoment.signedSecondMoment μ))).add_const
      (thirdAbsoluteMoment μ / 2)
  convert hd using 1
  · funext y
    rfl
  · simp only [id_eq]
    ring

theorem hasDerivAt_majorant (μ : ProbabilityMeasure ℝ) (n : ℕ) (H C x : ℝ) :
    HasDerivAt (majorant μ n H C) (majorantSlope μ n H C x) x := by
  have hlin := (hasDerivAt_id x).const_mul (Real.sqrt n)
  have hquad := (((hasDerivAt_id x).fun_pow 2).sub_const 1).const_mul
    ((H / Real.sqrt n) / 2)
  have hd := ((hasDerivAt_const x
    ((MixtureSum.iidSumLaw (μ : Measure ℝ) n).real (Iic H))).sub
    ((hlin.add hquad).const_mul (GaussianTools.phi (H / Real.sqrt n) / n))).add
    ((hasDerivAt_momentSlope μ x).const_mul (C / ((n : ℝ) * Real.sqrt n)))
  convert hd using 1
  · funext y
    rfl
  · simp only [majorantSlope, id_eq]
    ring

theorem continuous_majorant (μ : ProbabilityMeasure ℝ) (n : ℕ) (H C : ℝ) :
    Continuous (majorant μ n H C) :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_majorant μ n H C x).continuousAt

theorem continuous_majorantSlope (μ : ProbabilityMeasure ℝ) (n : ℕ) (H C : ℝ) :
    Continuous (majorantSlope μ n H C) := by
  unfold majorantSlope
  fun_prop

theorem contDiff_majorant (μ : ProbabilityMeasure ℝ) (n : ℕ) (H C : ℝ) :
    ContDiff ℝ 1 (majorant μ n H C) := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun x => (hasDerivAt_majorant μ n H C x).differentiableAt, ?_⟩
  have heq : deriv (majorant μ n H C) = majorantSlope μ n H C :=
    funext fun x => (hasDerivAt_majorant μ n H C x).deriv
  rw [heq]
  exact continuous_majorantSlope μ n H C

theorem D_eq_tail_sub_majorant (μ : ProbabilityMeasure ℝ) (n : ℕ) (hn : 0 < n)
    (H C x : ℝ) :
    ContactVariation.D μ n H C x = (n : ℝ) *
      ((predecessorTailLaw μ n H : Measure ℝ).real (Ici x) - majorant μ n H C x) := by
  have hn0 : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
  have hs0 : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)).ne'
  rw [predecessorTailLaw_closedTail]
  unfold ContactVariation.D majorant
  field_simp [hn0, hs0]
  ring

theorem closedTail_le_majorant (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (hn : 0 < n) (H C : ℝ)
    (hm : ContactVariation.PositiveClosedMaximum μ n H C) (x : ℝ) :
    (predecessorTailLaw μ n H : Measure ℝ).real (Ici x) ≤ majorant μ n H C x := by
  have hd := ContactVariation.D_nonpos μ h n hn H C hm x
  rw [D_eq_tail_sub_majorant μ n hn H C x] at hd
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  nlinarith

theorem majorant_eq_closedTail_on_support (μ : ProbabilityMeasure ℝ)
    (h : StandardizedLaw μ) (n : ℕ) (hn : 0 < n) (H C : ℝ)
    (hm : ContactVariation.PositiveClosedMaximum μ n H C) (x : ℝ)
    (hx : x ∈ (μ : Measure ℝ).support) :
    majorant μ n H C x = (predecessorTailLaw μ n H : Measure ℝ).real (Ici x) := by
  have hd := SupportContact.D_eq_zero_on_support μ h n hn H C hm x hx
  rw [D_eq_tail_sub_majorant μ n hn H C x] at hd
  have hzero := (mul_eq_zero.mp hd).resolve_left (Nat.cast_pos.mpr hn).ne'
  exact (sub_eq_zero.mp hzero).symm

theorem majorant_eq_closedTail_ae (μ : ProbabilityMeasure ℝ)
    (h : StandardizedLaw μ) (n : ℕ) (hn : 0 < n) (H C : ℝ)
    (hm : ContactVariation.PositiveClosedMaximum μ n H C) :
    majorant μ n H C =ᵐ[(μ : Measure ℝ)]
      (fun x => (predecessorTailLaw μ n H : Measure ℝ).real (Ici x)) := by
  filter_upwards [SupportContact.D_ae_eq_zero μ h n hn H C hm] with x hx
  change ContactVariation.D μ n H C x = 0 at hx
  rw [D_eq_tail_sub_majorant μ n hn H C x] at hx
  exact (sub_eq_zero.mp ((mul_eq_zero.mp hx).resolve_left (Nat.cast_pos.mpr hn).ne')).symm

end BerryEsseen.ContactPolynomial

#print axioms BerryEsseen.ContactPolynomial.predecessorTailLaw_closedTail
#print axioms BerryEsseen.ContactPolynomial.hasDerivAt_majorant
#print axioms BerryEsseen.ContactPolynomial.continuous_majorantSlope
#print axioms BerryEsseen.ContactPolynomial.contDiff_majorant
#print axioms BerryEsseen.ContactPolynomial.D_eq_tail_sub_majorant
#print axioms BerryEsseen.ContactPolynomial.closedTail_le_majorant
#print axioms BerryEsseen.ContactPolynomial.majorant_eq_closedTail_on_support
#print axioms BerryEsseen.ContactPolynomial.majorant_eq_closedTail_ae
