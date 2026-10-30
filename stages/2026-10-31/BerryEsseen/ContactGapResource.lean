module

public import BerryEsseen.ContactPolynomial
public import BerryEsseen.GapIntegration
public import BerryEsseen.GapDefect

@[expose] public section

/-!
The first resource evaluation for a single genuine gap of the original
law. The comparison law and majorant are the actual contact polynomial
objects. No summation or complement-coverage identity is asserted here.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology Interval

namespace BerryEsseen.ContactGapResource

open ZeroBias GapDefect ContactPolynomial

def Jg (μ : ProbabilityMeasure ℝ) (g : Gap μ) : ℝ := gapWeight μ g

def J1g (μ : ProbabilityMeasure ℝ) (g : Gap μ) : ℝ :=
  tau μ g.val.2 * (∫ t in g.val.1..g.val.2, (t - g.val.1) * t)

def J2g (μ : ProbabilityMeasure ℝ) (g : Gap μ) : ℝ :=
  tau μ g.val.2 * (∫ t in g.val.1..g.val.2, (t - g.val.1) * t * |t|)

def Lg (μ : ProbabilityMeasure ℝ) (n : ℕ) (H : ℝ) (g : Gap μ) : ℝ :=
  tau μ g.val.2 * (∫ y : ℝ in Ico g.val.1 g.val.2, y - g.val.1
    ∂(predecessorTailLaw μ n H : Measure ℝ))

def integrand (μ : ProbabilityMeasure ℝ) (n : ℕ) (H C t : ℝ) : ℝ :=
  tau μ t * (majorant μ n H C t - GapIntegration.closedTail (predecessorTailLaw μ n H) t)

def Ig (μ : ProbabilityMeasure ℝ) (n : ℕ) (H C : ℝ) (g : Gap μ) : ℝ :=
  ∫ t : ℝ in Ioo g.val.1 g.val.2, integrand μ n H C t

lemma Jg_eq_physical_gapWeight (μ : ProbabilityMeasure ℝ) (g : Gap μ) : Jg μ g = gapWeight μ g := rfl

lemma intervalIntegrable_gap0 (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ => t - a) volume a b :=
  (continuous_id.sub continuous_const).intervalIntegrable a b

lemma intervalIntegrable_gap1 (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ => (t - a) * t) volume a b :=
  ((continuous_id.sub continuous_const).mul continuous_id).intervalIntegrable a b

lemma intervalIntegrable_gap2 (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ => (t - a) * t * |t|) volume a b :=
  (((continuous_id.sub continuous_const).mul continuous_id).mul continuous_abs).intervalIntegrable a b

lemma integral_gap0 (a b : ℝ) : (∫ t in a..b, t - a) = (b - a) ^ 2 / 2 := by
  have hi : IntervalIntegrable (fun t : ℝ => t) volume a b := continuous_id.intervalIntegrable a b
  have hc : IntervalIntegrable (fun _ : ℝ => a) volume a b := intervalIntegrable_const
  rw [intervalIntegral.integral_sub hi hc,
    integral_id, intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

/-- Finite-interval evaluation of the actual slope; every term is L1
on the interval independently of any bound on the original support. -/
lemma majorantSlope_integral (μ : ProbabilityMeasure ℝ) (n : ℕ) (H C a b : ℝ) :
    (∫ t in a..b, (t - a) * majorantSlope μ n H C t) =
      (-(GaussianTools.phi (H / Real.sqrt n) / n) * Real.sqrt n -
          C / ((n : ℝ) * Real.sqrt n) * (3 * SignedMoment.signedSecondMoment μ)) * ((b - a) ^ 2 / 2) +
      (-(GaussianTools.phi (H / Real.sqrt n) / n) * (H / Real.sqrt n) -
          C / ((n : ℝ) * Real.sqrt n) * (3 * thirdAbsoluteMoment μ)) *
        (∫ t in a..b, (t - a) * t) +
      (C / ((n : ℝ) * Real.sqrt n) * 3) * (∫ t in a..b, (t - a) * t * |t|) := by
  let c0 := -(GaussianTools.phi (H / Real.sqrt n) / n) * Real.sqrt n -
    C / ((n : ℝ) * Real.sqrt n) * (3 * SignedMoment.signedSecondMoment μ)
  let c1 := -(GaussianTools.phi (H / Real.sqrt n) / n) * (H / Real.sqrt n) -
    C / ((n : ℝ) * Real.sqrt n) * (3 * thirdAbsoluteMoment μ)
  let c2 := C / ((n : ℝ) * Real.sqrt n) * 3
  have hfun : (fun t : ℝ => (t - a) * majorantSlope μ n H C t) =
      (fun t : ℝ => c0 * (t - a) + c1 * ((t - a) * t) + c2 * ((t - a) * t * |t|)) := by
    funext t
    dsimp [c0, c1, c2]
    unfold majorantSlope
    ring
  have h0 : IntervalIntegrable (fun t : ℝ => c0 * (t - a)) volume a b :=
    (intervalIntegrable_gap0 a b).const_mul c0
  have h1 : IntervalIntegrable (fun t : ℝ => c1 * ((t - a) * t)) volume a b :=
    (intervalIntegrable_gap1 a b).const_mul c1
  have h2 : IntervalIntegrable (fun t : ℝ => c2 * ((t - a) * t * |t|)) volume a b :=
    (intervalIntegrable_gap2 a b).const_mul c2
  have h01 : IntervalIntegrable (fun t : ℝ => c0 * (t - a) + c1 * ((t - a) * t)) volume a b := h0.add h1
  calc
    _ = ∫ t in a..b, c0 * (t - a) + c1 * ((t - a) * t) + c2 * ((t - a) * t * |t|) := by rw [hfun]
    _ = c0 * ((b - a) ^ 2 / 2) + c1 * (∫ t in a..b, (t - a) * t) +
        c2 * (∫ t in a..b, (t - a) * t * |t|) := by
      rw [intervalIntegral.integral_add h01 h2, intervalIntegral.integral_add h0 h1,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul, integral_gap0]
    _ = _ := rfl

lemma negative_tau_slope_integral (μ : ProbabilityMeasure ℝ) (n : ℕ) (hn : 0 < n)
    (H C : ℝ) (g : Gap μ) :
    -tau μ g.val.2 * (∫ t in g.val.1..g.val.2, (t - g.val.1) * majorantSlope μ n H C t) =
      GaussianTools.phi (H / Real.sqrt n) / (2 * Real.sqrt n) * Jg μ g +
      (((3 : ℝ) / 2) * C * SignedMoment.signedSecondMoment μ * Jg μ g +
        (H * GaussianTools.phi (H / Real.sqrt n) + 3 * C * thirdAbsoluteMoment μ) * J1g μ g -
        3 * C * J2g μ g) / ((n : ℝ) * Real.sqrt n) := by
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnR
  rw [majorantSlope_integral]
  unfold Jg gapWeight J1g J2g
  field_simp [hnR.ne', hs.ne']
  rw [Real.sq_sqrt (Nat.cast_nonneg n)]
  ring

theorem integrable_integrand_on_gap (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (H C : ℝ) (g : Gap μ) :
    IntegrableOn (integrand μ n H C) (Ioo g.val.1 g.val.2) := by
  unfold integrand
  exact GapIntegration.integrable_gap_resource μ (predecessorTailLaw μ n H) h
    g.val.1 g.val.2 g.property (majorant μ n H C) Set.univ isOpen_univ
    (contDiff_majorant μ n H C).contDiffOn (Set.subset_univ _)

theorem integrable_Lg_cost (μ : ProbabilityMeasure ℝ) (n : ℕ) (H : ℝ) (g : Gap μ) :
    IntegrableOn (fun y : ℝ => y - g.val.1) (Ico g.val.1 g.val.2)
      (predecessorTailLaw μ n H : Measure ℝ) :=
  GapIntegration.integrable_gap_cost (predecessorTailLaw μ n H) g.val.1 g.val.2

theorem Lg_nonneg (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (H : ℝ) (g : Gap μ) : 0 ≤ Lg μ n H g := by
  have hi : 0 ≤ (∫ y : ℝ in Ico g.val.1 g.val.2, y - g.val.1
      ∂(predecessorTailLaw μ n H : Measure ℝ)) := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ico] with y hy
    exact sub_nonneg.mpr hy.1
  exact mul_nonneg (tau_nonneg μ h g.val.2) hi

theorem Ig_nonneg (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (hn : 0 < n) (H C : ℝ)
    (hm : ContactVariation.PositiveClosedMaximum μ n H C) (g : Gap μ) : 0 ≤ Ig μ n H C g := by
  unfold Ig integrand GapIntegration.closedTail
  exact integral_nonneg fun t => mul_nonneg (tau_nonneg μ h t)
    (sub_nonneg.mpr (closedTail_le_majorant μ h n hn H C hm t))

/-- The exact single-gap contact resource, for the genuine predecessor
tail law and majorant of the same actual maximizer. -/
theorem single_gap_identity (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (hn : 0 < n) (H C : ℝ)
    (hm : ContactVariation.PositiveClosedMaximum μ n H C) (g : Gap μ) :
    Ig μ n H C g = GaussianTools.phi (H / Real.sqrt n) / (2 * Real.sqrt n) * Jg μ g +
      (((3 : ℝ) / 2) * C * SignedMoment.signedSecondMoment μ * Jg μ g +
        (H * GaussianTools.phi (H / Real.sqrt n) + 3 * C * thirdAbsoluteMoment μ) * J1g μ g -
        3 * C * J2g μ g) / ((n : ℝ) * Real.sqrt n) - Lg μ n H g := by
  have hqb : majorant μ n H C g.val.2 =
      GapIntegration.closedTail (predecessorTailLaw μ n H) g.val.2 := by
    unfold GapIntegration.closedTail
    exact majorant_eq_closedTail_on_support μ h n hn H C hm g.val.2 g.property.2.1
  have hb := GapIntegration.gap_resource_identity μ (predecessorTailLaw μ n H) h
    g.val.1 g.val.2 g.property (majorant μ n H C) Set.univ isOpen_univ
    (contDiff_majorant μ n H C).contDiffOn (Set.subset_univ _) hqb
  have hd : deriv (majorant μ n H C) = majorantSlope μ n H C :=
    funext (fun t => (hasDerivAt_majorant μ n H C t).deriv)
  rw [hd] at hb
  have hb' : Ig μ n H C g =
      -tau μ g.val.2 * (∫ t in g.val.1..g.val.2, (t - g.val.1) * majorantSlope μ n H C t) - Lg μ n H g := by
    simpa only [Ig, integrand, Lg] using hb
  rw [hb', negative_tau_slope_integral μ n hn H C g]

end BerryEsseen.ContactGapResource

#print axioms BerryEsseen.ContactGapResource.negative_tau_slope_integral
#print axioms BerryEsseen.ContactGapResource.integrable_integrand_on_gap
#print axioms BerryEsseen.ContactGapResource.Lg_nonneg
#print axioms BerryEsseen.ContactGapResource.Ig_nonneg
#print axioms BerryEsseen.ContactGapResource.single_gap_identity
