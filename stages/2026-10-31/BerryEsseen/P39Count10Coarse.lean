module

public import BerryEsseen.P39Count10Calculus
public import BerryEsseen.N26P39Count10Prices
public import BerryEsseen.PhaseInterpolation

@[expose] public section

/-! 2026-10-29: the actual fixed count-10 reference price on the whole
original P39 probability/phase box. Global Q supporting slopes are used
at its kinks. Signed product terms are retained before their signs are
proved; unequal endpoint heights are preserved in both chord bounds. -/

namespace BerryEsseen.P39Count10Coarse

open MeasureTheory Set Filter
open P39Count10Calculus
open P39Count11Face (strip domain)
open scoped Topology ContDiff

noncomputable section

private lemma delta_eq : N26P39Count10Prices.delta = P39Count11Face.delta := by
  norm_num [N26P39Count10Prices.delta, N26P39Count10Prices.deltaQ, P39Count11Face.delta, N26P39Price.inward]

private lemma ci_eq : N26P39Count10Prices.ci = ci := by
  norm_num [N26P39Count10Prices.ci, N26P39Count10Prices.ciQ, ci]

private lemma eta_eq (p : ℝ) : N26P39Count10Prices.eta p = eta p := by
  simp only [N26P39Count10Prices.eta, eta, delta_eq]

private lemma A_eq (p : ℝ) : N26P39Count10Prices.A p = A p := by
  simp only [N26P39Count10Prices.A, A, K, delta_eq]

private lemma argument_eq (p t : ℝ) : N26P39Count10Prices.argument p t = arg t p := by
  simp only [N26P39Count10Prices.argument, arg_eq, P39Reference.v, mul_assoc]

lemma price_eq (p t : ℝ) : N26P39Count10Prices.price p t = smoothBase t p + eta p *
    StopLossShape.Q N26P39Count10Prices.reference (A p + t) := by
  unfold N26P39Count10Prices.price
  rw [eta_eq, A_eq, argument_eq, ci_eq]
  unfold smoothBase baseline gaussian arg ProbabilityGaussianPrice.gaussianPrice
  ring

theorem probability_semiconvex {t : ℝ} (ht : t ∈ phaseStrip) :
    ConvexOn ℝ strip (fun p => N26P39Count10Prices.price p t + 27 * p ^ 2 / 2) := by
  have hconv := ConvexPriceComposition.Q_composition_semiconvex N26P39Count10Prices.reference
    N26P39Count10Prices.reference_integrable_sq (base := smoothBase t) (η := eta)
    (A := fun p => A p + t) (U := Ioo (0 : ℝ) 1) (a := 39 / 100) (b := 2 / 5) (M := 27)
    isOpen_Ioo (fun p hp => domain hp) (smoothBase_contDiffOn t) eta_contDiff.contDiffOn
    (A_contDiffOn.add contDiffOn_const) (fun p hp => eta_nonneg hp) (by
      intro p hp u hu
      have hpI : p ∈ strip := ⟨hp.1.le, hp.2.le⟩
      have hA := A_antitone hpI (by norm_num [strip]) hpI.2
      have hAt : N26P39Count10Prices.A (2 / 5) - (1 : ℝ) / 8 ≤ A p + t := by
        rw [A_eq]
        linarith only [hA, ht.1]
      have hQ := N26P39Count10Prices.Q_le_mill_of_threshold hAt
      have hQ0 := StopLossShape.Q_nonneg N26P39Count10Prices.reference (A p + t)
      have he := etaCurvature_bounds hpI
      have hcross : 0 ≤ 2 * etaSlope p * u * ASlope p :=
        mul_nonneg_of_nonpos_of_nonpos
          (mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by norm_num) (etaSlope_nonneg hpI)) hu.2)
          (ASlope_nonpos hpI)
      have hQterm : -(3 : ℝ) / 100 ≤ etaCurvature p * StopLossShape.Q N26P39Count10Prices.reference (A p + t) := by
        calc
          _ = (-30 : ℝ) * (1 / 1000) := by norm_num
          _ ≤ (-30 : ℝ) * StopLossShape.Q N26P39Count10Prices.reference (A p + t) :=
            mul_le_mul_of_nonpos_left hQ (by norm_num)
          _ ≤ _ := mul_le_mul_of_nonneg_right he.1 hQ0
      have ha := ACurvature_bounds hpI
      have hpA := mul_le_mul (eta_upper hpI) ha.2 ha.1 (by norm_num : (0 : ℝ) ≤ 9 / 50)
      have huA := mul_le_mul_of_nonneg_right hu.1 (mul_nonneg (eta_nonneg hpI) ha.1)
      have hlast : -(9 : ℝ) / 2 ≤ eta p * u * ACurvature p := by nlinarith only [hpA, huA]
      have hdA : deriv (fun q => A q + t) = deriv A := by funext q; simp only [deriv_add_const]
      rw [hdA, (hasDerivAt_eta (domain hpI)).deriv, (hasDerivAt_deriv_eta (domain hpI)).deriv,
        (hasDerivAt_A (domain hpI)).deriv, (hasDerivAt_deriv_A (domain hpI)).deriv]
      linarith only [smoothBaseCurvature_lower hpI ht, hQterm, hcross, hlast])
  simpa only [price_eq, strip] using hconv

theorem phase_semiconvex {p : ℝ} (hp : p ∈ strip) :
    ConvexOn ℝ phaseStrip (fun t => N26P39Count10Prices.price p t + (1 : ℝ) / 64 * t ^ 2 / 2) := by
  have hconv := ConvexPriceComposition.Q_composition_semiconvex N26P39Count10Prices.reference
    N26P39Count10Prices.reference_integrable_sq (base := phaseSmooth p) (η := fun _ => eta p)
    (A := fun t => A p + t) (U := univ) (a := -1 / 8) (b := 0) (M := 1 / 64)
    isOpen_univ (by intro t ht; trivial) (phaseSmooth_contDiff p).contDiffOn
    (by fun_prop) (by fun_prop) (fun t ht => eta_nonneg hp) (by
      intro t ht u hu
      have htI : t ∈ phaseStrip := ⟨ht.1.le, ht.2.le⟩
      have hdA : deriv (fun q : ℝ => A p + q) = (fun _ => 1) := by
        funext q
        exact ((hasDerivAt_id' q).const_add (A p)).deriv
      have hddA : deriv (deriv (fun q : ℝ => A p + q)) t = 0 := by rw [hdA]; simp
      simp only [deriv_const', deriv_const, zero_mul, mul_zero, add_zero, hddA]
      rw [deriv2_phaseSmooth hp]
      simpa only [neg_div] using phaseCurvature_lower hp htI)
  simpa only [price_eq, phaseSmooth, phaseStrip] using hconv

theorem lower_phase_face {p : ℝ} (hp : p ∈ strip) :
    N26P39Count10Prices.price p (-1 / 8) ≤ (-1 : ℝ) / 9000 := by
  have h := PhaseInterpolation.semiconvex_chord (fun q => N26P39Count10Prices.price q (-1 / 8))
    (39 / 100) (2 / 5) 27 (-28 / 100000) (-82 / 100000) (p - 39 / 100) (by norm_num)
    (probability_semiconvex (by norm_num [phaseStrip]))
    (by simpa only [neg_div] using N26P39Count10Prices.corner_lower_left)
    (by simpa only [neg_div] using N26P39Count10Prices.corner_lower_right)
    (by linarith only [hp.1]) (by linarith only [hp.2])
  rw [show (39 / 100 : ℝ) + (p - 39 / 100) = p by ring] at h
  nlinarith only [h, sq_nonneg (p - 39 / 100 - 3 / 1000)]

theorem upper_phase_face {p : ℝ} (hp : p ∈ strip) :
    N26P39Count10Prices.price p 0 ≤ (-1 : ℝ) / 9000 := by
  have h := PhaseInterpolation.semiconvex_chord (fun q => N26P39Count10Prices.price q 0)
    (39 / 100) (2 / 5) 27 (-69 / 100000) (-28 / 100000) (p - 39 / 100) (by norm_num)
    (probability_semiconvex (by norm_num [phaseStrip]))
    (by simpa only [neg_div] using N26P39Count10Prices.corner_upper_left)
    (by simpa only [neg_div] using N26P39Count10Prices.corner_upper_right)
    (by linarith only [hp.1]) (by linarith only [hp.2])
  rw [show (39 / 100 : ℝ) + (p - 39 / 100) = p by ring] at h
  nlinarith only [h, sq_nonneg (p - 39 / 100 - 22 / 3375)]

/-- The entire original scalar probability/phase box, with the same
actual fixed two-group reference measure at every interior point. -/
theorem whole_box {p t : ℝ} (hp : p ∈ strip) (ht : t ∈ phaseStrip) :
    N26P39Count10Prices.price p t ≤ (-1 : ℝ) / 15000 := by
  have h := PhaseInterpolation.semiconvex_chord (N26P39Count10Prices.price p) (-1 / 8) 0 (1 / 64)
    (-1 / 9000) (-1 / 9000) (t + 1 / 8) (by norm_num) (phase_semiconvex hp)
    (lower_phase_face hp) (upper_phase_face hp) (by linarith only [ht.1]) (by linarith only [ht.2])
  rw [show (-1 / 8 : ℝ) + (t + 1 / 8) = t by ring] at h
  nlinarith only [h, sq_nonneg (t + 1 / 16)]

end

end BerryEsseen.P39Count10Coarse

#print axioms BerryEsseen.P39Count10Coarse.probability_semiconvex
#print axioms BerryEsseen.P39Count10Coarse.phase_semiconvex
#print axioms BerryEsseen.P39Count10Coarse.lower_phase_face
#print axioms BerryEsseen.P39Count10Coarse.upper_phase_face
#print axioms BerryEsseen.P39Count10Coarse.whole_box
