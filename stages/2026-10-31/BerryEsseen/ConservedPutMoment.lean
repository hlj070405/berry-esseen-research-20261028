module

public import BerryEsseen.FourierRemainder
public import BerryEsseen.GaussianPeano
public import BerryEsseen.ZeroBiasClosedTail

@[expose] public section

/-! 2026-10-28: actual put-square moments in the conserved-resource second
evaluation. The Fourier correction retains its original signed third moment,
and all payoff identities are identities of integrable functions under the
original iid sum and the actual Gaussian probability law. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open BerryEsseen.GaussianTools

namespace BerryEsseen.ConservedPutMoment

def put (H y : ℝ) : ℝ := max (H - y) 0

theorem put_square_eq (H y : ℝ) :
    put H y ^ 2 = ((y - H) ^ 2 - (y - H) * |y - H|) / 2 := by
  by_cases hy : y ≤ H
  · rw [put, max_eq_left (sub_nonneg.mpr hy), abs_of_nonpos (sub_nonpos.mpr hy)]
    ring
  · have hHy : H ≤ y := (lt_of_not_ge hy).le
    rw [put, max_eq_right (sub_nonpos.mpr hHy), abs_of_nonneg (sub_nonneg.mpr hHy)]
    ring

theorem integrable_put (ν : ProbabilityMeasure ℝ)
    (h2 : Integrable (fun y : ℝ => y ^ 2) (ν : Measure ℝ)) (H : ℝ) :
    Integrable (put H) (ν : Measure ℝ) :=
  ((integrable_const H).sub (CompensatedExpectation.integrable_first_of_second ν h2)).pos_part

theorem integrable_put_square (ν : ProbabilityMeasure ℝ)
    (h2 : Integrable (fun y : ℝ => y ^ 2) (ν : Measure ℝ)) (H : ℝ) :
    Integrable (fun y => put H y ^ 2) (ν : Measure ℝ) := by
  have hi := ((CompensatedExpectation.integrable_shift_square ν h2 H).sub
    (CompensatedExpectation.integrable_shift_signed_square ν h2 H)).div_const 2
  apply hi.congr (Filter.Eventually.of_forall (fun y => ?_))
  exact (put_square_eq H y).symm

theorem integral_put_square (ν : ProbabilityMeasure ℝ)
    (h2 : Integrable (fun y : ℝ => y ^ 2) (ν : Measure ℝ)) (H : ℝ) :
    (∫ y : ℝ, put H y ^ 2 ∂(ν : Measure ℝ)) =
      ((∫ y : ℝ, (y - H) ^ 2 ∂(ν : Measure ℝ)) -
        ∫ y : ℝ, (y - H) * |y - H| ∂(ν : Measure ℝ)) / 2 := by
  rw [show (fun y : ℝ => put H y ^ 2) =
    (fun y : ℝ => ((y - H) ^ 2 - (y - H) * |y - H|) / 2) by
      funext y; exact put_square_eq H y,
    integral_div, integral_sub (CompensatedExpectation.integrable_shift_square ν h2 H)
      (CompensatedExpectation.integrable_shift_signed_square ν h2 H)]

theorem integral_shift_square (ν : ProbabilityMeasure ℝ)
    (h2 : Integrable (fun y : ℝ => y ^ 2) (ν : Measure ℝ)) (H : ℝ) :
    (∫ y : ℝ, (y - H) ^ 2 ∂(ν : Measure ℝ)) =
      (∫ y : ℝ, y ^ 2 ∂(ν : Measure ℝ)) -
        (2 * H) * (∫ y : ℝ, y ∂(ν : Measure ℝ)) + H ^ 2 := by
  have h1 := CompensatedExpectation.integrable_first_of_second ν h2
  have hA : Integrable (fun y : ℝ => y ^ 2 - (2 * H) * y) (ν : Measure ℝ) :=
    h2.sub (h1.const_mul (2 * H))
  rw [show (fun y : ℝ => (y - H) ^ 2) =
    (fun y : ℝ => y ^ 2 - (2 * H) * y + H ^ 2) by funext y; ring,
    integral_add hA (integrable_const (H ^ 2)),
    integral_sub h2 (h1.const_mul (2 * H)), integral_const_mul]
  simp

theorem gaussian_second_moment (n : ℕ) :
    (∫ y : ℝ, y ^ 2 ∂(FourierRemainder.gaussianProbability n : Measure ℝ)) = (n : ℝ) := by
  have hv := variance_fun_id_gaussianReal (μ := (0 : ℝ)) (v := (n : NNReal))
  rw [variance_eq_integral (show AEMeasurable (fun y : ℝ => y)
    (gaussianReal 0 (n : NNReal)) from measurable_id.aemeasurable), integral_id_gaussianReal] at hv
  change (∫ y : ℝ, y ^ 2 ∂gaussianReal 0 (n : NNReal)) = (n : ℝ)
  simpa only [sub_zero, NNReal.coe_natCast] using hv

/-- Equal actual means and second moments remove the shifted-square part. -/
theorem put_square_difference (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (n : ℕ) (H : ℝ) :
    (∫ y : ℝ, put H y ^ 2 ∂MixtureSum.iidSumLaw (μ : Measure ℝ) n) -
      (∫ y : ℝ, put H y ^ 2 ∂(FourierRemainder.gaussianProbability n : Measure ℝ)) =
      -(1 / 2 : ℝ) *
        ((∫ y : ℝ, (y - H) * |y - H| ∂(Extremizer.iidSumProbability μ n : Measure ℝ)) -
          ∫ y : ℝ, (y - H) * |y - H| ∂(FourierRemainder.gaussianProbability n : Measure ℝ)) := by
  have hs := Extremizer.iidSum_moments μ hμ n
  have hg := FourierRemainder.gaussian_second_integrable n
  change (∫ y : ℝ, put H y ^ 2 ∂(Extremizer.iidSumProbability μ n : Measure ℝ)) - _ = _
  rw [integral_put_square (Extremizer.iidSumProbability μ n) hs.2.1 H,
    integral_put_square (FourierRemainder.gaussianProbability n) hg H,
    integral_shift_square (Extremizer.iidSumProbability μ n) hs.2.1 H,
    integral_shift_square (FourierRemainder.gaussianProbability n) hg H,
    hs.2.2.1, hs.2.2.2, FourierRemainder.gaussian_mean, gaussian_second_moment]
  ring

/-- The original Fourier remainder gives the exact actual put-square
correction, with the signed Edgeworth term subtracted before division. -/
theorem iid_put_square_fourier (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (n : ℕ) (hn : 0 < n) (H : ℝ) :
    (∫ y : ℝ, put H y ^ 2 ∂MixtureSum.iidSumLaw (μ : Measure ℝ) n) =
      (∫ y : ℝ, put H y ^ 2 ∂(FourierRemainder.gaussianProbability n : Measure ℝ)) +
        (FourierRemainder.value μ n H -
          (n : ℝ) * ZeroBias.gamma μ * phi (H / Real.sqrt n) / 3) / Real.sqrt n := by
  have hp := put_square_difference μ hμ n H
  have hv := FourierRemainder.value_eq_payoff μ hμ n hn H
  rw [show FourierRemainder.thirdMoment μ = ZeroBias.gamma μ from rfl] at hv
  have hm := congrArg (fun z : ℝ => Real.sqrt n * z) hp
  have he : FourierRemainder.value μ n H = Real.sqrt n *
      ((∫ y : ℝ, put H y ^ 2 ∂MixtureSum.iidSumLaw (μ : Measure ℝ) n) -
        ∫ y : ℝ, put H y ^ 2 ∂(FourierRemainder.gaussianProbability n : Measure ℝ)) +
      (n : ℝ) * ZeroBias.gamma μ * phi (H / Real.sqrt n) / 3 := by
    nlinarith only [hm, hv]
  have hroot : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)).ne'
  have hd :
      (∫ y : ℝ, put H y ^ 2 ∂MixtureSum.iidSumLaw (μ : Measure ℝ) n) -
        (∫ y : ℝ, put H y ^ 2 ∂(FourierRemainder.gaussianProbability n : Measure ℝ)) =
      (FourierRemainder.value μ n H -
        (n : ℝ) * ZeroBias.gamma μ * phi (H / Real.sqrt n) / 3) / Real.sqrt n :=
    (eq_div_iff hroot).mpr (by nlinarith only [he])
  linarith only [hd]

/-- The standard Gaussian put moment follows from the already proved true
Gaussian hinge moment, using its measure-preserving reflection. -/
theorem standard_gaussian_put_square (H : ℝ) :
    (∫ y : ℝ, put H y ^ 2 ∂gaussianReal 0 1) =
      (1 + H ^ 2) * Phi H + H * phi H := by
  have hmap : (gaussianReal 0 1).map (fun y : ℝ => -y) = gaussianReal 0 1 := by
    simpa only [neg_zero] using (gaussianReal_map_neg (μ := 0) (v := 1))
  have hi := integral_map (f := fun y : ℝ => put H y ^ 2)
    (by fun_prop : AEMeasurable (fun y : ℝ => -y) (gaussianReal 0 1))
    (by unfold put; fun_prop)
  rw [hmap] at hi
  calc
    _ = ∫ y : ℝ, 2 * GaussianPeano.hinge (-H) y ∂gaussianReal 0 1 := by
      rw [hi]
      apply integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
      unfold put GaussianPeano.hinge
      rw [show H - -y = y - -H by ring]
      ring
    _ = 2 * GaussianPeano.expectation (GaussianPeano.hinge (-H)) := by
      rw [integral_const_mul]
      rfl
    _ = _ := by
      rw [GaussianPeano.expectation_hinge, GaussianMills.Phi_neg, GaussianMills.phi_neg]
      unfold GaussianMills.tail
      ring

theorem map_standard_gaussian (n : ℕ) :
    (gaussianReal 0 1).map (fun y : ℝ => Real.sqrt n * y) =
      (FourierRemainder.gaussianProbability n : Measure ℝ) := by
  have hm := gaussianReal_map_const_mul (μ := 0) (v := 1) (Real.sqrt n)
  have hv : (NNReal.mk (Real.sqrt n ^ 2) (sq_nonneg _) * 1 : NNReal) = (n : NNReal) := by
    apply NNReal.coe_injective
    simp only [NNReal.coe_mk, NNReal.coe_natCast, mul_one]
    exact Real.sq_sqrt (Nat.cast_nonneg n)
  rw [mul_zero, hv] at hm
  exact hm

theorem put_scale (s H y : ℝ) (hs : 0 < s) :
    put H (s * y) = s * put (H / s) y := by
  have harg : H - s * y = s * (H / s - y) := by field_simp [hs.ne']
  unfold put
  calc
    max (H - s * y) 0 = max (s * (H / s - y)) (s * 0) := by rw [harg, mul_zero]
    _ = s * max (H / s - y) 0 := (mul_max_of_nonneg _ _ hs.le).symm

private theorem scaled_put_algebra (s H a b : ℝ) (hs : s ≠ 0) :
    s ^ 2 * ((1 + (H / s) ^ 2) * a + (H / s) * b) =
      (s ^ 2 + H ^ 2) * a + H * s * b := by
  field_simp [hs]

/-- Closed-form put-square moment of the actual variance-n Gaussian law.
Both reflection and scaling are push-forwards of the genuine Gaussian. -/
theorem gaussian_put_square (n : ℕ) (hn : 0 < n) (H : ℝ) :
    (∫ y : ℝ, put H y ^ 2 ∂(FourierRemainder.gaussianProbability n : Measure ℝ)) =
      ((n : ℝ) + H ^ 2) * Phi (H / Real.sqrt n) +
        H * Real.sqrt n * phi (H / Real.sqrt n) := by
  have hN : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hN
  have hs2 : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt hN.le
  rw [← map_standard_gaussian n, integral_map (by fun_prop) (by unfold put; fun_prop)]
  have hfun : (fun y : ℝ => put H (Real.sqrt n * y) ^ 2) =
      (fun y : ℝ => (n : ℝ) * put (H / Real.sqrt n) y ^ 2) := by
    funext y
    rw [put_scale _ _ _ hs, mul_pow, hs2]
  rw [hfun, integral_const_mul, standard_gaussian_put_square]
  calc
    _ = Real.sqrt (n : ℝ) ^ 2 *
        ((1 + (H / Real.sqrt n) ^ 2) * Phi (H / Real.sqrt n) +
          (H / Real.sqrt n) * phi (H / Real.sqrt n)) := by rw [hs2]
    _ = (Real.sqrt (n : ℝ) ^ 2 + H ^ 2) * Phi (H / Real.sqrt n) +
        H * Real.sqrt n * phi (H / Real.sqrt n) :=
      scaled_put_algebra _ _ _ _ hs.ne'
    _ = _ := by rw [hs2]

theorem iid_put_square_formula (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (n : ℕ) (hn : 0 < n) (H : ℝ) :
    (∫ y : ℝ, put H y ^ 2 ∂MixtureSum.iidSumLaw (μ : Measure ℝ) n) =
      ((n : ℝ) + H ^ 2) * Phi (H / Real.sqrt n) +
        H * Real.sqrt n * phi (H / Real.sqrt n) +
        (FourierRemainder.value μ n H -
          (n : ℝ) * ZeroBias.gamma μ * phi (H / Real.sqrt n) / 3) / Real.sqrt n := by
  rw [iid_put_square_fourier μ hμ n hn H, gaussian_put_square n hn H]

def closedIndicator (H y : ℝ) : ℝ := if y ≤ H then 1 else 0

theorem measurable_closedIndicator (H : ℝ) : Measurable (closedIndicator H) :=
  Measurable.ite (measurableSet_Iic (a := H)) measurable_const measurable_const

theorem closedIndicator_eq (H : ℝ) :
    closedIndicator H = (Iic H).indicator (fun _ : ℝ => (1 : ℝ)) := rfl

theorem integral_closedIndicator (ν : ProbabilityMeasure ℝ) (H : ℝ) :
    (∫ y : ℝ, closedIndicator H y ∂(ν : Measure ℝ)) = (ν : Measure ℝ).real (Iic H) := by
  rw [closedIndicator_eq, integral_indicator_const (1 : ℝ) measurableSet_Iic]
  simp

theorem integrable_truncated_first (ν : ProbabilityMeasure ℝ)
    (h2 : Integrable (fun y : ℝ => y ^ 2) (ν : Measure ℝ)) (H : ℝ) :
    Integrable (fun y : ℝ => y * closedIndicator H y) (ν : Measure ℝ) := by
  have heq : (fun y : ℝ => y * closedIndicator H y) = (Iic H).indicator (fun y : ℝ => y) := by
    funext y
    by_cases hy : y ≤ H <;> simp [closedIndicator, hy]
  rw [heq]
  exact (CompensatedExpectation.integrable_first_of_second ν h2).indicator measurableSet_Iic

theorem integral_put (ν : ProbabilityMeasure ℝ)
    (h2 : Integrable (fun y : ℝ => y ^ 2) (ν : Measure ℝ)) (H : ℝ) :
    (∫ y : ℝ, put H y ∂(ν : Measure ℝ)) =
      H * (ν : Measure ℝ).real (Iic H) -
        ∫ y : ℝ, y * closedIndicator H y ∂(ν : Measure ℝ) := by
  have hI : Integrable (closedIndicator H) (ν : Measure ℝ) := by
    rw [closedIndicator_eq]
    exact (integrable_const 1).indicator measurableSet_Iic
  have hT := integrable_truncated_first ν h2 H
  have heq : put H =
      (fun y : ℝ => H * closedIndicator H y - y * closedIndicator H y) := by
    funext y
    by_cases hy : y ≤ H
    · simp [put, closedIndicator, hy]
    · simp [put, closedIndicator, hy, max_eq_right (sub_nonpos.mpr (lt_of_not_ge hy).le)]
  rw [heq, integral_sub (hI.const_mul H) hT, integral_const_mul, integral_closedIndicator]

theorem marked_put_eq (H y : ℝ) :
    y * put H y = H * put H y - put H y ^ 2 := by
  by_cases hy : y ≤ H
  · rw [put, max_eq_left (sub_nonneg.mpr hy)]
    ring
  · rw [put, max_eq_right (sub_nonpos.mpr (lt_of_not_ge hy).le)]
    ring

theorem integrable_marked_put (ν : ProbabilityMeasure ℝ)
    (h2 : Integrable (fun y : ℝ => y ^ 2) (ν : Measure ℝ)) (H : ℝ) :
    Integrable (fun y : ℝ => y * put H y) (ν : Measure ℝ) := by
  apply (((integrable_put ν h2 H).const_mul H).sub
    (integrable_put_square ν h2 H)).congr (Filter.Eventually.of_forall (fun y => ?_))
  exact (marked_put_eq H y).symm

theorem integral_marked_put (ν : ProbabilityMeasure ℝ)
    (h2 : Integrable (fun y : ℝ => y ^ 2) (ν : Measure ℝ)) (H : ℝ) :
    (∫ y : ℝ, y * put H y ∂(ν : Measure ℝ)) =
      H * (∫ y : ℝ, put H y ∂(ν : Measure ℝ)) -
        ∫ y : ℝ, put H y ^ 2 ∂(ν : Measure ℝ) := by
  rw [show (fun y : ℝ => y * put H y) =
    (fun y : ℝ => H * put H y - put H y ^ 2) from funext (marked_put_eq H),
    integral_sub ((integrable_put ν h2 H).const_mul H) (integrable_put_square ν h2 H),
    integral_const_mul]

/-- Fubini and the proved marked closed-indicator identity connect the
actual predecessor closed tail to the actual sum's truncated first moment. -/
theorem marked_predecessor_closedTail_identity (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (n : ℕ) (hn : 0 < n) (H : ℝ) :
    (∫ x : ℝ, x * (ContactPolynomial.predecessorTailLaw μ n H : Measure ℝ).real (Ici x)
      ∂(μ : Measure ℝ)) =
      (1 / (n : ℝ)) * ∫ s : ℝ, s * closedIndicator H s
        ∂MixtureSum.iidSumLaw (μ : Measure ℝ) n := by
  have hi := IidExchangeability.integrable_marked_convolution μ hμ (n - 1)
    (closedIndicator H) (measurable_closedIndicator H) 1 0 (by norm_num) (by norm_num)
    (by intro s; unfold closedIndicator; split_ifs <;> norm_num)
  have hfiber (x : ℝ) :
      (∫ y : ℝ, x * closedIndicator H (x + y)
        ∂MixtureSum.iidSumLaw (μ : Measure ℝ) (n - 1)) =
      x * (ContactPolynomial.predecessorTailLaw μ n H : Measure ℝ).real (Ici x) := by
    rw [integral_const_mul, ContactPolynomial.predecessorTailLaw_closedTail]
    have heq : (fun y : ℝ => closedIndicator H (x + y)) =
        (Iic (H - x)).indicator (fun _ : ℝ => (1 : ℝ)) := by
      funext y
      have hc : x + y ≤ H ↔ y ≤ H - x := by constructor <;> intro h <;> linarith
      simp only [closedIndicator, Set.indicator_apply, mem_Iic, hc]
    rw [heq, integral_indicator_const (1 : ℝ) measurableSet_Iic]
    simp
  calc
    _ = ∫ x : ℝ, (∫ y : ℝ, x * closedIndicator H (x + y)
        ∂MixtureSum.iidSumLaw (μ : Measure ℝ) (n - 1)) ∂(μ : Measure ℝ) :=
      integral_congr_ae (Filter.Eventually.of_forall (fun x => (hfiber x).symm))
    _ = ∫ p : ℝ × ℝ, p.1 * closedIndicator H (p.1 + p.2)
        ∂((μ : Measure ℝ).prod (MixtureSum.iidSumLaw (μ : Measure ℝ) (n - 1))) :=
      (integral_prod _ hi).symm
    _ = _ := IidExchangeability.marked_closed_indicator_identity μ hμ n hn H

/-- The required second-evaluation put moment uses the same actual closed
CDF and predecessor tail, including threshold atoms. -/
theorem iid_marked_put_identity (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (n : ℕ) (hn : 0 < n) (H : ℝ) :
    (∫ s : ℝ, s * put H s ∂MixtureSum.iidSumLaw (μ : Measure ℝ) n) =
      H ^ 2 * (MixtureSum.iidSumLaw (μ : Measure ℝ) n).real (Iic H) -
        H * (n : ℝ) * (∫ x : ℝ, x *
          (ContactPolynomial.predecessorTailLaw μ n H : Measure ℝ).real (Ici x) ∂(μ : Measure ℝ)) -
        ∫ s : ℝ, put H s ^ 2 ∂MixtureSum.iidSumLaw (μ : Measure ℝ) n := by
  have h2 := (Extremizer.iidSum_moments μ hμ n).2.1
  have hW := marked_predecessor_closedTail_identity μ hμ n hn H
  have hn0 : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
  have hT : (∫ s : ℝ, s * closedIndicator H s ∂MixtureSum.iidSumLaw (μ : Measure ℝ) n) =
      (n : ℝ) * (∫ x : ℝ, x *
        (ContactPolynomial.predecessorTailLaw μ n H : Measure ℝ).real (Ici x) ∂(μ : Measure ℝ)) := by
    rw [hW]
    field_simp
  change (∫ s : ℝ, s * put H s ∂(Extremizer.iidSumProbability μ n : Measure ℝ)) = _
  rw [integral_marked_put (Extremizer.iidSumProbability μ n) h2 H,
    integral_put (Extremizer.iidSumProbability μ n) h2 H]
  change H * (H * (MixtureSum.iidSumLaw (μ : Measure ℝ) n).real (Iic H) -
    (∫ s : ℝ, s * closedIndicator H s ∂MixtureSum.iidSumLaw (μ : Measure ℝ) n)) -
    (∫ s : ℝ, put H s ^ 2 ∂MixtureSum.iidSumLaw (μ : Measure ℝ) n) = _
  rw [hT]
  ring

end BerryEsseen.ConservedPutMoment

#print axioms BerryEsseen.ConservedPutMoment.iid_put_square_fourier
#print axioms BerryEsseen.ConservedPutMoment.gaussian_put_square
#print axioms BerryEsseen.ConservedPutMoment.iid_put_square_formula
#print axioms BerryEsseen.ConservedPutMoment.marked_predecessor_closedTail_identity
#print axioms BerryEsseen.ConservedPutMoment.iid_marked_put_identity
