module

public import BerryEsseen.ZeroBiasTransport
public import BerryEsseen.IidExchangeability
public import BerryEsseen.ContactPolynomial

@[expose] public section

/-! 2026-10-28: evaluation of the actual closed-tail zero-bias integral.
The primitive is obtained by finite-interval Fubini and Lebesgue interval
lengths. The original distribution function is never differentiated. -/

noncomputable section

open MeasureTheory Set
open scoped Interval

namespace BerryEsseen.ZeroBiasClosedTail

def closedTail (ν : ProbabilityMeasure ℝ) (t : ℝ) : ℝ :=
  (ν : Measure ℝ).real (Ici t)

theorem antitone_closedTail (ν : ProbabilityMeasure ℝ) : Antitone (closedTail ν) := by
  intro a b hab
  exact measureReal_mono (Ici_subset_Ici.mpr hab)

theorem measurable_closedTail (ν : ProbabilityMeasure ℝ) : Measurable (closedTail ν) :=
  (antitone_closedTail ν).measurable

theorem abs_closedTail_le_one (ν : ProbabilityMeasure ℝ) (t : ℝ) :
    |closedTail ν t| ≤ 1 := by
  rw [abs_of_nonneg (show 0 ≤ closedTail ν t from ENNReal.toReal_nonneg)]
  exact measureReal_le_one

theorem closedTail_eq_integral (ν : ProbabilityMeasure ℝ) (t : ℝ) :
    closedTail ν t = ∫ y : ℝ, (if t ≤ y then (1 : ℝ) else 0) ∂(ν : Measure ℝ) := by
  change (ν : Measure ℝ).real (Ici t) =
    ∫ y : ℝ, (Ici t).indicator (fun _ : ℝ => (1 : ℝ)) y ∂(ν : Measure ℝ)
  rw [integral_indicator measurableSet_Ici, setIntegral_const]
  simp

/-- A genuine L1 bound on the indicator product over each finite interval. -/
theorem integrable_indicator_product (ν : ProbabilityMeasure ℝ) (a b : ℝ) :
    Integrable (fun p : ℝ × ℝ => if p.2 ≤ p.1 then (1 : ℝ) else 0)
      ((ν : Measure ℝ).prod (volume.restrict (Ioc a b))) := by
  apply (integrable_const (1 : ℝ)).mono'
    ((Measurable.ite (measurableSet_le measurable_snd measurable_fst)
      measurable_const measurable_const).aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun p => by split_ifs <;> norm_num)

theorem integral_closed_indicator_Ioc (a b y : ℝ) :
    (∫ t : ℝ in Ioc a b, if t ≤ y then (1 : ℝ) else 0) =
      max (min b y - a) 0 := by
  change (∫ t : ℝ in Ioc a b, (Iic y).indicator (fun _ : ℝ => (1 : ℝ)) t) = _
  rw [integral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic]
  have hset : Iic y ∩ Ioc a b = Ioc a (min b y) := by
    rw [inter_comm, Ioc_inter_Iic]
  rw [hset, setIntegral_const, Real.volume_real_Ioc]
  simp

/-- Closed threshold atoms are retained under ν; the outer integration is
Lebesgue integration, where interval endpoints have zero measure. -/
theorem integral_tail_Ioc (ν : ProbabilityMeasure ℝ) (a b : ℝ) :
    (∫ t : ℝ in Ioc a b, closedTail ν t) =
      ∫ y : ℝ, (∫ t : ℝ in Ioc a b, if t ≤ y then (1 : ℝ) else 0) ∂(ν : Measure ℝ) := by
  calc
    _ = ∫ t : ℝ in Ioc a b,
        (∫ y : ℝ, if t ≤ y then (1 : ℝ) else 0 ∂(ν : Measure ℝ)) :=
      integral_congr_ae (Filter.Eventually.of_forall (closedTail_eq_integral ν))
    _ = _ := (integral_integral_swap (integrable_indicator_product ν a b)).symm

/-- The exact primitive follows from Fubini, with no primitive identity as
an input and with no moment assumption at all on the tail law. -/
theorem primitive_closedTail (ν : ProbabilityMeasure ℝ) (x : ℝ) :
    ZeroBiasTransport.primitive (closedTail ν) x =
      ∫ y : ℝ, (max y 0 - max (y - x) 0) ∂(ν : Measure ℝ) := by
  change (∫ t : ℝ in Ioc 0 x, closedTail ν t) -
    (∫ t : ℝ in Ioc x 0, closedTail ν t) = _
  rw [integral_tail_Ioc, integral_tail_Ioc]
  rw [← integral_sub (integrable_indicator_product ν 0 x).integral_prod_left
    (integrable_indicator_product ν x 0).integral_prod_left]
  apply integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
  rw [integral_closed_indicator_Ioc, integral_closed_indicator_Ioc]
  simp only [min_def, max_def]
  split_ifs <;> linarith

/-- A finite first moment of ν suffices, since the original law supplies
the square term in |X|(Y-X)+ ≤ |X||Y| + X². -/
theorem integrable_marked_stoploss (μ ν : ProbabilityMeasure ℝ)
    (hμ : StandardizedLaw μ) (hν : Integrable (fun y : ℝ => y) (ν : Measure ℝ)) :
    Integrable (fun p : ℝ × ℝ => p.1 * max (p.2 - p.1) 0)
      ((μ : Measure ℝ).prod (ν : Measure ℝ)) := by
  have hdom := (hμ.integrable_mean.abs.mul_prod hν.abs).add
    (hμ.integrable_square.comp_fst (ν : Measure ℝ))
  apply hdom.mono' (by fun_prop)
  apply Filter.Eventually.of_forall
  intro p
  change |p.1 * max (p.2 - p.1) 0| ≤ |p.1| * |p.2| + p.1 ^ 2
  rw [abs_mul, abs_of_nonneg (le_max_right (p.2 - p.1) (0 : ℝ))]
  have hmax : max (p.2 - p.1) 0 ≤ |p.2| + |p.1| := by
    apply max_le
    · linarith [le_abs_self p.2, neg_le_abs p.1]
    · positivity
  have hm := mul_le_mul_of_nonneg_left hmax (abs_nonneg p.1)
  nlinarith only [hm, sq_abs p.1]

theorem integrable_tau_closedTail (μ ν : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ) :
    Integrable (fun t : ℝ => ZeroBias.tau μ t * closedTail ν t) := by
  apply ZeroBiasTransport.integrable_tau_mul μ hμ (closedTail ν) (measurable_closedTail ν)
  exact ZeroBiasTransport.integrable_abs_mul_tau_of_bounded μ hμ (closedTail ν)
    (measurable_closedTail ν) 1 (by norm_num) (abs_closedTail_le_one ν)

/-- The actual closed-tail zero-bias integral equals the negative marked
stoploss under the actual product law. No distribution is differentiated. -/
theorem tau_closedTail_identity (μ ν : ProbabilityMeasure ℝ)
    (hμ : StandardizedLaw μ) (hν : Integrable (fun y : ℝ => y) (ν : Measure ℝ)) :
    (∫ t : ℝ, ZeroBias.tau μ t * closedTail ν t) =
      -(∫ p : ℝ × ℝ, p.1 * max (p.2 - p.1) 0
        ∂((μ : Measure ℝ).prod (ν : Measure ℝ))) := by
  have hpos := hμ.integrable_mean.mul_prod hν.pos_part
  have hstop := integrable_marked_stoploss μ ν hμ hν
  have hdiff : Integrable (fun p : ℝ × ℝ => p.1 * (max p.2 0 - max (p.2 - p.1) 0))
      ((μ : Measure ℝ).prod (ν : Measure ℝ)) := by
    apply (hpos.sub hstop).congr (Filter.Eventually.of_forall (fun p => ?_))
    change p.1 * max p.2 0 - p.1 * max (p.2 - p.1) 0 =
      p.1 * (max p.2 0 - max (p.2 - p.1) 0)
    ring
  have ht := (ZeroBiasTransport.transport_of_bounded μ hμ (closedTail ν)
    (measurable_closedTail ν) 1 (by norm_num) (abs_closedTail_le_one ν)).2.2
  rw [ht]
  calc
    _ = ∫ x : ℝ, (∫ y : ℝ, x * (max y 0 - max (y - x) 0) ∂(ν : Measure ℝ))
        ∂(μ : Measure ℝ) := by
      apply integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
      rw [primitive_closedTail, integral_const_mul]
    _ = ∫ p : ℝ × ℝ, p.1 * (max p.2 0 - max (p.2 - p.1) 0)
        ∂((μ : Measure ℝ).prod (ν : Measure ℝ)) := (integral_prod _ hdiff).symm
    _ = (∫ p : ℝ × ℝ, p.1 * max p.2 0 ∂((μ : Measure ℝ).prod (ν : Measure ℝ))) -
        ∫ p : ℝ × ℝ, p.1 * max (p.2 - p.1) 0
          ∂((μ : Measure ℝ).prod (ν : Measure ℝ)) := by
      rw [show (fun p : ℝ × ℝ => p.1 * (max p.2 0 - max (p.2 - p.1) 0)) =
        (fun p : ℝ × ℝ => p.1 * max p.2 0 - p.1 * max (p.2 - p.1) 0) by
          funext p; ring]
      exact integral_sub hpos hstop
    _ = _ := by
      rw [integral_prod_mul (μ := (μ : Measure ℝ)) (ν := (ν : Measure ℝ))
        (fun x : ℝ => x) (fun y : ℝ => max y 0), hμ.mean_zero, zero_mul, zero_sub]

/-- The actual predecessor tail law has a finite first moment; its input
is the genuine iid sum, including the empty predecessor sum when n = 1. -/
theorem integrable_predecessorTailLaw (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (n : ℕ) (H : ℝ) :
    Integrable (fun y : ℝ => y)
      (ContactPolynomial.predecessorTailLaw μ n H : Measure ℝ) := by
  have hsum : Integrable (fun s : ℝ => s) (MixtureSum.iidSumLaw (μ : Measure ℝ) (n - 1)) := by
    simpa only [mul_one] using IidExchangeability.integrable_sumlaw_marked μ hμ (n - 1)
      (fun _ : ℝ => (1 : ℝ)) measurable_const 1 0 (by norm_num) (by norm_num)
      (by intro s; norm_num)
  change Integrable (fun y : ℝ => y)
    ((MixtureSum.iidSumLaw (μ : Measure ℝ) (n - 1)).map (fun y : ℝ => H - y))
  apply (integrable_map_measure measurable_id.aestronglyMeasurable (by fun_prop)).mpr
  exact (integrable_const H).sub hsum

/-- Push the real predecessor sum through y = H-Sprev and apply the actual
iid exchangeability identity, rather than postulating a symmetric moment. -/
theorem predecessor_marked_stoploss_identity (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (n : ℕ) (hn : 0 < n) (H : ℝ) :
    (∫ p : ℝ × ℝ, p.1 * max (p.2 - p.1) 0
      ∂((μ : Measure ℝ).prod (ContactPolynomial.predecessorTailLaw μ n H : Measure ℝ))) =
      (1 / (n : ℝ)) * ∫ s : ℝ, s * max (H - s) 0
        ∂MixtureSum.iidSumLaw (μ : Measure ℝ) n := by
  have hf : Measurable (fun y : ℝ => H - y) := by fun_prop
  have hp := Measure.map_prod_map (μ : Measure ℝ)
    (MixtureSum.iidSumLaw (μ : Measure ℝ) (n - 1)) measurable_id hf
  rw [Measure.map_id] at hp
  change (∫ p : ℝ × ℝ, p.1 * max (p.2 - p.1) 0
    ∂((μ : Measure ℝ).prod
      ((MixtureSum.iidSumLaw (μ : Measure ℝ) (n - 1)).map (fun y : ℝ => H - y)))) = _
  rw [hp, integral_map (measurable_id.prodMap hf).aemeasurable (by fun_prop)]
  calc
    _ = ∫ p : ℝ × ℝ, p.1 * max (H - (p.1 + p.2)) 0
        ∂((μ : Measure ℝ).prod (MixtureSum.iidSumLaw (μ : Measure ℝ) (n - 1))) := by
      apply integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
      change p.1 * max ((H - p.2) - p.1) 0 = p.1 * max (H - (p.1 + p.2)) 0
      rw [show (H - p.2) - p.1 = H - (p.1 + p.2) by ring]
    _ = _ := IidExchangeability.marked_stoploss_identity μ hμ n hn H

/-- The second evaluation for the original parameters and actual iid laws,
with the closed threshold and all possible atoms preserved. -/
theorem tau_predecessor_closedTail_identity (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (n : ℕ) (hn : 0 < n) (H : ℝ) :
    (∫ t : ℝ, ZeroBias.tau μ t *
      (ContactPolynomial.predecessorTailLaw μ n H : Measure ℝ).real (Ici t)) =
      -(1 / (n : ℝ)) * ∫ s : ℝ, s * max (H - s) 0
        ∂MixtureSum.iidSumLaw (μ : Measure ℝ) n := by
  change (∫ t : ℝ, ZeroBias.tau μ t *
    closedTail (ContactPolynomial.predecessorTailLaw μ n H) t) = _
  rw [tau_closedTail_identity μ (ContactPolynomial.predecessorTailLaw μ n H) hμ
    (integrable_predecessorTailLaw μ hμ n H),
    predecessor_marked_stoploss_identity μ hμ n hn H]
  ring

end BerryEsseen.ZeroBiasClosedTail

#print axioms BerryEsseen.ZeroBiasClosedTail.primitive_closedTail
#print axioms BerryEsseen.ZeroBiasClosedTail.integrable_marked_stoploss
#print axioms BerryEsseen.ZeroBiasClosedTail.tau_closedTail_identity
#print axioms BerryEsseen.ZeroBiasClosedTail.tau_predecessor_closedTail_identity
