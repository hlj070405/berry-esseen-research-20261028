module

public import BerryEsseen.MixtureSum
public import BerryEsseen.Target
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith

@[expose] public section

/-! 2026-10-28: marked convolution identities for the actual i.i.d. product
measure. Coordinate symmetry is derived from measure-preserving permutations;
all signed integral manipulations are supported by finite-second-moment L1
bounds. No regularity of the underlying law beyond its moments is assumed. -/

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace BerryEsseen.IidExchangeability

def iidProduct (μ : ProbabilityMeasure ℝ) (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ => (μ : Measure ℝ))

instance iidProduct_isProbability (μ : ProbabilityMeasure ℝ) (n : ℕ) :
    IsProbabilityMeasure (iidProduct μ n) := by
  unfold iidProduct
  infer_instance

def sumCoordinates (n : ℕ) (ω : Fin n → ℝ) : ℝ := ∑ i, ω i

theorem measurable_sumCoordinates (n : ℕ) : Measurable (sumCoordinates n) := by
  unfold sumCoordinates
  fun_prop

theorem integrable_coordinate (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (n : ℕ) (i : Fin n) : Integrable (fun ω : Fin n → ℝ => ω i) (iidProduct μ n) := by
  exact (measurePreserving_eval (fun _ : Fin n => (μ : Measure ℝ)) i).integrable_comp_of_integrable
    hμ.integrable_mean

theorem integrable_coordinate_square (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (n : ℕ) (i : Fin n) : Integrable (fun ω : Fin n → ℝ => (ω i) ^ 2) (iidProduct μ n) := by
  exact (measurePreserving_eval (fun _ : Fin n => (μ : Measure ℝ)) i).integrable_comp_of_integrable
    hμ.integrable_square

theorem integrable_sum_square (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (n : ℕ) : Integrable (fun ω => sumCoordinates n ω ^ 2) (iidProduct μ n) := by
  have hs := (integrable_finsetSum Finset.univ (fun i _ =>
    integrable_coordinate_square μ hμ n i)).const_mul (n : ℝ)
  apply hs.mono' (((measurable_sumCoordinates n).pow_const 2).aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro ω
  change |sumCoordinates n ω ^ 2| ≤ (n : ℝ) * ∑ i, (ω i) ^ 2
  rw [abs_of_nonneg (sq_nonneg _)]
  simpa [sumCoordinates, mul_comm] using
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ ω (fun _ : Fin n => (1 : ℝ))

/-- The quadratic Young bound makes the marked summand integrable for every
measurable test function with at most linear growth. -/
theorem integrable_coordinate_marked (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (n : ℕ) (i : Fin n) (g : ℝ → ℝ) (hg : Measurable g)
    (A B : ℝ) (_hA : 0 ≤ A) (hB : 0 ≤ B)
    (hbound : ∀ s, |g s| ≤ A + B * |s|) :
    Integrable (fun ω : Fin n → ℝ => ω i * g (sumCoordinates n ω)) (iidProduct μ n) := by
  have hdom := ((integrable_coordinate μ hμ n i).abs.const_mul A).add
    (((integrable_coordinate_square μ hμ n i).add
      (integrable_sum_square μ hμ n)).const_mul (B / 2))
  apply hdom.mono' (((measurable_pi_apply i).mul
    (hg.comp (measurable_sumCoordinates n))).aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro ω
  change |ω i * g (sumCoordinates n ω)| ≤
    A * |ω i| + B / 2 * ((ω i) ^ 2 + sumCoordinates n ω ^ 2)
  rw [abs_mul]
  have hyoung : |ω i| * |sumCoordinates n ω| ≤
      ((ω i) ^ 2 + sumCoordinates n ω ^ 2) / 2 := by
    nlinarith [sq_nonneg (|ω i| - |sumCoordinates n ω|), sq_abs (ω i),
      sq_abs (sumCoordinates n ω)]
  have hmul := mul_le_mul_of_nonneg_left hyoung hB
  have htest := mul_le_mul_of_nonneg_left (hbound (sumCoordinates n ω)) (abs_nonneg (ω i))
  nlinarith

/-- Reindexing the actual identical product law by a coordinate swap preserves
both its measure and its total sum. -/
theorem integral_coordinate_marked_eq (μ : ProbabilityMeasure ℝ) (n : ℕ)
    (i j : Fin n) (g : ℝ → ℝ) :
    (∫ ω : Fin n → ℝ, ω i * g (sumCoordinates n ω) ∂iidProduct μ n) =
      ∫ ω : Fin n → ℝ, ω j * g (sumCoordinates n ω) ∂iidProduct μ n := by
  classical
  let e := MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) (Equiv.swap i j)
  have hp : MeasurePreserving e (iidProduct μ n) (iidProduct μ n) :=
    measurePreserving_piCongrLeft (fun _ : Fin n => (μ : Measure ℝ)) (Equiv.swap i j)
  have he (ω : Fin n → ℝ) (k : Fin n) : e ω k = ω ((Equiv.swap i j) k) := by
    have hh := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Fin n => ℝ) (Equiv.swap i j)
      ω ((Equiv.swap i j) k)
    simpa only [Equiv.swap_apply_self] using hh
  have hsum (ω : Fin n → ℝ) : sumCoordinates n (e ω) = sumCoordinates n ω := by
    simp only [sumCoordinates, he]
    exact Equiv.sum_comp (Equiv.swap i j) ω
  have hint := hp.integral_comp' (fun ω : Fin n → ℝ => ω j * g (sumCoordinates n ω))
  simpa only [he, Equiv.swap_apply_right, hsum] using hint

/-- The first coordinate together with the sum of all remaining coordinates. -/
def markedSumMap (n : ℕ) (ω : Fin (n + 1) → ℝ) : ℝ × ℝ :=
  (ω 0, ∑ i : Fin n, ω i.succ)

theorem measurable_markedSumMap (n : ℕ) : Measurable (markedSumMap n) := by
  unfold markedSumMap
  fun_prop

/-- This is a push-forward identity of actual measures, establishing the
independence of the marked coordinate and the remaining sum. -/
theorem map_markedSumMap (μ : ProbabilityMeasure ℝ) (n : ℕ) :
    (iidProduct μ (n + 1)).map (markedSumMap n) =
      (μ : Measure ℝ).prod (MixtureSum.iidSumLaw (μ : Measure ℝ) n) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  let f : ℝ × (Fin n → ℝ) → ℝ × ℝ := Prod.map id (sumCoordinates n)
  have hf : Measurable f := measurable_id.prodMap (measurable_sumCoordinates n)
  have heq : markedSumMap n = f ∘ e := by
    funext ω
    simp [markedSumMap, f, e, sumCoordinates,
      MeasurableEquiv.piFinSuccAbove_apply, Fin.tail]
  rw [heq, ← Measure.map_map hf e.measurable]
  have hp := (measurePreserving_piFinSuccAbove
    (fun _ : Fin (n + 1) => (μ : Measure ℝ)) 0).map_eq
  change ((Measure.pi (fun _ : Fin (n + 1) => (μ : Measure ℝ))).map e).map f = _
  rw [hp]
  have hm := Measure.map_prod_map (μ : Measure ℝ) (iidProduct μ n)
    measurable_id (measurable_sumCoordinates n)
  change ((μ : Measure ℝ).prod (iidProduct μ n)).map f =
    (μ : Measure ℝ).prod ((iidProduct μ n).map (sumCoordinates n))
  simpa only [Measure.map_id, f] using hm.symm

/-- The sum-marked integrand is integrable under the same actual product law. -/
theorem integrable_sum_marked (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (n : ℕ) (g : ℝ → ℝ) (hg : Measurable g)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hbound : ∀ s, |g s| ≤ A + B * |s|) :
    Integrable (fun ω => sumCoordinates n ω * g (sumCoordinates n ω)) (iidProduct μ n) := by
  have hs := integrable_finsetSum Finset.univ (fun i _ =>
    integrable_coordinate_marked μ hμ n i g hg A B hA hB hbound)
  apply hs.congr (Filter.Eventually.of_forall (fun ω => ?_))
  simp only [← Finset.sum_mul, sumCoordinates]

theorem integrable_sumlaw_marked (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (n : ℕ) (g : ℝ → ℝ) (hg : Measurable g)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hbound : ∀ s, |g s| ≤ A + B * |s|) :
    Integrable (fun s : ℝ => s * g s) (MixtureSum.iidSumLaw (μ : Measure ℝ) n) := by
  exact (integrable_map_measure ((measurable_id.mul hg).aestronglyMeasurable)
    (measurable_sumCoordinates n).aemeasurable).mpr
      (integrable_sum_marked μ hμ n g hg A B hA hB hbound)

/-- Summing equal coordinate integrals produces the genuine factor `n+1`. -/
theorem integral_sum_marked_eq (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (n : ℕ) (g : ℝ → ℝ) (hg : Measurable g)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hbound : ∀ s, |g s| ≤ A + B * |s|) :
    (∫ ω, sumCoordinates (n + 1) ω * g (sumCoordinates (n + 1) ω)
      ∂iidProduct μ (n + 1)) =
      ((n + 1 : ℕ) : ℝ) *
        ∫ ω : Fin (n + 1) → ℝ, ω 0 * g (sumCoordinates (n + 1) ω)
          ∂iidProduct μ (n + 1) := by
  calc
    _ = ∫ ω : Fin (n + 1) → ℝ,
        ∑ i, ω i * g (sumCoordinates (n + 1) ω) ∂iidProduct μ (n + 1) := by
      apply integral_congr_ae (Filter.Eventually.of_forall (fun ω => ?_))
      simp only [← Finset.sum_mul, sumCoordinates]
    _ = ∑ i : Fin (n + 1), ∫ ω : Fin (n + 1) → ℝ,
        ω i * g (sumCoordinates (n + 1) ω) ∂iidProduct μ (n + 1) :=
      integral_finsetSum _ (fun i _ =>
        integrable_coordinate_marked μ hμ (n + 1) i g hg A B hA hB hbound)
    _ = ∑ _i : Fin (n + 1), ∫ ω : Fin (n + 1) → ℝ,
        ω 0 * g (sumCoordinates (n + 1) ω) ∂iidProduct μ (n + 1) := by
      apply Finset.sum_congr rfl
      intro i _
      exact integral_coordinate_marked_eq μ (n + 1) i 0 g
    _ = _ := by simp

theorem integrable_marked_convolution (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (n : ℕ) (g : ℝ → ℝ) (hg : Measurable g)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hbound : ∀ s, |g s| ≤ A + B * |s|) :
    Integrable (fun z : ℝ × ℝ => z.1 * g (z.1 + z.2))
      ((μ : Measure ℝ).prod (MixtureSum.iidSumLaw (μ : Measure ℝ) n)) := by
  rw [← map_markedSumMap μ n]
  apply (integrable_map_measure (by fun_prop)
    (measurable_markedSumMap n).aemeasurable).mpr
  simpa [Function.comp_def, markedSumMap, sumCoordinates, Fin.sum_univ_succ] using
    integrable_coordinate_marked μ hμ (n + 1) 0 g hg A B hA hB hbound

/-- Exact marked convolution identity at every positive index for every
measurable test function of at most linear growth. -/
theorem marked_convolution_identity (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (n : ℕ) (hn : 0 < n) (g : ℝ → ℝ) (hg : Measurable g)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hbound : ∀ s, |g s| ≤ A + B * |s|) :
    (∫ z : ℝ × ℝ, z.1 * g (z.1 + z.2)
      ∂((μ : Measure ℝ).prod (MixtureSum.iidSumLaw (μ : Measure ℝ) (n - 1)))) =
      (1 / (n : ℝ)) * ∫ s : ℝ, s * g s ∂MixtureSum.iidSumLaw (μ : Measure ℝ) n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have hhead : (∫ z : ℝ × ℝ, z.1 * g (z.1 + z.2)
      ∂((μ : Measure ℝ).prod (MixtureSum.iidSumLaw (μ : Measure ℝ) k))) =
      ∫ ω : Fin (k + 1) → ℝ, ω 0 * g (sumCoordinates (k + 1) ω)
        ∂iidProduct μ (k + 1) := by
    rw [← map_markedSumMap μ k,
      integral_map (measurable_markedSumMap k).aemeasurable (by fun_prop)]
    apply integral_congr_ae (Filter.Eventually.of_forall (fun ω => ?_))
    simp [markedSumMap, sumCoordinates, Fin.sum_univ_succ]
  have hsumlaw : (∫ s : ℝ, s * g s ∂MixtureSum.iidSumLaw (μ : Measure ℝ) (k + 1)) =
      ∫ ω, sumCoordinates (k + 1) ω * g (sumCoordinates (k + 1) ω)
        ∂iidProduct μ (k + 1) := by
    exact integral_map (measurable_sumCoordinates (k + 1)).aemeasurable
      ((measurable_id.mul hg).aestronglyMeasurable)
  simp only [Nat.succ_sub_one]
  rw [hhead, hsumlaw, integral_sum_marked_eq μ hμ k g hg A B hA hB hbound]
  have hk : ((k + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
  field_simp

/-- The closed threshold keeps atoms on the boundary. -/
theorem marked_closed_indicator_identity (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (n : ℕ) (hn : 0 < n) (H : ℝ) :
    (∫ z : ℝ × ℝ, z.1 * (if z.1 + z.2 ≤ H then (1 : ℝ) else 0)
      ∂((μ : Measure ℝ).prod (MixtureSum.iidSumLaw (μ : Measure ℝ) (n - 1)))) =
      (1 / (n : ℝ)) * ∫ s : ℝ, s * (if s ≤ H then (1 : ℝ) else 0)
        ∂MixtureSum.iidSumLaw (μ : Measure ℝ) n := by
  have hg : Measurable (fun s : ℝ => if s ≤ H then (1 : ℝ) else 0) := by
    exact Measurable.ite (measurableSet_Iic (a := H)) measurable_const measurable_const
  apply marked_convolution_identity μ hμ n hn
    (fun s => if s ≤ H then (1 : ℝ) else 0) hg 1 0 (by norm_num) (by norm_num)
  intro s
  split_ifs <;> norm_num

/-- The same identity applies to the positive-part linear price. -/
theorem marked_stoploss_identity (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (n : ℕ) (hn : 0 < n) (H : ℝ) :
    (∫ z : ℝ × ℝ, z.1 * max (H - (z.1 + z.2)) 0
      ∂((μ : Measure ℝ).prod (MixtureSum.iidSumLaw (μ : Measure ℝ) (n - 1)))) =
      (1 / (n : ℝ)) * ∫ s : ℝ, s * max (H - s) 0
        ∂MixtureSum.iidSumLaw (μ : Measure ℝ) n := by
  apply marked_convolution_identity μ hμ n hn (fun s => max (H - s) 0)
    (by fun_prop) |H| 1 (abs_nonneg H) (by norm_num)
  intro s
  rw [abs_of_nonneg (le_max_right (H - s) 0)]
  apply max_le
  · linarith [le_abs_self H, neg_le_abs s]
  · positivity

end BerryEsseen.IidExchangeability

#print axioms BerryEsseen.IidExchangeability.integrable_coordinate_marked
#print axioms BerryEsseen.IidExchangeability.map_markedSumMap
#print axioms BerryEsseen.IidExchangeability.marked_convolution_identity
#print axioms BerryEsseen.IidExchangeability.marked_closed_indicator_identity
#print axioms BerryEsseen.IidExchangeability.marked_stoploss_identity
