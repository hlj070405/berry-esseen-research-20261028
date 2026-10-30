module

public import BerryEsseen.HighFrequencyTail
public import BerryEsseen.HighFrequencyPrice

@[expose] public section

/-! 2026-10-30: the genuine periodic CF tail can be priced at a qualified
sample floor while retaining an arbitrary positive physical tail start b.
The original distribution and conditional event stay at the actual n. -/

noncomputable section

open MeasureTheory Set Filter
open BerryEsseen.HighFrequencyEvent BerryEsseen.HighFrequencyDistance
open BerryEsseen.HighFrequencyZeroCell BerryEsseen.HighFrequencyFloor
open BerryEsseen.HighFrequencyCells

namespace BerryEsseen.HighFrequencyTailFloor

theorem Zbasic_le_floor (N n : ℕ) (a d b : ℝ)
    (hN : 0 < N) (hNn : N ≤ n) (ha : 0 < a) (hd : 0 < d) (hb : 0 < b) :
    Zbasic n a d b ≤ Zbasic N a d b := by
  have hk := kappa_pos a d ha hd
  have hr : 0 < kappa a d * b ^ 2 := mul_pos hk (sq_pos_of_pos hb)
  have heq (k : ℕ) : Zbasic k a d b =
      (1 / (2 * b ^ 4 * kappa a d)) * invSqrtExp (kappa a d * b ^ 2) k := by
    unfold Zbasic invSqrtExp
    rw [show -((k : ℝ) * kappa a d) * b ^ 2 =
      -((kappa a d * b ^ 2) * k) by ring]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [heq n, heq N]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact invSqrtExp_antitone _ hr (Nat.cast_pos.mpr hN)
    (Nat.cast_pos.mpr (hN.trans_le hNn)) (Nat.cast_le.mpr hNn)

theorem wingPrice_le_floor (N n : ℕ) (a b : ℝ)
    (hN : 0 < N) (hNn : N ≤ n)
    (hg : 1 ≤ 2 * (N : ℝ) * a * (23 / 48 : ℝ) ^ 2) :
    wingPrice n a b ≤ wingPrice N a b := by
  have heq (k : ℕ) : wingPrice k a b =
      sqrtExp (a * (23 / 48 : ℝ) ^ 2) k / (2 * b ^ 2) := by
    unfold wingPrice sqrtExp
    rw [show -(k : ℝ) * a * (23 / 48 : ℝ) ^ 2 =
      -((a * (23 / 48 : ℝ) ^ 2) * k) by ring]
  rw [heq n, heq N]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact HighFrequencyPrice.nat_sqrtExp_le N n _ hN hNn (by nlinarith only [hg])

theorem basicPrice_le_floor (N n : ℕ) (a d b w m : ℝ)
    (hN : 0 < N) (hNn : N ≤ n) (ha : 0 < a) (hd : 0 < d) (hb : 0 < b)
    (hw : 0 < w) (hwcap : w ≤ 1 / 4) (hm : 0 ≤ m)
    (hperiodic : 1 < 2 * (N : ℝ) * a * sineSlope w ^ 2 * w ^ 2)
    (hwing : 1 ≤ 2 * (N : ℝ) * a * (23 / 48 : ℝ) ^ 2) :
    HighFrequencyTail.basicPrice n a d b w m ≤ HighFrequencyTail.basicPrice N a d b w m := by
  unfold HighFrequencyTail.basicPrice
  exact add_le_add
    (add_le_add
      (mul_le_mul_of_nonneg_left
        (HighFrequencyPrice.nonzeroSlope_le N n a w hN hNn ha hw hwcap hperiodic) hm)
      (Zbasic_le_floor N n a d b hN hNn ha hd hb))
    (wingPrice_le_floor N n a b hN hNn hwing)

/-- The floor N selects a deterministic upper price, with no maximum-law
or probability assertion at N. All event licenses concern the actual μ. -/
theorem actual_event_tail_basic_floor (μ : ProbabilityMeasure ℝ)
    (E : Set (ℝ × ℝ)) (hE : MeasurableSet E) (N n : ℕ)
    (hN : 0 < N) (hNn : N ≤ n) (a d b w m : ℝ)
    (ha : 0 < a) (hpa : a ≤ eventProbability μ E)
    (hd : 0 < d) (hb : 0 < b) (hw : 0 < w) (hwcap : w ≤ 1 / 4) (hm : 0 ≤ m)
    (hD : ∀ᵐ p ∂eventLaw μ E, d ≤ distance p)
    (h2 : Integrable (fun p => distance p ^ 2) (eventLaw μ E))
    (hmean : conditionalSecondMoment μ E ≤ m)
    (hperiodic : 1 < 2 * (N : ℝ) * a * sineSlope w ^ 2 * w ^ 2)
    (hwing : 1 ≤ 2 * (N : ℝ) * a * (23 / 48 : ℝ) ^ 2) :
    IntegrableOn (HighFrequencyTail.actualIntegrand μ n) (Ioi b) ∧
      IntegrableOn (HighFrequencyTail.complexIntegrand μ n) (Ioi b) ∧
      Real.sqrt n * (∫ t in Ioi b, HighFrequencyTail.actualIntegrand μ n t) ≤
        HighFrequencyTail.basicPrice N a d b w m := by
  have hp := HighFrequencyTail.actual_event_tail_basic μ E hE n (hN.trans_le hNn)
    a d b w m ha hpa hd hb hw hwcap hD h2 hmean
  exact ⟨hp.1, hp.2.1, hp.2.2.trans
    (basicPrice_le_floor N n a d b w m hN hNn ha hd hb hw hwcap hm hperiodic hwing)⟩

end BerryEsseen.HighFrequencyTailFloor

#print axioms BerryEsseen.HighFrequencyTailFloor.Zbasic_le_floor
#print axioms BerryEsseen.HighFrequencyTailFloor.wingPrice_le_floor
#print axioms BerryEsseen.HighFrequencyTailFloor.basicPrice_le_floor
#print axioms BerryEsseen.HighFrequencyTailFloor.actual_event_tail_basic_floor
