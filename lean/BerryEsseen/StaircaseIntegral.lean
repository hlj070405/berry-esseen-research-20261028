module

public import BerryEsseen.Staircase
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

@[expose] public section

/-!
The coupled staircase bound on an arbitrary probability space.
Only the residual at count `k` must be integrable and centered. The
coupling bound may hold almost everywhere, and the CDF events are closed.
-/

namespace BerryEsseen.Staircase

open MeasureTheory
open scoped BigOperators

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A finite mixture of closed residual CDFs, on an arbitrary measure space. -/
def closedMixtureCDF (μ : Measure Ω) (π : ℕ → ℝ) (W : ℕ → Ω → ℝ)
    (n : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1), π j * μ.real {ω | (j : ℝ) + W j ω ≤ x}

lemma integrable_closedSummand (μ : Measure Ω) [IsFiniteMeasure μ]
    (π : ℕ → ℝ) (W : ℕ → Ω → ℝ) (j : ℕ) (x : ℝ)
    (hclosed : MeasurableSet {ω | (j : ℝ) + W j ω ≤ x}) :
    Integrable (fun ω => if (j : ℝ) + W j ω ≤ x then π j else 0) μ := by
  have hfun : (fun ω => if (j : ℝ) + W j ω ≤ x then π j else 0) =
      {ω | (j : ℝ) + W j ω ≤ x}.indicator (fun _ => π j) := by
    funext ω
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  rw [hfun]
  exact (integrable_const (π j)).indicator hclosed

theorem integrable_weightedClosedCDF (μ : Measure Ω) [IsFiniteMeasure μ]
    (π : ℕ → ℝ) (W : ℕ → Ω → ℝ) (n : ℕ) (x : ℝ)
    (hclosed : ∀ j : ℕ, j ≤ n → MeasurableSet {ω | (j : ℝ) + W j ω ≤ x}) :
    Integrable (fun ω => weightedClosedCDF π (fun j => W j ω) n x) μ := by
  unfold weightedClosedCDF
  apply integrable_finsetSum
  intro j hj
  exact integrable_closedSummand μ π W j x
    (hclosed j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)))

theorem integral_weightedClosedCDF (μ : Measure Ω) [IsFiniteMeasure μ]
    (π : ℕ → ℝ) (W : ℕ → Ω → ℝ) (n : ℕ) (x : ℝ)
    (hclosed : ∀ j : ℕ, j ≤ n → MeasurableSet {ω | (j : ℝ) + W j ω ≤ x}) :
    (∫ ω, weightedClosedCDF π (fun j => W j ω) n x ∂μ) =
      closedMixtureCDF μ π W n x := by
  unfold weightedClosedCDF closedMixtureCDF
  rw [integral_finsetSum (Finset.range (n + 1))
    (fun j hj => integrable_closedSummand μ π W j x
      (hclosed j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))))]
  apply Finset.sum_congr rfl
  intro j hj
  have hs := hclosed j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
  have hfun : (fun ω => if (j : ℝ) + W j ω ≤ x then π j else 0) =
      {ω | (j : ℝ) + W j ω ≤ x}.indicator (fun _ => π j) := by
    funext ω
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  rw [hfun, integral_indicator_const (π j) hs, smul_eq_mul]
  exact mul_comm _ _

/-- The stop-loss inequality for a common residual coupling on any
probability space. This is a finite mixture of arbitrary residual laws;
the residual distributions need not have finite support. -/
theorem coupledMixtureCDF_le_stopLoss (μ : Measure Ω) [IsProbabilityMeasure μ]
    (π : ℕ → ℝ) (W : ℕ → Ω → ℝ) (k N : ℕ) (Δ η t : ℝ)
    (hπ : ∀ j, 0 ≤ π j) (hd : 0 ≤ 1 - Δ) (hη : 0 < η)
    (hclosed : ∀ j : ℕ, j ≤ k + N →
      MeasurableSet {ω | (j : ℝ) + W j ω ≤ (k : ℝ) + t})
    (hWk : Integrable (W k) μ) (hcenter : ∫ ω, W k ω ∂μ = 0)
    (hcoupling : ∀ᵐ ω ∂μ, ∀ r : ℕ, 1 ≤ r → r ≤ N →
      W k ω - (r : ℝ) * Δ ≤ W (k + r) ω)
    (hprefix : ∀ r : ℕ, 1 ≤ r → r ≤ N →
      prefixMass (fun j => π (k + j)) r ≤ η * ((r : ℝ) * (1 - Δ))) :
    closedMixtureCDF μ π W (k + N) ((k : ℝ) + t) ≤
      lowerMass π k + η * (t + ∫ ω, max (W k ω - t - π k / η) 0 ∂μ) := by
  have hlin : Integrable (fun ω => η * (t - W k ω)) μ :=
    ((integrable_const t).sub hWk).const_mul η
  have hpos : Integrable (fun ω => max (W k ω - t - π k / η) 0) μ :=
    ((hWk.sub (integrable_const t)).sub (integrable_const (π k / η))).pos_part
  have hfirst : Integrable (fun ω => lowerMass π k + η * (t - W k ω)) μ :=
    (integrable_const (lowerMass π k)).add hlin
  have hrhs : Integrable (fun ω => lowerMass π k + η * (t - W k ω) +
      η * max (W k ω - t - π k / η) 0) μ :=
    hfirst.add (hpos.const_mul η)
  have hae : (fun ω => weightedClosedCDF π (fun j => W j ω) (k + N) ((k : ℝ) + t))
      ≤ᵐ[μ] (fun ω => lowerMass π k + η * (t - W k ω) +
        η * max (W k ω - t - π k / η) 0) :=
    hcoupling.mono (fun ω hc => coupledCDF_le_stopLoss π (fun j => W j ω)
      k N Δ η t hπ hd hη hc hprefix)
  have hint := integral_mono_ae
    (integrable_weightedClosedCDF μ π W (k + N) ((k : ℝ) + t) hclosed) hrhs hae
  have hidentity :
      (∫ ω, lowerMass π k + η * (t - W k ω) +
        η * max (W k ω - t - π k / η) 0 ∂μ) =
      lowerMass π k + η * (t + ∫ ω, max (W k ω - t - π k / η) 0 ∂μ) := by
    rw [integral_add hfirst (hpos.const_mul η),
      integral_add (integrable_const (lowerMass π k)) hlin,
      integral_const_mul, integral_const_mul,
      integral_sub (integrable_const t) hWk, hcenter]
    simp only [integral_const, probReal_univ, one_smul, sub_zero]
    nlinarith
  calc
    closedMixtureCDF μ π W (k + N) ((k : ℝ) + t) =
        ∫ ω, weightedClosedCDF π (fun j => W j ω) (k + N) ((k : ℝ) + t) ∂μ :=
      (integral_weightedClosedCDF μ π W (k + N) ((k : ℝ) + t) hclosed).symm
    _ ≤ _ := hint
    _ = _ := hidentity

end

end BerryEsseen.Staircase

#print axioms BerryEsseen.Staircase.coupledMixtureCDF_le_stopLoss
