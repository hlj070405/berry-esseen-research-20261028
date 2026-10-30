module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
The pointwise, finite part of the coupled staircase argument.

Incoming jumps use the closed condition `r * d ≤ y`; the outgoing jump
uses the strict condition `y < 0`. Thus every equality at a CDF atom is
included, and `t` is an arbitrary real number throughout.
-/

namespace BerryEsseen.Staircase

open scoped BigOperators

noncomputable section

def prefixMass (w : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ i ∈ Finset.range N, w (i + 1)

def incoming (w : ℕ → ℝ) (d y : ℝ) (N : ℕ) : ℝ :=
  ∑ i ∈ Finset.range N, if ((i + 1 : ℕ) : ℝ) * d ≤ y then w (i + 1) else 0

def signedStaircase (w : ℕ → ℝ) (a d y : ℝ) (N : ℕ) : ℝ :=
  -(if y < 0 then a else 0) + incoming w d y N

lemma incoming_eq_prefix_of_last_active (w : ℕ → ℝ) (d y : ℝ) (N : ℕ)
    (hd : 0 ≤ d) (hN : (N : ℝ) * d ≤ y) :
    incoming w d y N = prefixMass w N := by
  unfold incoming prefixMass
  apply Finset.sum_congr rfl
  intro i hi
  have hir : ((i + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by
    exact Nat.cast_le.mpr (Nat.succ_le_of_lt (Finset.mem_range.mp hi))
  exact ite_eq_left ((mul_le_mul_of_nonneg_right hir hd).trans hN)

/-- A bound on every prefix controls the whole incoming staircase.
Nonnegative weights are not needed for this pointwise implication. -/
theorem incoming_le_line (w : ℕ → ℝ) (d η y : ℝ) (N : ℕ)
    (hd : 0 ≤ d) (hη : 0 ≤ η) (hy : 0 ≤ y)
    (hprefix : ∀ r : ℕ, 1 ≤ r → r ≤ N →
      prefixMass w r ≤ η * ((r : ℝ) * d)) :
    incoming w d y N ≤ η * y := by
  induction N with
  | zero =>
      simpa [incoming] using mul_nonneg hη hy
  | succ N ih =>
      by_cases hlast : ((N + 1 : ℕ) : ℝ) * d ≤ y
      · rw [incoming_eq_prefix_of_last_active w d y (N + 1) hd hlast]
        exact (hprefix (N + 1) (Nat.succ_pos _) le_rfl).trans
          (mul_le_mul_of_nonneg_left hlast hη)
      · have hprev : incoming w d y N ≤ η * y :=
          ih (fun r hr hrN => hprefix r hr (Nat.le_succ_of_le hrN))
        unfold incoming
        rw [Finset.sum_range_succ, ite_eq_right hlast, add_zero]
        exact hprev

lemma incoming_eq_zero_of_negative_phase (w : ℕ → ℝ) (d y : ℝ) (N : ℕ)
    (hd : 0 ≤ d) (hy : y < 0) :
    incoming w d y N = 0 := by
  unfold incoming
  apply Finset.sum_eq_zero
  intro i hi
  have hnonneg : 0 ≤ ((i + 1 : ℕ) : ℝ) * d :=
    mul_nonneg (Nat.cast_nonneg _) hd
  exact ite_eq_right (by linarith)

/-- The signed finite staircase is majorized at every real phase,
including every incoming jump point. -/
theorem signedStaircase_le_max (w : ℕ → ℝ) (a d η y : ℝ) (N : ℕ)
    (hd : 0 ≤ d) (hη : 0 ≤ η)
    (hprefix : ∀ r : ℕ, 1 ≤ r → r ≤ N →
      prefixMass w r ≤ η * ((r : ℝ) * d)) :
    signedStaircase w a d y N ≤ max (-a) (η * y) := by
  by_cases hy : y < 0
  · simp only [signedStaircase, ite_eq_left hy,
      incoming_eq_zero_of_negative_phase w d y N hd hy, add_zero]
    exact le_max_left _ _
  · have hline := incoming_le_line w d η y N hd hη (le_of_not_gt hy) hprefix
    simp only [signedStaircase, ite_eq_right hy, neg_zero, zero_add]
    exact hline.trans (le_max_right _ _)

lemma max_eq_stopLoss (a η y : ℝ) (hη : 0 < η) :
    max (-a) (η * y) = η * y + η * max (-y - a / η) 0 := by
  have hcancel : η * (a / η) = a := mul_div_cancel₀ a (ne_of_gt hη)
  by_cases h : -a ≤ η * y
  · have harg : -y - a / η ≤ 0 :=
      nonpos_of_mul_nonpos_right (by nlinarith : η * (-y - a / η) ≤ 0) hη
    rw [max_eq_right h, max_eq_right harg]
    simp
  · have harg : 0 ≤ -y - a / η := by
      apply (mul_nonneg_iff_of_pos_left hη).mp
      nlinarith
    rw [max_eq_left (le_of_not_ge h), max_eq_left harg]
    nlinarith

theorem signedStaircase_le_stopLoss (w : ℕ → ℝ) (a d η y : ℝ) (N : ℕ)
    (hd : 0 ≤ d) (hη : 0 < η)
    (hprefix : ∀ r : ℕ, 1 ≤ r → r ≤ N →
      prefixMass w r ≤ η * ((r : ℝ) * d)) :
    signedStaircase w a d y N ≤ η * y + η * max (-y - a / η) 0 := by
  rw [← max_eq_stopLoss a η y hη]
  exact signedStaircase_le_max w a d η y N hd hη.le hprefix

/-- The closed weighted CDF for counts `0, ..., n`, evaluated at a
fixed outcome of the coupling. No normalization of the weights is needed. -/
def weightedClosedCDF (π W : ℕ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1), if (j : ℝ) + W j ≤ x then π j else 0

def lowerMass (π : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (k + 1), π j

/-- Dropping lower-count losses and using the common residual coupling
gives the signed staircase, with all CDF boundaries still closed. -/
theorem coupledCDF_deviation_le_staircase (π W : ℕ → ℝ) (k N : ℕ)
    (Δ t : ℝ) (hπ : ∀ j, 0 ≤ π j)
    (hcoupling : ∀ r : ℕ, 1 ≤ r → r ≤ N →
      W k - (r : ℝ) * Δ ≤ W (k + r)) :
    weightedClosedCDF π W (k + N) ((k : ℝ) + t) - lowerMass π k ≤
      signedStaircase (fun r => π (k + r)) (π k) (1 - Δ) (t - W k) N := by
  have hlower :
      (∑ j ∈ Finset.range k,
        if (j : ℝ) + W j ≤ (k : ℝ) + t then π j else 0) ≤
      ∑ j ∈ Finset.range k, π j := by
    apply Finset.sum_le_sum
    intro j hj
    by_cases hevent : (j : ℝ) + W j ≤ (k : ℝ) + t
    · rw [ite_eq_left hevent]
    · rw [ite_eq_right hevent]
      exact hπ j
  have hmiddle :
      (if (k : ℝ) + W k ≤ (k : ℝ) + t then π k else 0) - π k =
      -(if t - W k < 0 then π k else 0) := by
    by_cases hy : t - W k < 0
    · have hk : ¬ ((k : ℝ) + W k ≤ (k : ℝ) + t) := by linarith
      simp [hy, hk]
    · have hk : (k : ℝ) + W k ≤ (k : ℝ) + t := by linarith
      simp [hy, hk]
  have hupper :
      (∑ i ∈ Finset.range N,
        if ((k + 1 + i : ℕ) : ℝ) + W (k + 1 + i) ≤ (k : ℝ) + t
        then π (k + 1 + i) else 0) ≤
      incoming (fun r => π (k + r)) (1 - Δ) (t - W k) N := by
    unfold incoming
    apply Finset.sum_le_sum
    intro i hi
    have hindex : k + 1 + i = k + (i + 1) := by
      simp [Nat.add_comm, Nat.add_left_comm]
    rw [hindex]
    by_cases hevent : ((k + (i + 1) : ℕ) : ℝ) + W (k + (i + 1)) ≤
        (k : ℝ) + t
    · rw [ite_eq_left hevent]
      have hc := hcoupling (i + 1) (Nat.succ_pos _)
        (Nat.succ_le_of_lt (Finset.mem_range.mp hi))
      have hactive : ((i + 1 : ℕ) : ℝ) * (1 - Δ) ≤ t - W k := by
        rw [Nat.cast_add k (i + 1)] at hevent
        nlinarith
      rw [ite_eq_left hactive]
    · rw [ite_eq_right hevent]
      by_cases hactive : ((i + 1 : ℕ) : ℝ) * (1 - Δ) ≤ t - W k
      · rw [ite_eq_left hactive]
        exact hπ _
      · rw [ite_eq_right hactive]
  have hlength : k + N + 1 = (k + 1) + N := by
    simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  unfold weightedClosedCDF lowerMass
  rw [hlength, Finset.sum_range_add, Finset.sum_range_succ, Finset.sum_range_succ]
  unfold signedStaircase
  linarith

/-- The finite weighted closed CDF has the pointwise stop-loss bound.
The centering step needed to take expectations is intentionally separate. -/
theorem coupledCDF_le_stopLoss (π W : ℕ → ℝ) (k N : ℕ) (Δ η t : ℝ)
    (hπ : ∀ j, 0 ≤ π j) (hd : 0 ≤ 1 - Δ) (hη : 0 < η)
    (hcoupling : ∀ r : ℕ, 1 ≤ r → r ≤ N →
      W k - (r : ℝ) * Δ ≤ W (k + r))
    (hprefix : ∀ r : ℕ, 1 ≤ r → r ≤ N →
      prefixMass (fun j => π (k + j)) r ≤ η * ((r : ℝ) * (1 - Δ))) :
    weightedClosedCDF π W (k + N) ((k : ℝ) + t) ≤ lowerMass π k +
      η * (t - W k) + η * max (W k - t - π k / η) 0 := by
  have hstep := coupledCDF_deviation_le_staircase π W k N Δ t hπ hcoupling
  have hbound := signedStaircase_le_stopLoss (fun r => π (k + r)) (π k)
    (1 - Δ) η (t - W k) N hd hη hprefix
  have hphase : -(t - W k) - π k / η = W k - t - π k / η := by linarith
  rw [hphase] at hbound
  linarith


end

end BerryEsseen.Staircase

#print axioms BerryEsseen.Staircase.signedStaircase_le_stopLoss
#print axioms BerryEsseen.Staircase.coupledCDF_le_stopLoss

