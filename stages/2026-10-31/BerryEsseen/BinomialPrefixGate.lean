module

public import BerryEsseen.BinomialWeights
public import BerryEsseen.OptimizedStaircasePrice

@[expose] public section

/-!
An analytic sufficient condition for the actual binomial eta prefix gate.
The condition places k+1 in the nonincreasing tail; the original canonical
CDF and same-law third-moment bounds then use this explicit eta. Counts
outside this mode condition retain the general prefix-gate interfaces.
-/

namespace BerryEsseen.BinomialPrefixGate

open MeasureTheory
open scoped BigOperators ContDiff

noncomputable section

/-- Exact adjacent binomial mass flux, including the two end counts. -/
theorem adjacent_mass_flux (n j : ℕ) (p : ℝ) (hj : j < n) :
    ((j + 1 : ℕ) : ℝ) * (1 - p) * BinomialWeights.mass n (j + 1) p =
      ((n - j : ℕ) : ℝ) * p * BinomialWeights.mass n j p := by
  have hchoose : (n.choose (j + 1) : ℝ) * ((j + 1 : ℕ) : ℝ) =
      (n.choose j : ℝ) * ((n - j : ℕ) : ℝ) := by
    simpa only [Nat.cast_mul] using
      congrArg (fun m : ℕ => (m : ℝ)) (Nat.choose_succ_right_eq n j)
  have hexp : n - j = (n - (j + 1)) + 1 := by omega
  have hpow : (1 - p) ^ (n - j) = (1 - p) ^ (n - (j + 1)) * (1 - p) := by
    rw [hexp, pow_succ]
  calc
    _ = ((n.choose (j + 1) : ℝ) * ((j + 1 : ℕ) : ℝ)) *
        p ^ (j + 1) * (1 - p) ^ (n - j) := by
      unfold BinomialWeights.mass
      rw [hpow]
      ring
    _ = ((n.choose j : ℝ) * ((n - j : ℕ) : ℝ)) *
        p ^ (j + 1) * (1 - p) ^ (n - j) := by rw [hchoose]
    _ = _ := by
      unfold BinomialWeights.mass
      rw [pow_succ]
      ring

/-- Once (n+1)p is at most j+1, the next actual mass cannot increase. -/
theorem mass_succ_le (n j : ℕ) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hj : j < n) (hmode : ((n + 1 : ℕ) : ℝ) * p ≤ ((j + 1 : ℕ) : ℝ)) :
    BinomialWeights.mass n (j + 1) p ≤ BinomialWeights.mass n j p := by
  have hfactor : ((n - j : ℕ) : ℝ) * p ≤ ((j + 1 : ℕ) : ℝ) * (1 - p) := by
    rw [Nat.cast_sub hj.le]
    push_cast at hmode ⊢
    nlinarith only [hmode]
  have h := mul_le_mul_of_nonneg_right hfactor
    (BinomialWeights.mass_nonneg n j p hp.le hp1.le)
  rw [← adjacent_mass_flux n j p hj] at h
  exact (mul_le_mul_iff_of_pos_left (mul_pos (Nat.cast_pos.mpr (Nat.succ_pos j))
    (sub_pos.mpr hp1))).mp h

/-- Every tail count is bounded by the first mass after k. The inclusive
mode boundary allows equal adjacent masses. -/
theorem mass_tail_le (n k j : ℕ) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hmode : ((n + 1 : ℕ) : ℝ) * p ≤ ((k + 2 : ℕ) : ℝ))
    (hkj : k + 1 ≤ j) (hjn : j ≤ n) :
    BinomialWeights.mass n j p ≤ BinomialWeights.mass n (k + 1) p := by
  induction j, hkj using Nat.le_induction with
  | base => exact le_rfl
  | succ j hkj ih =>
    have hj : j < n := by omega
    have hmodej : ((n + 1 : ℕ) : ℝ) * p ≤ ((j + 1 : ℕ) : ℝ) :=
      hmode.trans (by exact_mod_cast (show k + 2 ≤ j + 1 by omega))
    exact (mass_succ_le n j p hp hp1 hj hmodej).trans (ih hj.le)

/-- prefixMass starts at k+1, exactly as in the original eta gate. This
bound includes the empty prefix r=0 as well as all r≤n-k. -/
theorem prefixMass_le (n k r : ℕ) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hmode : ((n + 1 : ℕ) : ℝ) * p ≤ ((k + 2 : ℕ) : ℝ))
    (hr : r ≤ n - k) :
    Staircase.prefixMass (fun j => BinomialWeights.mass n (k + j) p) r ≤
      (r : ℝ) * BinomialWeights.mass n (k + 1) p := by
  unfold Staircase.prefixMass
  calc
    _ ≤ ∑ _i ∈ Finset.range r, BinomialWeights.mass n (k + 1) p := by
      apply Finset.sum_le_sum
      intro i hi
      have hir : i < r := Finset.mem_range.mp hi
      exact mass_tail_le n k (k + (i + 1)) p hp hp1 hmode (by omega) (by omega)
    _ = _ := by simp

/-- The sufficient eta uses the actual next binomial mass. -/
def tailEta (n k : ℕ) (Δ p : ℝ) : ℝ :=
  BinomialWeights.mass n (k + 1) p / (1 - Δ)

theorem tailEta_pos (n k : ℕ) (Δ p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hk : k < n) (hΔ : Δ < 1) : 0 < tailEta n k Δ p :=
  div_pos (BinomialWeights.mass_pos n (k + 1) p hp hp1 (Nat.succ_le_of_lt hk))
    (sub_pos.mpr hΔ)

theorem eta_prefix_gate (n k : ℕ) (Δ p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hmode : ((n + 1 : ℕ) : ℝ) * p ≤ ((k + 2 : ℕ) : ℝ)) (hΔ : Δ < 1) :
    ∀ r : ℕ, 1 ≤ r → r ≤ n - k →
      Staircase.prefixMass (fun j => BinomialWeights.mass n (k + j) p) r ≤
        tailEta n k Δ p * ((r : ℝ) * (1 - Δ)) := by
  intro r _hr hrn
  calc
    _ ≤ (r : ℝ) * BinomialWeights.mass n (k + 1) p := prefixMass_le n k r p hp hp1 hmode hrn
    _ = _ := by
      unfold tailEta
      field_simp [(sub_pos.mpr hΔ).ne']

theorem contDiff_two_tailEta (n k : ℕ) (Δ : ℝ) : ContDiff ℝ 2 (tailEta n k Δ) := by
  unfold tailEta
  exact (BinomialWeights.contDiff_two_mass n (k + 1)).div_const (1 - Δ)

theorem hasDerivAt_tailEta (n k : ℕ) (Δ p : ℝ) (hp : 0 < p) (hp1 : p < 1) (hk : k < n) :
    HasDerivAt (tailEta n k Δ)
      (BinomialWeights.massSlope n (k + 1) p / (1 - Δ)) p := by
  unfold tailEta
  exact (BinomialWeights.hasDerivAt_mass n (k + 1) p hp hp1 (Nat.succ_le_of_lt hk)).div_const (1 - Δ)

/-- The analytically acquired gate is the original canonical gate, with
the same p and unchanged count indexing. -/
theorem canonical_eta_prefix_gate (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (n k : ℕ) (Δ : ℝ)
    (hmode : ((n + 1 : ℕ) : ℝ) * CanonicalSign.p μ ≤ ((k + 2 : ℕ) : ℝ)) (hΔ : Δ < 1) :
    ∀ r : ℕ, 1 ≤ r → r ≤ n - k →
      Staircase.prefixMass (fun j => CoupledPrice.canonicalBinomialWeight μ n (k + j)) r ≤
        tailEta n k Δ (CanonicalSign.p μ) * ((r : ℝ) * (1 - Δ)) := by
  simpa only [BinomialWeights.mass_at_canonical] using eta_prefix_gate n k Δ (CanonicalSign.p μ)
    (CanonicalSign.p_pos μ hμ) (CanonicalSign.p_lt_one μ hμ) hmode hΔ

theorem tailEta_at_canonical (μ : ProbabilityMeasure ℝ) (n k : ℕ) (Δ : ℝ) :
    tailEta n k Δ (CanonicalSign.p μ) =
      CoupledPrice.canonicalBinomialWeight μ n (k + 1) / (1 - Δ) := rfl

/-- On the stated tail-mode domain, the single analytic condition supplies
every prefix inequality needed by the actual canonical Q price. -/
theorem canonical_normalized_closedCDF_le_Q
    (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ) (n k : ℕ) (hn : 0 < n) (hk : k < n)
    (a0 a1 O1 Δ t : ℝ) (ha0 : 0 ≤ a0) (ha1 : 0 ≤ a1) (hO1 : 0 ≤ O1)
    (hcap : a0 + a1 ≤ Δ) (hΔ : Δ < 1)
    (hinner0 : ∀ᵐ u ∂(CanonicalSign.residual0 μ hμ : Measure ℝ), u ≤ a0)
    (hinner1 : ∀ᵐ u ∂(CanonicalSign.residual1 μ hμ : Measure ℝ), -a1 ≤ u)
    (houter1 : ∀ᵐ u ∂(CanonicalSign.residual1 μ hμ : Measure ℝ), u ≤ O1)
    (hmode : ((n + 1 : ℕ) : ℝ) * CanonicalSign.p μ ≤ ((k + 2 : ℕ) : ℝ)) :
    let η := tailEta n k Δ (CanonicalSign.p μ)
    (normalizedIidSumLaw μ n).real (Set.Iic (ConditionalResidual.canonicalThreshold μ hμ n k t)) ≤
      Staircase.lowerMass (CoupledPrice.canonicalBinomialWeight μ n) k + η *
        (t + StopLossShape.Q
          (TwoMoment.coupledReferenceLaw (CanonicalSign.residual0 μ hμ : Measure ℝ)
            (CanonicalSign.residual1 μ hμ : Measure ℝ) a0 O1 n k)
          (t + CoupledPrice.canonicalBinomialWeight μ n k / η)) := by
  exact OptimizedStaircasePrice.canonical_normalized_closedCDF_le_Q
    μ hμ n k hn hk.le a0 a1 O1 Δ (tailEta n k Δ (CanonicalSign.p μ)) t
    ha0 ha1 hO1 hcap hΔ
    (tailEta_pos n k Δ (CanonicalSign.p μ) (CanonicalSign.p_pos μ hμ)
      (CanonicalSign.p_lt_one μ hμ) hk hΔ)
    hinner0 hinner1 houter1 (canonical_eta_prefix_gate μ hμ n k Δ hmode hΔ)

/-- The same-law rho floor and actual target coefficient are unchanged;
only the eta gate has been analytically acquired on this mode domain. -/
theorem canonical_targetResidual_le_Q
    (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ) (n k : ℕ) (hn : 0 < n) (hk : k < n)
    (a0 a1 O1 Δ δ t ci : ℝ) (ha0 : 0 ≤ a0) (ha1 : 0 ≤ a1) (hO1 : 0 ≤ O1)
    (hcapΔ : a0 + a1 ≤ Δ) (hΔ : Δ < 1) (hδ : 0 < δ) (hcapδ : a0 + a1 ≤ δ)
    (hinner0 : ∀ᵐ u ∂(CanonicalSign.residual0 μ hμ : Measure ℝ), u ≤ a0)
    (hinner1 : ∀ᵐ u ∂(CanonicalSign.residual1 μ hμ : Measure ℝ), -a1 ≤ u)
    (houter1 : ∀ᵐ u ∂(CanonicalSign.residual1 μ hμ : Measure ℝ), u ≤ O1)
    (hmode : ((n + 1 : ℕ) : ℝ) * CanonicalSign.p μ ≤ ((k + 2 : ℕ) : ℝ))
    (hci0 : 0 ≤ ci) (hci : ci ≤ esseenConstant / Real.sqrt (n : ℝ)) :
    let η := tailEta n k Δ (CanonicalSign.p μ)
    ConditionalResidual.positiveTargetResidual μ n (ConditionalResidual.canonicalThreshold μ hμ n k t) ≤
      Staircase.lowerMass (CoupledPrice.canonicalBinomialWeight μ n) k + η *
        (t + StopLossShape.Q
          (TwoMoment.coupledReferenceLaw (CanonicalSign.residual0 μ hμ : Measure ℝ)
            (CanonicalSign.residual1 μ hμ : Measure ℝ) a0 O1 n k)
          (t + CoupledPrice.canonicalBinomialWeight μ n k / η)) -
        GaussianTools.Phi (ConditionalResidual.canonicalThreshold μ hμ n k t) -
        ci * MomentBudget.gDelta (CanonicalSign.p μ) (CanonicalSign.noiseVariance μ hμ) δ
          (ConditionalResidual.actualAllocation μ hμ) := by
  exact OptimizedStaircasePrice.canonical_targetResidual_le_Q
    μ hμ n k hn hk.le a0 a1 O1 Δ δ (tailEta n k Δ (CanonicalSign.p μ)) t ci
    ha0 ha1 hO1 hcapΔ hΔ hδ hcapδ
    (tailEta_pos n k Δ (CanonicalSign.p μ) (CanonicalSign.p_pos μ hμ)
      (CanonicalSign.p_lt_one μ hμ) hk hΔ)
    hinner0 hinner1 houter1 (canonical_eta_prefix_gate μ hμ n k Δ hmode hΔ) hci0 hci

end

end BerryEsseen.BinomialPrefixGate

#print axioms BerryEsseen.BinomialPrefixGate.mass_tail_le
#print axioms BerryEsseen.BinomialPrefixGate.prefixMass_le
#print axioms BerryEsseen.BinomialPrefixGate.canonical_eta_prefix_gate
#print axioms BerryEsseen.BinomialPrefixGate.hasDerivAt_tailEta
#print axioms BerryEsseen.BinomialPrefixGate.canonical_normalized_closedCDF_le_Q
#print axioms BerryEsseen.BinomialPrefixGate.canonical_targetResidual_le_Q
