module

public import BerryEsseen.Extremizer
public import BerryEsseen.Reflection
public import BerryEsseen.AnalyticConstants

@[expose] public section

/-! 2026-10-28: exact equivalence with the original absolute-error target,
and its genuine all-law minimal-counterexample reduction. No index bound
or finite-domain completion is asserted by this reduction.
-/

noncomputable section

open MeasureTheory Set

namespace BerryEsseen.GlobalReduction

open Extremizer Reflection

theorem positiveRawClosedBound_of_sup_le (n : ℕ) (hn : 0 < n) (C : ℝ)
    (hC : fixedNSup n ≤ C) : PositiveRawClosedBound n C := by
  intro μ h H
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  have hi := (positiveClosedScore_le_fixedNSup μ h n H).trans hC
  have hρ := thirdAbsoluteMoment_pos μ h
  change Real.sqrt n * ((MixtureSum.iidSumLaw (μ : Measure ℝ) n).real (Iic H) -
    GaussianTools.Phi (H / Real.sqrt n)) / thirdAbsoluteMoment μ ≤ C at hi
  have hp := (div_le_iff₀ hρ).mp hi
  apply (le_div_iff₀ hs).mpr
  nlinarith

theorem sup_le_of_positiveRawClosedBound (n : ℕ) (hn : 0 < n) (C : ℝ) (hC : 0 ≤ C)
    (hraw : PositiveRawClosedBound n C) : fixedNSup n ≤ C := by
  by_cases hne : (scoreSet n).Nonempty
  · apply csSup_le hne
    rintro q ⟨μ, h, H, rfl⟩
    have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
    have hi := hraw μ h H
    have hp := (le_div_iff₀ hs).mp hi
    unfold positiveClosedScore
    apply (div_le_iff₀ (thirdAbsoluteMoment_pos μ h)).mpr
    simpa only [coe_iidSumProbability, mul_comm] using hp
  · have hempty := Set.not_nonempty_iff_eq_empty.mp hne
    simpa only [fixedNSup, hempty, Real.sSup_empty] using hC

/-- This equivalence retains all real standardized laws, every positive
integer, closed threshold atoms, and the original exact Esseen constant. -/
theorem sharp_iff_all_sup_le : SharpIidBerryEsseen ↔
    ∀ n : ℕ, 0 < n → fixedNSup n ≤ esseenConstant := by
  constructor
  · intro hsharp n hn
    apply sup_le_of_positiveRawClosedBound n hn esseenConstant
      (by linarith [AnalyticConstants.esseenConstant_gt_819_2000])
    intro μ h H
    have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
    have hphase : Real.sqrt n * (H / Real.sqrt n) = H := by field_simp [hs.ne']
    have hi : |(normalizedIidSumLaw μ n).real (Iic (H / Real.sqrt n)) -
        GaussianTools.Phi (H / Real.sqrt n)| ≤
        esseenConstant * thirdAbsoluteMoment μ / Real.sqrt n := by
      simpa only [GaussianTools.Phi] using hsharp μ h n hn (H / Real.sqrt n)
    rw [normalized_closedCDF_eq_raw μ n hn, hphase] at hi
    exact (le_abs_self _).trans hi
  · intro hall
    exact sharpIidBerryEsseen_of_raw (fun n hn =>
      positiveRawClosedBound_of_sup_le n hn _ (hall n hn))

theorem exists_failing_index_of_not_sharp (hnot : ¬ SharpIidBerryEsseen) :
    ∃ n : ℕ, 0 < n ∧ esseenConstant < fixedNSup n := by
  classical
  by_contra hnone
  apply hnot
  apply sharp_iff_all_sup_le.mpr
  intro n hn
  exact le_of_not_gt (fun hc => hnone ⟨n, hn, hc⟩)

/-- Any failure of the original conjecture supplies an actual minimizing
index and an attained original global maximizer, with all smaller positive
indices satisfying the full Esseen bound. This theorem is conditional on failure. -/
theorem exists_minimal_counterexample_of_not_sharp (hnot : ¬ SharpIidBerryEsseen) :
    ∃ n : ℕ, 0 < n ∧ esseenConstant < fixedNSup n ∧
      (∀ k : ℕ, 0 < k → k < n → fixedNSup k ≤ esseenConstant) ∧
      ∃ μ : ProbabilityMeasure ℝ, StandardizedLaw μ ∧ ∃ H : ℝ,
        ContactVariation.PositiveClosedMaximum μ n H (fixedNSup n) := by
  classical
  have hex := exists_failing_index_of_not_sharp hnot
  let n := Nat.find hex
  have hn : 0 < n ∧ esseenConstant < fixedNSup n := Nat.find_spec hex
  have hC : 0 < fixedNSup n := by linarith [AnalyticConstants.esseenConstant_gt_819_2000]
  obtain ⟨μ, hμ, H, hmax⟩ := exists_PositiveClosedMaximum n hn.1 hC
  refine ⟨n, hn.1, hn.2, ?_, μ, hμ, H, hmax⟩
  intro k hk hkn
  by_contra hc
  have hbad : 0 < k ∧ esseenConstant < fixedNSup k := ⟨hk, lt_of_not_ge hc⟩
  have hnk : n ≤ k := Nat.find_min' hex hbad
  omega

end BerryEsseen.GlobalReduction

#print axioms BerryEsseen.GlobalReduction.sharp_iff_all_sup_le
#print axioms BerryEsseen.GlobalReduction.exists_minimal_counterexample_of_not_sharp
