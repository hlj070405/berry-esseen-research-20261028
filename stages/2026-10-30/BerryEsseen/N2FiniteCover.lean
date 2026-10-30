module

public import BerryEsseen.N2CompactReduction

@[expose] public section

/-! 2026-10-29: the original 65 closed threshold intervals remaining
after the analytic tails. Individual row estimates are explicit inputs. -/

noncomputable section
open MeasureTheory Set

namespace BerryEsseen.N2FiniteCover
open GaussianTools

theorem finite_interval_cover (n : ℕ) (hn : 0 < n) (a d x : ℝ)
    (hx : x ∈ Icc a (a + n * d)) :
    ∃ i : Fin n, x ∈ Icc (a + i.val * d) (a + (i.val + 1 : ℕ) * d) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hn0 : n = 0
    · subst n
      refine ⟨0, ?_⟩
      simpa using hx
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
      by_cases hmid : x ≤ a + n * d
      · obtain ⟨i, hi⟩ := ih hnpos ⟨hx.1, hmid⟩
        exact ⟨⟨i.val, Nat.lt_succ_of_lt i.isLt⟩, hi⟩
      · refine ⟨Fin.last n, ?_⟩
        constructor
        · simpa only [Fin.val_last] using (lt_of_not_ge hmid).le
        · simpa only [Fin.val_last] using hx.2

def lower (i : Fin 65) : ℝ := (-45 + i.val) / 20
def upper (i : Fin 65) : ℝ := (-44 + i.val) / 20

theorem middle_covered (H : ℝ) (hH : H ∈ Icc (-9 / 4 : ℝ) 1) :
    ∃ i : Fin 65, H ∈ Icc (lower i) (upper i) := by
  have hx : H ∈ Icc (-9 / 4 : ℝ) (-9 / 4 + (65 : ℕ) * (1 / 20)) := by
    refine ⟨hH.1, ?_⟩
    have he : (-9 / 4 : ℝ) + (65 : ℕ) * (1 / 20) = 1 := by norm_num
    simpa only [he] using hH.2
  obtain ⟨i, hi⟩ := finite_interval_cover 65 (by norm_num) (-9 / 4) (1 / 20) H hx
  refine ⟨i, ?_⟩
  have hl : (-9 / 4 : ℝ) + i.val * (1 / 20) = lower i := by
    dsimp [lower]
    ring
  have hu : (-9 / 4 : ℝ) + (i.val + 1 : ℕ) * (1 / 20) = upper i := by
    dsimp [upper]
    push_cast
    ring
  simpa only [hl, hu] using hi

def RowBound (L : ℝ) (i : Fin 65) : Prop :=
  ∀ (μ : ProbabilityMeasure ℝ), StandardizedLaw μ → thirdAbsoluteMoment μ ≤ 2 →
    (∀ᵐ x ∂(μ : Measure ℝ), |x| ≤ 6) → ∀ H ∈ Icc (lower i) (upper i),
      (MixtureSum.iidSumLaw (μ : Measure ℝ) 2).real (Iic H) - Phi (H / Real.sqrt 2) ≤
        L * thirdAbsoluteMoment μ

theorem compactMiddleBound_of_rows (L : ℝ) (hrows : ∀ i : Fin 65, RowBound L i) :
    N2CompactReduction.CompactMiddleBound L := by
  intro μ h hρ hR H hH
  obtain ⟨i, hi⟩ := middle_covered H hH
  exact hrows i μ h hρ hR H hi

/-- This implication does not supply its 65 row hypotheses. -/
theorem absoluteClosedBound_of_rows (L : ℝ) (hL : (2 : ℝ) / 7 ≤ L)
    (hprice : L * Real.sqrt 2 < esseenConstant) (hrows : ∀ i : Fin 65, RowBound L i) :
    Reflection.AbsoluteClosedBound 2 esseenConstant :=
  N2CompactReduction.absoluteClosedBound_of_compact_middle L hL hprice
    (compactMiddleBound_of_rows L hrows)

end BerryEsseen.N2FiniteCover

#print axioms BerryEsseen.N2FiniteCover.finite_interval_cover
#print axioms BerryEsseen.N2FiniteCover.middle_covered
#print axioms BerryEsseen.N2FiniteCover.compactMiddleBound_of_rows
#print axioms BerryEsseen.N2FiniteCover.absoluteClosedBound_of_rows
