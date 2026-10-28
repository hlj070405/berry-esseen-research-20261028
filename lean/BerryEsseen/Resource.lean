module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

/-! 2026-10-28: physical resource elimination and actual-index scaling. -/

namespace BerryEsseen

theorem scalar_noise_cap {n B g h δ lam R : ℝ}
    (hn : 0 < n) (hB : 0 < B) (hg : 0 < g) (hh : 0 ≤ h)
    (hnoise : lam ≤ n * B * δ) (hresource : g * δ + h * lam ≤ R) :
    lam ≤ R / (h + g / (n * B)) := by
  have hnB : 0 < n * B := mul_pos hn hB
  have hδ : lam / (n * B) ≤ δ := by
    apply (div_le_iff₀ hnB).2
    nlinarith [hnoise]
  apply (le_div_iff₀ (show 0 < h + g / (n * B) by positivity)).2
  calc
    lam * (h + g / (n * B)) = h * lam + g * (lam / (n * B)) := by ring
    _ ≤ h * lam + g * δ := by
      nlinarith [mul_le_mul_of_nonneg_left hδ (le_of_lt hg)]
    _ ≤ R := by linarith

theorem weighted_resource_export {n N D b g δ h s dJ : ℝ}
    (hn : 0 < n)
    (hphysical : b + g * δ + h * N * s ≤ D)
    (hweighted : n * D ≤ N * dJ) :
    g * δ + (N / n) * h * (n * s) ≤ (N / n) * dJ - b := by
  have hu : D ≤ N * dJ / n := by
    apply (le_div_iff₀ hn).2
    nlinarith [hweighted]
  have hn0 : n ≠ 0 := ne_of_gt hn
  have heq : (N / n) * h * (n * s) = h * N * s := by
    field_simp
  rw [heq]
  have hdiv : (N / n) * dJ = N * dJ / n := by ring
  rw [hdiv]
  linarith

theorem normalized_weighted_plane {n N D b g δ h s dJ : ℝ}
    (hn : 0 < n) (hN : 0 < N) (hg : 0 < g) (hh : 0 < h)
    (hR : 0 < dJ - b)
    (hphysical : b + g * δ + h * N * s ≤ D)
    (hweighted : n * D ≤ N * dJ) :
    δ / ((N / n) * ((dJ - b) / g)) + (n * s) / ((dJ - b) / h)
      ≤ 1 - (n / N - 1) * b / (dJ - b) := by
  have hn0 : n ≠ 0 := ne_of_gt hn
  have hN0 : N ≠ 0 := ne_of_gt hN
  have hg0 : g ≠ 0 := ne_of_gt hg
  have hh0 : h ≠ 0 := ne_of_gt hh
  have hR0 : dJ - b ≠ 0 := ne_of_gt hR
  have he : g * δ + (N / n) * h * (n * s) ≤ (N / n) * dJ - b :=
    weighted_resource_export hn hphysical hweighted
  have hden : 0 < (N / n) * (dJ - b) := mul_pos (div_pos hN hn) hR
  have hleft : δ / ((N / n) * ((dJ - b) / g)) +
      (n * s) / ((dJ - b) / h) =
      (g * δ + (N / n) * h * (n * s)) / ((N / n) * (dJ - b)) := by
    field_simp
  have hright : 1 - (n / N - 1) * b / (dJ - b) =
      ((N / n) * dJ - b) / ((N / n) * (dJ - b)) := by
    field_simp; ring
  rw [hleft, hright]
  exact div_le_div_of_nonneg_right he (le_of_lt hden)

end BerryEsseen

#print axioms BerryEsseen.scalar_noise_cap
#print axioms BerryEsseen.weighted_resource_export
#print axioms BerryEsseen.normalized_weighted_plane
