module

public import BerryEsseen.PrawitzSmoothing
public import Causalean.Stat.CLT.BerryEsseen.BerryEsseenWideCharFun

@[expose] public section

/-! 2026-10-29: global cubic characteristic-function damping for the original
standardized law. The price retains its actual third absolute moment plus
one. Exponential comparison precedes every natural power, with no sign gate
on the exponent. Normalized frequencies are explicitly t / sqrt n. -/

noncomputable section

open MeasureTheory ProbabilityTheory

namespace BerryEsseen.ClassicalDamping

def cubicExponent (μ : ProbabilityMeasure ℝ) (t : ℝ) : ℝ :=
  -(t ^ 2 / 2) + (thirdAbsoluteMoment μ + 1) * |t| ^ 3 / 10

theorem charFun_norm_sq_le (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ) (t : ℝ) :
    ‖charFun (μ : Measure ℝ) t‖ ^ 2 ≤
      1 - t ^ 2 + (thirdAbsoluteMoment μ + 1) * |t| ^ 3 / 5 := by
  exact Causalean.Stat.CLT.BerryEsseen.unit_variance_charFun_norm_sq_cubic_bound
    (μ : Measure ℝ) (thirdAbsoluteMoment μ) hμ.integrable_mean hμ.mean_zero
    hμ.integrable_square hμ.second_moment_one hμ.integrable_cube le_rfl t

theorem charFun_norm_le_exp (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ) (t : ℝ) :
    ‖charFun (μ : Measure ℝ) t‖ ≤ Real.exp (cubicExponent μ t) := by
  let e := cubicExponent μ t
  have hpoly : 1 - t ^ 2 + (thirdAbsoluteMoment μ + 1) * |t| ^ 3 / 5 = 2 * e + 1 := by
    dsimp [e, cubicExponent]
    ring
  have hsq : ‖charFun (μ : Measure ℝ) t‖ ^ 2 ≤ (Real.exp e) ^ 2 := by
    rw [← Real.exp_nat_mul]
    norm_num only [Nat.cast_ofNat]
    exact (charFun_norm_sq_le μ hμ t).trans (hpoly.trans_le (Real.add_one_le_exp (2 * e)))
  exact (sq_le_sq₀ (norm_nonneg _) (Real.exp_nonneg e)).mp hsq

theorem charFun_norm_le (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ) (t : ℝ) :
    ‖charFun (μ : Measure ℝ) t‖ ≤ min 1 (Real.exp (cubicExponent μ t)) :=
  le_min (norm_charFun_le_one (μ := (μ : Measure ℝ)) t) (charFun_norm_le_exp μ hμ t)

/-- Every natural power, including the empty power, uses the actual CF. -/
theorem charFun_power_norm_le (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (n : ℕ) (t : ℝ) :
    ‖charFun (μ : Measure ℝ) t ^ n‖ ≤ min 1 (Real.exp ((n : ℝ) * cubicExponent μ t)) := by
  apply le_min
  · rw [norm_pow]
    simpa only [one_pow] using pow_le_pow_left₀
      (norm_nonneg (charFun (μ : Measure ℝ) t)) (norm_charFun_le_one t) n
  · rw [norm_pow, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (norm_nonneg _) (charFun_norm_le_exp μ hμ t) n

theorem raw_iid_norm_le (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (n : ℕ) (t : ℝ) :
    ‖charFun (MixtureSum.iidSumLaw (μ : Measure ℝ) n) t‖ ≤
      min 1 (Real.exp ((n : ℝ) * cubicExponent μ t)) := by
  rw [MixtureSum.iidSumLaw_eq_convPower, FourierRemainder.charFun_convPower]
  exact charFun_power_norm_le μ hμ n t

/-- This form also covers n=0, without simplifying division by sqrt n. -/
theorem normalized_iid_norm_le (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (n : ℕ) (t : ℝ) :
    ‖charFun (normalizedIidSumLaw μ n) t‖ ≤
      min 1 (Real.exp ((n : ℝ) * cubicExponent μ (t / Real.sqrt n))) := by
  rw [PrawitzSmoothing.charFun_normalizedIidSumLaw]
  exact charFun_power_norm_le μ hμ n (t / Real.sqrt n)

theorem iid_exponent_scale (μ : ProbabilityMeasure ℝ) (n : ℕ) (hn : 0 < n) (t : ℝ) :
    (n : ℝ) * cubicExponent μ (t / Real.sqrt n) =
      -(t ^ 2 / 2) + (thirdAbsoluteMoment μ + 1) * |t| ^ 3 / (10 * Real.sqrt n) := by
  let s : ℝ := Real.sqrt n
  have hs : 0 < s := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  have hs2 : s ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
  change (n : ℝ) * cubicExponent μ (t / s) =
    -(t ^ 2 / 2) + (thirdAbsoluteMoment μ + 1) * |t| ^ 3 / (10 * s)
  dsimp [cubicExponent]
  rw [abs_div, abs_of_pos hs, div_pow, div_pow, ← hs2]
  field_simp [hs.ne']

theorem normalized_iid_norm_le_of_pos (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (n : ℕ) (hn : 0 < n) (t : ℝ) :
    ‖charFun (normalizedIidSumLaw μ n) t‖ ≤ min 1
      (Real.exp (-(t ^ 2 / 2) +
        (thirdAbsoluteMoment μ + 1) * |t| ^ 3 / (10 * Real.sqrt n))) := by
  simpa only [iid_exponent_scale μ n hn t] using normalized_iid_norm_le μ hμ n t

end BerryEsseen.ClassicalDamping

#print axioms Causalean.Stat.CLT.BerryEsseen.cos_le_quadratic_add_cubic
#print axioms Causalean.Stat.CLT.BerryEsseen.unit_variance_charFun_norm_sq_cubic_bound
#print axioms BerryEsseen.ClassicalDamping.charFun_norm_sq_le
#print axioms BerryEsseen.ClassicalDamping.charFun_norm_le
#print axioms BerryEsseen.ClassicalDamping.charFun_power_norm_le
#print axioms BerryEsseen.ClassicalDamping.raw_iid_norm_le
#print axioms BerryEsseen.ClassicalDamping.normalized_iid_norm_le
#print axioms BerryEsseen.ClassicalDamping.normalized_iid_norm_le_of_pos
