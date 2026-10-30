module

public import BerryEsseen.GaussianPrices
public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecificLimits.Normed

@[expose] public section

/-! 2026-10-28: Taylor enclosures of the actual standard Gaussian CDF.
The signed remainder comes from the integral Taylor theorem, on the entire
nonnegative half-line; no decreasing-term assumption is used. -/

noncomputable section

open MeasureTheory Set
open scoped BigOperators Topology

namespace BerryEsseen.GaussianEnclosures

open GaussianTools GaussianPrices

/-- The degree `m` Taylor polynomial for `exp (-u)` at zero. -/
def expTaylor (m : ℕ) (u : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (m + 1), (-1 : ℝ) ^ k * u ^ k / (k.factorial : ℝ)

lemma exp_neg_integral_remainder (m : ℕ) (u : ℝ) (hu : 0 ≤ u) :
    Real.exp (-u) - expTaylor m u = (-1 : ℝ) ^ (m + 1) *
      ∫ v in (0 : ℝ)..u, (u - v) ^ m / (m.factorial : ℝ) * Real.exp (-v) := by
  rcases eq_or_lt_of_le hu with heq | hpos
  · subst u
    simp [expTaylor, Finset.sum_range_succ']
  have hc : ∀ n : ℕ, ContDiff ℝ n (fun v : ℝ => Real.exp (-v)) := by
    intro n
    fun_prop
  have hd : ∀ (n : ℕ) (v : ℝ), v ∈ Icc 0 u →
      iteratedDerivWithin n (fun z : ℝ => Real.exp (-z)) (Icc 0 u) v =
        (-1 : ℝ) ^ n * Real.exp (-v) := by
    intro n v hv
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hpos) (hc n).contDiffAt hv]
    simpa only [neg_one_mul] using congrFun (iteratedDeriv_exp_const_mul n (-1)) v
  have ht : taylorWithinEval (fun v : ℝ => Real.exp (-v)) m (Icc 0 u) 0 u =
      expTaylor m u := by
    rw [taylor_within_apply]
    unfold expTaylor
    apply Finset.sum_congr rfl
    intro k hk
    rw [hd k 0 ⟨le_rfl, hu⟩]
    simp only [sub_zero, neg_zero, Real.exp_zero, mul_one, smul_eq_mul]
    ring
  have h := taylor_integral_remainder (f := fun v : ℝ => Real.exp (-v))
    (x₀ := 0) (x := u) (n := m) (hc (m + 1)).contDiffOn
  rw [uIcc_of_le hu, ht] at h
  rw [h, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro v hv
  rw [uIcc_of_le hu] at hv
  dsimp only
  rw [hd (m + 1) v hv]
  simp only [smul_eq_mul]
  ring

lemma integral_remainder_bounds (m : ℕ) (u : ℝ) (hu : 0 ≤ u) :
    0 ≤ (∫ v in (0 : ℝ)..u, (u - v) ^ m / (m.factorial : ℝ) * Real.exp (-v)) ∧
    (∫ v in (0 : ℝ)..u, (u - v) ^ m / (m.factorial : ℝ) * Real.exp (-v)) ≤
      u ^ (m + 1) / ((m + 1).factorial : ℝ) := by
  have hc : Continuous (fun v : ℝ => (u - v) ^ m / (m.factorial : ℝ)) := by fun_prop
  have he : Continuous (fun v : ℝ => Real.exp (-v)) := by fun_prop
  constructor
  · apply intervalIntegral.integral_nonneg hu
    intro v hv
    exact mul_nonneg (div_nonneg (pow_nonneg (sub_nonneg.mpr hv.2) _) (Nat.cast_nonneg _))
      (Real.exp_nonneg _)
  · have hle := intervalIntegral.integral_mono_on (μ := volume) hu
      ((hc.mul he).intervalIntegrable 0 u) (hc.intervalIntegrable 0 u) (fun v hv =>
        mul_le_of_le_one_right
          (div_nonneg (pow_nonneg (sub_nonneg.mpr hv.2) _) (Nat.cast_nonneg _))
          (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hv.1)))
    refine hle.trans_eq ?_
    rw [intervalIntegral.integral_div, intervalIntegral.integral_comp_sub_left
      (fun v : ℝ => v ^ m) u, integral_pow]
    simp only [sub_self, sub_zero, zero_pow (Nat.succ_ne_zero m), sub_zero]
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    rw [div_div]

theorem exp_neg_taylor_abs (m : ℕ) (u : ℝ) (hu : 0 ≤ u) :
    |Real.exp (-u) - expTaylor m u| ≤ u ^ (m + 1) / ((m + 1).factorial : ℝ) := by
  rw [exp_neg_integral_remainder m u hu, abs_mul, abs_neg_one_pow, one_mul,
    abs_of_nonneg (integral_remainder_bounds m u hu).1]
  exact (integral_remainder_bounds m u hu).2

theorem exp_neg_taylor_upper (m : ℕ) (hm : Even m) (u : ℝ) (hu : 0 ≤ u) :
    Real.exp (-u) ≤ expTaylor m u := by
  have h := exp_neg_integral_remainder m u hu
  rw [pow_succ, hm.neg_one_pow] at h
  have hb := (integral_remainder_bounds m u hu).1
  linarith

theorem exp_neg_taylor_lower (m : ℕ) (hm : Odd m) (u : ℝ) (hu : 0 ≤ u) :
    expTaylor m u ≤ Real.exp (-u) := by
  have h := exp_neg_integral_remainder m u hu
  rw [pow_succ, hm.neg_one_pow] at h
  have hb := (integral_remainder_bounds m u hu).1
  linarith

/-- The integrated degree `m` exponential polynomial, with rational coefficients. -/
def cdfTaylor (m : ℕ) (r : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (m + 1),
    (-1 : ℝ) ^ k * r ^ (2 * k + 1) /
      ((2 : ℝ) ^ k * (k.factorial : ℝ) * (2 * (k : ℝ) + 1))

lemma expTaylor_gaussian_eq (m : ℕ) (t : ℝ) :
    expTaylor m (t ^ 2 / 2) = ∑ k ∈ Finset.range (m + 1),
      ((-1 : ℝ) ^ k / ((2 : ℝ) ^ k * (k.factorial : ℝ))) * t ^ (2 * k) := by
  unfold expTaylor
  apply Finset.sum_congr rfl
  intro k hk
  rw [div_pow, ← pow_mul]
  ring

lemma continuous_expTaylor_gaussian (m : ℕ) :
    Continuous (fun t : ℝ => expTaylor m (t ^ 2 / 2)) := by
  simp_rw [expTaylor_gaussian_eq]
  fun_prop

lemma integral_expTaylor_gaussian (m : ℕ) (r : ℝ) :
    (∫ t in (0 : ℝ)..r, expTaylor m (t ^ 2 / 2)) = cdfTaylor m r := by
  simp_rw [expTaylor_gaussian_eq]
  rw [intervalIntegral.integral_finsetSum (fun k hk =>
    (show Continuous (fun t : ℝ =>
      ((-1 : ℝ) ^ k / ((2 : ℝ) ^ k * (k.factorial : ℝ))) * t ^ (2 * k)) by
        fun_prop).intervalIntegrable 0 r)]
  unfold cdfTaylor
  apply Finset.sum_congr rfl
  intro k hk
  rw [intervalIntegral.integral_const_mul, integral_pow]
  simp only [zero_pow (by omega : 2 * k + 1 ≠ 0), sub_zero,
    Nat.cast_mul, Nat.cast_ofNat]
  have hf : (k.factorial : ℝ) ≠ 0 := by positivity
  have hp : (2 : ℝ) ^ k ≠ 0 := by positivity
  have hd : 2 * (k : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hf, hp, hd]

theorem Phi_taylor_upper (m : ℕ) (hm : Even m) (r : ℝ) (hr : 0 ≤ r) :
    Phi r ≤ (1 : ℝ) / 2 + phi 0 * cdfTaylor m r := by
  have hc := continuous_expTaylor_gaussian m
  have hle := intervalIntegral.integral_mono_on (μ := volume) hr
    (continuous_phi.intervalIntegrable 0 r) ((hc.const_mul (phi 0)).intervalIntegrable 0 r)
    (fun t ht => by
      rw [phi_eq_phi_zero_mul_exp t]
      exact mul_le_mul_of_nonneg_left
        (exp_neg_taylor_upper m hm (t ^ 2 / 2) (by positivity)) (phi_nonneg 0))
  rw [intervalIntegral.integral_const_mul, integral_expTaylor_gaussian] at hle
  rw [Phi_eq_const_add_intervalIntegral, Phi_zero]
  linarith

theorem Phi_taylor_lower (m : ℕ) (hm : Odd m) (r : ℝ) (hr : 0 ≤ r) :
    (1 : ℝ) / 2 + phi 0 * cdfTaylor m r ≤ Phi r := by
  have hc := continuous_expTaylor_gaussian m
  have hle := intervalIntegral.integral_mono_on (μ := volume) hr
    ((hc.const_mul (phi 0)).intervalIntegrable 0 r) (continuous_phi.intervalIntegrable 0 r)
    (fun t ht => by
      rw [phi_eq_phi_zero_mul_exp t]
      exact mul_le_mul_of_nonneg_left
        (exp_neg_taylor_lower m hm (t ^ 2 / 2) (by positivity)) (phi_nonneg 0))
  rw [intervalIntegral.integral_const_mul, integral_expTaylor_gaussian] at hle
  rw [Phi_eq_const_add_intervalIntegral, Phi_zero]
  linarith

/-- The magnitude of the next integrated Taylor term. -/
def cdfTaylorError (m : ℕ) (r : ℝ) : ℝ :=
  r ^ (2 * m + 3) /
    ((2 : ℝ) ^ (m + 1) * ((m + 1).factorial : ℝ) * (2 * (m : ℝ) + 3))

lemma cdfTaylor_succ (m : ℕ) (r : ℝ) :
    cdfTaylor (m + 1) r = cdfTaylor m r + (-1 : ℝ) ^ (m + 1) * cdfTaylorError m r := by
  unfold cdfTaylor
  rw [Finset.sum_range_succ]
  congr 1
  unfold cdfTaylorError
  rw [show 2 * (m + 1) + 1 = 2 * m + 3 by omega]
  push_cast
  ring

/-- Any order gives an explicit error bound for the actual Gaussian CDF. -/
theorem Phi_taylor_abs (m : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    |Phi r - ((1 : ℝ) / 2 + phi 0 * cdfTaylor m r)| ≤ phi 0 * cdfTaylorError m r := by
  rcases Nat.even_or_odd m with hm | hm
  · have hu := Phi_taylor_upper m hm r hr
    have hl := Phi_taylor_lower (m + 1) hm.add_one r hr
    rw [cdfTaylor_succ, hm.add_one.neg_one_pow] at hl
    rw [abs_of_nonpos (by linarith : Phi r - (1 / 2 + phi 0 * cdfTaylor m r) ≤ 0)]
    linarith
  · have hl := Phi_taylor_lower m hm r hr
    have hu := Phi_taylor_upper (m + 1) hm.add_one r hr
    rw [cdfTaylor_succ, hm.add_one.neg_one_pow] at hu
    rw [abs_of_nonneg (by linarith : 0 ≤ Phi r - (1 / 2 + phi 0 * cdfTaylor m r))]
    linarith

/-- Reflection transfers every enclosure to a nonpositive argument. -/
theorem Phi_neg_taylor_abs (m : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    |Phi (-r) - ((1 : ℝ) / 2 - phi 0 * cdfTaylor m r)| ≤ phi 0 * cdfTaylorError m r := by
  rw [GaussianMills.Phi_neg, GaussianMills.tail]
  have heq : 1 - Phi r - ((1 : ℝ) / 2 - phi 0 * cdfTaylor m r) =
      -(Phi r - ((1 : ℝ) / 2 + phi 0 * cdfTaylor m r)) := by ring
  rw [heq, abs_neg]
  exact Phi_taylor_abs m r hr

lemma cdfTaylorError_nonneg (m : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    0 ≤ cdfTaylorError m r := by
  unfold cdfTaylorError
  positivity

lemma cdfTaylorError_eq (m : ℕ) (r : ℝ) :
    cdfTaylorError m r =
      (r * ((r ^ 2 / 2) ^ (m + 1) / ((m + 1).factorial : ℝ))) / (2 * (m : ℝ) + 3) := by
  unfold cdfTaylorError
  rw [div_pow, ← pow_mul]
  have hf : ((m + 1).factorial : ℝ) ≠ 0 := by positivity
  have hp : (2 : ℝ) ^ (m + 1) ≠ 0 := by positivity
  have hd : 2 * (m : ℝ) + 3 ≠ 0 := by positivity
  field_simp [hf, hp, hd]
  ring

/-- The displayed next-term bounds tend to zero, so the enclosures have
arbitrarily high accuracy at each fixed nonnegative argument. -/
theorem tendsto_cdfTaylorError (r : ℝ) (hr : 0 ≤ r) :
    Filter.Tendsto (fun m : ℕ => cdfTaylorError m r) Filter.atTop (𝓝 0) := by
  have ht := (Real.summable_pow_div_factorial (r ^ 2 / 2)).tendsto_atTop_zero.comp
    (Filter.tendsto_add_atTop_nat 1)
  have hm := tendsto_const_nhds.mul ht (a := r)
  simp only [mul_zero] at hm
  apply squeeze_zero (fun m => cdfTaylorError_nonneg m r hr) (fun m => ?_) hm
  rw [cdfTaylorError_eq]
  apply div_le_self
  · positivity
  · have hn : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith

theorem exists_Phi_taylor_accuracy (r : ℝ) (hr : 0 ≤ r) (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℕ, ∀ m ≥ M,
      |Phi r - ((1 : ℝ) / 2 + phi 0 * cdfTaylor m r)| < ε := by
  have ht := tendsto_const_nhds.mul (tendsto_cdfTaylorError r hr) (a := phi 0)
  simp only [mul_zero] at ht
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp (ht.eventually (gt_mem_nhds hε))
  exact ⟨M, fun m hm => (Phi_taylor_abs m r hr).trans_lt (hM m hm)⟩

end BerryEsseen.GaussianEnclosures

#print axioms BerryEsseen.GaussianEnclosures.exp_neg_integral_remainder
#print axioms BerryEsseen.GaussianEnclosures.exp_neg_taylor_abs
#print axioms BerryEsseen.GaussianEnclosures.Phi_taylor_upper
#print axioms BerryEsseen.GaussianEnclosures.Phi_taylor_lower
#print axioms BerryEsseen.GaussianEnclosures.Phi_taylor_abs
#print axioms BerryEsseen.GaussianEnclosures.Phi_neg_taylor_abs
#print axioms BerryEsseen.GaussianEnclosures.exists_Phi_taylor_accuracy
