module

public import BerryEsseen.HighFrequencyFloor

@[expose] public section

/-! 2026-10-30: keep the square-root sample normalization when a true
characteristic-function band has squared modulus at most 3/4.
The argument is discrete and uses no logarithmic or fractional powers. -/

noncomputable section

namespace BerryEsseen.ScaledPowerFloor

theorem sqrt_mul_pow_succ_le (x : ℝ) (hx0 : 0 ≤ x) (hx : x ^ 2 ≤ 3 / 4)
    (n : ℕ) (hn : 3 ≤ n) :
    Real.sqrt (n + 1 : ℕ) * x ^ (n + 1) ≤ Real.sqrt n * x ^ n := by
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hp := mul_le_mul_of_nonneg_left hx
    (Nat.cast_nonneg (n + 1) : (0 : ℝ) ≤ (n + 1 : ℕ))
  have hs : (Real.sqrt (n + 1 : ℕ) * x) ^ 2 ≤ (Real.sqrt n) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg (n + 1)),
      Real.sq_sqrt (Nat.cast_nonneg n)]
    simp only [Nat.cast_add, Nat.cast_one] at hp ⊢
    nlinarith only [hp, hnR]
  have hr := (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) hx0) (Real.sqrt_nonneg _)).mp hs
  have hm := mul_le_mul_of_nonneg_right hr (pow_nonneg hx0 n)
  simpa only [pow_succ, mul_assoc, mul_comm, mul_left_comm] using hm

theorem sqrt_mul_pow_le_floor (x : ℝ) (hx0 : 0 ≤ x) (hx : x ^ 2 ≤ 3 / 4)
    (N n : ℕ) (hN : 3 ≤ N) (hNn : N ≤ n) :
    Real.sqrt n * x ^ n ≤ Real.sqrt N * x ^ N := by
  induction n, hNn using Nat.le_induction with
  | base => exact le_rfl
  | succ n hn ih =>
      exact (sqrt_mul_pow_succ_le x hx0 hx n (hN.trans hn)).trans ih

end BerryEsseen.ScaledPowerFloor

#print axioms BerryEsseen.ScaledPowerFloor.sqrt_mul_pow_succ_le
#print axioms BerryEsseen.ScaledPowerFloor.sqrt_mul_pow_le_floor
