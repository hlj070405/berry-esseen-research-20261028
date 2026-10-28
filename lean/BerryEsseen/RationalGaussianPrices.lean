module

public import BerryEsseen.GaussianEnclosures

@[expose] public section

/-! 2026-10-28: rational Taylor prices for the actual standard Gaussian CDF.
Products select the density endpoint according to the sign of the Taylor sum.
Negative arguments use reflection, and endpoint prices extend to real intervals. -/

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace BerryEsseen.RationalGaussianPrices

open GaussianTools GaussianPrices GaussianEnclosures

def densityLower : ℚ := 398942280401432677 / 10 ^ 18
def densityUpper : ℚ := 398942280401432678 / 10 ^ 18

/-- The official twenty-place upper bound on pi gives the lower density price. -/
theorem densityLower_lt_phi_zero : (densityLower : ℝ) < phi 0 := by
  have hr : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hs := Real.sq_sqrt (show 0 ≤ 2 * Real.pi by positivity)
  have hp := Real.pi_lt_d20
  have hu : Real.sqrt (2 * Real.pi) < (10 ^ 18 : ℝ) / 398942280401432677 := by
    nlinarith
  rw [phi_zero_eq]
  apply (lt_div_iff₀ hr).mpr
  have hd : (densityLower : ℝ) = (398942280401432677 : ℝ) / 10 ^ 18 := by
    norm_num [densityLower]
  rw [hd]
  nlinarith only [hu]

/-- The official twenty-place lower bound on pi gives the upper density price. -/
theorem phi_zero_lt_densityUpper : phi 0 < (densityUpper : ℝ) := by
  have hr : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hs := Real.sq_sqrt (show 0 ≤ 2 * Real.pi by positivity)
  have hp := Real.pi_gt_d20
  have hl : (10 ^ 18 : ℝ) / 398942280401432678 < Real.sqrt (2 * Real.pi) := by
    nlinarith
  rw [phi_zero_eq]
  apply (div_lt_iff₀ hr).mpr
  have hd : (densityUpper : ℝ) = (398942280401432678 : ℝ) / 10 ^ 18 := by
    norm_num [densityUpper]
  rw [hd]
  nlinarith only [hl]

/-- A finite sum calculated entirely in the rational numbers. -/
def rationalTaylor (m : ℕ) (q : ℚ) : ℚ :=
  ∑ k ∈ Finset.range (m + 1),
    (-1 : ℚ) ^ k * q ^ (2 * k + 1) /
      ((2 : ℚ) ^ k * (k.factorial : ℚ) * (2 * (k : ℚ) + 1))

def rationalError (m : ℕ) (q : ℚ) : ℚ :=
  q ^ (2 * m + 3) /
    ((2 : ℚ) ^ (m + 1) * ((m + 1).factorial : ℚ) * (2 * (m : ℚ) + 3))

@[simp] theorem coe_rationalTaylor (m : ℕ) (q : ℚ) :
    (rationalTaylor m q : ℝ) = cdfTaylor m (q : ℝ) := by
  unfold rationalTaylor cdfTaylor
  push_cast
  rfl

@[simp] theorem coe_rationalError (m : ℕ) (q : ℚ) :
    (rationalError m q : ℝ) = cdfTaylorError m (q : ℝ) := by
  unfold rationalError cdfTaylorError
  push_cast
  rfl

/-- A negative multiplier reverses the choice of density endpoint. -/
def mulLower (s : ℚ) : ℚ :=
  if 0 ≤ s then densityLower * s else densityUpper * s

def mulUpper (s : ℚ) : ℚ :=
  if 0 ≤ s then densityUpper * s else densityLower * s

lemma mulLower_le (s : ℚ) : (mulLower s : ℝ) ≤ phi 0 * (s : ℝ) := by
  unfold mulLower
  split_ifs with hs
  · push_cast
    exact mul_le_mul_of_nonneg_right densityLower_lt_phi_zero.le (by exact_mod_cast hs)
  · push_cast
    exact mul_le_mul_of_nonpos_right phi_zero_lt_densityUpper.le
      (by exact_mod_cast (le_of_lt (lt_of_not_ge hs)))

lemma le_mulUpper (s : ℚ) : phi 0 * (s : ℝ) ≤ (mulUpper s : ℝ) := by
  unfold mulUpper
  split_ifs with hs
  · push_cast
    exact mul_le_mul_of_nonneg_right phi_zero_lt_densityUpper.le (by exact_mod_cast hs)
  · push_cast
    exact mul_le_mul_of_nonpos_right densityLower_lt_phi_zero.le
      (by exact_mod_cast (le_of_lt (lt_of_not_ge hs)))

def nonnegLower (m : ℕ) (q : ℚ) : ℚ :=
  1 / 2 + mulLower (rationalTaylor m q) - densityUpper * rationalError m q

def nonnegUpper (m : ℕ) (q : ℚ) : ℚ :=
  1 / 2 + mulUpper (rationalTaylor m q) + densityUpper * rationalError m q

/-- Both prices work at every order; the error uses the positive upper density price. -/
theorem Phi_nonneg_rational_bounds (m : ℕ) (q : ℚ) (hq : 0 ≤ q) :
    (nonnegLower m q : ℝ) ≤ Phi (q : ℝ) ∧ Phi (q : ℝ) ≤ (nonnegUpper m q : ℝ) := by
  have hqr : (0 : ℝ) ≤ q := by exact_mod_cast hq
  have herr := (Phi_taylor_abs m (q : ℝ) hqr).trans
    (mul_le_mul_of_nonneg_right phi_zero_lt_densityUpper.le
      (cdfTaylorError_nonneg m (q : ℝ) hqr))
  rw [← coe_rationalTaylor, ← coe_rationalError] at herr
  have hab := abs_le.mp herr
  have hlo := mulLower_le (rationalTaylor m q)
  have hup := le_mulUpper (rationalTaylor m q)
  dsimp only [nonnegLower, nonnegUpper]
  push_cast
  constructor <;> linarith [hab.1, hab.2]

/-- A rational lower price, including negative rational arguments by reflection. -/
def PhiLower (m : ℕ) (q : ℚ) : ℚ :=
  if 0 ≤ q then nonnegLower m q else 1 - nonnegUpper m (-q)

def PhiUpper (m : ℕ) (q : ℚ) : ℚ :=
  if 0 ≤ q then nonnegUpper m q else 1 - nonnegLower m (-q)

theorem Phi_rational_bounds (m : ℕ) (q : ℚ) :
    (PhiLower m q : ℝ) ≤ Phi (q : ℝ) ∧ Phi (q : ℝ) ≤ (PhiUpper m q : ℝ) := by
  by_cases hq : 0 ≤ q
  · simpa only [PhiLower, PhiUpper, ite_eq_left hq] using Phi_nonneg_rational_bounds m q hq
  · have hn : 0 ≤ -q := neg_nonneg.mpr (le_of_lt (lt_of_not_ge hq))
    have h := Phi_nonneg_rational_bounds m (-q) hn
    have hrefl : Phi (q : ℝ) = 1 - Phi ((-q : ℚ) : ℝ) := by
      simpa only [Rat.cast_neg, neg_neg, GaussianMills.tail] using
        GaussianMills.Phi_neg ((-q : ℚ) : ℝ)
    simp only [PhiLower, PhiUpper, ite_eq_right hq, Rat.cast_sub, Rat.cast_one]
    rw [hrefl]
    constructor <;> linarith [h.1, h.2]

/-- Monotonicity of the actual closed CDF extends prices over whole real intervals. -/
theorem Phi_interval_rational_bounds (m n : ℕ) (qL qU : ℚ) (r : ℝ)
    (hL : (qL : ℝ) ≤ r) (hU : r ≤ (qU : ℝ)) :
    (PhiLower m qL : ℝ) ≤ Phi r ∧ Phi r ≤ (PhiUpper n qU : ℝ) := by
  have hm : Monotone Phi := fun a b hab => measureReal_mono (Iic_subset_Iic.mpr hab)
  exact ⟨(Phi_rational_bounds m qL).1.trans (hm hL),
    (hm hU).trans (Phi_rational_bounds n qU).2⟩

/-- One fixed order demonstrates a narrow price without floating-point evaluation. -/
theorem Phi_one_tight :
    (8413447460685429 : ℝ) / 10 ^ 16 < Phi 1 ∧
      Phi 1 < (8413447460685430 : ℝ) / 10 ^ 16 := by
  have h := Phi_rational_bounds 20 1
  have hL : (8413447460685429 : ℚ) / 10 ^ 16 < PhiLower 20 1 := by
    norm_num [PhiLower, nonnegLower, mulLower, densityLower, densityUpper,
      rationalTaylor, rationalError, Finset.sum_range_succ]
  have hU : PhiUpper 20 1 < (8413447460685430 : ℚ) / 10 ^ 16 := by
    norm_num [PhiUpper, nonnegUpper, mulUpper, densityLower, densityUpper,
      rationalTaylor, rationalError, Finset.sum_range_succ]
  norm_num only [Rat.cast_one] at h
  constructor
  · calc
      (8413447460685429 : ℝ) / 10 ^ 16 = (((8413447460685429 : ℚ) / 10 ^ 16 : ℚ) : ℝ) := by norm_num
      _ < (PhiLower 20 1 : ℝ) := Rat.cast_lt.mpr hL
      _ ≤ Phi 1 := h.1
  · calc
      Phi 1 ≤ (PhiUpper 20 1 : ℝ) := h.2
      _ < (((8413447460685430 : ℚ) / 10 ^ 16 : ℚ) : ℝ) := Rat.cast_lt.mpr hU
      _ = (8413447460685430 : ℝ) / 10 ^ 16 := by norm_num

end BerryEsseen.RationalGaussianPrices

#print axioms BerryEsseen.RationalGaussianPrices.densityLower_lt_phi_zero
#print axioms BerryEsseen.RationalGaussianPrices.phi_zero_lt_densityUpper
#print axioms BerryEsseen.RationalGaussianPrices.Phi_rational_bounds
#print axioms BerryEsseen.RationalGaussianPrices.Phi_interval_rational_bounds
#print axioms BerryEsseen.RationalGaussianPrices.Phi_one_tight
