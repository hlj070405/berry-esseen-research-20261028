module

public import BerryEsseen.IidTaylorPrice
public import Mathlib.Analysis.SpecialFunctions.Bernstein

@[expose] public section

/-! 2026-10-30: exact center powers and whole-interval Bernstein controls.
All powers are deterministic frequency polynomials.  The law specialization
uses only the original compensated Taylor disk, hence only its existing
standardization and finite third absolute moment hypotheses. -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace BerryEsseen.GenericCenterPower

def center (a b : ℝ) : ℂ := (a : ℂ) - Complex.I * (b : ℂ)

def coefficient (n : ℕ) (a g : ℝ) (j : ℕ) : ℝ :=
  if j = 0 then (a ^ n - g) ^ 2 else
    (n.choose j : ℝ) * a ^ (2 * n - 2 * j) -
      if 2 * j ≤ n then 2 * g * (-1 : ℝ) ^ j * (n.choose (2 * j) : ℝ) * a ^ (n - 2 * j)
      else 0

def phasePolynomial (n : ℕ) (a g B : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1), coefficient n a g j * B ^ j

def control (n : ℕ) (a g L : ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (k + 1),
    coefficient n a g j * L ^ j * (k.choose j : ℝ) / (n.choose j : ℝ)

def ControlsLe (n : ℕ) (a g L M : ℝ) : Prop :=
  ∀ k ≤ n, control n a g L k ≤ M

def basis (n k : ℕ) (x : ℝ) : ℝ := (bernsteinPolynomial ℝ n k).eval x

lemma basis_eq (n k : ℕ) (x : ℝ) :
    basis n k x = (n.choose k : ℝ) * x ^ k * (1 - x) ^ (n - k) := by
  simp [basis, bernsteinPolynomial]

lemma basis_nonneg (n k : ℕ) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ basis n k x := by
  rw [basis_eq]
  positivity

lemma basis_sum (n : ℕ) (x : ℝ) :
    ∑ k ∈ Finset.range (n + 1), basis n k x = 1 := by
  simpa only [Polynomial.eval_finsetSum, Polynomial.eval_one, basis] using
    congrArg (Polynomial.eval x) (bernsteinPolynomial.sum ℝ n)

lemma choose_ratio (n k j : ℕ) (hjk : j ≤ k) (hjn : j ≤ n) :
    (k.choose j : ℝ) / (n.choose j : ℝ) * (n.choose k : ℝ) =
      ((n - j).choose (k - j) : ℝ) := by
  have hn : (n.choose j : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_ne_zero hjn)
  have hh : (n.choose k : ℝ) * (k.choose j : ℝ) =
      (n.choose j : ℝ) * ((n - j).choose (k - j) : ℝ) := by
    exact_mod_cast (Nat.choose_mul hjk : n.choose k * k.choose j = _)
  apply (mul_right_cancel₀ hn)
  field_simp
  nlinarith only [hh]

/-- Exact conversion of one monomial to degree-n Bernstein coordinates. -/
theorem monomial_bernstein (n j : ℕ) (hj : j ≤ n) (x : ℝ) :
    x ^ j = ∑ k ∈ Finset.range (n + 1),
      ((k.choose j : ℝ) / (n.choose j : ℝ)) * basis n k x := by
  have hlen : n + 1 = j + (n - j + 1) := by omega
  rw [hlen, Finset.sum_range_add]
  have hzero : ∑ k ∈ Finset.range j,
      ((k.choose j : ℝ) / (n.choose j : ℝ)) * basis n k x = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    simp [Nat.choose_eq_zero_of_lt (Finset.mem_range.mp hk)]
  rw [hzero, zero_add]
  calc
    x ^ j = x ^ j * (x + (1 - x)) ^ (n - j) := by simp
    _ = x ^ j * ∑ k ∈ Finset.range (n - j + 1),
        x ^ k * (1 - x) ^ (n - j - k) * ((n - j).choose k : ℝ) := by rw [add_pow]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have hsub : n - (j + k) = n - j - k := by omega
      rw [basis_eq]
      symm
      calc
        _ = (((j + k).choose j : ℝ) / (n.choose j : ℝ) * (n.choose (j + k) : ℝ)) *
            x ^ (j + k) * (1 - x) ^ (n - (j + k)) := by ring
        _ = _ := by
          rw [choose_ratio n (j + k) j (by omega) hj]
          simp only [Nat.add_sub_cancel_left, hsub, pow_add]
          ring

lemma norm_center_sq (a b : ℝ) : ‖center a b‖ ^ 2 = a ^ 2 + b ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [center, Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, mul_zero,
    one_mul, zero_sub, sub_zero, zero_add]
  ring

lemma neg_I_even (j : ℕ) : ((-Complex.I) ^ (2 * j)).re = (-1 : ℝ) ^ j := by
  rw [pow_mul]
  have h : (-Complex.I) ^ 2 = (-1 : ℂ) := by simp
  rw [h]
  norm_cast

lemma neg_I_odd (j : ℕ) : ((-Complex.I) ^ (2 * j + 1)).re = 0 := by
  rw [pow_succ, pow_mul]
  have h : (-Complex.I) ^ 2 = (-1 : ℂ) := by simp
  rw [h]
  have hreal : ((-1 : ℂ) ^ j).im = 0 := by
    rw [show (-1 : ℂ) = ((-1 : ℝ) : ℂ) from by norm_num, ← Complex.ofReal_pow]
    exact Complex.ofReal_im _
  simp [Complex.mul_re, hreal]

lemma center_power_re_sum (n : ℕ) (a b : ℝ) :
    (center a b ^ n).re = ∑ k ∈ Finset.range (n + 1),
      (n.choose k : ℝ) * a ^ (n - k) * b ^ k * ((-Complex.I) ^ k).re := by
  have hz : center a b = (-Complex.I * (b : ℂ)) + (a : ℂ) := by unfold center; ring
  rw [hz, add_pow, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [mul_pow, ← Complex.ofReal_pow, ← Complex.ofReal_pow]
  simp only [Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.natCast_re, Complex.natCast_im]
  ring

lemma center_power_re_even (n : ℕ) (a b : ℝ) :
    (center a b ^ n).re = ∑ j ∈ Finset.range (n / 2 + 1),
      (-1 : ℝ) ^ j * (n.choose (2 * j) : ℝ) * a ^ (n - 2 * j) * (b ^ 2) ^ j := by
  classical
  rw [center_power_re_sum]
  let term := fun k : ℕ => (n.choose k : ℝ) * a ^ (n - k) * b ^ k * ((-Complex.I) ^ k).re
  change ∑ k ∈ Finset.range (n + 1), term k = _
  have hf : ∑ k ∈ (Finset.range (n + 1)).filter Even, term k =
      ∑ k ∈ Finset.range (n + 1), term k := by
    apply Finset.sum_filter_of_ne
    intro k hk ht
    rcases Nat.even_or_odd' k with ⟨j, h | h⟩
    · exact even_iff_exists_two_mul.mpr ⟨j, h⟩
    · exfalso
      apply ht
      dsimp [term]
      rw [h, neg_I_odd, mul_zero]
  rw [← hf]
  symm
  apply Finset.sum_bij (fun j _ => 2 * j)
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by have := Finset.mem_range.mp hj; omega,
      even_iff_exists_two_mul.mpr ⟨j, rfl⟩⟩
  · intro j hj k hk he
    omega
  · intro k hk
    obtain ⟨hkn, hkEven⟩ := Finset.mem_filter.mp hk
    obtain ⟨j, rfl⟩ := even_iff_exists_two_mul.mp hkEven
    exact ⟨j, Finset.mem_range.mpr (by have := Finset.mem_range.mp hkn; omega), rfl⟩
  · intro j hj
    dsimp [term]
    rw [neg_I_even, pow_mul]
    ring

lemma center_power_re_full (n : ℕ) (a b : ℝ) :
    (center a b ^ n).re = ∑ j ∈ Finset.range (n + 1),
      (-1 : ℝ) ^ j * (n.choose (2 * j) : ℝ) * a ^ (n - 2 * j) * (b ^ 2) ^ j := by
  rw [center_power_re_even]
  apply Finset.sum_subset
  · exact Finset.range_mono (by omega)
  · intro j hjn hj
    have hh : n < 2 * j := by simp only [Finset.mem_range] at *; omega
    simp [Nat.choose_eq_zero_of_lt hh]

lemma norm_power_sub_real_sq (z : ℂ) (n : ℕ) (g : ℝ) :
    ‖z ^ n - (g : ℂ)‖ ^ 2 = (‖z‖ ^ 2) ^ n - 2 * g * (z ^ n).re + g ^ 2 := by
  have hpow : (‖z‖ ^ 2) ^ n = ‖z ^ n‖ ^ 2 := by rw [norm_pow]; ring
  rw [hpow, Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

lemma coefficient_pos_index (n j : ℕ) (a g : ℝ) (hj : j ≠ 0) :
    coefficient n a g j = (n.choose j : ℝ) * a ^ (2 * n - 2 * j) -
      2 * g * (-1 : ℝ) ^ j * (n.choose (2 * j) : ℝ) * a ^ (n - 2 * j) := by
  unfold coefficient
  rw [ite_eq_right hj]
  split_ifs with hh
  · rfl
  · simp [Nat.choose_eq_zero_of_lt (by omega : n < 2 * j)]

lemma binomial_norm (n : ℕ) (a B : ℝ) :
    (a ^ 2 + B) ^ n = ∑ j ∈ Finset.range (n + 1),
      (n.choose j : ℝ) * a ^ (2 * n - 2 * j) * B ^ j := by
  rw [add_comm, add_pow]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← pow_mul]
  have hpow : 2 * (n - j) = 2 * n - 2 * j := Nat.mul_sub_left_distrib 2 n j
  rw [hpow]
  ring

/-- The explicitly combined power coefficients are exactly the binomial
norm expression, including its constant term. -/
theorem phasePolynomial_eq (n : ℕ) (a g B : ℝ) :
    phasePolynomial n a g B = (a ^ 2 + B) ^ n -
      2 * g * (∑ j ∈ Finset.range (n + 1),
        (-1 : ℝ) ^ j * (n.choose (2 * j) : ℝ) * a ^ (n - 2 * j) * B ^ j) + g ^ 2 := by
  rw [binomial_norm]
  unfold phasePolynomial
  rw [Finset.sum_range_succ', Finset.sum_range_succ', Finset.sum_range_succ']
  rw [show coefficient n a g 0 = (a ^ n - g) ^ 2 by simp [coefficient]]
  simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one,
    mul_zero, Nat.sub_zero, one_mul, mul_one]
  have hsum : ∑ j ∈ Finset.range n, coefficient n a g (j + 1) * B ^ (j + 1) =
      (∑ j ∈ Finset.range n, (n.choose (j + 1) : ℝ) *
        a ^ (2 * n - 2 * (j + 1)) * B ^ (j + 1)) -
      2 * g * (∑ j ∈ Finset.range n,
        (-1 : ℝ) ^ (j + 1) * (n.choose (2 * (j + 1)) : ℝ) *
          a ^ (n - 2 * (j + 1)) * B ^ (j + 1)) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [coefficient_pos_index n (j + 1) a g (by omega)]
    ring
  rw [hsum]
  rw [show a ^ (2 * n) = (a ^ n) ^ 2 by rw [Nat.mul_comm 2 n, pow_mul]]
  ring

/-- Exact all-n phase identity. No sign restriction on a, b or g. -/
theorem norm_center_power_sub_real_sq (n : ℕ) (a b g : ℝ) :
    ‖center a b ^ n - (g : ℂ)‖ ^ 2 = phasePolynomial n a g (b ^ 2) := by
  rw [norm_power_sub_real_sq, norm_center_sq, center_power_re_full, phasePolynomial_eq]

lemma control_full (n k : ℕ) (a g L : ℝ) (hk : k ≤ n) :
    control n a g L k = ∑ j ∈ Finset.range (n + 1),
      coefficient n a g j * L ^ j * (k.choose j : ℝ) / (n.choose j : ℝ) := by
  unfold control
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro j hj hjk
  have hh : k < j := by simp only [Finset.mem_range] at hjk; omega
  simp [Nat.choose_eq_zero_of_lt hh]

/-- Exact conversion, with the same controls as the rational power algorithm.
The controls are coefficients, not sampled values at the Bernstein nodes. -/
theorem bernstein_identity (n : ℕ) (a g L x : ℝ) :
    phasePolynomial n a g (L * x) =
      ∑ k ∈ Finset.range (n + 1), control n a g L k * basis n k x := by
  unfold phasePolynomial
  calc
    _ = ∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
        (coefficient n a g j * L ^ j) *
          (((k.choose j : ℝ) / (n.choose j : ℝ)) * basis n k x) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [← Finset.mul_sum, ← monomial_bernstein n j (by have := Finset.mem_range.mp hj; omega)]
      rw [mul_pow]
      ring
    _ = ∑ k ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
        (coefficient n a g j * L ^ j) *
          (((k.choose j : ℝ) / (n.choose j : ℝ)) * basis n k x) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [control_full n k a g L (by have := Finset.mem_range.mp hk; omega), Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      ring

lemma phasePolynomial_zero (n : ℕ) (a g : ℝ) :
    phasePolynomial n a g 0 = coefficient n a g 0 := by
  unfold phasePolynomial
  rw [Finset.sum_eq_single 0]
  · simp
  · intro j hj hj0
    simp [zero_pow hj0]
  · simp

lemma control_zero (n : ℕ) (a g L : ℝ) : control n a g L 0 = coefficient n a g 0 := by
  simp [control]

/-- A single finite list of controls bounds every B in the closed interval,
including the degenerate interval L=0. -/
theorem phasePolynomial_le_of_controls (n : ℕ) (a g L B M : ℝ) (hL : 0 ≤ L)
    (hB0 : 0 ≤ B) (hBL : B ≤ L) (hc : ControlsLe n a g L M) :
    phasePolynomial n a g B ≤ M := by
  by_cases hL0 : L = 0
  · have hB : B = 0 := by linarith only [hB0, hBL, hL0]
    rw [hB, phasePolynomial_zero, ← control_zero n a g L]
    exact hc 0 (Nat.zero_le n)
  · have hLp : 0 < L := lt_of_le_of_ne hL (Ne.symm hL0)
    let x := B / L
    have hx0 : 0 ≤ x := div_nonneg hB0 hL
    have hx1 : x ≤ 1 := (div_le_one hLp).mpr hBL
    have hBx : B = L * x := by dsimp [x]; field_simp [hL0]
    rw [hBx, bernstein_identity]
    calc
      _ ≤ ∑ k ∈ Finset.range (n + 1), M * basis n k x := by
        apply Finset.sum_le_sum
        intro k hk
        exact mul_le_mul_of_nonneg_right
          (hc k (by have := Finset.mem_range.mp hk; omega)) (basis_nonneg n k x hx0 hx1)
      _ = M := by rw [← Finset.mul_sum, basis_sum, mul_one]

theorem norm_center_power_sub_real_le_sqrt (n : ℕ) (a b g L M : ℝ) (hL : 0 ≤ L)
    (hb : b ^ 2 ≤ L) (hM : 0 ≤ M) (hc : ControlsLe n a g L M) :
    ‖center a b ^ n - (g : ℂ)‖ ≤ Real.sqrt M := by
  apply (Real.le_sqrt (norm_nonneg _) hM).mpr
  rw [norm_center_power_sub_real_sq]
  exact phasePolynomial_le_of_controls n a g L (b ^ 2) M hL (sq_nonneg b) hb hc

theorem disk_perturbation_le (n : ℕ) (f : ℂ) (a b g L M r q C : ℝ)
    (hL : 0 ≤ L) (hb : b ^ 2 ≤ L) (hM : 0 ≤ M) (hc : ControlsLe n a g L M)
    (hf : ‖f‖ ≤ q) (hz : ‖center a b‖ ≤ C) (hr : ‖f - center a b‖ ≤ r) :
    ‖f ^ n - (g : ℂ)‖ ≤ r * IidTaylorPrice.geometric n q C + Real.sqrt M := by
  have hp := IidTaylorPrice.norm_pow_sub_pow_le f (center a b) n q C r hf hz hr
  have hphase := norm_center_power_sub_real_le_sqrt n a b g L M hL hb hM hc
  calc
    _ = ‖(f ^ n - center a b ^ n) + (center a b ^ n - (g : ℂ))‖ := by congr 1; ring
    _ ≤ ‖f ^ n - center a b ^ n‖ + ‖center a b ^ n - (g : ℂ)‖ := norm_add_le _ _
    _ ≤ _ := add_le_add hp hphase

lemma center_actual (μ : ProbabilityMeasure ℝ) (u : ℝ) :
    center (1 - u ^ 2 / 2) (ZeroBias.gamma μ * u ^ 3 / 16) = IidTaylorPrice.center μ u := by
  simp only [center, IidTaylorPrice.center, Complex.ofReal_sub, Complex.ofReal_one]

/-- Actual same-law disk and phase bound. Supplied numerical caps remain
explicit, while the original compensated Taylor radius is derived here.
This theorem also covers n=0 algebraically; its intended use is n≥1. -/
theorem charFun_power_sub_real_le (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (u g L M r q C : ℝ) (hL : 0 ≤ L)
    (hb : (ZeroBias.gamma μ * u ^ 3 / 16) ^ 2 ≤ L)
    (hM : 0 ≤ M) (hc : ControlsLe n (1 - u ^ 2 / 2) g L M)
    (hq : ‖charFun (μ : Measure ℝ) u‖ ≤ q) (hC : ‖IidTaylorPrice.center μ u‖ ≤ C)
    (hr : IidTaylorPrice.radius μ u ≤ r) :
    ‖charFun (μ : Measure ℝ) u ^ n - (g : ℂ)‖ ≤
      r * IidTaylorPrice.geometric n q C + Real.sqrt M := by
  apply disk_perturbation_le n (charFun (μ : Measure ℝ) u) (1 - u ^ 2 / 2)
    (ZeroBias.gamma μ * u ^ 3 / 16) g L M r q C hL hb hM hc hq
  · rw [center_actual]
    exact hC
  · rw [center_actual]
    exact (IidTaylorPrice.norm_sub_center_le μ h u).trans hr

/-- Direct specialization to the actual normalized iid sum and its exact
Gaussian reference, with no change to the original law or its phase. -/
theorem normalized_charFun_sub_gaussian_le (μ : ProbabilityMeasure ℝ)
    (h : StandardizedLaw μ) (n : ℕ) (t L M r q C : ℝ) (hL : 0 ≤ L)
    (hb : (ZeroBias.gamma μ * (t / Real.sqrt n) ^ 3 / 16) ^ 2 ≤ L)
    (hM : 0 ≤ M)
    (hc : ControlsLe n (1 - (t / Real.sqrt n) ^ 2 / 2)
      (Real.exp (-(t ^ 2 / 2))) L M)
    (hq : ‖charFun (μ : Measure ℝ) (t / Real.sqrt n)‖ ≤ q)
    (hC : ‖IidTaylorPrice.center μ (t / Real.sqrt n)‖ ≤ C)
    (hr : IidTaylorPrice.radius μ (t / Real.sqrt n) ≤ r) :
    ‖charFun (normalizedIidSumLaw μ n) t - (Real.exp (-(t ^ 2 / 2)) : ℂ)‖ ≤
      r * IidTaylorPrice.geometric n q C + Real.sqrt M := by
  rw [PrawitzSmoothing.charFun_normalizedIidSumLaw]
  exact charFun_power_sub_real_le μ h n (t / Real.sqrt n)
    (Real.exp (-(t ^ 2 / 2))) L M r q C hL hb hM hc hq hC hr

end BerryEsseen.GenericCenterPower

#print axioms BerryEsseen.GenericCenterPower.norm_center_power_sub_real_sq
#print axioms BerryEsseen.GenericCenterPower.monomial_bernstein
#print axioms BerryEsseen.GenericCenterPower.bernstein_identity
#print axioms BerryEsseen.GenericCenterPower.phasePolynomial_le_of_controls
#print axioms BerryEsseen.GenericCenterPower.norm_center_power_sub_real_le_sqrt
#print axioms BerryEsseen.GenericCenterPower.disk_perturbation_le
#print axioms BerryEsseen.GenericCenterPower.charFun_power_sub_real_le
#print axioms BerryEsseen.GenericCenterPower.normalized_charFun_sub_gaussian_le
