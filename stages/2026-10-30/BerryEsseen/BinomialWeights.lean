module

public import BerryEsseen.CoupledPrice
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Inv

@[expose] public section

/-!
Native C2 interfaces for the actual binomial masses and finite lower
prefixes used by the canonical staircase. The logarithmic formulas are
proved on 0<p<1, including the zero exponents at k=0 and k=n.
The prefix identities follow from finite summation and an exact adjacent
mass flux recurrence, rather than an assumed cumulative formula.
-/

namespace BerryEsseen.BinomialWeights

open MeasureTheory Filter Set
open scoped BigOperators Topology ContDiff

noncomputable section

def mass (n k : ℕ) (p : ℝ) : ℝ :=
  (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k)

def lowerPrefix (n k : ℕ) (p : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (k + 1), mass n j p

def massSlope (n k : ℕ) (p : ℝ) : ℝ :=
  mass n k p * ((k : ℝ) - (n : ℝ) * p) / (p * (1 - p))

def massCurvature (n k : ℕ) (p : ℝ) : ℝ :=
  mass n k p * (((k : ℝ) - (n : ℝ) * p) ^ 2 -
    (k : ℝ) * (1 - p) ^ 2 - ((n - k : ℕ) : ℝ) * p ^ 2) /
    (p ^ 2 * (1 - p) ^ 2)

def prefixSlope (n k : ℕ) (p : ℝ) : ℝ :=
  -((n - k : ℕ) : ℝ) * mass n k p / (1 - p)

def prefixCurvature (n k : ℕ) (p : ℝ) : ℝ :=
  -((n - k : ℕ) : ℝ) * mass n k p * ((k : ℝ) - ((n - 1 : ℕ) : ℝ) * p) /
    (p * (1 - p) ^ 2)

theorem mass_at_canonical (μ : ProbabilityMeasure ℝ) (n k : ℕ) :
    mass n k (CanonicalSign.p μ) = CoupledPrice.canonicalBinomialWeight μ n k := rfl

theorem prefix_at_canonical (μ : ProbabilityMeasure ℝ) (n k : ℕ) :
    lowerPrefix n k (CanonicalSign.p μ) =
      Staircase.lowerMass (CoupledPrice.canonicalBinomialWeight μ n) k := rfl

/-- Polynomial regularity is proved for the actual mass, independently
of the rational forms used to express its derivatives inside (0,1). -/
theorem contDiff_two_mass (n k : ℕ) : ContDiff ℝ 2 (mass n k) := by
  unfold mass
  fun_prop

theorem contDiff_two_prefix (n k : ℕ) : ContDiff ℝ 2 (lowerPrefix n k) := by
  unfold lowerPrefix
  exact ContDiff.sum (fun j _ => contDiff_two_mass n j)

theorem mass_nonneg (n k : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) : 0 ≤ mass n k p := by
  unfold mass
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp _))
    (pow_nonneg (sub_nonneg.mpr hp1) _)

theorem mass_pos (n k : ℕ) (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (hk : k ≤ n) :
    0 < mass n k p := by
  unfold mass
  exact mul_pos (mul_pos (Nat.cast_pos.mpr (Nat.choose_pos hk)) (pow_pos hp _))
    (pow_pos (sub_pos.mpr hp1) _)

/-- The full finite prefix is the actual total binomial mass. -/
theorem lowerPrefix_self (n : ℕ) (p : ℝ) : lowerPrefix n n p = 1 := by
  unfold lowerPrefix mass
  calc
    _ = ∑ j ∈ Finset.range (n + 1), p ^ j * (1 - p) ^ (n - j) * (n.choose j : ℝ) := by
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = (p + (1 - p)) ^ n := (add_pow p (1 - p) n).symm
    _ = 1 := by rw [show p + (1 - p) = 1 by ring, one_pow]

private theorem hasDerivAt_pow_ratio (k : ℕ) (p : ℝ) (hp : p ≠ 0) :
    HasDerivAt (fun x : ℝ => x ^ k) (p ^ k * (k : ℝ) / p) p := by
  cases k with
  | zero => simpa only [pow_zero, Nat.cast_zero, mul_zero, zero_div] using hasDerivAt_const p (1 : ℝ)
  | succ k =>
    convert (hasDerivAt_id' p).fun_pow (k + 1) using 1
    simp only [Nat.add_sub_cancel, mul_one, pow_succ]
    field_simp [hp]

theorem hasDerivAt_mass (n k : ℕ) (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (hk : k ≤ n) :
    HasDerivAt (mass n k) (massSlope n k p) p := by
  have hq : 0 < 1 - p := sub_pos.mpr hp1
  have hP := hasDerivAt_pow_ratio k p hp.ne'
  have hQ : HasDerivAt (fun x : ℝ => (1 - x) ^ (n - k))
      (-(1 - p) ^ (n - k) * ((n - k : ℕ) : ℝ) / (1 - p)) p := by
    have hinner : HasDerivAt (fun x : ℝ => 1 - x) (-1) p :=
      HasDerivAt.const_sub 1 (hasDerivAt_id' p)
    convert (hasDerivAt_pow_ratio (n - k) (1 - p) hq.ne').comp p hinner using 1
    · funext x
      rfl
    · ring
  have hcast : ((n - k : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) := Nat.cast_sub hk
  unfold massSlope mass
  convert (hP.const_mul (n.choose k : ℝ)).fun_mul hQ using 1
  rw [hcast]
  field_simp [hp.ne', hq.ne'] ; ring

theorem deriv_mass (n k : ℕ) (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (hk : k ≤ n) :
    deriv (mass n k) p =
      mass n k p * ((k : ℝ) - (n : ℝ) * p) / (p * (1 - p)) :=
  (hasDerivAt_mass n k p hp hp1 hk).deriv

theorem hasDerivAt_deriv_mass (n k : ℕ) (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (hk : k ≤ n) :
    HasDerivAt (deriv (mass n k)) (massCurvature n k p) p := by
  have hq : 0 < 1 - p := sub_pos.mpr hp1
  have hfirst := hasDerivAt_mass n k p hp hp1 hk
  have hnum : HasDerivAt (fun x : ℝ => (k : ℝ) - (n : ℝ) * x) (-(n : ℝ)) p := by
    simpa only [mul_one] using HasDerivAt.const_sub (k : ℝ) ((hasDerivAt_id' p).const_mul (n : ℝ))
  have hden : HasDerivAt (fun x : ℝ => x * (1 - x)) (1 - 2 * p) p := by
    convert (hasDerivAt_id' p).fun_mul (HasDerivAt.const_sub (1 : ℝ) (hasDerivAt_id' p)) using 1
    ring
  have hscore := hnum.fun_div hden (mul_ne_zero hp.ne' hq.ne')
  have hraw := hfirst.fun_mul hscore
  have heq : deriv (mass n k) =ᶠ[𝓝 p]
      (fun x : ℝ => mass n k x * (((k : ℝ) - (n : ℝ) * x) / (x * (1 - x)))) := by
    filter_upwards [Ioo_mem_nhds hp hp1] with x hx
    have h := (hasDerivAt_mass n k x hx.1 hx.2 hk).deriv
    simpa only [massSlope, div_eq_mul_inv, mul_assoc] using h
  have hcast : ((n - k : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) := Nat.cast_sub hk
  convert hraw.congr_of_eventuallyEq heq using 1
  unfold massCurvature massSlope
  rw [hcast]
  field_simp [hp.ne', hq.ne'] ; ring

theorem secondDeriv_mass (n k : ℕ) (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (hk : k ≤ n) :
    deriv (deriv (mass n k)) p =
      mass n k p * (((k : ℝ) - (n : ℝ) * p) ^ 2 -
        (k : ℝ) * (1 - p) ^ 2 - ((n - k : ℕ) : ℝ) * p ^ 2) /
        (p ^ 2 * (1 - p) ^ 2) :=
  (hasDerivAt_deriv_mass n k p hp hp1 hk).deriv

/-- The generic finite-sum derivative is also exposed before telescoping. -/
theorem hasDerivAt_prefix_sum (n k : ℕ) (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (hk : k ≤ n) :
    HasDerivAt (lowerPrefix n k) (∑ j ∈ Finset.range (k + 1), massSlope n j p) p := by
  unfold lowerPrefix
  exact HasDerivAt.fun_sum (fun j hj => hasDerivAt_mass n j p hp hp1
    ((Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)).trans hk))

private lemma adjacent_mass_flux (n k : ℕ) (p : ℝ)
    (hp : 0 < p) (hp1 : p < 1) (hk : k < n) :
    ((k + 1 : ℕ) : ℝ) * mass n (k + 1) p / p =
      ((n - k : ℕ) : ℝ) * mass n k p / (1 - p) := by
  have hq : 0 < 1 - p := sub_pos.mpr hp1
  have hchoose : (n.choose (k + 1) : ℝ) * ((k + 1 : ℕ) : ℝ) =
      (n.choose k : ℝ) * ((n - k : ℕ) : ℝ) := by
    simpa only [Nat.cast_mul] using
      congrArg (fun m : ℕ => (m : ℝ)) (Nat.choose_succ_right_eq n k)
  have hexp : n - k = (n - (k + 1)) + 1 := by
    have hpos : 1 ≤ n - k := Nat.succ_le_of_lt (Nat.sub_pos_of_lt hk)
    calc
      n - k = (n - k - 1) + 1 := (Nat.sub_add_cancel hpos).symm
      _ = _ := by rw [Nat.sub_sub]
  have hpow : (1 - p) ^ (n - k) = (1 - p) ^ (n - (k + 1)) * (1 - p) := by
    rw [hexp, pow_succ]
  unfold mass
  rw [pow_succ, hpow]
  field_simp [hp.ne', hq.ne']
  nlinarith only [hchoose]

private lemma massSlope_zero (n : ℕ) (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    massSlope n 0 p = -(n : ℝ) * mass n 0 p / (1 - p) := by
  have hq : 0 < 1 - p := sub_pos.mpr hp1
  unfold massSlope
  simp only [Nat.cast_zero, zero_sub]
  field_simp [hp.ne', hq.ne']

private lemma massSlope_succ_flux (n k : ℕ) (p : ℝ)
    (hp : 0 < p) (hp1 : p < 1) (hk : k < n) :
    massSlope n (k + 1) p =
      ((n - k : ℕ) : ℝ) * mass n k p / (1 - p) -
        ((n - (k + 1) : ℕ) : ℝ) * mass n (k + 1) p / (1 - p) := by
  have hq : 0 < 1 - p := sub_pos.mpr hp1
  have hcast : ((n - (k + 1) : ℕ) : ℝ) = (n : ℝ) - ((k + 1 : ℕ) : ℝ) :=
    Nat.cast_sub (Nat.succ_le_of_lt hk)
  have hsplit : massSlope n (k + 1) p =
      ((k + 1 : ℕ) : ℝ) * mass n (k + 1) p / p -
        ((n - (k + 1) : ℕ) : ℝ) * mass n (k + 1) p / (1 - p) := by
    unfold massSlope
    rw [hcast]
    field_simp [hp.ne', hq.ne'] ; ring
  rw [hsplit, adjacent_mass_flux n k p hp hp1 hk]

private theorem sum_massSlope_prefix (n k : ℕ) (p : ℝ)
    (hp : 0 < p) (hp1 : p < 1) (hk : k ≤ n) :
    (∑ j ∈ Finset.range (k + 1), massSlope n j p) = prefixSlope n k p := by
  induction k with
  | zero =>
    simpa only [Nat.zero_add, Finset.sum_range_one, prefixSlope, Nat.sub_zero] using massSlope_zero n p hp hp1
  | succ k ih =>
    have hklt : k < n := lt_of_lt_of_le (Nat.lt_succ_self _) hk
    rw [Finset.sum_range_succ, ih (Nat.le_of_lt hklt), massSlope_succ_flux n k p hp hp1 hklt]
    unfold prefixSlope
    ring

/-- Closed finite-prefix first derivative, obtained by exact flux telescoping.
The full prefix k=n is included and has derivative zero. -/
theorem hasDerivAt_prefix (n k : ℕ) (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (hk : k ≤ n) :
    HasDerivAt (lowerPrefix n k) (prefixSlope n k p) p :=
  (hasDerivAt_prefix_sum n k p hp hp1 hk).congr_deriv (sum_massSlope_prefix n k p hp hp1 hk)

theorem deriv_prefix (n k : ℕ) (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (hk : k ≤ n) :
    deriv (lowerPrefix n k) p = -((n - k : ℕ) : ℝ) * mass n k p / (1 - p) :=
  (hasDerivAt_prefix n k p hp hp1 hk).deriv

theorem hasDerivAt_deriv_prefix (n k : ℕ) (p : ℝ)
    (hp : 0 < p) (hp1 : p < 1) (hk : k < n) :
    HasDerivAt (deriv (lowerPrefix n k)) (prefixCurvature n k p) p := by
  have hq : 0 < 1 - p := sub_pos.mpr hp1
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le k) hk
  have hfirst := hasDerivAt_mass n k p hp hp1 hk.le
  have hnum := hfirst.const_mul (-((n - k : ℕ) : ℝ))
  have hden : HasDerivAt (fun x : ℝ => 1 - x) (-1) p :=
    HasDerivAt.const_sub 1 (hasDerivAt_id' p)
  have hraw := hnum.fun_div hden hq.ne'
  have heq : deriv (lowerPrefix n k) =ᶠ[𝓝 p]
      (fun x : ℝ => -((n - k : ℕ) : ℝ) * mass n k x / (1 - x)) := by
    filter_upwards [Ioo_mem_nhds hp hp1] with x hx
    exact (hasDerivAt_prefix n k x hx.1 hx.2 hk.le).deriv
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (Nat.succ_le_of_lt hn), Nat.cast_one]
  convert hraw.congr_of_eventuallyEq heq using 1
  unfold prefixCurvature massSlope
  rw [hcast]
  field_simp [hp.ne', hq.ne'] ; ring

theorem secondDeriv_prefix (n k : ℕ) (p : ℝ)
    (hp : 0 < p) (hp1 : p < 1) (hk : k < n) :
    deriv (deriv (lowerPrefix n k)) p =
      -((n - k : ℕ) : ℝ) * mass n k p * ((k : ℝ) - ((n - 1 : ℕ) : ℝ) * p) /
        (p * (1 - p) ^ 2) :=
  (hasDerivAt_deriv_prefix n k p hp hp1 hk).deriv

theorem hasDerivAt_deriv_prefix_self (n : ℕ) (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    HasDerivAt (deriv (lowerPrefix n n)) 0 p := by
  have heq : deriv (lowerPrefix n n) =ᶠ[𝓝 p] (fun _ : ℝ => 0) := by
    filter_upwards [Ioo_mem_nhds hp hp1] with x hx
    have h := (hasDerivAt_prefix n n x hx.1 hx.2 le_rfl).deriv
    simpa only [prefixSlope, Nat.sub_self, Nat.cast_zero, neg_zero, zero_mul, zero_div] using h
  exact (hasDerivAt_const p (0 : ℝ)).congr_of_eventuallyEq heq

theorem secondDeriv_prefix_self (n : ℕ) (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    deriv (deriv (lowerPrefix n n)) p = 0 :=
  (hasDerivAt_deriv_prefix_self n p hp hp1).deriv

end

end BerryEsseen.BinomialWeights

#print axioms BerryEsseen.BinomialWeights.hasDerivAt_mass
#print axioms BerryEsseen.BinomialWeights.hasDerivAt_deriv_mass
#print axioms BerryEsseen.BinomialWeights.hasDerivAt_prefix_sum
#print axioms BerryEsseen.BinomialWeights.hasDerivAt_prefix
#print axioms BerryEsseen.BinomialWeights.hasDerivAt_deriv_prefix
#print axioms BerryEsseen.BinomialWeights.hasDerivAt_deriv_prefix_self
#print axioms BerryEsseen.BinomialWeights.lowerPrefix_self
