module

public import BerryEsseen.MixtureSum
public import BerryEsseen.PerturbationMoment
public import Mathlib.Analysis.Calculus.Deriv.Pow

@[expose] public section

noncomputable section

namespace BerryEsseen.PerturbationCDF

open MeasureTheory Filter Set
open scoped Topology BigOperators NNReal ENNReal

theorem convPower_dirac (x : ℝ) (j : ℕ) :
    MixtureSum.convPower (Measure.dirac x) j = Measure.dirac ((j : ℝ) * x) := by
  induction j with
  | zero => simp [MixtureSum.convPower]
  | succ j ih =>
    rw [MixtureSum.convPower, ih, Measure.dirac_conv_dirac]
    congr 1
    push_cast
    ring

/-- All CDF events remain closed, including at atoms of either summand. -/
theorem component_closedCDF (μ : ProbabilityMeasure ℝ) (x H : ℝ) (n j : ℕ) :
    (MixtureSum.convPower (Measure.dirac x) j ∗
      MixtureSum.convPower (μ : Measure ℝ) (n - j)).real (Iic H) =
    (MixtureSum.iidSumLaw (μ : Measure ℝ) (n - j)).real (Iic (H - (j : ℝ) * x)) := by
  rw [convPower_dirac, Measure.dirac_conv]
  have hf : Measurable (fun u : ℝ => (j : ℝ) * x + u) := by fun_prop
  rw [map_measureReal_apply hf measurableSet_Iic]
  have hs : (fun u : ℝ => (j : ℝ) * x + u) ⁻¹' Iic H = Iic (H - (j : ℝ) * x) := by
    ext u
    simp only [mem_preimage, mem_Iic]
    constructor <;> intro hu <;> linarith
  rw [hs, MixtureSum.iidSumLaw_eq_convPower]

def weight (n j : ℕ) (ε : ℝ) : ℝ :=
  (n.choose j : ℝ) * ε ^ j * (1 - ε) ^ (n - j)

def componentCDF (μ : ProbabilityMeasure ℝ) (x H : ℝ) (n j : ℕ) : ℝ :=
  (MixtureSum.iidSumLaw (μ : Measure ℝ) (n - j)).real (Iic (H - (j : ℝ) * x))

/-- A polynomial on all real parameters, used to compute the right derivative. -/
def cdfPolynomial (μ : ProbabilityMeasure ℝ) (x H : ℝ) (n : ℕ) (ε : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1), weight n j ε * componentCDF μ x H n j

def actualCDF (μ : ProbabilityMeasure ℝ) (x H : ℝ) (n : ℕ) (ε : ℝ) : ℝ :=
  (MixtureSum.iidSumLaw (PerturbationMoment.mixtureMeasure μ x ε) n).real (Iic H)

/-- The finite polynomial is derived from the actual product-mixture law. -/
theorem actualCDF_eq_polynomial (μ : ProbabilityMeasure ℝ) (x H ε : ℝ) (n : ℕ)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) : actualCDF μ x H n ε = cdfPolynomial μ x H n ε := by
  have hm : PerturbationMoment.mixtureMeasure μ x ε =
      (NNReal.mk (1 - ε) (sub_nonneg.mpr hε1)) • (μ : Measure ℝ) +
        (NNReal.mk ε hε0) • Measure.dirac x := by
    rw [PerturbationMoment.mixtureMeasure,
      ENNReal.ofReal_eq_coe_nnreal (sub_nonneg.mpr hε1),
      ENNReal.ofReal_eq_coe_nnreal hε0]
    rfl
  unfold actualCDF
  rw [hm, MixtureSum.iidSumLaw_mixture_closedCDF]
  unfold cdfPolynomial
  apply Finset.sum_congr rfl
  intro j hj
  rw [component_closedCDF]
  rfl

def weightDerivative (n j : ℕ) : ℝ :=
  if j = 0 then -(n : ℝ) else if j = 1 then (n : ℝ) else 0

theorem hasDerivAt_weight (n j : ℕ) :
    HasDerivAt (weight n j) (weightDerivative n j) 0 := by
  have hd := (((hasDerivAt_id (0 : ℝ)).fun_pow j).const_mul (n.choose j : ℝ)).mul
    (((hasDerivAt_const (0 : ℝ) 1).sub (hasDerivAt_id 0)).fun_pow (n - j))
  convert hd using 1
  · funext ε
    rfl
  · by_cases hj0 : j = 0
    · subst j
      simp [weightDerivative]
    · by_cases hj1 : j = 1
      · subst j
        simp [weightDerivative, Nat.choose_one_right]
      · have hpred : j - 1 ≠ 0 := by omega
        simp [weightDerivative, hj0, hj1, zero_pow hj0, zero_pow hpred]

private theorem derivative_sum (C : ℕ → ℝ) (n : ℕ) (hn : 0 < n) :
    (∑ j ∈ Finset.range (n + 1), weightDerivative n j * C j) =
      (n : ℝ) * (C 1 - C 0) := by
  have hterm (j : ℕ) : weightDerivative n j * C j =
      (if j = 0 then -(n : ℝ) * C j else 0) +
        (if j = 1 then (n : ℝ) * C j else 0) := by
    by_cases h0 : j = 0
    · subst j; simp [weightDerivative]
    · by_cases h1 : j = 1
      · subst j; simp [weightDerivative]
      · simp [weightDerivative, h0, h1]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib]
  have h0 : 0 ∈ Finset.range (n + 1) := by simp
  have h1 : 1 ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
  simp only [Finset.sum_ite_eq', h0, h1, ite_true]
  ring

/-- Ordinary differentiation of the genuine finite polynomial extension. -/
theorem hasDerivAt_cdfPolynomial (μ : ProbabilityMeasure ℝ) (x H : ℝ)
    (n : ℕ) (hn : 0 < n) :
    HasDerivAt (cdfPolynomial μ x H n)
      ((n : ℝ) *
        ((MixtureSum.iidSumLaw (μ : Measure ℝ) (n - 1)).real (Iic (H - x)) -
          (MixtureSum.iidSumLaw (μ : Measure ℝ) n).real (Iic H))) 0 := by
  have hd := HasDerivAt.fun_sum (u := Finset.range (n + 1))
    (fun j _ => (hasDerivAt_weight n j).mul_const (componentCDF μ x H n j))
  convert hd using 1
  · funext ε
    rfl
  · simpa only [componentCDF, Nat.sub_zero, Nat.cast_zero, zero_mul, sub_zero,
      Nat.cast_one, one_mul] using (derivative_sum (componentCDF μ x H n) n hn).symm

private theorem eventually_valid_weight :
    ∀ᶠ ε in 𝓝[Set.Ici (0 : ℝ)] 0, ε ∈ Set.Icc (0 : ℝ) 1 := by
  have hlt0 : ∀ᶠ ε : ℝ in 𝓝 (0 : ℝ), ε < 1 :=
    Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)
  have hlt : ∀ᶠ ε : ℝ in 𝓝[Set.Ici (0 : ℝ)] 0, ε < 1 :=
    hlt0.filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hlt] with ε hε0 hε1
  exact ⟨hε0, le_of_lt hε1⟩

/-- The actual i.i.d. product perturbation has this right derivative for
every positive sample size and every closed threshold, without CDF regularity. -/
theorem actualCDF_hasDerivWithinAt (μ : ProbabilityMeasure ℝ) (x H : ℝ)
    (n : ℕ) (hn : 0 < n) :
    HasDerivWithinAt (actualCDF μ x H n)
      ((n : ℝ) *
        ((MixtureSum.iidSumLaw (μ : Measure ℝ) (n - 1)).real (Iic (H - x)) -
          (MixtureSum.iidSumLaw (μ : Measure ℝ) n).real (Iic H))) (Ici 0) 0 := by
  apply (hasDerivAt_cdfPolynomial μ x H n hn).hasDerivWithinAt.congr_of_eventuallyEq_of_mem
    ?_ (by simp)
  filter_upwards [eventually_valid_weight] with ε hε
  exact actualCDF_eq_polynomial μ x H ε n hε.1 hε.2

end BerryEsseen.PerturbationCDF

#print axioms BerryEsseen.PerturbationCDF.convPower_dirac
#print axioms BerryEsseen.PerturbationCDF.actualCDF_eq_polynomial
#print axioms BerryEsseen.PerturbationCDF.hasDerivAt_cdfPolynomial
#print axioms BerryEsseen.PerturbationCDF.actualCDF_hasDerivWithinAt
