module

public import BerryEsseen.StaircaseIntegral
public import Mathlib.MeasureTheory.Group.Convolution
public import Mathlib.MeasureTheory.Measure.FiniteMeasure
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Data.Nat.Choose.Sum

@[expose] public section

namespace BerryEsseen.MixtureSum

open MeasureTheory
open scoped BigOperators NNReal ENNReal

noncomputable section

local instance : Mul (FiniteMeasure ℝ) :=
  ⟨fun μ ν => ⟨(μ : Measure ℝ) ∗ (ν : Measure ℝ), inferInstance⟩⟩

local instance : One (FiniteMeasure ℝ) := ⟨⟨Measure.dirac 0, inferInstance⟩⟩

private theorem coe_conv (μ ν : FiniteMeasure ℝ) :
    ((μ * ν : FiniteMeasure ℝ) : Measure ℝ) = (μ : Measure ℝ) ∗ (ν : Measure ℝ) := rfl

local instance : CommSemiring (FiniteMeasure ℝ) where
  __ := FiniteMeasure.instAddCommMonoid
  mul_assoc μ ν ρ := FiniteMeasure.toMeasure_injective (Measure.conv_assoc _ _ _)
  one_mul μ := FiniteMeasure.toMeasure_injective (Measure.dirac_zero_conv _)
  mul_one μ := FiniteMeasure.toMeasure_injective (Measure.conv_dirac_zero _)
  left_distrib μ ν ρ := FiniteMeasure.toMeasure_injective (Measure.conv_add _ _ _)
  right_distrib μ ν ρ := FiniteMeasure.toMeasure_injective (Measure.add_conv _ _ _)
  zero_mul μ := FiniteMeasure.toMeasure_injective (Measure.zero_conv _)
  mul_zero μ := FiniteMeasure.toMeasure_injective (Measure.conv_zero _)
  mul_comm μ ν := FiniteMeasure.toMeasure_injective (Measure.conv_comm _ _)

/-- Repeated additive convolution, including the empty sum law. -/
def convPower (μ : Measure ℝ) : ℕ → Measure ℝ
  | 0 => Measure.dirac 0
  | n + 1 => μ ∗ convPower μ n

instance convPower_isFinite (μ : Measure ℝ) [IsFiniteMeasure μ] (n : ℕ) :
    IsFiniteMeasure (convPower μ n) := by
  induction n with
  | zero => dsimp [convPower]; infer_instance
  | succ n ih => dsimp [convPower]; infer_instance

private theorem coe_pow (μ : FiniteMeasure ℝ) (n : ℕ) :
    ((μ ^ n : FiniteMeasure ℝ) : Measure ℝ) = convPower μ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', coe_conv, ih]; rfl

private theorem smul_mul (a b : ℝ≥0) (μ ν : FiniteMeasure ℝ) :
    (a • μ) * (b • ν) = (a * b) • (μ * ν) := by
  apply FiniteMeasure.toMeasure_injective
  change ((a : ℝ≥0∞) • (μ : Measure ℝ)) ∗ ((b : ℝ≥0∞) • (ν : Measure ℝ)) =
    ((a * b : ℝ≥0) : ℝ≥0∞) • ((μ : Measure ℝ) ∗ (ν : Measure ℝ))
  rw [Measure.conv_smul_left, Measure.conv_smul_right, smul_smul, ENNReal.coe_mul]

private theorem smul_pow (a : ℝ≥0) (μ : FiniteMeasure ℝ) (n : ℕ) :
    (a • μ) ^ n = a ^ n • μ ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', ih, smul_mul]; simp only [pow_succ']

/-- Binomial expansion of arbitrary finite component laws. -/
theorem convPower_mixture (ν0 ν1 : Measure ℝ) [IsFiniteMeasure ν0] [IsFiniteMeasure ν1]
    (q p : ℝ≥0) (n : ℕ) :
    convPower (q • ν0 + p • ν1) n =
      ∑ j ∈ Finset.range (n + 1),
        ((n.choose j : ℝ≥0) * p ^ j * q ^ (n - j)) •
          (convPower ν1 j ∗ convPower ν0 (n - j)) := by
  let a : FiniteMeasure ℝ := ⟨ν1, inferInstance⟩
  let b : FiniteMeasure ℝ := ⟨ν0, inferInstance⟩
  have hterm (j : ℕ) :
      (p • a) ^ j * (q • b) ^ (n - j) * (n.choose j : FiniteMeasure ℝ) =
        ((n.choose j : ℝ≥0) * p ^ j * q ^ (n - j)) • (a ^ j * b ^ (n - j)) := by
    rw [← nsmul_eq_mul', ← Nat.cast_smul_eq_nsmul ℝ≥0,
      smul_pow, smul_pow, smul_mul, smul_smul]
    congr 1
    ring
  calc
    convPower (q • ν0 + p • ν1) n =
        (((p • a + q • b) ^ n : FiniteMeasure ℝ) : Measure ℝ) := by
      rw [coe_pow]
      congr 1
      change q • ν0 + p • ν1 = p • ν1 + q • ν0
      exact add_comm _ _
    _ = ((∑ j ∈ Finset.range (n + 1),
        ((n.choose j : ℝ≥0) * p ^ j * q ^ (n - j)) • (a ^ j * b ^ (n - j)) :
          FiniteMeasure ℝ) : Measure ℝ) := by
      congr 1
      simpa only [hterm] using add_pow (p • a) (q • b) n
    _ = _ := by
      rw [FiniteMeasure.toMeasure_sum]
      apply Finset.sum_congr rfl
      intro j hj
      change ((n.choose j : ℝ≥0) * p ^ j * q ^ (n - j)) •
        ((a ^ j * b ^ (n - j) : FiniteMeasure ℝ) : Measure ℝ) = _
      rw [coe_conv, coe_pow, coe_pow]
      rfl

/-- The sum of the actual independent coordinates under their product law. -/
def iidSumLaw (μ : Measure ℝ) (n : ℕ) : Measure ℝ :=
  (Measure.pi fun _ : Fin n => μ).map (fun x => ∑ i, x i)

theorem iidSumLaw_eq_convPower (μ : Measure ℝ) [IsFiniteMeasure μ] (n : ℕ) :
    iidSumLaw μ n = convPower μ n := by
  induction n with
  | zero =>
    simp [iidSumLaw, convPower]
  | succ n ih =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
    let f : ℝ × (Fin n → ℝ) → ℝ := fun z => z.1 + ∑ i, z.2 i
    have hf : Measurable f := by dsimp [f]; fun_prop
    have hsplit : (fun x : Fin (n + 1) → ℝ => ∑ i, x i) = f ∘ e := by
      funext x
      simp [f, e, MeasurableEquiv.piFinSuccAbove_apply, Fin.sum_univ_succ, Fin.tail]
    have hprod := (measurePreserving_piFinSuccAbove
      (fun _ : Fin (n + 1) => μ) 0).map_eq
    change (Measure.pi fun _ : Fin (n + 1) => μ).map _ = _
    rw [hsplit, ← Measure.map_map hf e.measurable, hprod]
    change (μ.prod (Measure.pi fun _ : Fin n => μ)).map f = _
    rw [convPower, ← ih]
    unfold iidSumLaw Measure.conv
    have hm : Measurable (fun x : Fin n → ℝ => ∑ i, x i) := by fun_prop
    have hp := Measure.map_prod_map μ (Measure.pi fun _ : Fin n => μ) measurable_id hm
    rw [Measure.map_id] at hp
    rw [hp, Measure.map_map measurable_add (measurable_id.prodMap hm)]
    rfl

/-- The independent sum of a two-component mixture is its binomial
mixture of convolution laws. The components can have arbitrary support. -/
theorem iidSumLaw_mixture (ν0 ν1 : Measure ℝ) [IsFiniteMeasure ν0] [IsFiniteMeasure ν1]
    (q p : ℝ≥0) (n : ℕ) :
    iidSumLaw (q • ν0 + p • ν1) n =
      ∑ j ∈ Finset.range (n + 1),
        ((n.choose j : ℝ≥0) * p ^ j * q ^ (n - j)) •
          (convPower ν1 j ∗ convPower ν0 (n - j)) := by
  rw [iidSumLaw_eq_convPower, convPower_mixture]

/-- Real closed-CDF form, retaining all atoms at the threshold. -/
theorem iidSumLaw_mixture_closedCDF (ν0 ν1 : Measure ℝ)
    [IsFiniteMeasure ν0] [IsFiniteMeasure ν1] (q p : ℝ≥0) (n : ℕ) (x : ℝ) :
    (iidSumLaw (q • ν0 + p • ν1) n).real (Set.Iic x) =
      ∑ j ∈ Finset.range (n + 1),
        ((n.choose j : ℝ) * (p : ℝ) ^ j * (q : ℝ) ^ (n - j)) *
          (convPower ν1 j ∗ convPower ν0 (n - j)).real (Set.Iic x) := by
  rw [iidSumLaw_mixture]
  simp only [Measure.real, Measure.finsetSum_apply]
  rw [ENNReal.toReal_sum (by intro j hj; finiteness)]
  apply Finset.sum_congr rfl
  intro j hj
  simp [Measure.smul_apply, ENNReal.toReal_mul]

/-- Translation commutes with convolution, with offsets adding. -/
theorem conv_translate (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (a b : ℝ) :
    μ.map (a + ·) ∗ ν.map (b + ·) = (μ ∗ ν).map (a + b + ·) := by
  have ha : Measurable (fun y : ℝ => a + y) := by fun_prop
  have hb : Measurable (fun y : ℝ => b + y) := by fun_prop
  have hab : Measurable (fun y : ℝ => a + b + y) := by fun_prop
  unfold Measure.conv
  rw [Measure.map_prod_map _ _ ha hb,
    Measure.map_map measurable_add (ha.prodMap hb),
    Measure.map_map hab measurable_add]
  congr 1
  funext z
  dsimp
  ring

theorem convPower_translate (μ : Measure ℝ) [IsFiniteMeasure μ] (a : ℝ) (n : ℕ) :
    convPower (μ.map (a + ·)) n = (convPower μ n).map ((n : ℝ) * a + ·) := by
  induction n with
  | zero => simp [convPower]
  | succ n ih =>
    rw [convPower, ih, conv_translate]
    congr 1
    funext z
    push_cast
    ring

/-- For `B + U`, count `j` produces the unshifted residual convolution
translated by exactly `j`. This is a measure equality. -/
theorem iidSumLaw_residualMixture (ν0 ν1 : Measure ℝ)
    [IsFiniteMeasure ν0] [IsFiniteMeasure ν1] (q p : ℝ≥0) (n : ℕ) :
    iidSumLaw (q • ν0 + p • ν1.map (1 + ·)) n =
      ∑ j ∈ Finset.range (n + 1),
        ((n.choose j : ℝ≥0) * p ^ j * q ^ (n - j)) •
          (convPower ν1 j ∗ convPower ν0 (n - j)).map ((j : ℝ) + ·) := by
  rw [iidSumLaw_mixture]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  rw [convPower_translate]
  simpa [mul_one, add_zero, zero_add] using
    conv_translate (convPower ν1 j) (convPower ν0 (n - j)) (j : ℝ) 0

/-- The residual-mixture identity at every closed threshold, including
thresholds carrying atoms of either component. -/
theorem iidSumLaw_residualMixture_closedCDF (ν0 ν1 : Measure ℝ)
    [IsFiniteMeasure ν0] [IsFiniteMeasure ν1] (q p : ℝ≥0) (n : ℕ) (x : ℝ) :
    (iidSumLaw (q • ν0 + p • ν1.map (1 + ·)) n).real (Set.Iic x) =
      ∑ j ∈ Finset.range (n + 1),
        ((n.choose j : ℝ) * (p : ℝ) ^ j * (q : ℝ) ^ (n - j)) *
          (convPower ν1 j ∗ convPower ν0 (n - j)).real {u | (j : ℝ) + u ≤ x} := by
  rw [iidSumLaw_residualMixture]
  simp only [Measure.real, Measure.finsetSum_apply]
  rw [ENNReal.toReal_sum (by intro j hj; finiteness)]
  apply Finset.sum_congr rfl
  intro j hj
  have hm : Measurable (fun u : ℝ => (j : ℝ) + u) := by fun_prop
  rw [Measure.coe_nnreal_smul_apply, Measure.map_apply hm measurableSet_Iic]
  change (((((n.choose j : ℝ≥0) * p ^ j * q ^ (n - j)) : ℝ≥0∞) *
    ((convPower ν1 j ∗ convPower ν0 (n - j)) {u | (j : ℝ) + u ≤ x})).toReal) = _
  simp

/-- Interface to the existing staircase CDF on a common probability
space. Only the individual residual-law identification is a hypothesis;
the independent mixture expansion is the proved theorem above. -/
theorem iidSumLaw_eq_staircaseCDF {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν0 ν1 : Measure ℝ)
    [IsFiniteMeasure ν0] [IsFiniteMeasure ν1] (q p : ℝ≥0)
    (W : ℕ → Ω → ℝ) (n : ℕ) (x : ℝ)
    (hWm : ∀ j : ℕ, j ≤ n → Measurable (W j))
    (hWlaw : ∀ j : ℕ, j ≤ n →
      μ.map (W j) = convPower ν1 j ∗ convPower ν0 (n - j)) :
    (iidSumLaw (q • ν0 + p • ν1.map (1 + ·)) n).real (Set.Iic x) =
      Staircase.closedMixtureCDF μ
        (fun j => (n.choose j : ℝ) * (p : ℝ) ^ j * (q : ℝ) ^ (n - j)) W n x := by
  rw [iidSumLaw_residualMixture_closedCDF]
  unfold Staircase.closedMixtureCDF
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  congr 1
  rw [← hWlaw j hjn]
  have hs : MeasurableSet {u : ℝ | (j : ℝ) + u ≤ x} := by
    exact measurableSet_le (measurable_const.add measurable_id) measurable_const
  rw [map_measureReal_apply (hWm j hjn) hs]
  rfl

end
end BerryEsseen.MixtureSum

#print axioms BerryEsseen.MixtureSum.iidSumLaw_eq_convPower
#print axioms BerryEsseen.MixtureSum.iidSumLaw_mixture
#print axioms BerryEsseen.MixtureSum.iidSumLaw_mixture_closedCDF
#print axioms BerryEsseen.MixtureSum.iidSumLaw_residualMixture
#print axioms BerryEsseen.MixtureSum.iidSumLaw_residualMixture_closedCDF
#print axioms BerryEsseen.MixtureSum.iidSumLaw_eq_staircaseCDF
