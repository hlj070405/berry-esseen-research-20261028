module

public import BerryEsseen.MixtureSum
public import BerryEsseen.CoupledResidual

@[expose] public section

namespace BerryEsseen.CommonProduct

open MeasureTheory
open scoped BigOperators NNReal ENNReal

noncomputable section

/-- The same independent pairs are used for every count. -/
abbrev Space (n : ℕ) := Fin n → ℝ × ℝ

def pairProduct (ν0 ν1 : Measure ℝ) (n : ℕ) : Measure (Space n) :=
  Measure.pi fun _ : Fin n => ν0.prod ν1

instance pairProduct_isProbability (ν0 ν1 : Measure ℝ)
    [IsProbabilityMeasure ν0] [IsProbabilityMeasure ν1] (n : ℕ) :
    IsProbabilityMeasure (pairProduct ν0 ν1 n) := by
  unfold pairProduct
  infer_instance

def U0 (n i : ℕ) (ω : Space n) : ℝ :=
  if h : i < n then (ω ⟨i, h⟩).1 else 0

def U1 (n i : ℕ) (ω : Space n) : ℝ :=
  if h : i < n then (ω ⟨i, h⟩).2 else 0

def W (n j : ℕ) : Space n → ℝ :=
  CoupledResidual.randomValue (U0 n) (U1 n) n j

theorem measurable_U0 (n i : ℕ) : Measurable (U0 n i) := by
  unfold U0
  split_ifs with h
  · exact measurable_fst.comp (measurable_pi_apply (⟨i, h⟩ : Fin n))
  · exact measurable_const

theorem measurable_U1 (n i : ℕ) : Measurable (U1 n i) := by
  unfold U1
  split_ifs with h
  · exact measurable_snd.comp (measurable_pi_apply (⟨i, h⟩ : Fin n))
  · exact measurable_const

theorem measurable_W (n j : ℕ) (hj : j ≤ n) : Measurable (W n j) :=
  CoupledResidual.measurable_randomValue (U0 n) (U1 n) n j hj
    (fun i _ => measurable_U0 n i) (fun i _ => measurable_U1 n i)

private theorem value_eq_selected (u0 u1 : ℕ → ℝ) (n j : ℕ) (hj : j ≤ n) :
    CoupledResidual.value u0 u1 n j =
      ∑ i ∈ Finset.range n, if i < j then u1 i else u0 i := by
  rw [CoupledResidual.value_eq_split u0 u1 n j hj]
  have hs := Finset.sum_range_add (fun i => if i < j then u1 i else u0 i) j (n - j)
  rw [Nat.add_sub_of_le hj] at hs
  rw [hs]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    simp [Finset.mem_range.mp hi]
  · apply Finset.sum_congr rfl
    intro i hi
    simp

def chooseCoord {n : ℕ} (j : ℕ) (i : Fin n) (z : ℝ × ℝ) : ℝ :=
  if (i : ℕ) < j then z.2 else z.1

theorem measurable_chooseCoord {n : ℕ} (j : ℕ) (i : Fin n) :
    Measurable (chooseCoord j i) := by
  unfold chooseCoord
  split_ifs <;> fun_prop

theorem W_eq_sum_selected (n j : ℕ) (hj : j ≤ n) (ω : Space n) :
    W n j ω = ∑ i : Fin n, chooseCoord j i (ω i) := by
  change CoupledResidual.value (fun i => U0 n i ω) (fun i => U1 n i ω) n j = _
  rw [value_eq_selected _ _ n j hj]
  rw [← Fin.sum_univ_eq_sum_range
    (fun i => if i < j then U1 n i ω else U0 n i ω) n]
  apply Finset.sum_congr rfl
  intro i hi
  simp [chooseCoord, U0, U1, i.isLt]

def heterogeneousSumLaw {n : ℕ} (ν : Fin n → Measure ℝ) : Measure ℝ :=
  (Measure.pi ν).map (fun x => ∑ i, x i)

theorem heterogeneousSumLaw_succ {n : ℕ} (ν : Fin (n + 1) → Measure ℝ)
    [∀ i, IsFiniteMeasure (ν i)] :
    heterogeneousSumLaw ν = ν 0 ∗ heterogeneousSumLaw (fun i : Fin n => ν i.succ) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  let f : ℝ × (Fin n → ℝ) → ℝ := fun z => z.1 + ∑ i, z.2 i
  have hf : Measurable f := by dsimp [f]; fun_prop
  have hsplit : (fun x : Fin (n + 1) → ℝ => ∑ i, x i) = f ∘ e := by
    funext x
    simp [f, e, MeasurableEquiv.piFinSuccAbove_apply, Fin.sum_univ_succ, Fin.tail]
  have hprod := (measurePreserving_piFinSuccAbove ν 0).map_eq
  unfold heterogeneousSumLaw
  rw [hsplit, ← Measure.map_map hf e.measurable, hprod]
  change ((ν 0).prod (Measure.pi fun i : Fin n => ν i.succ)).map f = _
  unfold Measure.conv
  have hm : Measurable (fun x : Fin n → ℝ => ∑ i, x i) := by fun_prop
  have hp := Measure.map_prod_map (ν 0) (Measure.pi fun i : Fin n => ν i.succ)
    measurable_id hm
  rw [Measure.map_id] at hp
  rw [hp, Measure.map_map measurable_add (measurable_id.prodMap hm)]
  rfl

def component (ν0 ν1 : Measure ℝ) {n : ℕ} (j : ℕ) (i : Fin n) : Measure ℝ :=
  if (i : ℕ) < j then ν1 else ν0

instance component_isFinite (ν0 ν1 : Measure ℝ) [IsFiniteMeasure ν0] [IsFiniteMeasure ν1]
    {n : ℕ} (j : ℕ) (i : Fin n) : IsFiniteMeasure (component ν0 ν1 j i) := by
  unfold component
  split_ifs <;> infer_instance

theorem heterogeneousSumLaw_component (ν0 ν1 : Measure ℝ)
    [IsFiniteMeasure ν0] [IsFiniteMeasure ν1] (n j : ℕ) (hj : j ≤ n) :
    heterogeneousSumLaw (component ν0 ν1 (n := n) j) =
      MixtureSum.convPower ν1 j ∗ MixtureSum.convPower ν0 (n - j) := by
  induction n generalizing j with
  | zero =>
    have : j = 0 := Nat.eq_zero_of_le_zero hj
    subst j
    simp [heterogeneousSumLaw, MixtureSum.convPower]
  | succ n ih =>
    cases j with
    | zero =>
      have hz : component ν0 ν1 (n := n + 1) 0 = fun _ => ν0 := by
        funext i
        simp [component]
      rw [hz]
      simpa [heterogeneousSumLaw, MixtureSum.iidSumLaw,
        MixtureSum.convPower] using MixtureSum.iidSumLaw_eq_convPower ν0 (n + 1)
    | succ j =>
      rw [heterogeneousSumLaw_succ]
      have ht : (fun i : Fin n => component ν0 ν1 (j + 1) i.succ) =
          component ν0 ν1 j := by
        funext i
        simp [component]
      rw [ht, ih j (Nat.succ_le_succ_iff.mp hj)]
      simp [component, MixtureSum.convPower, Measure.conv_assoc]

theorem map_chooseCoord (ν0 ν1 : Measure ℝ)
    [IsProbabilityMeasure ν0] [IsProbabilityMeasure ν1] {n : ℕ} (j : ℕ) (i : Fin n) :
    (ν0.prod ν1).map (chooseCoord j i) = component ν0 ν1 j i := by
  unfold chooseCoord component
  split_ifs <;> simp

theorem map_selected (ν0 ν1 : Measure ℝ)
    [IsProbabilityMeasure ν0] [IsProbabilityMeasure ν1] (n j : ℕ) :
    (pairProduct ν0 ν1 n).map (fun ω i => chooseCoord j i (ω i)) =
      Measure.pi (component ν0 ν1 (n := n) j) := by
  unfold pairProduct
  have h := Measure.pi_map_pi (μ := fun _ : Fin n => ν0.prod ν1)
    (f := fun i => chooseCoord j i)
    (fun i => (measurable_chooseCoord j i).aemeasurable)
  simpa only [map_chooseCoord] using h

/-- The law of every residual count in the one common pair product.
No residual-law identification is assumed. -/
theorem map_W (ν0 ν1 : Measure ℝ)
    [IsProbabilityMeasure ν0] [IsProbabilityMeasure ν1] (n j : ℕ) (hj : j ≤ n) :
    (pairProduct ν0 ν1 n).map (W n j) =
      MixtureSum.convPower ν1 j ∗ MixtureSum.convPower ν0 (n - j) := by
  let select : Space n → Fin n → ℝ := fun ω i => chooseCoord j i (ω i)
  have hm : Measurable (fun x : Fin n → ℝ => ∑ i, x i) := by fun_prop
  have hs : Measurable select := by
    apply measurable_pi_iff.mpr
    intro i
    exact (measurable_chooseCoord j i).comp (measurable_pi_apply i)
  calc
    (pairProduct ν0 ν1 n).map (W n j) =
        ((pairProduct ν0 ν1 n).map select).map (fun x : Fin n → ℝ => ∑ i, x i) := by
      rw [Measure.map_map hm hs]
      congr 1
      funext ω
      exact W_eq_sum_selected n j hj ω
    _ = heterogeneousSumLaw (component ν0 ν1 (n := n) j) := by
      rw [show (pairProduct ν0 ν1 n).map select =
        Measure.pi (component ν0 ν1 (n := n) j) from map_selected ν0 ν1 n j]
      rfl
    _ = _ := heterogeneousSumLaw_component ν0 ν1 n j hj

/-- The actual i.i.d. mixture and the common residual staircase now
have the same closed CDF, with no `hWlaw` premise. -/
theorem iidSumLaw_eq_staircaseCDF (ν0 ν1 : Measure ℝ)
    [IsProbabilityMeasure ν0] [IsProbabilityMeasure ν1] (q p : ℝ≥0) (n : ℕ) (x : ℝ) :
    (MixtureSum.iidSumLaw (q • ν0 + p • ν1.map (1 + ·)) n).real (Set.Iic x) =
      Staircase.closedMixtureCDF (pairProduct ν0 ν1 n)
        (fun j => (n.choose j : ℝ) * (p : ℝ) ^ j * (q : ℝ) ^ (n - j)) (W n) n x :=
  MixtureSum.iidSumLaw_eq_staircaseCDF (pairProduct ν0 ν1 n) ν0 ν1 q p (W n) n x
    (fun j hj => measurable_W n j hj) (fun j hj => map_W ν0 ν1 n j hj)

end
end BerryEsseen.CommonProduct

#print axioms BerryEsseen.CommonProduct.W_eq_sum_selected
#print axioms BerryEsseen.CommonProduct.heterogeneousSumLaw_component
#print axioms BerryEsseen.CommonProduct.map_W
#print axioms BerryEsseen.CommonProduct.iidSumLaw_eq_staircaseCDF
