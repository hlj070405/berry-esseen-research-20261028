module

public import BerryEsseen.VarianceSmoothing
public import Mathlib.MeasureTheory.Group.Convolution
public import Mathlib.Data.List.Perm.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Basic

@[expose] public section

/-!
Finite variance equalization by an exact finite induction. The laws are
genuine additive convolutions, hence product/map independent-sum laws.
Each nontrivial step fixes one variance at the common target while
preserving a nonnegative remainder and the remaining variance total.
-/

namespace BerryEsseen.TwoMoment

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

instance referenceLaw_isFiniteMeasure (b z : ℝ) : IsFiniteMeasure (referenceLaw b z) := by
  constructor
  simp [referenceLaw]

/-- The independent sum law of a finite list of reference variances. -/
def referenceListSumLaw (b : ℝ) : List ℝ → Measure ℝ
  | [] => Measure.dirac 0
  | z :: zs => referenceLaw b z ∗ referenceListSumLaw b zs

instance referenceListSumLaw_isFiniteMeasure (b : ℝ) (zs : List ℝ) :
    IsFiniteMeasure (referenceListSumLaw b zs) := by
  induction zs with
  | nil => dsimp [referenceListSumLaw]; infer_instance
  | cons z zs ih =>
    have := ih
    dsimp [referenceListSumLaw]
    infer_instance

theorem referenceListSumLaw_isProbabilityMeasure (b : ℝ) (hb : 0 < b)
    (zs : List ℝ) (hz : ∀ z ∈ zs, 0 ≤ z) :
    IsProbabilityMeasure (referenceListSumLaw b zs) := by
  induction zs with
  | nil => dsimp [referenceListSumLaw]; infer_instance
  | cons z zs ih =>
    have := referenceLaw_isProbabilityMeasure b z hb (hz z (by simp))
    have := ih (fun w hw => hz w (by simp [hw]))
    dsimp [referenceListSumLaw]
    infer_instance

theorem referenceListSumLaw_perm (b : ℝ) {xs ys : List ℝ} (h : xs.Perm ys) :
    referenceListSumLaw b xs = referenceListSumLaw b ys := by
  induction h with
  | nil => rfl
  | cons z h ih => simp only [referenceListSumLaw, ih]
  | swap x y zs =>
    dsimp [referenceListSumLaw]
    rw [← Measure.conv_assoc, ← Measure.conv_assoc,
      Measure.conv_comm (referenceLaw b y) (referenceLaw b x)]
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

theorem referenceListSumLaw_append (b : ℝ) (xs ys : List ℝ) :
    referenceListSumLaw b (xs ++ ys) = referenceListSumLaw b xs ∗ referenceListSumLaw b ys := by
  induction xs with
  | nil => simp [referenceListSumLaw]
  | cons x xs ih =>
    simp only [List.cons_append, referenceListSumLaw, ih]
    exact (Measure.conv_assoc _ _ _).symm

theorem squarePositiveOrder_trans {μ ν ρ : Measure ℝ}
    (h₁ : SquarePositiveOrder μ ν) (h₂ : SquarePositiveOrder ν ρ) :
    SquarePositiveOrder μ ρ := fun c => (h₁ c).trans (h₂ c)

theorem squarePositiveOrder_conv (μ₁ μ₂ ν₁ ν₂ : Measure ℝ)
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂]
    (hμ : SquarePositiveOrder μ₁ μ₂) (hν : SquarePositiveOrder ν₁ ν₂) :
    SquarePositiveOrder (μ₁ ∗ ν₁) (μ₂ ∗ ν₂) :=
  squarePositiveOrder_add μ₁ μ₂ ν₁ ν₂ hμ hν

private lemma sum_le_length_mul (xs : List ℝ) (t : ℝ) (h : ∀ x ∈ xs, x ≤ t) :
    xs.sum ≤ (xs.length : ℝ) * t := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have hs := ih (fun y hy => h y (by simp [hy]))
    simp only [List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    nlinarith

private lemma length_mul_le_sum (xs : List ℝ) (t : ℝ) (h : ∀ x ∈ xs, t ≤ x) :
    (xs.length : ℝ) * t ≤ xs.sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have hs := ih (fun y hy => h y (by simp [hy]))
    simp only [List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    nlinarith

private lemma replicate_nonneg (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    ∀ x ∈ List.replicate n t, 0 ≤ x := by
  intro x hx
  have hx' := (List.mem_replicate.mp hx).2
  simpa only [hx'] using ht

private lemma reference_pair_straddles_target (b x y t : ℝ)
    (hb : 0 < b) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hcross : (x ≤ t ∧ t ≤ y) ∨ (y ≤ t ∧ t ≤ x)) :
    0 ≤ t ∧ 0 ≤ x + y - t ∧
      SquarePositiveOrder (referenceLaw b x ∗ referenceLaw b y)
        (referenceLaw b t ∗ referenceLaw b (x + y - t)) := by
  have ht : 0 ≤ t := by rcases hcross with h | h <;> linarith [h.1]
  have hrest : 0 ≤ x + y - t := by rcases hcross with h | h <;> linarith [h.2]
  have hp : x * y ≤ t * (x + y - t) := by
    rcases hcross with h | h
    · nlinarith [mul_nonneg (sub_nonneg.mpr h.1) (sub_nonneg.mpr h.2)]
    · nlinarith [mul_nonneg (sub_nonneg.mpr h.1) (sub_nonneg.mpr h.2)]
  exact ⟨ht, hrest, squarePositiveOrder_reference_pair_smoothed b x y t (x + y - t)
    hb hx hy ht hrest (by ring) hp⟩

/-- A finite induction at a fixed target mean. The number of unfixed
coordinates drops by one at every step; no limiting process is used. -/
theorem referenceListSumLaw_le_equalized_fixedMean (b t : ℝ) (hb : 0 < b) (ht : 0 ≤ t)
    (n : ℕ) (zs : List ℝ) (hlen : zs.length = n) (hz : ∀ z ∈ zs, 0 ≤ z)
    (hsum : zs.sum = (n : ℝ) * t) :
    SquarePositiveOrder (referenceListSumLaw b zs)
      (referenceListSumLaw b (List.replicate n t)) := by
  induction n generalizing zs with
  | zero =>
    have hnil : zs = [] := List.length_eq_zero_iff.mp hlen
    subst zs
    exact squarePositiveOrder_refl _
  | succ n ih =>
    cases zs with
    | nil => simp at hlen
    | cons x ys =>
      have hlenys : ys.length = n := Nat.succ.inj hlen
      have hx : 0 ≤ x := hz x (by simp)
      have hys : ∀ y ∈ ys, 0 ≤ y := fun y hy => hz y (by simp [hy])
      have hsum' : x + ys.sum = (n : ℝ) * t + t := by
        simpa only [List.sum_cons, Nat.cast_add, Nat.cast_one, add_mul, one_mul] using hsum
      have hprobRep : IsProbabilityMeasure (referenceListSumLaw b (List.replicate n t)) :=
        referenceListSumLaw_isProbabilityMeasure b hb _ (replicate_nonneg n t ht)
      have hprobT := referenceLaw_isProbabilityMeasure b t hb ht
      by_cases hxt : x = t
      · subst x
        have htail : ys.sum = (n : ℝ) * t := by linarith
        have horder := ih ys hlenys hys htail
        have := referenceListSumLaw_isProbabilityMeasure b hb ys hys
        simpa only [List.replicate_succ, referenceListSumLaw] using
          squarePositiveOrder_conv (referenceLaw b t) (referenceLaw b t)
            (referenceListSumLaw b ys) (referenceListSumLaw b (List.replicate n t))
            (squarePositiveOrder_refl _) horder
      have hex : ∃ y ∈ ys, (x ≤ t ∧ t ≤ y) ∨ (y ≤ t ∧ t ≤ x) := by
        rcases lt_or_gt_of_ne hxt with hlt | hgt
        · have hy : ∃ y ∈ ys, t < y := by
            by_contra hnone
            have hall : ∀ y ∈ ys, y ≤ t := by
              intro y hy
              exact le_of_not_gt (fun h => hnone ⟨y, hy, h⟩)
            have hs := sum_le_length_mul ys t hall
            rw [hlenys] at hs
            linarith
          rcases hy with ⟨y, hy, hty⟩
          exact ⟨y, hy, Or.inl ⟨hlt.le, hty.le⟩⟩
        · have hy : ∃ y ∈ ys, y < t := by
            by_contra hnone
            have hall : ∀ y ∈ ys, t ≤ y := by
              intro y hy
              exact le_of_not_gt (fun h => hnone ⟨y, hy, h⟩)
            have hs := length_mul_le_sum ys t hall
            rw [hlenys] at hs
            linarith
          rcases hy with ⟨y, hy, hyt⟩
          exact ⟨y, hy, Or.inr ⟨hyt.le, hgt.le⟩⟩
      rcases hex with ⟨y, hy, hcross⟩
      classical
      let rest := ys.erase y
      have hperm : ys.Perm (y :: rest) := List.perm_cons_erase hy
      have hlenRest : ((x + y - t) :: rest).length = n := by
        simpa only [List.length_cons, hlenys] using hperm.length_eq.symm
      have hrestNonneg : ∀ z ∈ rest, 0 ≤ z := by
        intro z hzrest
        exact hys z (List.mem_of_mem_erase hzrest)
      have hstep := reference_pair_straddles_target b x y t hb hx (hys y hy) hcross
      have hremaining : ∀ z ∈ (x + y - t) :: rest, 0 ≤ z := by
        intro z hzmem
        rcases List.mem_cons.mp hzmem with hzeq | hzrest
        · simpa only [hzeq] using hstep.2.1
        · exact hrestNonneg z hzrest
      have hsumRest : ((x + y - t) :: rest).sum = (n : ℝ) * t := by
        have hp := hperm.sum_eq
        simp only [List.sum_cons] at hp ⊢
        linarith
      have horderRest := ih ((x + y - t) :: rest) hlenRest hremaining hsumRest
      have := referenceLaw_isProbabilityMeasure b x hb hx
      have := referenceLaw_isProbabilityMeasure b y hb (hys y hy)
      have := referenceLaw_isProbabilityMeasure b (x + y - t) hb hstep.2.1
      have := referenceListSumLaw_isProbabilityMeasure b hb rest hrestNonneg
      have := referenceListSumLaw_isProbabilityMeasure b hb ((x + y - t) :: rest) hremaining
      have hstepRest := squarePositiveOrder_conv
        (referenceLaw b x ∗ referenceLaw b y)
        (referenceLaw b t ∗ referenceLaw b (x + y - t))
        (referenceListSumLaw b rest) (referenceListSumLaw b rest)
        hstep.2.2 (squarePositiveOrder_refl _)
      simp only [Measure.conv_assoc] at hstepRest
      have hfinish := squarePositiveOrder_conv (referenceLaw b t) (referenceLaw b t)
        (referenceListSumLaw b ((x + y - t) :: rest))
        (referenceListSumLaw b (List.replicate n t)) (squarePositiveOrder_refl _) horderRest
      have hcombined := squarePositiveOrder_trans hstepRest hfinish
      simpa only [referenceListSumLaw, referenceListSumLaw_perm b hperm,
        List.replicate_succ, Measure.conv_assoc] using hcombined

/-- Empty and singleton laws are the genuine empty sum and one-summand law. -/
theorem referenceListSumLaw_nil (b : ℝ) : referenceListSumLaw b [] = Measure.dirac 0 := rfl

theorem referenceListSumLaw_singleton (b z : ℝ) :
    referenceListSumLaw b [z] = referenceLaw b z := by
  simp [referenceListSumLaw]

/-- Exact-total-variance form. Division by the number of summands is only
used for a strictly positive number of coordinates. -/
theorem referenceListSumLaw_le_uniform_total (b V : ℝ) (n : ℕ) (zs : List ℝ)
    (hb : 0 < b) (hn : 0 < n) (hlen : zs.length = n)
    (hz : ∀ z ∈ zs, 0 ≤ z) (hV : zs.sum = V) :
    SquarePositiveOrder (referenceListSumLaw b zs)
      (referenceListSumLaw b (List.replicate n (V / (n : ℝ)))) := by
  have hV0 : 0 ≤ V := by
    have hs := length_mul_le_sum zs 0 hz
    simpa only [mul_zero, hV] using hs
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  apply referenceListSumLaw_le_equalized_fixedMean b (V / (n : ℝ)) hb
    (div_nonneg hV0 hnR.le) n zs hlen hz
  rw [hV]
  field_simp [hnR.ne']

/-- The convolution-list construction is the existing genuine recursive
product/map sum law, for arbitrary real reference parameters. -/
theorem referenceListSumLaw_range_eq_finiteIndependentSumLaw
    (b : ℝ) (z : ℕ → ℝ) (n : ℕ) :
    referenceListSumLaw b ((List.range n).map z) =
      finiteIndependentSumLaw (fun i => referenceLaw b (z i)) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.map_append]
    change referenceListSumLaw b (((List.range n).map z) ++ [z n]) = _
    rw [referenceListSumLaw_append, referenceListSumLaw_singleton,
      Measure.conv_comm (referenceListSumLaw b ((List.range n).map z)) (referenceLaw b (z n)), ih]
    rfl

theorem referenceListSumLaw_replicate_eq_finiteIndependentSumLaw
    (b t : ℝ) (n : ℕ) :
    referenceListSumLaw b (List.replicate n t) =
      finiteIndependentSumLaw (fun _ => referenceLaw b t) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [List.replicate_succ, referenceListSumLaw]
    rw [ih]
    rfl

private lemma sum_map_range_eq_sum_range (z : ℕ → ℝ) (n : ℕ) :
    ((List.range n).map z).sum = ∑ i ∈ Finset.range n, z i := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]

/-- Finite Bentkus variance equalization for the actual independent
reference sum: the supplied total is exactly the sum of its coordinate
variances, and the comparison holds at every real threshold. -/
theorem finiteIndependentSumLaw_reference_le_equalized
    (b V : ℝ) (z : ℕ → ℝ) (n : ℕ) (hb : 0 < b) (hn : 0 < n)
    (hz : ∀ i, i < n → 0 ≤ z i) (hV : (∑ i ∈ Finset.range n, z i) = V) :
    SquarePositiveOrder (finiteIndependentSumLaw (fun i => referenceLaw b (z i)) n)
      (finiteIndependentSumLaw (fun _ => referenceLaw b (V / (n : ℝ))) n) := by
  rw [← referenceListSumLaw_range_eq_finiteIndependentSumLaw b z n,
    ← referenceListSumLaw_replicate_eq_finiteIndependentSumLaw b (V / (n : ℝ)) n]
  apply referenceListSumLaw_le_uniform_total b V n ((List.range n).map z) hb hn (by simp)
  · intro w hw
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
    exact hz i (List.mem_range.mp hi)
  · rw [sum_map_range_eq_sum_range, hV]

theorem finiteIndependentSumLaw_reference_zero (b : ℝ) (z : ℕ → ℝ) :
    finiteIndependentSumLaw (fun i => referenceLaw b (z i)) 0 = Measure.dirac 0 := rfl

theorem finiteIndependentSumLaw_reference_one (b : ℝ) (z : ℕ → ℝ) :
    finiteIndependentSumLaw (fun i => referenceLaw b (z i)) 1 = referenceLaw b (z 0) := by
  rw [← referenceListSumLaw_range_eq_finiteIndependentSumLaw]
  simp [referenceListSumLaw]

theorem squarePositiveOrder_referenceLaw_variance_mono (b z₁ z₂ : ℝ)
    (hb : 0 < b) (hz₁ : 0 ≤ z₁) (hz : z₁ ≤ z₂) :
    SquarePositiveOrder (referenceLaw b z₁) (referenceLaw b z₂) := by
  intro c
  have hz₂ := hz₁.trans hz
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_referenceLaw b z₁ _)
      (Filter.Eventually.of_forall (fun x => sq_nonneg _)),
    ← ofReal_integral_eq_lintegral_ofReal (integrable_referenceLaw b z₂ _)
      (Filter.Eventually.of_forall (fun x => sq_nonneg _)),
    integral_referenceLaw_squarePositivePart b z₁ c hb hz₁,
    integral_referenceLaw_squarePositivePart b z₂ c hb hz₂]
  exact ENNReal.ofReal_le_ofReal (referencePrice_mono b b z₁ z₂ c hb le_rfl hz₁ hz)

/-- The budget form follows only after exact finite equalization: enlarge
each equal reference variance by the already-proved one-coordinate order. -/
theorem finiteIndependentSumLaw_reference_le_uniform_budget
    (b V : ℝ) (z : ℕ → ℝ) (n : ℕ) (hb : 0 < b) (hn : 0 < n)
    (hz : ∀ i, i < n → 0 ≤ z i) (hV : (∑ i ∈ Finset.range n, z i) ≤ V) :
    SquarePositiveOrder (finiteIndependentSumLaw (fun i => referenceLaw b (z i)) n)
      (finiteIndependentSumLaw (fun _ => referenceLaw b (V / (n : ℝ))) n) := by
  let S : ℝ := ∑ i ∈ Finset.range n, z i
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i hi => hz i (Finset.mem_range.mp hi))
  have hSV : S ≤ V := hV
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hsmall : 0 ≤ S / (n : ℝ) := div_nonneg hS hnR.le
  have hbig : 0 ≤ V / (n : ℝ) := div_nonneg (hS.trans hSV) hnR.le
  have hmean : S / (n : ℝ) ≤ V / (n : ℝ) := div_le_div_of_nonneg_right hSV hnR.le
  have hexact := finiteIndependentSumLaw_reference_le_equalized b S z n hb hn hz rfl
  have hincrease := @squarePositiveOrder_finiteIndependentSumLaw
    (fun _ => referenceLaw b (S / (n : ℝ))) (fun _ => referenceLaw b (V / (n : ℝ)))
    (fun _ => referenceLaw_isProbabilityMeasure b (S / (n : ℝ)) hb hsmall)
    (fun _ => referenceLaw_isProbabilityMeasure b (V / (n : ℝ)) hb hbig)
    (fun _ => squarePositiveOrder_referenceLaw_variance_mono b (S / (n : ℝ))
      (V / (n : ℝ)) hb hsmall hmean) n
  exact squarePositiveOrder_trans hexact hincrease

end

end BerryEsseen.TwoMoment

#print axioms BerryEsseen.TwoMoment.referenceListSumLaw_perm
#print axioms BerryEsseen.TwoMoment.referenceListSumLaw_le_equalized_fixedMean
#print axioms BerryEsseen.TwoMoment.finiteIndependentSumLaw_reference_le_equalized
#print axioms BerryEsseen.TwoMoment.finiteIndependentSumLaw_reference_le_uniform_budget
