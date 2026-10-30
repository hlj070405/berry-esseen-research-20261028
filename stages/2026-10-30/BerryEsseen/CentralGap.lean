module

public import BerryEsseen.CanonicalSign
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.Topology.Order.Monotone

@[expose] public section

/-!
The maximal central support gap of the original law, and its actual
canonical residual bounds. Strict gap positivity is conditional on
`0 ∉ support μ`; it is not asserted for an arbitrary standardized law.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace BerryEsseen.CentralGap

def nonnegativeSupport (μ : ProbabilityMeasure ℝ) : Set ℝ :=
  (μ : Measure ℝ).support ∩ Ici 0

def nonpositiveSupport (μ : ProbabilityMeasure ℝ) : Set ℝ :=
  (μ : Measure ℝ).support ∩ Iic 0

/-- The actual left endpoint of the nonnegative part of the original support. -/
def Aplus (μ : ProbabilityMeasure ℝ) : ℝ := sInf (nonnegativeSupport μ)

/-- The magnitude of the actual right endpoint of the nonpositive support. -/
def Aminus (μ : ProbabilityMeasure ℝ) : ℝ := -sSup (nonpositiveSupport μ)

lemma nonnegativeSupport_nonempty (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    (nonnegativeSupport μ).Nonempty := by
  obtain ⟨x, hxpos, hxsp⟩ := (μ : Measure ℝ).nonempty_inter_support_of_pos
    (bot_lt_iff_ne_bot.mpr (SignSplit.positive_mass_ne_zero μ h))
  exact ⟨x, hxsp, le_of_lt hxpos⟩

lemma nonpositiveSupport_nonempty (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    (nonpositiveSupport μ).Nonempty := by
  obtain ⟨x, hxneg, hxsp⟩ := (μ : Measure ℝ).nonempty_inter_support_of_pos
    (bot_lt_iff_ne_bot.mpr (SignSplit.negative_mass_ne_zero μ h))
  exact ⟨x, hxsp, le_of_lt hxneg⟩

lemma nonnegativeSupport_bddBelow (μ : ProbabilityMeasure ℝ) :
    BddBelow (nonnegativeSupport μ) := ⟨0, fun _ hx => hx.2⟩

lemma nonpositiveSupport_bddAbove (μ : ProbabilityMeasure ℝ) :
    BddAbove (nonpositiveSupport μ) := ⟨0, fun _ hx => hx.2⟩

theorem Aplus_mem (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    Aplus μ ∈ nonnegativeSupport μ := by
  exact ((μ : Measure ℝ).isClosed_support.inter isClosed_Ici).csInf_mem
    (nonnegativeSupport_nonempty μ h) (nonnegativeSupport_bddBelow μ)

theorem neg_Aminus_mem (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    -Aminus μ ∈ nonpositiveSupport μ := by
  have hm := ((μ : Measure ℝ).isClosed_support.inter isClosed_Iic).csSup_mem
    (nonpositiveSupport_nonempty μ h) (nonpositiveSupport_bddAbove μ)
  simpa only [Aminus, nonpositiveSupport, neg_neg] using hm

lemma Aplus_nonneg (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) : 0 ≤ Aplus μ :=
  (Aplus_mem μ h).2

lemma Aminus_nonneg (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) : 0 ≤ Aminus μ := by
  have hm := (neg_Aminus_mem μ h).2
  change -Aminus μ ≤ 0 at hm
  linarith

theorem Aplus_pos (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hzero : (0 : ℝ) ∉ (μ : Measure ℝ).support) : 0 < Aplus μ := by
  by_contra hn
  have hz : Aplus μ = 0 := le_antisymm (le_of_not_gt hn) (Aplus_nonneg μ h)
  have hm := (Aplus_mem μ h).1
  rw [hz] at hm
  exact hzero hm

theorem Aminus_pos (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hzero : (0 : ℝ) ∉ (μ : Measure ℝ).support) : 0 < Aminus μ := by
  by_contra hn
  have hz : Aminus μ = 0 := le_antisymm (le_of_not_gt hn) (Aminus_nonneg μ h)
  have hm := (neg_Aminus_mem μ h).1
  rw [hz, neg_zero] at hm
  exact hzero hm

theorem support_nonpositive_le (μ : ProbabilityMeasure ℝ) (x : ℝ)
    (hx : x ∈ (μ : Measure ℝ).support) (hneg : x ≤ 0) : x ≤ -Aminus μ := by
  have hm : x ≤ sSup (nonpositiveSupport μ) :=
    le_csSup (nonpositiveSupport_bddAbove μ) ⟨hx, hneg⟩
  simpa only [Aminus, neg_neg] using hm

theorem Aplus_le_support_nonnegative (μ : ProbabilityMeasure ℝ) (x : ℝ)
    (hx : x ∈ (μ : Measure ℝ).support) (hpos : 0 ≤ x) : Aplus μ ≤ x :=
  csInf_le (nonnegativeSupport_bddBelow μ) ⟨hx, hpos⟩

theorem support_disjoint_openGap (μ : ProbabilityMeasure ℝ) :
    Disjoint (μ : Measure ℝ).support (Ioo (-Aminus μ) (Aplus μ)) := by
  apply Set.disjoint_left.mpr
  intro x hx hgap
  rcases le_total x 0 with hn | hp
  · have hb := support_nonpositive_le μ x hx hn
    linarith [hgap.1]
  · have hb := Aplus_le_support_nonnegative μ x hx hp
    linarith [hgap.2]

/-- Excluding zero from the actual support excludes only its actual atom;
no atomlessness hypothesis is imposed on any other point. -/
theorem zero_atom_mass (μ : ProbabilityMeasure ℝ)
    (hzero : (0 : ℝ) ∉ (μ : Measure ℝ).support) : (μ : Measure ℝ) {0} = 0 := by
  apply measure_mono_null (t := (μ : Measure ℝ).supportᶜ) _ (μ : Measure ℝ).measure_compl_support
  intro x hx
  have hx0 : x = 0 := Set.mem_singleton_iff.mp hx
  simpa only [hx0, mem_compl_iff] using hzero

lemma nonpositiveLaw_support_ae (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    ∀ᵐ x ∂(SignSplit.nonpositiveLaw μ h : Measure ℝ), x ∈ (μ : Measure ℝ).support := by
  have hac : (SignSplit.nonpositiveLaw μ h : Measure ℝ) ≪ (μ : Measure ℝ) :=
    cond_absolutelyContinuous
  exact hac.ae_le (μ : Measure ℝ).support_mem_ae

lemma positiveLaw_support_ae (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    ∀ᵐ x ∂(SignSplit.positiveLaw μ h : Measure ℝ), x ∈ (μ : Measure ℝ).support := by
  have hac : (SignSplit.positiveLaw μ h : Measure ℝ) ≪ (μ : Measure ℝ) :=
    cond_absolutelyContinuous
  exact hac.ae_le (μ : Measure ℝ).support_mem_ae

lemma nonpositiveLaw_le_gap (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    ∀ᵐ x ∂(SignSplit.nonpositiveLaw μ h : Measure ℝ), x ≤ -Aminus μ := by
  filter_upwards [nonpositiveLaw_support_ae μ h, CanonicalSign.nonpositive_ae μ h] with x hx hn
  exact support_nonpositive_le μ x hx hn

lemma positiveLaw_ge_gap (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    ∀ᵐ x ∂(SignSplit.positiveLaw μ h : Measure ℝ), Aplus μ ≤ x := by
  filter_upwards [positiveLaw_support_ae μ h, CanonicalSign.positive_ae μ h] with x hx hp
  exact Aplus_le_support_nonnegative μ x hx hp.le

def a0 (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) : ℝ :=
  CanonicalSign.p μ - CanonicalSign.scale μ h * Aminus μ

def a1 (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) : ℝ :=
  CanonicalSign.q μ - CanonicalSign.scale μ h * Aplus μ

theorem residual0_upper (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    ∀ᵐ u ∂(CanonicalSign.residual0 μ h : Measure ℝ), u ≤ a0 μ h := by
  have hf : Measurable (fun x : ℝ => CanonicalSign.scale μ h * x + CanonicalSign.p μ) := by fun_prop
  change ∀ᵐ u ∂(SignSplit.nonpositiveLaw μ h : Measure ℝ).map
    (fun x : ℝ => CanonicalSign.scale μ h * x + CanonicalSign.p μ), u ≤ a0 μ h
  apply (ae_map_iff hf.aemeasurable measurableSet_Iic).mpr
  filter_upwards [nonpositiveLaw_le_gap μ h] with x hx
  have hm := mul_le_mul_of_nonneg_left hx (CanonicalSign.scale_pos μ h).le
  change CanonicalSign.scale μ h * x + CanonicalSign.p μ ≤
    CanonicalSign.p μ - CanonicalSign.scale μ h * Aminus μ
  nlinarith

theorem residual1_lower (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    ∀ᵐ u ∂(CanonicalSign.residual1 μ h : Measure ℝ), -a1 μ h ≤ u := by
  have hf : Measurable (fun x : ℝ => CanonicalSign.scale μ h * x + -(CanonicalSign.q μ)) := by fun_prop
  change ∀ᵐ u ∂(SignSplit.positiveLaw μ h : Measure ℝ).map
    (fun x : ℝ => CanonicalSign.scale μ h * x + -(CanonicalSign.q μ)), -a1 μ h ≤ u
  apply (ae_map_iff hf.aemeasurable measurableSet_Ici).mpr
  filter_upwards [positiveLaw_ge_gap μ h] with x hx
  have hm := mul_le_mul_of_nonneg_left hx (CanonicalSign.scale_pos μ h).le
  change -(CanonicalSign.q μ - CanonicalSign.scale μ h * Aplus μ) ≤
    CanonicalSign.scale μ h * x + -(CanonicalSign.q μ)
  nlinarith

theorem a0_nonneg (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) : 0 ≤ a0 μ h := by
  have hc := CanonicalSign.residual0_centered μ h
  have hi := integral_mono_ae hc.integrable_first (integrable_const (a0 μ h)) (residual0_upper μ h)
  rw [hc.mean_zero, integral_const, probReal_univ, one_smul] at hi
  exact hi

theorem a1_nonneg (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) : 0 ≤ a1 μ h := by
  have hc := CanonicalSign.residual1_centered μ h
  have hi := integral_mono_ae (integrable_const (-a1 μ h)) hc.integrable_first (residual1_lower μ h)
  rw [hc.mean_zero, integral_const, probReal_univ, one_smul] at hi
  linarith

theorem caps_sum (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    a0 μ h + a1 μ h = 1 - CanonicalSign.scale μ h * (Aminus μ + Aplus μ) := by
  unfold a0 a1 CanonicalSign.q
  ring

/-- The strict staircase gap is derived from the original law's actual
maximal central support gap, under its explicit support exclusion. -/
theorem caps_sum_lt_one (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hzero : (0 : ℝ) ∉ (μ : Measure ℝ).support) : a0 μ h + a1 μ h < 1 := by
  rw [caps_sum]
  have hp := mul_pos (CanonicalSign.scale_pos μ h)
    (add_pos (Aminus_pos μ h hzero) (Aplus_pos μ h hzero))
  linarith

lemma positive_cap_of_centered_strict_upper (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ)
    (hi : Integrable f (ν : Measure ℝ)) (hm : (∫ x, f x ∂(ν : Measure ℝ)) = 0)
    (A : ℝ) (hstrict : ∀ᵐ x ∂(ν : Measure ℝ), f x < A) : 0 < A := by
  have hle := integral_mono_ae hi (integrable_const A) (hstrict.mono fun _ hx => hx.le)
  rw [hm, integral_const, probReal_univ, one_smul] at hle
  by_contra hn
  have hA : A = 0 := le_antisymm (le_of_not_gt hn) hle
  have hneg : 0 ≤ᵐ[(ν : Measure ℝ)] (fun x => -f x) := by
    filter_upwards [hstrict] with x hx
    change 0 ≤ -f x
    rw [hA] at hx
    linarith
  have hmean : (∫ x, -f x ∂(ν : Measure ℝ)) = 0 := by rw [integral_neg, hm, neg_zero]
  have hzero := (integral_eq_zero_iff_of_nonneg_ae hneg hi.neg).mp hmean
  obtain ⟨x, hx, hz⟩ := (hstrict.and hzero).exists
  rw [hA] at hx
  change -f x = 0 at hz
  linarith

def O0 (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (Rminus : ℝ) : ℝ :=
  CanonicalSign.scale μ h * Rminus - CanonicalSign.p μ

def O1 (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (Rplus : ℝ) : ℝ :=
  CanonicalSign.scale μ h * Rplus - CanonicalSign.q μ

theorem residual0_lower_strict (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (Rminus : ℝ) (hbound : ∀ x ∈ (μ : Measure ℝ).support, -Rminus < x) :
    ∀ᵐ u ∂(CanonicalSign.residual0 μ h : Measure ℝ), -O0 μ h Rminus < u := by
  have hf : Measurable (fun x : ℝ => CanonicalSign.scale μ h * x + CanonicalSign.p μ) := by fun_prop
  change ∀ᵐ u ∂(SignSplit.nonpositiveLaw μ h : Measure ℝ).map
    (fun x : ℝ => CanonicalSign.scale μ h * x + CanonicalSign.p μ), -O0 μ h Rminus < u
  apply (ae_map_iff hf.aemeasurable measurableSet_Ioi).mpr
  filter_upwards [nonpositiveLaw_support_ae μ h] with x hx
  have hm := mul_lt_mul_of_pos_left (hbound x hx) (CanonicalSign.scale_pos μ h)
  change -(CanonicalSign.scale μ h * Rminus - CanonicalSign.p μ) <
    CanonicalSign.scale μ h * x + CanonicalSign.p μ
  nlinarith

theorem residual1_upper_strict (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (Rplus : ℝ) (hbound : ∀ x ∈ (μ : Measure ℝ).support, x < Rplus) :
    ∀ᵐ u ∂(CanonicalSign.residual1 μ h : Measure ℝ), u < O1 μ h Rplus := by
  have hf : Measurable (fun x : ℝ => CanonicalSign.scale μ h * x + -(CanonicalSign.q μ)) := by fun_prop
  change ∀ᵐ u ∂(SignSplit.positiveLaw μ h : Measure ℝ).map
    (fun x : ℝ => CanonicalSign.scale μ h * x + -(CanonicalSign.q μ)), u < O1 μ h Rplus
  apply (ae_map_iff hf.aemeasurable measurableSet_Iio).mpr
  filter_upwards [positiveLaw_support_ae μ h] with x hx
  have hm := mul_lt_mul_of_pos_left (hbound x hx) (CanonicalSign.scale_pos μ h)
  change CanonicalSign.scale μ h * x + -(CanonicalSign.q μ) <
    CanonicalSign.scale μ h * Rplus - CanonicalSign.q μ
  nlinarith

theorem O0_pos (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (Rminus : ℝ) (hbound : ∀ x ∈ (μ : Measure ℝ).support, -Rminus < x) : 0 < O0 μ h Rminus := by
  have hc := CanonicalSign.residual0_centered μ h
  have hm : (∫ u : ℝ, -u ∂(CanonicalSign.residual0 μ h : Measure ℝ)) = 0 := by
    rw [integral_neg, hc.mean_zero, neg_zero]
  apply positive_cap_of_centered_strict_upper (CanonicalSign.residual0 μ h) (fun u => -u)
    hc.integrable_first.neg hm (O0 μ h Rminus)
  filter_upwards [residual0_lower_strict μ h Rminus hbound] with u hu
  linarith

theorem O1_pos (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (Rplus : ℝ) (hbound : ∀ x ∈ (μ : Measure ℝ).support, x < Rplus) : 0 < O1 μ h Rplus := by
  have hc := CanonicalSign.residual1_centered μ h
  exact positive_cap_of_centered_strict_upper (CanonicalSign.residual1 μ h) (fun u => u)
    hc.integrable_first hc.mean_zero (O1 μ h Rplus) (residual1_upper_strict μ h Rplus hbound)

/-- The manuscript's canonical support interface, derived from the same
original law, its maximal inner endpoints and its open outer support bounds. -/
theorem canonical_residual_support (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (hzero : (0 : ℝ) ∉ (μ : Measure ℝ).support) (Rminus Rplus : ℝ)
    (hbound : (μ : Measure ℝ).support ⊆ Ioo (-Rminus) Rplus) :
    0 < O0 μ h Rminus ∧ 0 < O1 μ h Rplus ∧ 0 ≤ a0 μ h ∧ 0 ≤ a1 μ h ∧
      a0 μ h + a1 μ h = 1 - CanonicalSign.scale μ h * (Aminus μ + Aplus μ) ∧
      a0 μ h + a1 μ h < 1 ∧
      (∀ᵐ u ∂(CanonicalSign.residual0 μ h : Measure ℝ), -O0 μ h Rminus ≤ u ∧ u ≤ a0 μ h) ∧
      (∀ᵐ u ∂(CanonicalSign.residual1 μ h : Measure ℝ), -a1 μ h ≤ u ∧ u ≤ O1 μ h Rplus) := by
  have hlower : ∀ x ∈ (μ : Measure ℝ).support, -Rminus < x := fun _ hx => (hbound hx).1
  have hupper : ∀ x ∈ (μ : Measure ℝ).support, x < Rplus := fun _ hx => (hbound hx).2
  refine ⟨O0_pos μ h Rminus hlower, O1_pos μ h Rplus hupper, a0_nonneg μ h, a1_nonneg μ h,
    caps_sum μ h, caps_sum_lt_one μ h hzero, ?_, ?_⟩
  · filter_upwards [residual0_lower_strict μ h Rminus hlower, residual0_upper μ h] with u hL hU
    exact ⟨hL.le, hU⟩
  · filter_upwards [residual1_lower μ h, residual1_upper_strict μ h Rplus hupper] with u hL hU
    exact ⟨hL, hU.le⟩

end BerryEsseen.CentralGap

#print axioms BerryEsseen.CentralGap.Aplus_mem
#print axioms BerryEsseen.CentralGap.neg_Aminus_mem
#print axioms BerryEsseen.CentralGap.zero_atom_mass
#print axioms BerryEsseen.CentralGap.residual0_upper
#print axioms BerryEsseen.CentralGap.residual1_lower
#print axioms BerryEsseen.CentralGap.caps_sum_lt_one
#print axioms BerryEsseen.CentralGap.O0_pos
#print axioms BerryEsseen.CentralGap.O1_pos
#print axioms BerryEsseen.CentralGap.canonical_residual_support
