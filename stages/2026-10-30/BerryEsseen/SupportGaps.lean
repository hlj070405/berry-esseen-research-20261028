module

public import BerryEsseen.ZeroBias
public import Mathlib.Topology.Order.Basic
public import Mathlib.Topology.Order.Compact

@[expose] public section

/-! 2026-10-28: the genuine countable gaps of an arbitrary compact real set.
No finiteness of the support or of its gap family is assumed. For measure
supports only the open gap is null; its endpoint atoms are retained. -/

noncomputable section

open MeasureTheory Set

namespace BerryEsseen.SupportGaps

def gapSet (S : Set ℝ) : Set (ℝ × ℝ) :=
  {g | g.1 ∈ S ∧ g.2 ∈ S ∧ g.1 < g.2 ∧ Disjoint (Ioo g.1 g.2) S}

/-- Two gaps which contain the same point must have both endpoints equal. -/
lemma gap_eq_of_overlap (S : Set ℝ) (g h : ℝ × ℝ) (t : ℝ)
    (hg : g ∈ gapSet S) (hh : h ∈ gapSet S)
    (htg : t ∈ Ioo g.1 g.2) (hth : t ∈ Ioo h.1 h.2) : g = h := by
  apply Prod.ext
  · apply le_antisymm
    · by_contra hn
      have hlt : h.1 < g.1 := lt_of_not_ge hn
      exact (Set.disjoint_left.mp hh.2.2.2) ⟨hlt, htg.1.trans hth.2⟩ hg.1
    · by_contra hn
      have hlt : g.1 < h.1 := lt_of_not_ge hn
      exact (Set.disjoint_left.mp hg.2.2.2) ⟨hlt, hth.1.trans htg.2⟩ hh.1
  · apply le_antisymm
    · by_contra hn
      have hlt : h.2 < g.2 := lt_of_not_ge hn
      exact (Set.disjoint_left.mp hg.2.2.2) ⟨htg.1.trans hth.2, hlt⟩ hh.2.1
    · by_contra hn
      have hlt : g.2 < h.2 := lt_of_not_ge hn
      exact (Set.disjoint_left.mp hh.2.2.2) ⟨hth.1.trans htg.2, hlt⟩ hg.2.1

theorem gapSet_pairwiseDisjoint (S : Set ℝ) :
    (gapSet S).PairwiseDisjoint (fun g => Ioo g.1 g.2) := by
  intro g hg h hh hne
  exact Set.disjoint_left.mpr fun t htg hth => hne (gap_eq_of_overlap S g h t hg hh htg hth)

/-- Countability follows from disjoint nonempty open intervals in the real line. -/
theorem gapSet_countable (S : Set ℝ) : (gapSet S).Countable :=
  (gapSet_pairwiseDisjoint S).countable_of_isOpen (fun _ _ => isOpen_Ioo)
    (fun _ hg => nonempty_Ioo.mpr hg.2.2.1)

/-- For a missing point in the compact hull, the actual nearest support
endpoints are the supremum below it and the infimum above it. -/
theorem exists_gap_of_mem_hull_diff (S : Set ℝ) (hS : IsCompact S) (hne : S.Nonempty)
    (t : ℝ) (ht : t ∈ Icc (sInf S) (sSup S) \ S) :
    ∃ g ∈ gapSet S, t ∈ Ioo g.1 g.2 := by
  have hmin : sInf S ∈ S := hS.isClosed.csInf_mem hne hS.bddBelow
  have hmax : sSup S ∈ S := hS.isClosed.csSup_mem hne hS.bddAbove
  let L : Set ℝ := S ∩ Iic t
  let R : Set ℝ := S ∩ Ici t
  have hLne : L.Nonempty := ⟨sInf S, hmin, ht.1.1⟩
  have hRne : R.Nonempty := ⟨sSup S, hmax, ht.1.2⟩
  have hLbdd : BddAbove L := ⟨t, fun _ hx => hx.2⟩
  have hRbdd : BddBelow R := ⟨t, fun _ hx => hx.2⟩
  have ha : sSup L ∈ L := (hS.isClosed.inter isClosed_Iic).csSup_mem hLne hLbdd
  have hb : sInf R ∈ R := (hS.isClosed.inter isClosed_Ici).csInf_mem hRne hRbdd
  have hat : sSup L < t := by
    by_contra hn
    have heq : sSup L = t := le_antisymm ha.2 (le_of_not_gt hn)
    exact ht.2 (heq ▸ ha.1)
  have htb : t < sInf R := by
    by_contra hn
    have heq : sInf R = t := le_antisymm (le_of_not_gt hn) hb.2
    exact ht.2 (heq ▸ hb.1)
  refine ⟨(sSup L, sInf R), ⟨ha.1, hb.1, hat.trans htb, ?_⟩, hat, htb⟩
  apply Set.disjoint_left.mpr
  intro x hx hxS
  rcases le_total x t with hxt | htx
  · have hxa : x ≤ sSup L := le_csSup hLbdd ⟨hxS, hxt⟩
    linarith [hx.1]
  · have hbx : sInf R ≤ x := csInf_le hRbdd ⟨hxS, htx⟩
    linarith [hx.2]

/-- The full compact-hull complement is the union of all its genuine gaps. -/
theorem hull_diff_eq_iUnion_gaps (S : Set ℝ) (hS : IsCompact S) (hne : S.Nonempty) :
    Icc (sInf S) (sSup S) \ S = ⋃ g ∈ gapSet S, Ioo g.1 g.2 := by
  ext t
  constructor
  · intro ht
    obtain ⟨g, hg, htg⟩ := exists_gap_of_mem_hull_diff S hS hne t ht
    exact Set.mem_iUnion.mpr ⟨g, Set.mem_iUnion.mpr ⟨hg, htg⟩⟩
  · intro ht
    obtain ⟨g, ht⟩ := Set.mem_iUnion.mp ht
    obtain ⟨hg, htg⟩ := Set.mem_iUnion.mp ht
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact (csInf_le hS.bddBelow hg.1).trans htg.1.le
    · exact htg.2.le.trans (le_csSup hS.bddAbove hg.2.1)
    · exact fun hxS => (Set.disjoint_left.mp hg.2.2.2) htg hxS

/-- Every open gap of the original measure's support has actual measure zero. -/
theorem measure_gap_eq_zero (μ : Measure ℝ) (g : ℝ × ℝ) (hg : g ∈ gapSet μ.support) :
    μ (Ioo g.1 g.2) = 0 :=
  measure_mono_null hg.2.2.2.subset_compl_right μ.measure_compl_support

theorem support_hull_diff_eq_iUnion_gaps (μ : ProbabilityMeasure ℝ)
    (hcompact : IsCompact (μ : Measure ℝ).support) :
    Icc (sInf (μ : Measure ℝ).support) (sSup (μ : Measure ℝ).support) \
        (μ : Measure ℝ).support =
      ⋃ g ∈ gapSet (μ : Measure ℝ).support, Ioo g.1 g.2 :=
  hull_diff_eq_iUnion_gaps _ hcompact
    ((μ : Measure ℝ).nonempty_support (IsProbabilityMeasure.ne_zero _))

/-- For the closed-tail convention the constant is the right-endpoint value;
the interval is `(a,b]`, leaving the original atoms untouched. -/
theorem tau_constant_on_support_gap (μ : ProbabilityMeasure ℝ) (g : ℝ × ℝ)
    (hg : g ∈ gapSet (μ : Measure ℝ).support) :
    Set.EqOn (ZeroBias.tau μ) (fun _ => ZeroBias.tau μ g.2) (Ioc g.1 g.2) := by
  intro t ht
  exact ZeroBias.tau_constant_on_openGap μ g.1 g.2 t
    (measure_gap_eq_zero (μ : Measure ℝ) g hg) ht.1 ht.2

end BerryEsseen.SupportGaps

#print axioms BerryEsseen.SupportGaps.gapSet_pairwiseDisjoint
#print axioms BerryEsseen.SupportGaps.gapSet_countable
#print axioms BerryEsseen.SupportGaps.hull_diff_eq_iUnion_gaps
#print axioms BerryEsseen.SupportGaps.measure_gap_eq_zero
#print axioms BerryEsseen.SupportGaps.support_hull_diff_eq_iUnion_gaps
#print axioms BerryEsseen.SupportGaps.tau_constant_on_support_gap
