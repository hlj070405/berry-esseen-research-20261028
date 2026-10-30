module

public import BerryEsseen.StopLossShape

@[expose] public section

/-! 2026-10-28: global supporting lines for the genuine inf-width price.
The canonical slopes below are the actual left and right derivatives,
`derivWithin` on the corresponding half-lines, rather than a two-sided
derivative at a possible kink. No width optimizer or C1 assumption is used. -/

noncomputable section

namespace BerryEsseen.StopLossSubgradient

open MeasureTheory Set

def Supports (f : ℝ → ℝ) (x u : ℝ) : Prop :=
  ∀ y : ℝ, f x + u * (y - x) ≤ f y

def leftSlope (f : ℝ → ℝ) (x : ℝ) : ℝ := derivWithin f (Iio x) x

def rightSlope (f : ℝ → ℝ) (x : ℝ) : ℝ := derivWithin f (Ioi x) x

theorem leftSlope_hasDerivWithinAt {f : ℝ → ℝ} (hc : ConvexOn ℝ univ f) (x : ℝ) :
    HasDerivWithinAt f (leftSlope f x) (Iio x) x :=
  hc.hasDerivWithinAt_leftDeriv_of_mem_interior (by simp)

theorem rightSlope_hasDerivWithinAt {f : ℝ → ℝ} (hc : ConvexOn ℝ univ f) (x : ℝ) :
    HasDerivWithinAt f (rightSlope f x) (Ioi x) x :=
  hc.hasDerivWithinAt_rightDeriv_of_mem_interior (by simp)

lemma support_le_secant {f : ℝ → ℝ} {x y u : ℝ}
    (hs : Supports f x u) (hxy : x < y) : u ≤ slope f x y := by
  rw [slope_def_field]
  apply (le_div_iff₀ (sub_pos.mpr hxy)).mpr
  have h := hs y
  linarith

lemma secant_le_support {f : ℝ → ℝ} {x y u : ℝ}
    (hs : Supports f y u) (hxy : x < y) : slope f x y ≤ u := by
  rw [slope_def_field]
  apply (div_le_iff₀ (sub_pos.mpr hxy)).mpr
  have h := hs x
  nlinarith only [h]

theorem supports_order {f : ℝ → ℝ} {x y u v : ℝ}
    (hu : Supports f x u) (hv : Supports f y v) (hxy : x < y) : u ≤ v :=
  (support_le_secant hu hxy).trans (secant_le_support hv hxy)

/-- The full interval between the genuine one-sided derivatives consists
of supporting slopes, including both endpoint derivatives. -/
theorem supports_of_oneSided_bounds {f : ℝ → ℝ}
    (hc : ConvexOn ℝ univ f) (x u : ℝ)
    (hl : leftSlope f x ≤ u) (hr : u ≤ rightSlope f x) : Supports f x u := by
  intro y
  rcases lt_trichotomy y x with hyx | rfl | hxy
  · have hsec := hc.slope_le_leftDeriv_of_mem_interior (mem_univ y)
      (by simp : x ∈ interior (univ : Set ℝ)) hyx
    have hu : slope f y x ≤ u := hsec.trans hl
    rw [slope_def_field] at hu
    have hm := (div_le_iff₀ (sub_pos.mpr hyx)).mp hu
    nlinarith only [hm]
  · simp
  · have hsec := hc.rightDeriv_le_slope_of_mem_interior
      (by simp : x ∈ interior (univ : Set ℝ)) (mem_univ y) hxy
    have hu : u ≤ slope f x y := hr.trans hsec
    rw [slope_def_field] at hu
    have hm := (le_div_iff₀ (sub_pos.mpr hxy)).mp hu
    linarith

theorem oneSided_bounds_of_supports {f : ℝ → ℝ}
    (hc : ConvexOn ℝ univ f) {x u : ℝ} (hs : Supports f x u) :
    leftSlope f x ≤ u ∧ u ≤ rightSlope f x := by
  have hx : x ∈ interior (univ : Set ℝ) := by simp
  constructor
  · unfold leftSlope
    rw [hc.leftDeriv_eq_sSup_slope_of_mem_interior hx]
    apply csSup_le
    · exact ⟨slope f x (x - 1), x - 1, ⟨mem_univ _, by linarith⟩, rfl⟩
    · rintro _ ⟨y, ⟨_, hyx⟩, rfl⟩
      rw [slope_comm]
      exact secant_le_support hs hyx
  · unfold rightSlope
    rw [hc.rightDeriv_eq_sInf_slope_of_mem_interior hx]
    apply le_csInf
    · exact ⟨slope f x (x + 1), x + 1, ⟨mem_univ _, by linarith⟩, rfl⟩
    · rintro _ ⟨y, ⟨_, hxy⟩, rfl⟩
      exact support_le_secant hs hxy

theorem supports_iff_oneSided_bounds {f : ℝ → ℝ}
    (hc : ConvexOn ℝ univ f) (x u : ℝ) :
    Supports f x u ↔ u ∈ Icc (leftSlope f x) (rightSlope f x) :=
  ⟨oneSided_bounds_of_supports hc, fun hu => supports_of_oneSided_bounds hc x u hu.1 hu.2⟩

theorem leftSlope_supports {f : ℝ → ℝ} (hc : ConvexOn ℝ univ f) (x : ℝ) :
    Supports f x (leftSlope f x) :=
  supports_of_oneSided_bounds hc x _ le_rfl
    (hc.leftDeriv_le_rightDeriv_of_mem_interior (by simp))

theorem rightSlope_supports {f : ℝ → ℝ} (hc : ConvexOn ℝ univ f) (x : ℝ) :
    Supports f x (rightSlope f x) :=
  supports_of_oneSided_bounds hc x _
    (hc.leftDeriv_le_rightDeriv_of_mem_interior (by simp)) le_rfl

theorem exists_support {f : ℝ → ℝ} (hc : ConvexOn ℝ univ f) (x : ℝ) :
    ∃ u : ℝ, Supports f x u := ⟨rightSlope f x, rightSlope_supports hc x⟩

/-- Every supporting slope of a nonincreasing 1-Lipschitz function is
in the closed interval [-1,0], including at nondifferentiable points. -/
theorem support_mem_Icc {f : ℝ → ℝ} (hanti : Antitone f)
    (hLip : LipschitzWith 1 f) {x u : ℝ} (hs : Supports f x u) : u ∈ Icc (-1) 0 := by
  have hright := hs (x + 1)
  have hm := hanti (show x ≤ x + 1 by linarith)
  have hleft := hs (x - 1)
  have hdist := hLip.dist_le_mul (x - 1) x
  have hstep : f (x - 1) - f x ≤ 1 := by
    calc
      _ ≤ |f (x - 1) - f x| := le_abs_self _
      _ ≤ |(x - 1) - x| := by simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using hdist
      _ = 1 := by ring_nf; norm_num
  constructor <;> nlinarith only [hright, hm, hleft, hstep]

theorem leftSlope_monotone {f : ℝ → ℝ} (hc : ConvexOn ℝ univ f) :
    Monotone (leftSlope f) := by
  intro x y hxy
  rcases eq_or_lt_of_le hxy with rfl | hxy
  · rfl
  · exact supports_order (leftSlope_supports hc x) (leftSlope_supports hc y) hxy

theorem rightSlope_monotone {f : ℝ → ℝ} (hc : ConvexOn ℝ univ f) :
    Monotone (rightSlope f) := by
  intro x y hxy
  rcases eq_or_lt_of_le hxy with rfl | hxy
  · rfl
  · exact supports_order (rightSlope_supports hc x) (rightSlope_supports hc y) hxy

/-- Distinct endpoints bound every supporting slope at an interior point.
At the endpoints themselves, use the one-sided derivative interval. -/
theorem support_endpoint_bounds {f : ℝ → ℝ} {l x r ul u ur : ℝ}
    (hl : Supports f l ul) (hx : Supports f x u) (hr : Supports f r ur)
    (hlx : l < x) (hxr : x < r) : u ∈ Icc ul ur :=
  ⟨supports_order hl hx hlx, supports_order hx hr hxr⟩

theorem rightSlope_endpoint_range {f : ℝ → ℝ} (hc : ConvexOn ℝ univ f)
    {l x r : ℝ} (hx : x ∈ Icc l r) :
    rightSlope f x ∈ Icc (rightSlope f l) (rightSlope f r) :=
  ⟨rightSlope_monotone hc hx.1, rightSlope_monotone hc hx.2⟩

theorem Q_exists_support (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hSq : Integrable (fun z : ℝ => z ^ 2) ν) (A : ℝ) :
    ∃ u : ℝ, Supports (StopLossShape.Q ν) A u :=
  exists_support (StopLossShape.Q_convex ν hSq) A

theorem Q_support_mem_Icc (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hSq : Integrable (fun z : ℝ => z ^ 2) ν) {A u : ℝ}
    (hs : Supports (StopLossShape.Q ν) A u) : u ∈ Icc (-1) 0 :=
  support_mem_Icc (StopLossShape.Q_antitone ν hSq) (StopLossShape.Q_lipschitz ν hSq) hs

/-- This is the direct interface for a smooth lower-touch construction. -/
theorem Q_exists_support_in_range (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hSq : Integrable (fun z : ℝ => z ^ 2) ν) (A : ℝ) :
    ∃ u : ℝ, u ∈ Icc (-1) 0 ∧ ∀ y : ℝ,
      StopLossShape.Q ν A + u * (y - A) ≤ StopLossShape.Q ν y := by
  obtain ⟨u, hu⟩ := Q_exists_support ν hSq A
  exact ⟨u, Q_support_mem_Icc ν hSq hu, hu⟩

theorem Q_supports_iff_oneSided_bounds (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hSq : Integrable (fun z : ℝ => z ^ 2) ν) (A u : ℝ) :
    Supports (StopLossShape.Q ν) A u ↔
      u ∈ Icc (leftSlope (StopLossShape.Q ν) A) (rightSlope (StopLossShape.Q ν) A) :=
  supports_iff_oneSided_bounds (StopLossShape.Q_convex ν hSq) A u

theorem Q_support_order (ν : Measure ℝ) {A B u v : ℝ}
    (hu : Supports (StopLossShape.Q ν) A u) (hv : Supports (StopLossShape.Q ν) B v)
    (hAB : A < B) : u ≤ v := supports_order hu hv hAB

theorem Q_rightSlope_supports (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hSq : Integrable (fun z : ℝ => z ^ 2) ν) (A : ℝ) :
    Supports (StopLossShape.Q ν) A (rightSlope (StopLossShape.Q ν) A) :=
  rightSlope_supports (StopLossShape.Q_convex ν hSq) A

theorem Q_rightSlope_mem_Icc (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hSq : Integrable (fun z : ℝ => z ^ 2) ν) (A : ℝ) :
    rightSlope (StopLossShape.Q ν) A ∈ Icc (-1) 0 :=
  Q_support_mem_Icc ν hSq (Q_rightSlope_supports ν hSq A)

theorem Q_rightSlope_monotone (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hSq : Integrable (fun z : ℝ => z ^ 2) ν) : Monotone (rightSlope (StopLossShape.Q ν)) :=
  rightSlope_monotone (StopLossShape.Q_convex ν hSq)

theorem Q_support_endpoint_bounds (ν : Measure ℝ) {l A r ul u ur : ℝ}
    (hl : Supports (StopLossShape.Q ν) l ul) (hA : Supports (StopLossShape.Q ν) A u)
    (hr : Supports (StopLossShape.Q ν) r ur) (hlA : l < A) (hAr : A < r) :
    u ∈ Icc ul ur := support_endpoint_bounds hl hA hr hlA hAr

theorem Q_rightSlope_endpoint_range (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hSq : Integrable (fun z : ℝ => z ^ 2) ν) {l A r : ℝ} (hA : A ∈ Icc l r) :
    rightSlope (StopLossShape.Q ν) A ∈
      Icc (rightSlope (StopLossShape.Q ν) l) (rightSlope (StopLossShape.Q ν) r) :=
  rightSlope_endpoint_range (StopLossShape.Q_convex ν hSq) hA

end BerryEsseen.StopLossSubgradient

#print axioms BerryEsseen.StopLossSubgradient.leftSlope_hasDerivWithinAt
#print axioms BerryEsseen.StopLossSubgradient.rightSlope_hasDerivWithinAt
#print axioms BerryEsseen.StopLossSubgradient.supports_iff_oneSided_bounds
#print axioms BerryEsseen.StopLossSubgradient.support_mem_Icc
#print axioms BerryEsseen.StopLossSubgradient.Q_exists_support_in_range
#print axioms BerryEsseen.StopLossSubgradient.Q_supports_iff_oneSided_bounds
#print axioms BerryEsseen.StopLossSubgradient.Q_support_order
#print axioms BerryEsseen.StopLossSubgradient.Q_rightSlope_monotone
#print axioms BerryEsseen.StopLossSubgradient.Q_support_endpoint_bounds
#print axioms BerryEsseen.StopLossSubgradient.Q_rightSlope_endpoint_range
