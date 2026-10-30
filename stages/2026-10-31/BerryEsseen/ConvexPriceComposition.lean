module

public import BerryEsseen.StopLossSubgradient
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.DerivativeTest
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Topology.Order.Compact
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FunProp

@[expose] public section

/-! 2026-10-28: semiconvexity of a smooth coefficient times a genuinely convex,
possibly nonsmooth price. The proof uses smooth lower supports and never
substitutes a default native derivative at a kink of the convex price. -/

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace BerryEsseen.ConvexPriceComposition

lemma deriv2_add {f g : ℝ → ℝ} {x : ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    deriv (deriv (fun t => f t + g t)) x = deriv (deriv f) x + deriv (deriv g) x := by
  have heq : deriv (fun t => f t + g t) =ᶠ[𝓝 x] (fun t => deriv f t + deriv g t) := by
    filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)] with t ht kt
    exact deriv_fun_add (ht.differentiableAt (by norm_num)) (kt.differentiableAt (by norm_num))
  rw [heq.deriv_eq]
  exact deriv_fun_add (hf.derivWithin (by norm_num)).differentiableAt_one
    (hg.derivWithin (by norm_num)).differentiableAt_one

lemma deriv2_mul {f g : ℝ → ℝ} {x : ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    deriv (deriv (fun t => f t * g t)) x =
      deriv (deriv f) x * g x + 2 * deriv f x * deriv g x + f x * deriv (deriv g) x := by
  have hft := hf.differentiableAt (by norm_num)
  have hgt := hg.differentiableAt (by norm_num)
  have hdft := (hf.derivWithin (by norm_num)).differentiableAt_one
  have hdgt := (hg.derivWithin (by norm_num)).differentiableAt_one
  have heq : deriv (fun t => f t * g t) =ᶠ[𝓝 x]
      (fun t => deriv f t * g t + f t * deriv g t) := by
    filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)] with t ht kt
    exact deriv_fun_mul (ht.differentiableAt (by norm_num)) (kt.differentiableAt (by norm_num))
  rw [heq.deriv_eq]
  have hd := (hdft.hasDerivAt.mul hgt.hasDerivAt).add (hft.hasDerivAt.mul hdgt.hasDerivAt)
  convert hd.deriv using 1
  ring

lemma deriv2_polynomial (c m d x : ℝ) :
    deriv (deriv (fun t : ℝ => c * t ^ 2 + m * t + d)) x = 2 * c := by
  have heq : deriv (fun t : ℝ => c * t ^ 2 + m * t + d) = (fun t => 2 * c * t + m) := by
    funext t
    have hd := ((((hasDerivAt_id' t).pow 2).const_mul c).add
      ((hasDerivAt_id' t).const_mul m)).add_const d
    convert hd.deriv using 1
    ring
  rw [heq, deriv_add_const, deriv_const_mul_id]

lemma deriv2_add_polynomial {g : ℝ → ℝ} {x : ℝ}
    (hg : ContDiffAt ℝ 2 g x) (c m d : ℝ) :
    deriv (deriv (fun t => g t + (c * t ^ 2 + m * t + d))) x =
      deriv (deriv g) x + 2 * c := by
  rw [deriv2_add hg (by fun_prop), deriv2_polynomial]

/-- At a local maximum a C² test cannot have a strictly positive
native second derivative. The official derivative test and local constancy
supply this conclusion without any differentiability-by-default argument. -/
lemma second_deriv_nonpos_at_localMax {g : ℝ → ℝ} {x : ℝ}
    (hmax : IsLocalMax g x) (hg : ContDiffAt ℝ 2 g x) :
    deriv (deriv g) x ≤ 0 := by
  by_contra hn
  have hp : 0 < deriv (deriv g) x := lt_of_not_ge hn
  have hstationary := hmax.hasDerivAt_eq_zero (hg.differentiableAt (by norm_num)).hasDerivAt
  have hmin := isLocalMin_of_deriv_deriv_pos hp hstationary hg.continuousAt
  have heq := eventuallyEq_of_isMinFilter_of_isMaxFilter hmin hmax
  have hd := heq.deriv.deriv_eq
  simp only [deriv_const', deriv_const] at hd
  linarith

/-- A continuous function with a smooth strictly positive-curvature lower
support at every interior point lies below every chord. -/
theorem convexOn_of_strict_smooth_lower_supports {f : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b))
    (hsupport : ∀ x ∈ Ioo a b, ∃ g : ℝ → ℝ,
      ContDiffAt ℝ 2 g x ∧ g x = f x ∧
      (∀ᶠ y in 𝓝 x, g y ≤ f y) ∧ 0 < deriv (deriv g) x) :
    ConvexOn ℝ (Icc a b) f := by
  apply LinearOrder.convexOn_of_lt (convex_Icc a b)
  intro x hx y hy hxy α β hα hβ hαβ
  simp only [smul_eq_mul]
  let z := α * x + β * y
  have hz : z ∈ Icc x y := by
    exact (convex_Icc x y) ⟨le_rfl, hxy.le⟩ ⟨hxy.le, le_rfl⟩ hα.le hβ.le hαβ
  let m := (f y - f x) / (y - x)
  let d := f x - m * x
  have hden : y - x ≠ 0 := (sub_pos.mpr hxy).ne'
  have hleft : f x - (m * x + d) = 0 := by dsimp [d]; ring
  have hright : f y - (m * y + d) = 0 := by
    dsimp [d, m]
    field_simp [hden]
    ring
  have hchord : m * z + d = α * f x + β * f y := by
    have hαeq : α = 1 - β := by linarith
    dsimp [d, m, z]
    rw [hαeq]
    field_simp [hden]
    ring
  by_contra hbad
  have hbad' : 0 < f z - (m * z + d) := by rw [hchord]; linarith
  have hsub : Icc x y ⊆ Icc a b := Icc_subset_Icc hx.1 hy.2
  have hcont : ContinuousOn (fun t => f t - (m * t + d)) (Icc x y) :=
    (hf.mono hsub).sub (by fun_prop)
  obtain ⟨t, ht, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hxy.le) hcont
  have htpos : 0 < f t - (m * t + d) := hbad'.trans_le (hmax hz)
  have htx : x < t := by
    by_contra h
    have hteq : t = x := le_antisymm (le_of_not_gt h) ht.1
    simp [hteq, hleft] at htpos
  have hty : t < y := by
    by_contra h
    have hteq : t = y := le_antisymm ht.2 (le_of_not_gt h)
    simp [hteq, hright] at htpos
  obtain ⟨g, hg, htouch, hbelow, hcurv⟩ := hsupport t ⟨hx.1.trans_lt htx, hty.trans_le hy.2⟩
  let r := fun s => g s + ((0 : ℝ) * s ^ 2 + (-m) * s + (-d))
  have hr : IsLocalMax r t := by
    filter_upwards [hbelow, Icc_mem_nhds htx hty] with s hs hsI
    dsimp [r]
    have hsm := hmax hsI
    change f s - (m * s + d) ≤ f t - (m * t + d) at hsm
    rw [← htouch] at hsm
    linarith
  have hsec := second_deriv_nonpos_at_localMax hr (hg.add (by fun_prop))
  have heq := deriv2_add_polynomial hg 0 (-m) (-d)
  change deriv (deriv r) t = _ at heq
  rw [heq] at hsec
  linarith

/-- Nonnegative curvature at the touching point is enough. A small quadratic
makes supports strict, and passing its coefficient to zero restores f. -/
theorem convexOn_of_smooth_lower_supports {f : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b))
    (hsupport : ∀ x ∈ Ioo a b, ∃ g : ℝ → ℝ,
      ContDiffAt ℝ 2 g x ∧ g x = f x ∧
      (∀ᶠ y in 𝓝 x, g y ≤ f y) ∧ 0 ≤ deriv (deriv g) x) :
    ConvexOn ℝ (Icc a b) f := by
  have hconv (ε : ℝ) (hε : 0 < ε) :
      ConvexOn ℝ (Icc a b) (fun t => f t + ε * t ^ 2) := by
    apply convexOn_of_strict_smooth_lower_supports (hf.add (by fun_prop))
    intro x hx
    obtain ⟨g, hg, ht, hb, hc⟩ := hsupport x hx
    refine ⟨fun t => g t + (ε * t ^ 2 + 0 * t + 0), hg.add (by fun_prop), ?_, ?_, ?_⟩
    · simp only [Pi.add_apply, zero_mul, add_zero, ht]
    · filter_upwards [hb] with y hy
      simpa using add_le_add_right hy (ε * y ^ 2)
    · rw [deriv2_add_polynomial hg ε 0 0]
      linarith
  refine ⟨convex_Icc a b, ?_⟩
  intro x hx y hy α β hα hβ hαβ
  simp only [smul_eq_mul]
  let C := α * x ^ 2 + β * y ^ 2 - (α * x + β * y) ^ 2
  have hbound (ε : ℝ) (hε : 0 < ε) :
      f (α * x + β * y) ≤ α * f x + β * f y + ε * C := by
    have h := (hconv ε hε).2 hx hy hα hβ hαβ
    simp only [smul_eq_mul] at h
    dsimp [C]
    nlinarith
  have hlim : Tendsto (fun ε : ℝ => α * f x + β * f y + ε * C)
      (𝓝[>] 0) (𝓝 (α * f x + β * f y)) := by
    have hc : Continuous (fun ε : ℝ => α * f x + β * f y + ε * C) := by fun_prop
    simpa using (hc.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact hbound ε hε



/-- Semiconvexity needs lower tests, not C¹ regularity of the envelope itself. -/
theorem convexOn_quadratic_of_smooth_lower_supports {f : ℝ → ℝ} {a b M : ℝ}
    (hf : ContinuousOn f (Icc a b))
    (hsupport : ∀ x ∈ Ioo a b, ∃ g : ℝ → ℝ,
      ContDiffAt ℝ 2 g x ∧ g x = f x ∧
      (∀ᶠ y in 𝓝 x, g y ≤ f y) ∧ -M ≤ deriv (deriv g) x) :
    ConvexOn ℝ (Icc a b) (fun t => f t + M * t ^ 2 / 2) := by
  apply convexOn_of_smooth_lower_supports (hf.add (by fun_prop))
  intro x hx
  obtain ⟨g, hg, ht, hb, hc⟩ := hsupport x hx
  refine ⟨fun t => g t + (M / 2 * t ^ 2 + 0 * t + 0), hg.add (by fun_prop), ?_, ?_, ?_⟩
  · simp only [Pi.add_apply]
    rw [ht]
    ring
  · filter_upwards [hb] with y hy
    simp only [Pi.add_apply]
    nlinarith [hy]
  · rw [deriv2_add_polynomial hg (M / 2) 0 0]
    linarith

/-- The affine support for T is held fixed when differentiating. Both signed
cross terms survive, including changes in the sign of η'. -/
theorem support_test_deriv2 {base η A : ℝ → ℝ} {x : ℝ}
    (hb : ContDiffAt ℝ 2 base x) (hη : ContDiffAt ℝ 2 η x)
    (hA : ContDiffAt ℝ 2 A x) (c u : ℝ) :
    deriv (deriv (fun t => base t + η t * (c + u * (A t - A x)))) x =
      deriv (deriv base) x + deriv (deriv η) x * c +
      2 * deriv η x * u * deriv A x + η x * u * deriv (deriv A) x := by
  let V := fun t => c + u * (A t - A x)
  have hV : ContDiffAt ℝ 2 V x := by dsimp [V]; fun_prop
  have hdV : deriv V = (fun t => u * deriv A t) := by
    funext t
    simp only [V, deriv_const_add, deriv_const_mul_field, deriv_sub_const]
  have hddV : deriv (deriv V) x = u * deriv (deriv A) x := by
    rw [hdV, deriv_const_mul_field]
  change deriv (deriv (fun t => base t + η t * V t)) x = _
  rw [deriv2_add hb (hη.mul hV), deriv2_mul hη hV, hddV, hdV]
  simp only [V, sub_self, mul_zero, add_zero]
  ring

lemma convex_univ_continuous {T : ℝ → ℝ} (hT : ConvexOn ℝ univ T) : Continuous T := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply continuousAt_iff_continuous_left'_right'.mpr
  exact ⟨(hT.differentiableWithinAt_Iio_of_mem_interior (by simp)).continuousWithinAt,
    (hT.differentiableWithinAt_Ioi_of_mem_interior (by simp)).continuousWithinAt⟩

/-- Minimal support-slope interface. A separate slope can be chosen at each
point; T itself need only be continuous and can have genuine kinks. -/
theorem composition_semiconvex_of_supports {base η A T : ℝ → ℝ}
    {U : Set ℝ} {a b M : ℝ} (hU : IsOpen U) (hI : Icc a b ⊆ U)
    (hb : ContDiffOn ℝ 2 base U) (hη : ContDiffOn ℝ 2 η U)
    (hA : ContDiffOn ℝ 2 A U) (hT : Continuous T)
    (hηnonneg : ∀ t ∈ Icc a b, 0 ≤ η t)
    (hsupport : ∀ x ∈ Ioo a b, ∃ u : ℝ,
      (∀ y : ℝ, T (A x) + u * (y - A x) ≤ T y) ∧
      -M ≤ deriv (deriv base) x + deriv (deriv η) x * T (A x) +
        2 * deriv η x * u * deriv A x + η x * u * deriv (deriv A) x) :
    ConvexOn ℝ (Icc a b) (fun t => base t + η t * T (A t) + M * t ^ 2 / 2) := by
  have hcont : ContinuousOn (fun t => base t + η t * T (A t)) (Icc a b) :=
    (hb.continuousOn.mono hI).add
      ((hη.continuousOn.mono hI).mul (hT.comp_continuousOn (hA.continuousOn.mono hI)))
  apply convexOn_quadratic_of_smooth_lower_supports hcont
  intro x hx
  obtain ⟨u, hu, hcurv⟩ := hsupport x hx
  have hxU := hI ⟨hx.1.le, hx.2.le⟩
  have hbx := hb.contDiffAt (hU.mem_nhds hxU)
  have hηx := hη.contDiffAt (hU.mem_nhds hxU)
  have hAx := hA.contDiffAt (hU.mem_nhds hxU)
  refine ⟨fun t => base t + η t * (T (A x) + u * (A t - A x)),
    hbx.add (hηx.mul (contDiffAt_const.add (contDiffAt_const.mul (hAx.sub contDiffAt_const)))),
    ?_, ?_, ?_⟩
  · simp only [sub_self, mul_zero, add_zero]
  · filter_upwards [Icc_mem_nhds hx.1 hx.2] with t ht
    have hm := mul_le_mul_of_nonneg_left (hu (A t)) (hηnonneg t ht)
    linarith
  · rw [support_test_deriv2 hbx hηx hAx]
    exact hcurv

/-- Every real finite convex T is admitted. The inequality is required for
its genuine supporting slopes, rather than an artificial derivative at kinks. -/
theorem convex_composition_semiconvex {base η A T : ℝ → ℝ}
    {U : Set ℝ} {a b M : ℝ} (hU : IsOpen U) (hI : Icc a b ⊆ U)
    (hb : ContDiffOn ℝ 2 base U) (hη : ContDiffOn ℝ 2 η U)
    (hA : ContDiffOn ℝ 2 A U) (hT : ConvexOn ℝ univ T)
    (hηnonneg : ∀ t ∈ Icc a b, 0 ≤ η t)
    (hcurv : ∀ x ∈ Ioo a b, ∀ u : ℝ, StopLossSubgradient.Supports T (A x) u →
      -M ≤ deriv (deriv base) x + deriv (deriv η) x * T (A x) +
        2 * deriv η x * u * deriv A x + η x * u * deriv (deriv A) x) :
    ConvexOn ℝ (Icc a b) (fun t => base t + η t * T (A t) + M * t ^ 2 / 2) := by
  apply composition_semiconvex_of_supports hU hI hb hη hA (convex_univ_continuous hT) hηnonneg
  intro x hx
  obtain ⟨u, hu⟩ := StopLossSubgradient.exists_support hT (A x)
  exact ⟨u, hu, hcurv x hx u hu⟩

/-- The actual optimized stop-loss price, including nonattained width optima
and top-atom kinks. The only remaining arithmetic is the displayed signed bound. -/
theorem Q_composition_semiconvex (ν : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure ν]
    (hSq : MeasureTheory.Integrable (fun z : ℝ => z ^ 2) ν)
    {base η A : ℝ → ℝ} {U : Set ℝ} {a b M : ℝ}
    (hU : IsOpen U) (hI : Icc a b ⊆ U)
    (hb : ContDiffOn ℝ 2 base U) (hη : ContDiffOn ℝ 2 η U)
    (hA : ContDiffOn ℝ 2 A U) (hηnonneg : ∀ t ∈ Icc a b, 0 ≤ η t)
    (hcurv : ∀ x ∈ Ioo a b, ∀ u ∈ Icc (-1 : ℝ) 0,
      -M ≤ deriv (deriv base) x + deriv (deriv η) x * StopLossShape.Q ν (A x) +
        2 * deriv η x * u * deriv A x + η x * u * deriv (deriv A) x) :
    ConvexOn ℝ (Icc a b)
      (fun t => base t + η t * StopLossShape.Q ν (A t) + M * t ^ 2 / 2) := by
  apply composition_semiconvex_of_supports hU hI hb hη hA
    (StopLossShape.Q_lipschitz ν hSq).continuous hηnonneg
  intro x hx
  obtain ⟨u, hu, hs⟩ := StopLossSubgradient.Q_exists_support_in_range ν hSq (A x)
  exact ⟨u, hs, hcurv x hx u hu⟩

end BerryEsseen.ConvexPriceComposition

#print axioms BerryEsseen.ConvexPriceComposition.convexOn_of_smooth_lower_supports
#print axioms BerryEsseen.ConvexPriceComposition.convexOn_quadratic_of_smooth_lower_supports
#print axioms BerryEsseen.ConvexPriceComposition.support_test_deriv2
#print axioms BerryEsseen.ConvexPriceComposition.convex_composition_semiconvex
#print axioms BerryEsseen.ConvexPriceComposition.Q_composition_semiconvex






