module

public import BerryEsseen.CommonProductMoments

@[expose] public section

noncomputable section

namespace BerryEsseen.CommonProductHigherMoments

open MeasureTheory
open CommonProductMoments

private theorem integral_fst (ν μ : Measure ℝ) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    (f : ℝ → ℝ) (hf : Integrable f ν) :
    (∫ z : ℝ × ℝ, f z.1 ∂(ν.prod μ)) = ∫ x, f x ∂ν := by
  rw [integral_prod _ (hf.comp_fst μ)]
  simp

private theorem integral_snd (ν μ : Measure ℝ) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    (f : ℝ → ℝ) (hf : Integrable f μ) :
    (∫ z : ℝ × ℝ, f z.2 ∂(ν.prod μ)) = ∫ x, f x ∂μ := by
  rw [integral_prod _ (hf.comp_snd ν)]
  simp

/-- Genuine L1 integrability of the cube under convolution. Each mixed monomial
is integrable on the product measure by `Integrable.mul_prod`. -/
theorem conv_integrable_cube (ν μ : Measure ℝ)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    (hν1 : Integrable (fun x : ℝ => x) ν)
    (hν2 : Integrable (fun x : ℝ => x ^ 2) ν)
    (hν3 : Integrable (fun x : ℝ => x ^ 3) ν)
    (hμ1 : Integrable (fun x : ℝ => x) μ)
    (hμ2 : Integrable (fun x : ℝ => x ^ 2) μ)
    (hμ3 : Integrable (fun x : ℝ => x ^ 3) μ) :
    Integrable (fun x : ℝ => x ^ 3) (ν ∗ μ) := by
  have hi := (((hν3.comp_fst μ).add ((hν2.mul_prod hμ1).const_mul 3)).add
    ((hν1.mul_prod hμ2).const_mul 3)).add (hμ3.comp_snd ν)
  unfold Measure.conv
  apply (integrable_map_measure (by fun_prop) measurable_add.aemeasurable).mpr
  exact hi.congr (Filter.Eventually.of_forall fun z => by
    simp only [Pi.add_apply]
    change z.1 ^ 3 + 3 * (z.1 ^ 2 * z.2) + 3 * (z.1 * z.2 ^ 2) + z.2 ^ 3 =
      (z.1 + z.2) ^ 3
    ring)

/-- Genuine L1 integrability of the fourth power under convolution. -/
theorem conv_integrable_fourth (ν μ : Measure ℝ)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    (hν1 : Integrable (fun x : ℝ => x) ν)
    (hν2 : Integrable (fun x : ℝ => x ^ 2) ν)
    (hν3 : Integrable (fun x : ℝ => x ^ 3) ν)
    (hν4 : Integrable (fun x : ℝ => x ^ 4) ν)
    (hμ1 : Integrable (fun x : ℝ => x) μ)
    (hμ2 : Integrable (fun x : ℝ => x ^ 2) μ)
    (hμ3 : Integrable (fun x : ℝ => x ^ 3) μ)
    (hμ4 : Integrable (fun x : ℝ => x ^ 4) μ) :
    Integrable (fun x : ℝ => x ^ 4) (ν ∗ μ) := by
  have hi := ((((hν4.comp_fst μ).add ((hν3.mul_prod hμ1).const_mul 4)).add
    ((hν2.mul_prod hμ2).const_mul 6)).add
    ((hν1.mul_prod hμ3).const_mul 4)).add (hμ4.comp_snd ν)
  unfold Measure.conv
  apply (integrable_map_measure (by fun_prop) measurable_add.aemeasurable).mpr
  exact hi.congr (Filter.Eventually.of_forall fun z => by
    simp only [Pi.add_apply]
    change z.1 ^ 4 + 4 * (z.1 ^ 3 * z.2) + 6 * (z.1 ^ 2 * z.2 ^ 2) +
      4 * (z.1 * z.2 ^ 3) + z.2 ^ 4 = (z.1 + z.2) ^ 4
    ring)

/-- The signed third moment of the independent sum of two centered laws. -/
theorem integral_conv_cube (ν μ : Measure ℝ)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    (hν1 : Integrable (fun x : ℝ => x) ν)
    (hν2 : Integrable (fun x : ℝ => x ^ 2) ν)
    (hν3 : Integrable (fun x : ℝ => x ^ 3) ν)
    (hμ1 : Integrable (fun x : ℝ => x) μ)
    (hμ2 : Integrable (fun x : ℝ => x ^ 2) μ)
    (hμ3 : Integrable (fun x : ℝ => x ^ 3) μ)
    (hmν : (∫ x : ℝ, x ∂ν) = 0) (hmμ : (∫ x : ℝ, x ∂μ) = 0) :
    (∫ x : ℝ, x ^ 3 ∂(ν ∗ μ)) = (∫ x : ℝ, x ^ 3 ∂ν) + ∫ x : ℝ, x ^ 3 ∂μ := by
  have hx := hν3.comp_fst μ
  have hy := hμ3.comp_snd ν
  have hxxy := (hν2.mul_prod hμ1).const_mul 3
  have hxyy := (hν1.mul_prod hμ2).const_mul 3
  have hA : Integrable (fun z : ℝ × ℝ => z.1 ^ 3 + 3 * (z.1 ^ 2 * z.2))
      (ν.prod μ) := hx.add hxxy
  have hB : Integrable (fun z : ℝ × ℝ =>
      z.1 ^ 3 + 3 * (z.1 ^ 2 * z.2) + 3 * (z.1 * z.2 ^ 2))
      (ν.prod μ) := hA.add hxyy
  have heq : (fun z : ℝ × ℝ => (z.1 + z.2) ^ 3) =
      (fun z => z.1 ^ 3 + 3 * (z.1 ^ 2 * z.2) + 3 * (z.1 * z.2 ^ 2) + z.2 ^ 3) := by
    funext z
    ring
  unfold Measure.conv
  rw [integral_map (f := fun x : ℝ => x ^ 3) measurable_add.aemeasurable (by fun_prop),
    heq, integral_add hB hy, integral_add hA hxyy, integral_add hx hxxy,
    integral_const_mul, integral_const_mul,
    integral_fst ν μ _ hν3, integral_snd ν μ _ hμ3,
    integral_prod_mul (μ := ν) (ν := μ) (fun x : ℝ => x ^ 2) (fun x : ℝ => x),
    integral_prod_mul (μ := ν) (ν := μ) (fun x : ℝ => x) (fun x : ℝ => x ^ 2),
    hmν, hmμ]
  ring

/-- The fourth moment of the independent sum of two centered laws, retaining
the genuine product of their (possibly zero) second moments. -/
theorem integral_conv_fourth (ν μ : Measure ℝ)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    (hν1 : Integrable (fun x : ℝ => x) ν)
    (hν2 : Integrable (fun x : ℝ => x ^ 2) ν)
    (hν3 : Integrable (fun x : ℝ => x ^ 3) ν)
    (hν4 : Integrable (fun x : ℝ => x ^ 4) ν)
    (hμ1 : Integrable (fun x : ℝ => x) μ)
    (hμ2 : Integrable (fun x : ℝ => x ^ 2) μ)
    (hμ3 : Integrable (fun x : ℝ => x ^ 3) μ)
    (hμ4 : Integrable (fun x : ℝ => x ^ 4) μ)
    (hmν : (∫ x : ℝ, x ∂ν) = 0) (hmμ : (∫ x : ℝ, x ∂μ) = 0) :
    (∫ x : ℝ, x ^ 4 ∂(ν ∗ μ)) =
      (∫ x : ℝ, x ^ 4 ∂ν) + (∫ x : ℝ, x ^ 4 ∂μ) +
        6 * (∫ x : ℝ, x ^ 2 ∂ν) * ∫ x : ℝ, x ^ 2 ∂μ := by
  have hx := hν4.comp_fst μ
  have hy := hμ4.comp_snd ν
  have hxxxy := (hν3.mul_prod hμ1).const_mul 4
  have hxxyy := (hν2.mul_prod hμ2).const_mul 6
  have hxyyy := (hν1.mul_prod hμ3).const_mul 4
  have hA : Integrable (fun z : ℝ × ℝ => z.1 ^ 4 + 4 * (z.1 ^ 3 * z.2))
      (ν.prod μ) := hx.add hxxxy
  have hB : Integrable (fun z : ℝ × ℝ =>
      z.1 ^ 4 + 4 * (z.1 ^ 3 * z.2) + 6 * (z.1 ^ 2 * z.2 ^ 2))
      (ν.prod μ) := hA.add hxxyy
  have hC : Integrable (fun z : ℝ × ℝ =>
      z.1 ^ 4 + 4 * (z.1 ^ 3 * z.2) + 6 * (z.1 ^ 2 * z.2 ^ 2) + 4 * (z.1 * z.2 ^ 3))
      (ν.prod μ) := hB.add hxyyy
  have heq : (fun z : ℝ × ℝ => (z.1 + z.2) ^ 4) =
      (fun z => z.1 ^ 4 + 4 * (z.1 ^ 3 * z.2) + 6 * (z.1 ^ 2 * z.2 ^ 2) +
        4 * (z.1 * z.2 ^ 3) + z.2 ^ 4) := by
    funext z
    ring
  unfold Measure.conv
  rw [integral_map (f := fun x : ℝ => x ^ 4) measurable_add.aemeasurable (by fun_prop),
    heq, integral_add hC hy, integral_add hB hxyyy, integral_add hA hxxyy,
    integral_add hx hxxxy, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_fst ν μ _ hν4, integral_snd ν μ _ hμ4,
    integral_prod_mul (μ := ν) (ν := μ) (fun x : ℝ => x ^ 3) (fun x : ℝ => x),
    integral_prod_mul (μ := ν) (ν := μ) (fun x : ℝ => x ^ 2) (fun x : ℝ => x ^ 2),
    integral_prod_mul (μ := ν) (ν := μ) (fun x : ℝ => x) (fun x : ℝ => x ^ 3),
    hmν, hmμ]
  ring

/-- All four genuine L1 moments of a repeated independent centered sum.
The cubic integral remains signed, and the formula also covers the empty sum. -/
theorem convPower_higher_moments (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h1 : Integrable (fun x : ℝ => x) ν)
    (h2 : Integrable (fun x : ℝ => x ^ 2) ν)
    (h3 : Integrable (fun x : ℝ => x ^ 3) ν)
    (h4 : Integrable (fun x : ℝ => x ^ 4) ν)
    (hm : (∫ x : ℝ, x ∂ν) = 0) (n : ℕ) :
    Integrable (fun x : ℝ => x) (MixtureSum.convPower ν n) ∧
    Integrable (fun x : ℝ => x ^ 2) (MixtureSum.convPower ν n) ∧
    Integrable (fun x : ℝ => x ^ 3) (MixtureSum.convPower ν n) ∧
    Integrable (fun x : ℝ => x ^ 4) (MixtureSum.convPower ν n) ∧
    (∫ x : ℝ, x ∂(MixtureSum.convPower ν n)) = 0 ∧
    (∫ x : ℝ, x ^ 2 ∂(MixtureSum.convPower ν n)) =
      (n : ℝ) * (∫ x : ℝ, x ^ 2 ∂ν) ∧
    (∫ x : ℝ, x ^ 3 ∂(MixtureSum.convPower ν n)) =
      (n : ℝ) * (∫ x : ℝ, x ^ 3 ∂ν) ∧
    (∫ x : ℝ, x ^ 4 ∂(MixtureSum.convPower ν n)) =
      (n : ℝ) * (∫ x : ℝ, x ^ 4 ∂ν) +
        3 * (((n : ℝ) * (∫ x : ℝ, x ^ 2 ∂ν)) ^ 2 -
          (n : ℝ) * (∫ x : ℝ, x ^ 2 ∂ν) ^ 2) := by
  induction n with
  | zero =>
    dsimp only [MixtureSum.convPower]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact integrable_dirac (a := (0 : ℝ)) (f := fun x : ℝ => x) (by simp)
    · exact integrable_dirac (a := (0 : ℝ)) (f := fun x : ℝ => x ^ 2) (by simp)
    · exact integrable_dirac (a := (0 : ℝ)) (f := fun x : ℝ => x ^ 3) (by simp)
    · exact integrable_dirac (a := (0 : ℝ)) (f := fun x : ℝ => x ^ 4) (by simp)
    · simp
    · simp
    · simp
    · simp
  | succ n ih =>
    obtain ⟨hn1, hn2, hn3, hn4, hnm, hnv, hnt, hnu⟩ := ih
    obtain ⟨hs1, hs2, hsm, hsv⟩ := convPower_moments ν h1 h2 hm (n + 1)
    refine ⟨hs1, hs2, ?_, ?_, hsm, hsv, ?_, ?_⟩
    · exact conv_integrable_cube ν _ h1 h2 h3 hn1 hn2 hn3
    · exact conv_integrable_fourth ν _ h1 h2 h3 h4 hn1 hn2 hn3 hn4
    · change (∫ x : ℝ, x ^ 3 ∂(ν ∗ MixtureSum.convPower ν n)) = _
      rw [integral_conv_cube ν _ h1 h2 h3 hn1 hn2 hn3 hm hnm, hnt]
      push_cast
      ring
    · change (∫ x : ℝ, x ^ 4 ∂(ν ∗ MixtureSum.convPower ν n)) = _
      rw [integral_conv_fourth ν _ h1 h2 h3 h4 hn1 hn2 hn3 hn4 hm hnm, hnu, hnv]
      push_cast
      ring

/-- Unified actual moments for two groups with arbitrary nonnegative counts.
No normalization or positive-variance hypothesis is needed. -/
theorem twoGroup_moments (ν0 ν1 : Measure ℝ)
    [IsProbabilityMeasure ν0] [IsProbabilityMeasure ν1]
    (h01 : Integrable (fun x : ℝ => x) ν0)
    (h02 : Integrable (fun x : ℝ => x ^ 2) ν0)
    (h03 : Integrable (fun x : ℝ => x ^ 3) ν0)
    (h04 : Integrable (fun x : ℝ => x ^ 4) ν0)
    (h11 : Integrable (fun x : ℝ => x) ν1)
    (h12 : Integrable (fun x : ℝ => x ^ 2) ν1)
    (h13 : Integrable (fun x : ℝ => x ^ 3) ν1)
    (h14 : Integrable (fun x : ℝ => x ^ 4) ν1)
    (hm0 : (∫ x : ℝ, x ∂ν0) = 0) (hm1 : (∫ x : ℝ, x ∂ν1) = 0)
    (n0 n1 : ℕ) :
    let R := MixtureSum.convPower ν1 n1 ∗ MixtureSum.convPower ν0 n0
    let V := (n0 : ℝ) * (∫ x : ℝ, x ^ 2 ∂ν0) + (n1 : ℝ) * (∫ x : ℝ, x ^ 2 ∂ν1)
    Integrable (fun x : ℝ => x) R ∧
    Integrable (fun x : ℝ => x ^ 2) R ∧
    Integrable (fun x : ℝ => x ^ 3) R ∧
    Integrable (fun x : ℝ => x ^ 4) R ∧
    (∫ x : ℝ, x ∂R) = 0 ∧
    (∫ x : ℝ, x ^ 2 ∂R) = V ∧
    (∫ x : ℝ, x ^ 3 ∂R) =
      (n0 : ℝ) * (∫ x : ℝ, x ^ 3 ∂ν0) + (n1 : ℝ) * (∫ x : ℝ, x ^ 3 ∂ν1) ∧
    (∫ x : ℝ, x ^ 4 ∂R) =
      (n0 : ℝ) * (∫ x : ℝ, x ^ 4 ∂ν0) + (n1 : ℝ) * (∫ x : ℝ, x ^ 4 ∂ν1) +
        3 * (V ^ 2 - (n0 : ℝ) * (∫ x : ℝ, x ^ 2 ∂ν0) ^ 2 -
          (n1 : ℝ) * (∫ x : ℝ, x ^ 2 ∂ν1) ^ 2) := by
  dsimp only
  obtain ⟨ha1, ha2, ha3, ha4, ham, hav, hat, hau⟩ :=
    convPower_higher_moments ν1 h11 h12 h13 h14 hm1 n1
  obtain ⟨hb1, hb2, hb3, hb4, hbm, hbv, hbt, hbu⟩ :=
    convPower_higher_moments ν0 h01 h02 h03 h04 hm0 n0
  refine ⟨conv_integrable_first _ _ ha1 hb1,
    conv_integrable_square _ _ ha1 ha2 hb1 hb2,
    conv_integrable_cube _ _ ha1 ha2 ha3 hb1 hb2 hb3,
    conv_integrable_fourth _ _ ha1 ha2 ha3 ha4 hb1 hb2 hb3 hb4, ?_, ?_, ?_, ?_⟩
  · rw [integral_conv_first _ _ ha1 hb1, ham, hbm]
    ring
  · rw [integral_conv_square _ _ ha1 ha2 hb1 hb2 ham hbm, hav, hbv]
    ring
  · rw [integral_conv_cube _ _ ha1 ha2 ha3 hb1 hb2 hb3 ham hbm, hat, hbt]
    ring
  · rw [integral_conv_fourth _ _ ha1 ha2 ha3 ha4 hb1 hb2 hb3 hb4 ham hbm,
      hau, hbu, hav, hbv]
    ring

end BerryEsseen.CommonProductHigherMoments

#print axioms BerryEsseen.CommonProductHigherMoments.conv_integrable_cube
#print axioms BerryEsseen.CommonProductHigherMoments.conv_integrable_fourth
#print axioms BerryEsseen.CommonProductHigherMoments.integral_conv_cube
#print axioms BerryEsseen.CommonProductHigherMoments.integral_conv_fourth
#print axioms BerryEsseen.CommonProductHigherMoments.convPower_higher_moments
#print axioms BerryEsseen.CommonProductHigherMoments.twoGroup_moments
