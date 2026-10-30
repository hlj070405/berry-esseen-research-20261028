module

public import BerryEsseen.MixtureSum
public import BerryEsseen.ZeroBias
public import Mathlib.Tactic.FinCases

@[expose] public section

/-! 2026-10-29: the original fifteen-coefficient two-summand majorant,
its actual product-law expectation, and a closed-CDF consumption interface. -/

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace BerryEsseen.N2MomentMajorant

/-- Exactly the upper-triangular source coefficient indices. -/
abbrev Index := {ij : Fin 5 × Fin 5 // ij.1 ≤ ij.2}

abbrev Coefficients := Index → ℚ

theorem index_card : Fintype.card Index = 15 := by decide

/-- The original source basis is uncentered in its square coordinate. -/
def basis (i : Fin 5) (x : ℝ) : ℝ :=
  match i.val with
  | 0 => 1
  | 1 => x
  | 2 => x ^ 2
  | 3 => x ^ 3
  | _ => |x| ^ 3

def momentVector (γ ρ : ℝ) (i : Fin 5) : ℝ :=
  match i.val with
  | 0 => 1
  | 1 => 0
  | 2 => 1
  | 3 => γ
  | _ => ρ

/-- Off-diagonal coefficients multiply a sum of two products, never an average. -/
def sourceTerm (ij : Index) (x y : ℝ) : ℝ :=
  if ij.val.1 = ij.val.2 then basis ij.val.1 x * basis ij.val.2 y
  else basis ij.val.1 x * basis ij.val.2 y + basis ij.val.2 x * basis ij.val.1 y

def expectedTerm (γ ρ : ℝ) (ij : Index) : ℝ :=
  if ij.val.1 = ij.val.2 then momentVector γ ρ ij.val.1 * momentVector γ ρ ij.val.2
  else 2 * momentVector γ ρ ij.val.1 * momentVector γ ρ ij.val.2

def majorant (c : Coefficients) (x y : ℝ) : ℝ :=
  ∑ ij : Index, (c ij : ℝ) * sourceTerm ij x y

/-- The source scalar polynomial, with its two arguments still explicit. -/
def expected (c : Coefficients) (γ ρ : ℝ) : ℝ :=
  ∑ ij : Index, (c ij : ℝ) * expectedTerm γ ρ ij

theorem integrable_basis (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (i : Fin 5) :
    Integrable (basis i) (μ : Measure ℝ) := by
  fin_cases i
  · exact integrable_const 1
  · exact h.integrable_mean
  · exact h.integrable_square
  · exact ZeroBias.integrable_signed_cube μ h
  · exact h.integrable_cube

/-- In particular, the signed cubic coordinate is `ZeroBias.gamma`, not the signed square. -/
theorem integral_basis (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (i : Fin 5) :
    (∫ x : ℝ, basis i x ∂(μ : Measure ℝ)) =
      momentVector (ZeroBias.gamma μ) (thirdAbsoluteMoment μ) i := by
  fin_cases i
  · simp [basis, momentVector]
  · exact h.mean_zero
  · exact h.second_moment_one
  · rfl
  · rfl

theorem integrable_sourceTerm (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (ij : Index) :
    Integrable (fun z : ℝ × ℝ => sourceTerm ij z.1 z.2)
      ((μ : Measure ℝ).prod (μ : Measure ℝ)) := by
  have hab := (integrable_basis μ h ij.val.1).mul_prod (integrable_basis μ h ij.val.2)
  have hba := (integrable_basis μ h ij.val.2).mul_prod (integrable_basis μ h ij.val.1)
  have hsum : Integrable (fun z : ℝ × ℝ => basis ij.val.1 z.1 * basis ij.val.2 z.2 +
      basis ij.val.2 z.1 * basis ij.val.1 z.2) ((μ : Measure ℝ).prod (μ : Measure ℝ)) :=
    hab.add hba
  by_cases hd : ij.val.1 = ij.val.2
  · simpa only [sourceTerm, hd, ite_true] using hab
  · simpa only [sourceTerm, hd, ite_false] using hsum

theorem integral_sourceTerm (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (ij : Index) :
    (∫ z : ℝ × ℝ, sourceTerm ij z.1 z.2 ∂((μ : Measure ℝ).prod (μ : Measure ℝ))) =
      expectedTerm (ZeroBias.gamma μ) (thirdAbsoluteMoment μ) ij := by
  have hab := (integrable_basis μ h ij.val.1).mul_prod (integrable_basis μ h ij.val.2)
  have hba := (integrable_basis μ h ij.val.2).mul_prod (integrable_basis μ h ij.val.1)
  by_cases hd : ij.val.1 = ij.val.2
  · simp only [sourceTerm, expectedTerm, hd, ite_true]
    simp only [integral_prod_mul, integral_basis μ h]
  · simp only [sourceTerm, expectedTerm, hd, ite_false]
    rw [integral_add hab hba]
    simp only [integral_prod_mul, integral_basis μ h]
    ring

theorem integrable_majorant (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (c : Coefficients) :
    Integrable (fun z : ℝ × ℝ => majorant c z.1 z.2)
      ((μ : Measure ℝ).prod (μ : Measure ℝ)) := by
  unfold majorant
  apply integrable_finsetSum
  intro ij _
  exact (integrable_sourceTerm μ h ij).const_mul (c ij : ℝ)

/-- Every moment and every coordinate in this identity belongs to the same original law. -/
theorem integral_majorant (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (c : Coefficients) :
    (∫ z : ℝ × ℝ, majorant c z.1 z.2 ∂((μ : Measure ℝ).prod (μ : Measure ℝ))) =
      expected c (ZeroBias.gamma μ) (thirdAbsoluteMoment μ) := by
  unfold majorant expected
  rw [integral_finsetSum Finset.univ (fun ij _ =>
    (integrable_sourceTerm μ h ij).const_mul (c ij : ℝ))]
  apply Finset.sum_congr rfl
  intro ij _
  rw [integral_const_mul, integral_sourceTerm μ h]

/-- This is the original product-pushforward sum law, identified through its proven recursion. -/
theorem iidSumLaw_two_eq_add_map (μ : ProbabilityMeasure ℝ) :
    MixtureSum.iidSumLaw (μ : Measure ℝ) 2 =
      ((μ : Measure ℝ).prod (μ : Measure ℝ)).map (fun z : ℝ × ℝ => z.1 + z.2) := by
  rw [MixtureSum.iidSumLaw_eq_convPower]
  simp only [MixtureSum.convPower, Measure.conv_dirac_zero]
  rfl

def closedIndicator (H x y : ℝ) : ℝ := if x + y ≤ H then 1 else 0

@[simp] theorem closedIndicator_of_le (H x y : ℝ) (hxy : x + y ≤ H) :
    closedIndicator H x y = 1 := ite_eq_left hxy

@[simp] theorem closedIndicator_of_gt (H x y : ℝ) (hxy : H < x + y) :
    closedIndicator H x y = 0 := ite_eq_right (not_le.mpr hxy)

/-- Equality at the threshold stays inside the actual iid closed event. -/
theorem iidSumLaw_two_closedCDF_eq_integral (μ : ProbabilityMeasure ℝ) (H : ℝ) :
    (MixtureSum.iidSumLaw (μ : Measure ℝ) 2).real (Iic H) =
      ∫ z : ℝ × ℝ, closedIndicator H z.1 z.2 ∂((μ : Measure ℝ).prod (μ : Measure ℝ)) := by
  rw [iidSumLaw_two_eq_add_map, map_measureReal_apply measurable_add measurableSet_Iic]
  have hs : MeasurableSet {z : ℝ × ℝ | z.1 + z.2 ≤ H} :=
    measurableSet_le (measurable_fst.add measurable_snd) measurable_const
  change ((μ : Measure ℝ).prod (μ : Measure ℝ)).real {z : ℝ × ℝ | z.1 + z.2 ≤ H} = _
  rw [← integral_indicator_one hs]
  apply integral_congr_ae
  filter_upwards [] with z
  by_cases hz : z.1 + z.2 ≤ H <;> simp [closedIndicator, hz]

private theorem closedCDF_le_integral_on_square (μ : ProbabilityMeasure ℝ)
    (f : ℝ × ℝ → ℝ) (hf : Integrable f ((μ : Measure ℝ).prod (μ : Measure ℝ)))
    (R H : ℝ) (hR : ∀ᵐ x ∂(μ : Measure ℝ), |x| ≤ R)
    (hPointwise : ∀ x y : ℝ, |x| ≤ R → |y| ≤ R → closedIndicator H x y ≤ f (x, y)) :
    (MixtureSum.iidSumLaw (μ : Measure ℝ) 2).real (Iic H) ≤
      ∫ z : ℝ × ℝ, f z ∂((μ : Measure ℝ).prod (μ : Measure ℝ)) := by
  have hs : MeasurableSet {z : ℝ × ℝ | z.1 + z.2 ≤ H} :=
    measurableSet_le (measurable_fst.add measurable_snd) measurable_const
  have hi : Integrable (fun z : ℝ × ℝ => closedIndicator H z.1 z.2)
      ((μ : Measure ℝ).prod (μ : Measure ℝ)) := by
    have hI : Integrable ({z : ℝ × ℝ | z.1 + z.2 ≤ H}.indicator (fun _ => (1 : ℝ)))
        ((μ : Measure ℝ).prod (μ : Measure ℝ)) := (integrable_const (1 : ℝ)).indicator hs
    exact hI.congr (Filter.Eventually.of_forall fun z => by
      by_cases hz : z.1 + z.2 ≤ H <;> simp [closedIndicator, hz])
  have hprod : ∀ᵐ z ∂((μ : Measure ℝ).prod (μ : Measure ℝ)), |z.1| ≤ R ∧ |z.2| ≤ R := by
    have hm : MeasurableSet {z : ℝ × ℝ | |z.1| ≤ R ∧ |z.2| ≤ R} :=
      (measurableSet_le (continuous_abs.comp continuous_fst).measurable measurable_const).inter
        (measurableSet_le (continuous_abs.comp continuous_snd).measurable measurable_const)
    apply (Measure.ae_prod_iff_ae_ae hm).mpr
    filter_upwards [hR] with x hx
    filter_upwards [hR] with y hy
    exact ⟨hx, hy⟩
  rw [iidSumLaw_two_closedCDF_eq_integral]
  apply integral_mono_ae hi hf
  filter_upwards [hprod] with z hz
  exact hPointwise z.1 z.2 hz.1 hz.2

/-- The pointwise premise is the future geometry/checker interface, not a certificate assertion. -/
theorem closedCDF_le_expected (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (c : Coefficients) (R H : ℝ) (hR : ∀ᵐ x ∂(μ : Measure ℝ), |x| ≤ R)
    (hPointwise : ∀ x y : ℝ, |x| ≤ R → |y| ≤ R →
      closedIndicator H x y ≤ majorant c x y) :
    (MixtureSum.iidSumLaw (μ : Measure ℝ) 2).real (Iic H) ≤
      expected c (ZeroBias.gamma μ) (thirdAbsoluteMoment μ) := by
  rw [← integral_majorant μ h c]
  exact closedCDF_le_integral_on_square μ (fun z => majorant c z.1 z.2)
    (integrable_majorant μ h c) R H hR hPointwise

theorem integrable_majorant_add_const (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (c : Coefficients) (ε : ℝ) :
    Integrable (fun z : ℝ × ℝ => majorant c z.1 z.2 + ε)
      ((μ : Measure ℝ).prod (μ : Measure ℝ)) :=
  (integrable_majorant μ h c).add (integrable_const ε)

theorem integral_majorant_add_const (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (c : Coefficients) (ε : ℝ) :
    (∫ z : ℝ × ℝ, (majorant c z.1 z.2 + ε) ∂((μ : Measure ℝ).prod (μ : Measure ℝ))) =
      expected c (ZeroBias.gamma μ) (thirdAbsoluteMoment μ) + ε := by
  rw [integral_add (integrable_majorant μ h c) (integrable_const ε), integral_majorant μ h c]
  simp

theorem closedCDF_le_expected_add_const (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (c : Coefficients) (R H ε : ℝ) (hR : ∀ᵐ x ∂(μ : Measure ℝ), |x| ≤ R)
    (hPointwise : ∀ x y : ℝ, |x| ≤ R → |y| ≤ R →
      closedIndicator H x y ≤ majorant c x y + ε) :
    (MixtureSum.iidSumLaw (μ : Measure ℝ) 2).real (Iic H) ≤
      expected c (ZeroBias.gamma μ) (thirdAbsoluteMoment μ) + ε := by
  rw [← integral_majorant_add_const μ h c ε]
  exact closedCDF_le_integral_on_square μ (fun z => majorant c z.1 z.2 + ε)
    (integrable_majorant_add_const μ h c ε) R H hR hPointwise

end BerryEsseen.N2MomentMajorant

#print axioms BerryEsseen.N2MomentMajorant.integral_basis
#print axioms BerryEsseen.N2MomentMajorant.integrable_majorant
#print axioms BerryEsseen.N2MomentMajorant.integral_majorant
#print axioms BerryEsseen.N2MomentMajorant.iidSumLaw_two_eq_add_map
#print axioms BerryEsseen.N2MomentMajorant.iidSumLaw_two_closedCDF_eq_integral
#print axioms BerryEsseen.N2MomentMajorant.closedCDF_le_expected
#print axioms BerryEsseen.N2MomentMajorant.closedCDF_le_expected_add_const
