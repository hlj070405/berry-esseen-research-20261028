module

public import BerryEsseen.LowFrequencyCancellation

@[expose] public section

/-! 2026-10-28: fixed-floor evaluation of the existing low-frequency prices.
Only coefficient indices move to the floor. The actual law, sample index,
threshold, and all physical inputs in the left-hand integral are retained. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators Interval
open BerryEsseen.CharacteristicExpansion BerryEsseen.LowFrequencyError
open BerryEsseen.LowFrequencyLeading BerryEsseen.LowFrequencyCancellation

namespace BerryEsseen.LowFrequencyFloor

lemma rateA_monotone (N n : ℕ) (hN : 2 < N) (hNn : N ≤ n) : rateA N ≤ rateA n := by
  have hNr : (2 : ℝ) < (N : ℝ) := Nat.cast_lt.mpr hN
  have hnn : (N : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hNn
  unfold rateA
  apply (div_le_div_iff₀ (by linarith : (0 : ℝ) < 2 * (N : ℝ))
    (by linarith : (0 : ℝ) < 2 * (n : ℝ))).mpr
  nlinarith

lemma rateB_monotone (N n : ℕ) (hN : 2 < N) (hNn : N ≤ n) (M : ℝ) (hM : M ≤ 111 / 10) :
    rateB N M ≤ rateB n M := by
  have hNr : (2 : ℝ) < (N : ℝ) := Nat.cast_lt.mpr hN
  have hnn : (N : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hNn
  have hκ : 0 ≤ (45 - M) / 96 := by linarith
  have hi : 2 / (n : ℝ) ≤ 2 / (N : ℝ) := div_le_div_of_nonneg_left (by norm_num) (by linarith) hnn
  unfold rateB
  exact mul_le_mul_of_nonneg_left (by linarith : 1 - 2 / (N : ℝ) ≤ 1 - 2 / (n : ℝ)) hκ

lemma factorF_antitone (N n : ℕ) (hN : 2 < N) (hNn : N ≤ n) : factorF n ≤ factorF N := by
  have hNr : (2 : ℝ) < (N : ℝ) := Nat.cast_lt.mpr hN
  have hnn : (N : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hNn
  have hN1 : 0 < (N : ℝ) - 1 := by linarith
  have hn1 : 0 < (n : ℝ) - 1 := by linarith
  unfold factorF
  apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
  apply (div_le_div_iff₀ hn1 hN1).mpr
  nlinarith

lemma factorF_div_antitone (N n : ℕ) (hN : 2 < N) (hNn : N ≤ n) :
    factorF n / ((n : ℝ) - 1) ≤ factorF N / ((N : ℝ) - 1) := by
  have hNr : (2 : ℝ) < (N : ℝ) := Nat.cast_lt.mpr hN
  have hnn : (N : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hNn
  calc
    _ ≤ factorF N / ((n : ℝ) - 1) :=
      div_le_div_of_nonneg_right (factorF_antitone N n hN hNn) (by linarith)
    _ ≤ _ := div_le_div_of_nonneg_left (factorF_nonneg N hN) (by linarith) (by linarith)

/-- Nonnegativity is stated for the existing L₂ definition, without a replacement price. -/
lemma coefficientL2_nonneg (n : ℕ) (hn : 2 < n) (M g M6bar aStar Z : ℝ)
    (hM : M ≤ 111 / 10) (hE : 0 ≤ sixthPrice g M6bar) :
    0 ≤ coefficientL2 n M g M6bar aStar Z := by
  have hA := rateA_pos n hn
  have hB := rateB_pos n hn M hM
  unfold coefficientL2
  positivity

lemma coefficientL2_antitone (N n : ℕ) (hN : 2 < N) (hNn : N ≤ n) (M g M6bar aStar Z : ℝ)
    (hM : M ≤ 111 / 10) (hE : 0 ≤ sixthPrice g M6bar) :
    coefficientL2 n M g M6bar aStar Z ≤ coefficientL2 N M g M6bar aStar Z := by
  have hA := rateA_monotone N n hN hNn
  have hB := rateB_monotone N n hN hNn M hM
  have hAN := rateA_pos N hN
  have hBN := rateB_pos N hN M hM
  have hA2 : 2 * rateA N ^ 2 ≤ 2 * rateA n ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hAN.le hA 2) (by norm_num)
  have hB3 : 2 * rateB N M ^ 3 ≤ 2 * rateB n M ^ 3 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hBN.le hB 3) (by norm_num)
  unfold coefficientL2
  exact add_le_add (div_le_div_of_nonneg_left hE (by positivity) hA2)
    (div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hB3)

lemma scaledL2_antitone (N n : ℕ) (hN : 2 < N) (hNn : N ≤ n) (M g M6bar aStar Z : ℝ)
    (hM : M ≤ 111 / 10) (hE : 0 ≤ sixthPrice g M6bar) :
    coefficientL2 n M g M6bar aStar Z / Real.sqrt n ≤
      coefficientL2 N M g M6bar aStar Z / Real.sqrt N := by
  have hN0 : 0 < (N : ℝ) := Nat.cast_pos.mpr (by omega : 0 < N)
  have hnn : (N : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hNn
  calc
    _ ≤ coefficientL2 N M g M6bar aStar Z / Real.sqrt n :=
      div_le_div_of_nonneg_right (coefficientL2_antitone N n hN hNn M g M6bar aStar Z hM hE) (Real.sqrt_nonneg _)
    _ ≤ _ := div_le_div_of_nonneg_left (coefficientL2_nonneg N hN M g M6bar aStar Z hM hE)
      (Real.sqrt_pos.mpr hN0) (Real.sqrt_le_sqrt hnn)

lemma triangleL0_antitone (N n : ℕ) (hN : 2 < N) (hNn : N ≤ n) (g aStar Z Iu : ℝ)
    (hg : 0 ≤ g) (ha : 0 ≤ aStar) (hZ : 0 ≤ Z) (hIu : 0 ≤ Iu) :
    triangleL0 n g aStar Z Iu ≤ triangleL0 N g aStar Z Iu := by
  have hF := mul_le_mul_of_nonneg_left (factorF_antitone N n hN hNn) hIu
  have hp := mul_le_mul_of_nonneg_right hF (show 0 ≤ Z + aStar * g / 2 by positivity)
  unfold triangleL0
  exact add_le_add hp (le_refl _)

lemma triangleLH_antitone (N n : ℕ) (hN : 2 < N) (hNn : N ≤ n) (g aStar Iu : ℝ)
    (ha : 0 ≤ aStar) (hIu : 0 ≤ Iu) :
    triangleLH n g aStar Iu ≤ triangleLH N g aStar Iu := by
  have hF := mul_le_mul_of_nonneg_left (factorF_antitone N n hN hNn) hIu
  unfold triangleLH
  exact add_le_add (mul_le_mul_of_nonneg_right hF ha) (le_refl _)

/-- Jstar≥0 is essential because the F_n Jstar summand also moves with n. -/
lemma pairedL0_antitone (N n : ℕ) (hN : 2 < N) (hNn : N ≤ n) (g aStar Z Iu Jstar : ℝ)
    (hg : 0 ≤ g) (ha : 0 ≤ aStar) (hZ : 0 ≤ Z) (hIu : 0 ≤ Iu) (hJ : 0 ≤ Jstar) :
    pairedL0 n g aStar Z Iu Jstar ≤ pairedL0 N g aStar Z Iu Jstar := by
  have hF := mul_le_mul_of_nonneg_right (factorF_antitone N n hN hNn) hJ
  have hR : factorF n * Iu / ((n : ℝ) - 1) ≤ factorF N * Iu / ((N : ℝ) - 1) := by
    convert mul_le_mul_of_nonneg_right (factorF_div_antitone N n hN hNn) hIu using 1 <;> ring
  have hp := mul_le_mul_of_nonneg_right hR
    (show 0 ≤ 35 * aStar * g ^ 3 / 48 + 35 * Z * g ^ 2 / 24 by positivity)
  unfold pairedL0
  exact add_le_add (add_le_add hF hp) (le_refl _)

lemma pairedLH_antitone (N n : ℕ) (hN : 2 < N) (hNn : N ≤ n) (g aStar Z Iu : ℝ)
    (hg : 0 ≤ g) (ha : 0 ≤ aStar) (hZ : 0 ≤ Z) (hIu : 0 ≤ Iu) :
    pairedLH n g aStar Z Iu ≤ pairedLH N g aStar Z Iu := by
  have hNr : (2 : ℝ) < (N : ℝ) := Nat.cast_lt.mpr hN
  have hnn : (N : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hNn
  have hN1 : 0 < (N : ℝ) - 1 := by linarith
  have hn1 : 0 < (n : ℝ) - 1 := by linarith
  have hd : 5 * Z * g / (2 * ((n : ℝ) - 1)) ≤ 5 * Z * g / (2 * ((N : ℝ) - 1)) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  have hbracket := add_le_add (le_refl aStar) hd
  have hF := mul_le_mul_of_nonneg_right (factorF_antitone N n hN hNn) hIu
  have hp := mul_le_mul hF hbracket
    (show 0 ≤ aStar + 5 * Z * g / (2 * ((n : ℝ) - 1)) by positivity)
    (mul_nonneg (factorF_nonneg N hN) hIu)
  unfold pairedLH
  exact add_le_add hp (le_refl _)

end BerryEsseen.LowFrequencyFloor
#print axioms BerryEsseen.LowFrequencyFloor.factorF_antitone
#print axioms BerryEsseen.LowFrequencyFloor.rateA_monotone
#print axioms BerryEsseen.LowFrequencyFloor.rateB_monotone
#print axioms BerryEsseen.LowFrequencyFloor.scaledL2_antitone
#print axioms BerryEsseen.LowFrequencyFloor.pairedL0_antitone
#print axioms BerryEsseen.LowFrequencyFloor.pairedLH_antitone

namespace BerryEsseen.LowFrequencyFloor

/-- Inherit the actual-n triangle estimate by evaluating its fixed physical
coefficients at N. The law and threshold remain μ,n,H throughout. -/
theorem actual_triangle_floor (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (h6 : Integrable (fun x : ℝ => |x| ^ 6) (μ : Measure ℝ)) (N n : ℕ) (hN : 2 < N) (hNn : N ≤ n)
    (H g M M6bar aStar Z Iu : ℝ) (hg : |gamma μ| ≤ g) (hgcap : g ≤ 37 / 20)
    (hM4 : moment μ 4 ≤ M) (hMupper : M ≤ 111 / 10) (hM6 : sixthMoment μ ≤ M6bar)
    (ha : |quarticCoeff μ| ≤ aStar) (hZ : |fifthCoeff μ| ≤ Z) (hIu : gaussianMass ≤ Iu) :
    IntegrableOn (lowIntegrand μ n H) (Ioc (0 : ℝ) (1 / 2)) ∧
    Real.sqrt n * I0 μ n H ≤ triangleL0 N g aStar Z Iu + triangleLH N g aStar Iu * |H| +
      coefficientL2 N M g M6bar aStar Z / Real.sqrt N := by
  have hn : 2 < n := lt_of_lt_of_le hN hNn
  have hg0 : 0 ≤ g := (abs_nonneg _).trans hg
  have ha0 : 0 ≤ aStar := (abs_nonneg _).trans ha
  have hZ0 : 0 ≤ Z := (abs_nonneg _).trans hZ
  have hIu0 : 0 ≤ Iu := gaussianMass_nonneg.trans hIu
  have hE : 0 ≤ sixthPrice g M6bar := sixthPrice_nonneg g M6bar ((sixthMoment_nonneg μ).trans hM6)
  have hactual := low_frequency_triangle μ h h6 n hn H g M M6bar aStar Z Iu hg hgcap hM4 hMupper hM6 ha hZ hIu
  refine ⟨hactual.1, hactual.2.trans ?_⟩
  exact add_le_add
    (add_le_add (triangleL0_antitone N n hN hNn g aStar Z Iu hg0 ha0 hZ0 hIu0)
      (mul_le_mul_of_nonneg_right (triangleLH_antitone N n hN hNn g aStar Iu ha0 hIu0) (abs_nonneg H)))
    (scaledL2_antitone N n hN hNn M g M6bar aStar Z hMupper hE)

/-- The same actual-n inheritance for the cancellation candidate. Nonnegative
Jstar is derived from the actual J price and is not silently omitted. -/
theorem actual_paired_floor (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (h6 : Integrable (fun x : ℝ => |x| ^ 6) (μ : Measure ℝ)) (N n : ℕ) (hN : 2 < N) (hNn : N ≤ n)
    (H g M M6bar aStar Z Iu Jstar : ℝ) (hg : |gamma μ| ≤ g) (hgcap : g ≤ 37 / 20)
    (hM4 : moment μ 4 ≤ M) (hMupper : M ≤ 111 / 10) (hM6 : sixthMoment μ ≤ M6bar)
    (ha : |quarticCoeff μ| ≤ aStar) (hZ : |fifthCoeff μ| ≤ Z) (hIu : gaussianMass ≤ Iu)
    (hJ : J (fifthCoeff μ) (actualC5 μ) ≤ Jstar) :
    IntegrableOn (lowIntegrand μ n H) (Ioc (0 : ℝ) (1 / 2)) ∧
    Real.sqrt n * I0 μ n H ≤ pairedL0 N g aStar Z Iu Jstar + pairedLH N g aStar Z Iu * |H| +
      coefficientL2 N M g M6bar aStar Z / Real.sqrt N := by
  have hn : 2 < n := lt_of_lt_of_le hN hNn
  have hg0 : 0 ≤ g := (abs_nonneg _).trans hg
  have ha0 : 0 ≤ aStar := (abs_nonneg _).trans ha
  have hZ0 : 0 ≤ Z := (abs_nonneg _).trans hZ
  have hIu0 : 0 ≤ Iu := gaussianMass_nonneg.trans hIu
  have hJ0 : 0 ≤ Jstar := (J_nonneg _ _).trans hJ
  have hE : 0 ≤ sixthPrice g M6bar := sixthPrice_nonneg g M6bar ((sixthMoment_nonneg μ).trans hM6)
  have hactual := low_frequency_paired μ h h6 n hn H g M M6bar aStar Z Iu Jstar hg hgcap hM4 hMupper hM6 ha hZ hIu hJ
  refine ⟨hactual.1, hactual.2.trans ?_⟩
  exact add_le_add
    (add_le_add (pairedL0_antitone N n hN hNn g aStar Z Iu Jstar hg0 ha0 hZ0 hIu0 hJ0)
      (mul_le_mul_of_nonneg_right (pairedLH_antitone N n hN hNn g aStar Z Iu hg0 ha0 hZ0 hIu0) (abs_nonneg H)))
    (scaledL2_antitone N n hN hNn M g M6bar aStar Z hMupper hE)

/-- Floor 25 is only a coefficient-evaluation index. No statement about the
law's score, optimality, or extremality at sample size 25 is required. -/
theorem actual_triangle_floor25 (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (h6 : Integrable (fun x : ℝ => |x| ^ 6) (μ : Measure ℝ)) (n : ℕ) (hn : 25 ≤ n)
    (H g M M6bar aStar Z Iu : ℝ) (hg : |gamma μ| ≤ g) (hgcap : g ≤ 37 / 20)
    (hM4 : moment μ 4 ≤ M) (hMupper : M ≤ 111 / 10) (hM6 : sixthMoment μ ≤ M6bar)
    (ha : |quarticCoeff μ| ≤ aStar) (hZ : |fifthCoeff μ| ≤ Z) (hIu : gaussianMass ≤ Iu) :
    IntegrableOn (lowIntegrand μ n H) (Ioc (0 : ℝ) (1 / 2)) ∧
    Real.sqrt n * I0 μ n H ≤ triangleL0 25 g aStar Z Iu + triangleLH 25 g aStar Iu * |H| +
      coefficientL2 25 M g M6bar aStar Z / Real.sqrt 25 := by
  exact actual_triangle_floor μ h h6 25 n (by decide) hn H g M M6bar aStar Z Iu
    hg hgcap hM4 hMupper hM6 ha hZ hIu

theorem actual_paired_floor25 (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (h6 : Integrable (fun x : ℝ => |x| ^ 6) (μ : Measure ℝ)) (n : ℕ) (hn : 25 ≤ n)
    (H g M M6bar aStar Z Iu Jstar : ℝ) (hg : |gamma μ| ≤ g) (hgcap : g ≤ 37 / 20)
    (hM4 : moment μ 4 ≤ M) (hMupper : M ≤ 111 / 10) (hM6 : sixthMoment μ ≤ M6bar)
    (ha : |quarticCoeff μ| ≤ aStar) (hZ : |fifthCoeff μ| ≤ Z) (hIu : gaussianMass ≤ Iu)
    (hJ : J (fifthCoeff μ) (actualC5 μ) ≤ Jstar) :
    IntegrableOn (lowIntegrand μ n H) (Ioc (0 : ℝ) (1 / 2)) ∧
    Real.sqrt n * I0 μ n H ≤ pairedL0 25 g aStar Z Iu Jstar + pairedLH 25 g aStar Z Iu * |H| +
      coefficientL2 25 M g M6bar aStar Z / Real.sqrt 25 := by
  exact actual_paired_floor μ h h6 25 n (by decide) hn H g M M6bar aStar Z Iu Jstar
    hg hgcap hM4 hMupper hM6 ha hZ hIu hJ

end BerryEsseen.LowFrequencyFloor
#print axioms BerryEsseen.LowFrequencyFloor.actual_triangle_floor
#print axioms BerryEsseen.LowFrequencyFloor.actual_paired_floor
#print axioms BerryEsseen.LowFrequencyFloor.actual_triangle_floor25
#print axioms BerryEsseen.LowFrequencyFloor.actual_paired_floor25
