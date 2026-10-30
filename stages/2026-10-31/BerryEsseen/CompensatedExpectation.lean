module

public import BerryEsseen.CompensatedFourier
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

@[expose] public section

/-! 2026-10-28: the compensated Fourier identity for an actual probability law
with only a finite second moment. Tonelli's norm criterion proves actual
law/Lebesgue absolute integrability before the Fubini step. -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology
open BerryEsseen.CompensatedFourier

namespace BerryEsseen.CompensatedExpectation

open CompensatedFourier

/-- The real compensation uses the official characteristic function of the actual law. -/
def transform (ν : ProbabilityMeasure ℝ) (H t : ℝ) : ℝ :=
  (t * ((∫ y : ℝ, y ∂(ν : Measure ℝ)) - H) -
    (Complex.exp (-Complex.I * (t : ℂ) * (H : ℂ)) * charFun (ν : Measure ℝ) t).im) / t ^ 3

lemma integrable_first_of_second (ν : ProbabilityMeasure ℝ)
    (h2 : Integrable (fun y : ℝ => y ^ 2) (ν : Measure ℝ)) :
    Integrable (fun y : ℝ => y) (ν : Measure ℝ) := by
  have hid : AEStronglyMeasurable (fun y : ℝ => y) (ν : Measure ℝ) := measurable_id.aestronglyMeasurable
  have hn2 : Integrable (fun y : ℝ => ‖y‖ ^ 2) (ν : Measure ℝ) := by
    simpa only [Real.norm_eq_abs, sq_abs] using h2
  have hn1 := integrable_norm_pow_of_le hid (by decide : 1 ≤ 2) hn2
  exact (integrable_norm_iff hid).mp (by simpa only [pow_one] using hn1)

lemma integrable_shift_square (ν : ProbabilityMeasure ℝ)
    (h2 : Integrable (fun y : ℝ => y ^ 2) (ν : Measure ℝ)) (H : ℝ) :
    Integrable (fun y : ℝ => (y - H) ^ 2) (ν : Measure ℝ) := by
  have h1 := integrable_first_of_second ν h2
  have hA : Integrable (fun y : ℝ => y ^ 2 - (2 * H) * y) (ν : Measure ℝ) :=
    h2.sub (h1.const_mul _)
  have hB : Integrable (fun y : ℝ => y ^ 2 - (2 * H) * y + H ^ 2) (ν : Measure ℝ) :=
    hA.add (integrable_const _)
  convert hB using 1
  ext y
  ring

lemma integrable_shift_signed_square (ν : ProbabilityMeasure ℝ)
    (h2 : Integrable (fun y : ℝ => y ^ 2) (ν : Measure ℝ)) (H : ℝ) :
    Integrable (fun y : ℝ => (y - H) * |y - H|) (ν : Measure ℝ) := by
  have hm : AEStronglyMeasurable (fun y : ℝ => (y - H) * |y - H|) (ν : Measure ℝ) := by
    apply Continuous.aestronglyMeasurable
    fun_prop
  apply (integrable_norm_iff hm).mp
  have heq : (fun y : ℝ => ‖(y - H) * |y - H|‖) = (fun y : ℝ => (y - H) ^ 2) := by
    ext y
    simp only [Real.norm_eq_abs, abs_mul, abs_abs, ← sq, sq_abs]
  rw [heq]
  exact integrable_shift_square ν h2 H

/-- The exact scalar absolute price discharges the law/Lebesgue Tonelli condition. -/
theorem integrable_payoff_product (ν : ProbabilityMeasure ℝ)
    (h2 : Integrable (fun y : ℝ => y ^ 2) (ν : Measure ℝ)) (H : ℝ) :
    Integrable (fun p : ℝ × ℝ => payoff (p.1 - H) p.2)
      ((ν : Measure ℝ).prod positiveLebesgue) := by
  have hm : Measurable (fun p : ℝ × ℝ => payoff (p.1 - H) p.2) := by
    unfold payoff
    fun_prop
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  refine ⟨Filter.Eventually.of_forall (fun y => integrable_payoff (y - H)), ?_⟩
  have heq : (fun y : ℝ => ∫ t : ℝ, ‖payoff (y - H) t‖ ∂positiveLebesgue) =
      (fun y : ℝ => Real.pi * (y - H) ^ 2 / 4) := by
    ext y
    simpa only [Real.norm_eq_abs, payoff] using integral_abs_compensated_fourier (y - H)
  rw [heq]
  exact ((integrable_shift_square ν h2 H).const_mul Real.pi).div_const 4

lemma phase_character (t H y : ℝ) :
    Complex.exp (-Complex.I * (t : ℂ) * (H : ℂ)) * Complex.exp (((t * y : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((t * (y - H) : ℝ) : ℂ) * Complex.I) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma integrable_shift_character (ν : ProbabilityMeasure ℝ) (H t : ℝ) :
    Integrable (fun y : ℝ => Complex.exp (((t * (y - H) : ℝ) : ℂ) * Complex.I)) (ν : Measure ℝ) := by
  have hc : Continuous (fun y : ℝ => Complex.exp (((t * (y - H) : ℝ) : ℂ) * Complex.I)) := by fun_prop
  apply (integrable_const (1 : ℝ)).mono' hc.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun y => (Complex.norm_exp_ofReal_mul_I (t * (y - H))).le

lemma integrable_shift_sine (ν : ProbabilityMeasure ℝ) (H t : ℝ) :
    Integrable (fun y : ℝ => Real.sin (t * (y - H))) (ν : Measure ℝ) := by
  have h : Integrable (fun y : ℝ => (Complex.exp (((t * (y - H) : ℝ) : ℂ) * Complex.I)).im)
      (ν : Measure ℝ) := (integrable_shift_character ν H t).im
  simpa only [Complex.exp_ofReal_mul_I_im] using h

/-- The phase sign is fixed by the official +i*t*y characteristic-function convention. -/
theorem integral_shift_sine (ν : ProbabilityMeasure ℝ) (H t : ℝ) :
    (∫ y : ℝ, Real.sin (t * (y - H)) ∂(ν : Measure ℝ)) =
      (Complex.exp (-Complex.I * (t : ℂ) * (H : ℂ)) * charFun (ν : Measure ℝ) t).im := by
  have hi := integrable_shift_character ν H t
  have heq : (fun y : ℝ => Complex.exp (((t * (y - H) : ℝ) : ℂ) * Complex.I)) =
      (fun y : ℝ => Complex.exp (-Complex.I * (t : ℂ) * (H : ℂ)) *
        Complex.exp (((t * y : ℝ) : ℂ) * Complex.I)) :=
    funext fun y => (phase_character t H y).symm
  have hcomplex : (∫ y : ℝ, Complex.exp (((t * (y - H) : ℝ) : ℂ) * Complex.I) ∂(ν : Measure ℝ)) =
      Complex.exp (-Complex.I * (t : ℂ) * (H : ℂ)) * charFun (ν : Measure ℝ) t := by
    calc
      _ = ∫ y : ℝ, Complex.exp (-Complex.I * (t : ℂ) * (H : ℂ)) *
          Complex.exp (((t * y : ℝ) : ℂ) * Complex.I) ∂(ν : Measure ℝ) :=
        congrArg (fun f : ℝ → ℂ => ∫ y : ℝ, f y ∂(ν : Measure ℝ)) heq
      _ = Complex.exp (-Complex.I * (t : ℂ) * (H : ℂ)) *
          (∫ y : ℝ, Complex.exp (((t * y : ℝ) : ℂ) * Complex.I) ∂(ν : Measure ℝ)) :=
        integral_const_mul _ _
      _ = _ := by simp only [charFun_apply_real, Complex.ofReal_mul]
  calc
    (∫ y : ℝ, Real.sin (t * (y - H)) ∂(ν : Measure ℝ)) =
        ∫ y : ℝ, (Complex.exp (((t * (y - H) : ℝ) : ℂ) * Complex.I)).im ∂(ν : Measure ℝ) := by
      simp only [Complex.exp_ofReal_mul_I_im]
    _ = (∫ y : ℝ, Complex.exp (((t * (y - H) : ℝ) : ℂ) * Complex.I) ∂(ν : Measure ℝ)).im := integral_im hi
    _ = _ := congrArg Complex.im hcomplex

lemma integral_payoff_eq_transform (ν : ProbabilityMeasure ℝ)
    (h2 : Integrable (fun y : ℝ => y ^ 2) (ν : Measure ℝ)) (H t : ℝ) :
    (∫ y : ℝ, payoff (y - H) t ∂(ν : Measure ℝ)) = transform ν H t := by
  have h1 := integrable_first_of_second ν h2
  have hlin : Integrable (fun y : ℝ => t * (y - H)) (ν : Measure ℝ) :=
    (h1.sub (integrable_const H)).const_mul t
  simp only [payoff]
  rw [integral_div, integral_sub hlin (integrable_shift_sine ν H t), integral_const_mul,
    integral_sub h1 (integrable_const H), integral_shift_sine ν H t]
  simp only [integral_const, probReal_univ, one_smul, transform]

/-- The actual characteristic-function compensation, divided by t^3, is absolutely integrable. -/
theorem integrable_transform (ν : ProbabilityMeasure ℝ)
    (h2 : Integrable (fun y : ℝ => y ^ 2) (ν : Measure ℝ)) (H : ℝ) :
    IntegrableOn (transform ν H) (Ioi 0) := by
  have h := (integrable_payoff_product ν h2 H).integral_prod_right
  exact h.congr (Filter.Eventually.of_forall (fun t => integral_payoff_eq_transform ν h2 H t))

/-- The compensated expectation identity for an arbitrary actual probability law with finite second moment. -/
theorem compensated_expectation (ν : ProbabilityMeasure ℝ)
    (h2 : Integrable (fun y : ℝ => y ^ 2) (ν : Measure ℝ)) (H : ℝ) :
    (∫ y : ℝ, (y - H) * |y - H| ∂(ν : Measure ℝ)) =
      (4 / Real.pi) * (∫ t in Ioi 0, transform ν H t) := by
  have hF := integral_integral_swap (μ := (ν : Measure ℝ)) (ν := positiveLebesgue)
    (f := fun y t : ℝ => payoff (y - H) t) (integrable_payoff_product ν h2 H)
  have hleft : (∫ y : ℝ, (∫ t : ℝ, payoff (y - H) t ∂positiveLebesgue) ∂(ν : Measure ℝ)) =
      (Real.pi / 4) * (∫ y : ℝ, (y - H) * |y - H| ∂(ν : Measure ℝ)) := by
    calc
      _ = ∫ y : ℝ, (Real.pi / 4) * ((y - H) * |y - H|) ∂(ν : Measure ℝ) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun y => by
          have h := integral_compensated_fourier (y - H)
          change (∫ t : ℝ in Ioi 0, (t * (y - H) - Real.sin (t * (y - H))) / t ^ 3) = _
          rw [h]
          ring
      _ = _ := integral_const_mul _ _
  have hright : (∫ t : ℝ, (∫ y : ℝ, payoff (y - H) t ∂(ν : Measure ℝ)) ∂positiveLebesgue) =
      ∫ t in Ioi 0, transform ν H t := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun t => integral_payoff_eq_transform ν h2 H t)
  rw [hleft, hright] at hF
  rw [← hF]
  field_simp [Real.pi_ne_zero]

end BerryEsseen.CompensatedExpectation

#print axioms BerryEsseen.CompensatedExpectation.integrable_payoff_product
#print axioms BerryEsseen.CompensatedExpectation.integral_shift_sine
#print axioms BerryEsseen.CompensatedExpectation.integrable_transform
#print axioms BerryEsseen.CompensatedExpectation.compensated_expectation

namespace BerryEsseen.CompensatedExpectation

/-- H=0 sanity check: the official characteristic function enters with a minus imaginary part. -/
lemma transform_zero_threshold (ν : ProbabilityMeasure ℝ) (t : ℝ) :
    transform ν 0 t = (t * (∫ y : ℝ, y ∂(ν : Measure ℝ)) - (charFun (ν : Measure ℝ) t).im) / t ^ 3 := by
  simp [transform]

/-- Dirac sanity check: the actual characteristic-function expression reduces to the frozen scalar payoff. -/
lemma transform_dirac (ν : ProbabilityMeasure ℝ) (a H t : ℝ)
    (hν : (ν : Measure ℝ) = Measure.dirac a) : transform ν H t = payoff (a - H) t := by
  rw [transform, hν, integral_dirac, charFun_apply_real, integral_dirac]
  have hp : Complex.exp (-Complex.I * (t : ℂ) * (H : ℂ)) *
      Complex.exp ((t : ℂ) * (a : ℂ) * Complex.I) =
      Complex.exp (((t * (a - H) : ℝ) : ℂ) * Complex.I) := by
    simpa only [Complex.ofReal_mul] using phase_character t H a
  rw [hp]
  simp only [Complex.exp_ofReal_mul_I_im, payoff]

def differenceTransform (ν η : ProbabilityMeasure ℝ) (H t : ℝ) : ℝ :=
  (Complex.exp (-Complex.I * (t : ℂ) * (H : ℂ)) *
    (charFun (η : Measure ℝ) t - charFun (ν : Measure ℝ) t)).im / t ^ 3

/-- Equal real means cancel the linear compensation; the CF order is deliberately reversed. -/
lemma transform_sub_eq (ν η : ProbabilityMeasure ℝ) (H t : ℝ)
    (hmean : (∫ y : ℝ, y ∂(ν : Measure ℝ)) = ∫ y : ℝ, y ∂(η : Measure ℝ)) :
    transform ν H t - transform η H t = differenceTransform ν η H t := by
  simp only [transform, differenceTransform, mul_sub, Complex.sub_im, hmean]
  ring

theorem integrable_differenceTransform (ν η : ProbabilityMeasure ℝ)
    (hν2 : Integrable (fun y : ℝ => y ^ 2) (ν : Measure ℝ))
    (hη2 : Integrable (fun y : ℝ => y ^ 2) (η : Measure ℝ)) (H : ℝ)
    (hmean : (∫ y : ℝ, y ∂(ν : Measure ℝ)) = ∫ y : ℝ, y ∂(η : Measure ℝ)) :
    IntegrableOn (differenceTransform ν η H) (Ioi 0) := by
  have h : IntegrableOn (fun t : ℝ => transform ν H t - transform η H t) (Ioi 0) :=
    (integrable_transform ν hν2 H).sub (integrable_transform η hη2 H)
  exact h.congr (Filter.Eventually.of_forall fun t => transform_sub_eq ν η H t hmean)

/-- Same-mean law subtraction gives a genuinely absolutely integrable, uncompensated CF difference. -/
theorem compensated_expectation_difference (ν η : ProbabilityMeasure ℝ)
    (hν2 : Integrable (fun y : ℝ => y ^ 2) (ν : Measure ℝ))
    (hη2 : Integrable (fun y : ℝ => y ^ 2) (η : Measure ℝ)) (H : ℝ)
    (hmean : (∫ y : ℝ, y ∂(ν : Measure ℝ)) = ∫ y : ℝ, y ∂(η : Measure ℝ)) :
    (∫ y : ℝ, (y - H) * |y - H| ∂(ν : Measure ℝ)) -
      (∫ y : ℝ, (y - H) * |y - H| ∂(η : Measure ℝ)) =
      (4 / Real.pi) * (∫ t in Ioi 0, differenceTransform ν η H t) := by
  have hν := integrable_transform ν hν2 H
  have hη := integrable_transform η hη2 H
  have hInt : (∫ t in Ioi 0, transform ν H t) - (∫ t in Ioi 0, transform η H t) =
      ∫ t in Ioi 0, transform ν H t - transform η H t := (integral_sub hν hη).symm
  rw [compensated_expectation ν hν2 H, compensated_expectation η hη2 H, ← mul_sub, hInt]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => transform_sub_eq ν η H t hmean

end BerryEsseen.CompensatedExpectation

#print axioms BerryEsseen.CompensatedExpectation.transform_dirac
#print axioms BerryEsseen.CompensatedExpectation.integrable_differenceTransform
#print axioms BerryEsseen.CompensatedExpectation.compensated_expectation_difference
