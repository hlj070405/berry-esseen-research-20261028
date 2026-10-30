module

public import BerryEsseen.ZeroBiasTransport
public import BerryEsseen.PerturbationMoment

@[expose] public section

/-! 2026-10-28: higher moments of the actual zero-bias density.
Each assertion requires the corresponding original absolute moment.
Product integrability precedes Fubini; the law may have atoms or unbounded
support. These are the fourth/fifth-moment inputs of the resource identity. -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology Interval

namespace BerryEsseen.ZeroBiasHigherMoments

open ZeroBias ZeroBiasTransport

def absoluteMoment (μ : ProbabilityMeasure ℝ) (m : ℕ) : ℝ :=
  ∫ x : ℝ, |x| ^ m ∂(μ : Measure ℝ)

lemma integrable_abs_pow_kernel_t (m : ℕ) (x : ℝ) :
    Integrable (fun t : ℝ => |t| ^ m * kernel x t) := by
  rw [mul_kernel_indicator]
  change Integrable ((Ioc (min 0 x) (max 0 x)).indicator (fun t : ℝ => |t| ^ m * |x|))
  exact ((continuous_abs.pow m).mul continuous_const).integrableOn_Ioc.integrable_indicator
    measurableSet_Ioc

lemma integral_abs_pow_kernel_t (m : ℕ) (x : ℝ) :
    (∫ t : ℝ, |t| ^ m * kernel x t) = |x| ^ (m + 2) / ((m : ℝ) + 1) := by
  rw [mul_kernel_indicator, integral_indicator measurableSet_uIoc, integral_mul_const]
  have hp := integral_pow_abs_sub_uIoc (n := m) (a := 0) (b := x)
  simp only [sub_zero] at hp
  rw [hp]
  rw [show m + 2 = (m + 1) + 1 by omega, pow_succ]
  ring

theorem integrable_abs_pow_kernel_prod (μ : ProbabilityMeasure ℝ) (m : ℕ)
    (hmoment : Integrable (fun x : ℝ => |x| ^ (m + 2)) (μ : Measure ℝ)) :
    Integrable (fun p : ℝ × ℝ => |p.2| ^ m * kernel p.1 p.2)
      ((μ : Measure ℝ).prod volume) := by
  have ha : Measurable (fun p : ℝ × ℝ => |p.2| ^ m) := by fun_prop
  have hm : Measurable (fun p : ℝ × ℝ => |p.2| ^ m * kernel p.1 p.2) :=
    ha.mul measurable_kernel
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  refine ⟨Eventually.of_forall (integrable_abs_pow_kernel_t m), ?_⟩
  have heq : (fun x : ℝ => ∫ t : ℝ, ‖|t| ^ m * kernel x t‖) =
      (fun x : ℝ => |x| ^ (m + 2) / ((m : ℝ) + 1)) := by
    funext x
    calc
      _ = ∫ t : ℝ, |t| ^ m * kernel x t := integral_congr_ae
        (Eventually.of_forall fun t => by
          rw [Real.norm_eq_abs, abs_of_nonneg
            (mul_nonneg (pow_nonneg (abs_nonneg t) m) (kernel_nonneg x t))])
      _ = _ := integral_abs_pow_kernel_t m x
  rw [heq]
  exact hmoment.div_const _

theorem integrable_abs_pow_tau (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (m : ℕ) (hmoment : Integrable (fun x : ℝ => |x| ^ (m + 2)) (μ : Measure ℝ)) :
    Integrable (fun t : ℝ => |t| ^ m * tau μ t) := by
  have hi := (integrable_abs_pow_kernel_prod μ m hmoment).integral_prod_right
  have heq : (fun t : ℝ => ∫ x : ℝ, |t| ^ m * kernel x t ∂(μ : Measure ℝ)) =
      (fun t : ℝ => |t| ^ m * tau μ t) := by
    funext t
    rw [integral_const_mul, ← tau_eq_integral_kernel μ h t]
  rw [heq] at hi
  exact hi

theorem integral_abs_pow_tau (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (m : ℕ) (hmoment : Integrable (fun x : ℝ => |x| ^ (m + 2)) (μ : Measure ℝ)) :
    (∫ t : ℝ, |t| ^ m * tau μ t) = absoluteMoment μ (m + 2) / ((m : ℝ) + 1) := by
  calc
    _ = ∫ t : ℝ, ∫ x : ℝ, |t| ^ m * kernel x t ∂(μ : Measure ℝ) :=
      integral_congr_ae (Eventually.of_forall fun t => by
        change |t| ^ m * tau μ t = ∫ x : ℝ, |t| ^ m * kernel x t ∂(μ : Measure ℝ)
        rw [integral_const_mul, ← tau_eq_integral_kernel μ h t])
    _ = ∫ x : ℝ, (∫ t : ℝ, |t| ^ m * kernel x t) ∂(μ : Measure ℝ) :=
      (integral_integral_swap (integrable_abs_pow_kernel_prod μ m hmoment)).symm
    _ = ∫ x : ℝ, |x| ^ (m + 2) / ((m : ℝ) + 1) ∂(μ : Measure ℝ) :=
      integral_congr_ae (Eventually.of_forall (integral_abs_pow_kernel_t m))
    _ = _ := by rw [integral_div]; rfl

lemma abs_pow_four (x : ℝ) : |x| ^ 4 = x ^ 4 := by
  calc
    |x| ^ 4 = (|x| ^ 2) ^ 2 := by ring
    _ = (x ^ 2) ^ 2 := by rw [sq_abs]
    _ = x ^ 4 := by ring

theorem integrable_square_tau (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (h4 : Integrable (fun x : ℝ => x ^ 4) (μ : Measure ℝ)) :
    Integrable (fun t : ℝ => t ^ 2 * tau μ t) := by
  have h4abs : Integrable (fun x : ℝ => |x| ^ (2 + 2)) (μ : Measure ℝ) := by
    simpa only [show (2 + 2 : ℕ) = 4 from rfl, abs_pow_four] using h4
  simpa only [sq_abs] using integrable_abs_pow_tau μ h 2 h4abs

theorem integral_square_tau (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (h4 : Integrable (fun x : ℝ => x ^ 4) (μ : Measure ℝ)) :
    (∫ t : ℝ, t ^ 2 * tau μ t) = (∫ x : ℝ, x ^ 4 ∂(μ : Measure ℝ)) / 3 := by
  have h4abs : Integrable (fun x : ℝ => |x| ^ (2 + 2)) (μ : Measure ℝ) := by
    simpa only [show (2 + 2 : ℕ) = 4 from rfl, abs_pow_four] using h4
  simpa only [sq_abs, absoluteMoment, show (2 + 2 : ℕ) = 4 from rfl,
    abs_pow_four, Nat.cast_ofNat, show (2 : ℝ) + 1 = 3 by norm_num] using
    integral_abs_pow_tau μ h 2 h4abs

theorem integral_abs_cube_tau (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (h5 : Integrable (fun x : ℝ => |x| ^ 5) (μ : Measure ℝ)) :
    (∫ t : ℝ, |t| ^ 3 * tau μ t) = absoluteMoment μ 5 / 4 := by
  simpa only [show (3 + 2 : ℕ) = 5 from rfl, Nat.cast_ofNat,
    show (3 : ℝ) + 1 = 4 by norm_num] using integral_abs_pow_tau μ h 3 h5

lemma primitive_signed_square (x : ℝ) :
    primitive (fun t : ℝ => t * |t|) x = |x| ^ 3 / 3 := by
  have hd (t : ℝ) : HasDerivAt (fun y : ℝ => |y| ^ 3 / 3) (t * |t|) t := by
    convert (PerturbationMoment.hasDerivAt_abs_cube t).div_const 3 using 1 <;> ring
  have hc : Continuous (fun t : ℝ => t * |t|) := continuous_id.mul continuous_abs
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hd t) (hc.intervalIntegrable 0 x)
  unfold primitive
  simpa using hFTC

theorem integrable_signed_square_tau (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (h4 : Integrable (fun x : ℝ => x ^ 4) (μ : Measure ℝ)) :
    Integrable (fun t : ℝ => t * |t| * tau μ t) := by
  have hm : AEStronglyMeasurable (fun t : ℝ => t * |t| * tau μ t) :=
    ((measurable_id.mul continuous_abs.measurable).mul (measurable_tau μ h)).aestronglyMeasurable
  apply (integrable_norm_iff hm).mp
  have heq : (fun t : ℝ => ‖t * |t| * tau μ t‖) =
      (fun t : ℝ => t ^ 2 * tau μ t) := by
    funext t
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_abs,
      abs_of_nonneg (tau_nonneg μ h t), ← pow_two, sq_abs]
  rw [heq]
  exact integrable_square_tau μ h h4

theorem integral_signed_square_tau (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (h4 : Integrable (fun x : ℝ => x ^ 4) (μ : Measure ℝ)) :
    (∫ t : ℝ, t * |t| * tau μ t) =
      (∫ x : ℝ, x * |x| ^ 3 ∂(μ : Measure ℝ)) / 3 := by
  have hweight : Integrable (fun t : ℝ => |t * (|t|)| * tau μ t) := by
    simpa only [abs_mul, abs_abs, ← pow_two, sq_abs] using integrable_square_tau μ h h4
  have ht := transport_identity μ h (fun t : ℝ => t * |t|)
    (measurable_id.mul continuous_abs.measurable) hweight
  calc
    _ = ∫ t : ℝ, tau μ t * (t * |t|) := integral_congr_ae
      (Eventually.of_forall fun t => by ring)
    _ = ∫ x : ℝ, x * primitive (fun t : ℝ => t * |t|) x ∂(μ : Measure ℝ) := ht
    _ = ∫ x : ℝ, x * |x| ^ 3 / 3 ∂(μ : Measure ℝ) := integral_congr_ae
      (Eventually.of_forall fun x => by
        change x * primitive (fun t : ℝ => t * |t|) x = x * |x| ^ 3 / 3
        rw [primitive_signed_square]
        ring)
    _ = _ := integral_div _ _

end BerryEsseen.ZeroBiasHigherMoments

#print axioms BerryEsseen.ZeroBiasHigherMoments.integrable_abs_pow_kernel_prod
#print axioms BerryEsseen.ZeroBiasHigherMoments.integrable_abs_pow_tau
#print axioms BerryEsseen.ZeroBiasHigherMoments.integral_abs_pow_tau
#print axioms BerryEsseen.ZeroBiasHigherMoments.integral_square_tau
#print axioms BerryEsseen.ZeroBiasHigherMoments.integral_abs_cube_tau
#print axioms BerryEsseen.ZeroBiasHigherMoments.integral_signed_square_tau
