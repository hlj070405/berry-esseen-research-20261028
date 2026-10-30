module

public import BerryEsseen.CriticalTaylorBounds
public import BerryEsseen.IidSmoothingPrice

@[expose] public section

/-! 2026-10-29: geometric-sum iid prices from the actual compensated
Taylor disk. The signed third moment remains in the disk center. The
geometric polynomial never divides by the difference of two envelopes. -/

noncomputable section

open MeasureTheory ProbabilityTheory

namespace BerryEsseen.IidTaylorPrice

def center (μ : ProbabilityMeasure ℝ) (t : ℝ) : ℂ :=
  1 - ((t ^ 2 / 2 : ℝ) : ℂ) - Complex.I * ((ZeroBias.gamma μ * t ^ 3 / 16 : ℝ) : ℂ)

def radius (μ : ProbabilityMeasure ℝ) (t : ℝ) : ℝ :=
  (5 * thirdAbsoluteMoment μ / 48) * |t| ^ 3

theorem norm_sub_center_le (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (t : ℝ) :
    ‖charFun (μ : Measure ℝ) t - center μ t‖ ≤ radius μ t := by
  unfold radius
  convert CriticalTaylorBounds.function_compensated μ h t using 1
  congr 1
  unfold center
  ring

def modulus (μ : ProbabilityMeasure ℝ) (t : ℝ) : ℝ := radius μ t + ‖center μ t‖

theorem charFun_norm_le (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (t : ℝ) :
    ‖charFun (μ : Measure ℝ) t‖ ≤ modulus μ t := by
  calc
    _ = ‖(charFun (μ : Measure ℝ) t - center μ t) + center μ t‖ := by congr 1; ring
    _ ≤ ‖charFun (μ : Measure ℝ) t - center μ t‖ + ‖center μ t‖ := norm_add_le _ _
    _ ≤ _ := by
      unfold modulus
      exact add_le_add (norm_sub_center_le μ h t) le_rfl

def oneStepPrice (μ : ProbabilityMeasure ℝ) (t : ℝ) : ℝ :=
  radius μ t + ‖center μ t - SquareBiasFourier.gaussianFactor t‖

theorem norm_sub_gaussian_le_oneStepPrice (μ : ProbabilityMeasure ℝ)
    (h : StandardizedLaw μ) (t : ℝ) :
    ‖charFun (μ : Measure ℝ) t - SquareBiasFourier.gaussianFactor t‖ ≤ oneStepPrice μ t := by
  calc
    _ = ‖(charFun (μ : Measure ℝ) t - center μ t) +
        (center μ t - SquareBiasFourier.gaussianFactor t)‖ := by congr 1; ring
    _ ≤ ‖charFun (μ : Measure ℝ) t - center μ t‖ +
        ‖center μ t - SquareBiasFourier.gaussianFactor t‖ := norm_add_le _ _
    _ ≤ _ := by
      unfold oneStepPrice
      exact add_le_add (norm_sub_center_le μ h t) le_rfl

def geometric : ℕ → ℝ → ℝ → ℝ
  | 0, _, _ => 0
  | n + 1, q, a => q ^ n + a * geometric n q a

lemma geometric_nonneg (n : ℕ) (q a : ℝ) (hq : 0 ≤ q) (ha : 0 ≤ a) :
    0 ≤ geometric n q a := by
  induction n with
  | zero => rfl
  | succ n ih => exact add_nonneg (pow_nonneg hq n) (mul_nonneg ha ih)

/-- A finite geometric majorant, valid also when q=a and n=0. -/
theorem norm_pow_sub_pow_le (z w : ℂ) (n : ℕ) (q a d : ℝ)
    (hz : ‖z‖ ≤ q) (hw : ‖w‖ ≤ a) (hd : ‖z - w‖ ≤ d) :
    ‖z ^ n - w ^ n‖ ≤ d * geometric n q a := by
  have hq : 0 ≤ q := (norm_nonneg z).trans hz
  have ha : 0 ≤ a := (norm_nonneg w).trans hw
  have hd0 : 0 ≤ d := (norm_nonneg (z - w)).trans hd
  induction n with
  | zero => simp [geometric]
  | succ n ih =>
      have hp := pow_le_pow_left₀ (norm_nonneg z) hz n
      have h1 := mul_le_mul hp hd (norm_nonneg (z - w)) (pow_nonneg hq n)
      have h2 := mul_le_mul hw ih (norm_nonneg (z ^ n - w ^ n)) ha
      calc
        _ = ‖z ^ n * (z - w) + w * (z ^ n - w ^ n)‖ := by congr 1; ring
        _ ≤ ‖z ^ n * (z - w)‖ + ‖w * (z ^ n - w ^ n)‖ := norm_add_le _ _
        _ ≤ q ^ n * d + a * (d * geometric n q a) := by
          simpa only [norm_mul, norm_pow] using add_le_add h1 h2
        _ = _ := by rw [geometric]; ring

def iidPrice (μ : ProbabilityMeasure ℝ) (n : ℕ) (q t : ℝ) : ℝ :=
  oneStepPrice μ t * geometric n q (Real.exp (-(t ^ 2 / 2)))

theorem norm_iid_sub_gaussian_le (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (q t : ℝ) (hq : ‖charFun (μ : Measure ℝ) t‖ ≤ q) :
    ‖charFun (μ : Measure ℝ) t ^ n - IidSmoothingPrice.scaledGaussian n t‖ ≤
      iidPrice μ n q t := by
  have hnorm := SquareBiasFourier.norm_gaussianFactor t
  have hb := norm_pow_sub_pow_le (charFun (μ : Measure ℝ) t) (SquareBiasFourier.gaussianFactor t)
    n q (Real.exp (-(t ^ 2 / 2))) (oneStepPrice μ t) hq hnorm.le
    (norm_sub_gaussian_le_oneStepPrice μ h t)
  have heq : SquareBiasFourier.gaussianFactor t ^ n = IidSmoothingPrice.scaledGaussian n t := by
    unfold SquareBiasFourier.gaussianFactor IidSmoothingPrice.scaledGaussian
    rw [← Complex.ofReal_pow, ← Real.exp_nat_mul]
    congr 2
    ring
  simpa only [heq, iidPrice] using hb

end BerryEsseen.IidTaylorPrice

#print axioms BerryEsseen.IidTaylorPrice.norm_sub_center_le
#print axioms BerryEsseen.IidTaylorPrice.charFun_norm_le
#print axioms BerryEsseen.IidTaylorPrice.norm_sub_gaussian_le_oneStepPrice
#print axioms BerryEsseen.IidTaylorPrice.norm_pow_sub_pow_le
#print axioms BerryEsseen.IidTaylorPrice.norm_iid_sub_gaussian_le
