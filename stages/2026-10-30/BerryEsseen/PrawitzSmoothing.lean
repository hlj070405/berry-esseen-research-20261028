module

public import BerryEsseen.FourierRemainder
public import Causalean.Stat.CLT.BerryEsseen.PrawitzSmoothing

@[expose] public section

/-! 2026-10-29: Prawitz smoothing for the same actual normalized iid sum
as Target. The first moment and the characteristic function below are proved
from that law; the smoothing bound retains closed threshold atoms. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped Interval NNReal

namespace BerryEsseen.PrawitzSmoothing

open Causalean.Stat.CLT.BerryEsseen (prawitzKernel)

theorem normalizedIidSumLaw_eq_raw_map (μ : ProbabilityMeasure ℝ) (n : ℕ) :
    normalizedIidSumLaw μ n =
      (MixtureSum.iidSumLaw (μ : Measure ℝ) n).map (fun u : ℝ => u / Real.sqrt n) := by
  have hid : (μ : Measure ℝ) = (μ : Measure ℝ).map (fun u : ℝ => (u - 0) / 1) := by
    simp
  simpa only [mul_zero, sub_zero, one_mul] using
    AffineSum.normalizedIidSumLaw_eq_map μ (μ : Measure ℝ) 0 1 hid n

theorem integrable_normalizedIidSumLaw (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (n : ℕ) : Integrable (fun y : ℝ => y) (normalizedIidSumLaw μ n) := by
  have hraw := (Extremizer.iidSum_moments μ hμ n).1
  rw [Extremizer.coe_iidSumProbability] at hraw
  rw [normalizedIidSumLaw_eq_raw_map]
  exact (integrable_map_measure measurable_id.aestronglyMeasurable
    (by fun_prop : AEMeasurable (fun u : ℝ => u / Real.sqrt n)
      (MixtureSum.iidSumLaw (μ : Measure ℝ) n))).mpr (hraw.div_const _)

/-- Scaling acts on the frequency before taking the nth power. -/
theorem charFun_normalizedIidSumLaw (μ : ProbabilityMeasure ℝ) (n : ℕ) (t : ℝ) :
    charFun (normalizedIidSumLaw μ n) t = charFun (μ : Measure ℝ) (t / Real.sqrt n) ^ n := by
  rw [normalizedIidSumLaw_eq_raw_map]
  have hscale : (fun u : ℝ => u / Real.sqrt n) = (fun u : ℝ => (Real.sqrt n)⁻¹ * u) := by
    funext u
    rw [div_eq_mul_inv, mul_comm]
  rw [hscale, charFun_map_mul, MixtureSum.iidSumLaw_eq_convPower,
    FourierRemainder.charFun_convPower]
  rw [div_eq_mul_inv, mul_comm]

theorem charFun_standardGaussian (t : ℝ) :
    charFun (gaussianReal 0 1) t = (Real.exp (-(t ^ 2 / 2)) : ℂ) := by
  simpa only [NNReal.coe_one, one_mul, neg_div] using
    FourierRemainder.gaussian_charFun_real (1 : ℝ≥0) t

/-- The four Prawitz terms for the actual normalized iid characteristic function. -/
def normalizedEnvelope (μ : ProbabilityMeasure ℝ) (n : ℕ) (U0 U : ℝ) : ℝ :=
  (2 / U) * (∫ t in (0 : ℝ)..U0,
    ‖prawitzKernel (t / U)‖ *
      ‖charFun (μ : Measure ℝ) (t / Real.sqrt n) ^ n -
        (Real.exp (-(t ^ 2 / 2)) : ℂ)‖) +
  (2 / U) * (∫ t in U0..U,
    ‖prawitzKernel (t / U)‖ * ‖charFun (μ : Measure ℝ) (t / Real.sqrt n) ^ n‖) +
  2 * (∫ t in (0 : ℝ)..U0,
    ‖prawitzKernel (t / U) / (U : ℂ) - Complex.I / ((2 * Real.pi * t : ℝ) : ℂ)‖ *
      Real.exp (-(t ^ 2 / 2))) +
  (1 / Real.pi) * (∫ t in Ioi U0, Real.exp (-(t ^ 2 / 2)) / t)

theorem normalized_actual_cdf_le (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (n : ℕ) (hn : 0 < n) (U0 U : ℝ) (hU0 : 0 < U0) (hcut : U0 ≤ U) (x : ℝ) :
    |(normalizedIidSumLaw μ n).real (Iic x) - GaussianTools.Phi x| ≤
      normalizedEnvelope μ n U0 U := by
  have h := Causalean.Stat.CLT.BerryEsseen.normal_cdf_prawitz_smoothing
    (normalizedIidSumLaw μ n) (integrable_normalizedIidSumLaw μ hμ n) U0 U hU0 hcut x
  simpa only [Measure.real, GaussianTools.Phi, normalizedEnvelope,
    charFun_normalizedIidSumLaw, charFun_standardGaussian] using h

/-- The same four terms in the raw-sum frequency coordinate. -/
def rawEnvelope (μ : ProbabilityMeasure ℝ) (n : ℕ) (T0 T : ℝ) : ℝ :=
  (2 / T) * (∫ s in (0 : ℝ)..T0,
    ‖prawitzKernel (s / T)‖ *
      ‖charFun (μ : Measure ℝ) s ^ n - (Real.exp (-((n : ℝ) * s ^ 2 / 2)) : ℂ)‖) +
  (2 / T) * (∫ s in T0..T,
    ‖prawitzKernel (s / T)‖ * ‖charFun (μ : Measure ℝ) s ^ n‖) +
  2 * (∫ s in (0 : ℝ)..T0,
    ‖prawitzKernel (s / T) / (T : ℂ) - Complex.I / ((2 * Real.pi * s : ℝ) : ℂ)‖ *
      Real.exp (-((n : ℝ) * s ^ 2 / 2))) +
  (1 / Real.pi) * (∫ s in Ioi T0, Real.exp (-((n : ℝ) * s ^ 2 / 2)) / s)

private theorem intervalIntegral_dilate (f : ℝ → ℝ) (r a b : ℝ) :
    (∫ t in r * a..r * b, f t) = r * ∫ s in a..b, f (r * s) := by
  simpa only [smul_eq_mul] using
    (intervalIntegral.smul_integral_comp_mul_left (a := a) (b := b) f r).symm

private theorem tailIntegral_dilate (f : ℝ → ℝ) (r a : ℝ) (hr : 0 < r) :
    (∫ t in Ioi (r * a), f t) = r * ∫ s in Ioi a, f (r * s) := by
  simpa only [smul_eq_mul] using (integral_comp_mul_left_Ioi' f a hr).symm

/-- Actual frequency substitution, including the unbounded Gaussian tail.
No regularity or symmetry of the original law is used in this identity. -/
theorem normalizedEnvelope_scale_eq_raw (μ : ProbabilityMeasure ℝ) (n : ℕ) (hn : 0 < n)
    (T0 T : ℝ) :
    normalizedEnvelope μ n (Real.sqrt n * T0) (Real.sqrt n * T) = rawEnvelope μ n T0 T := by
  let r : ℝ := Real.sqrt n
  have hr : 0 < r := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  have hdivide (s : ℝ) : (r * s) / (r * T) = s / T := mul_div_mul_left s T hr.ne'
  have hfreq (s : ℝ) : (r * s) / Real.sqrt n = s := by
    change r * s / r = s
    exact mul_div_cancel_left₀ s hr.ne'
  have hgauss (s : ℝ) :
      Real.exp (-((r * s) ^ 2 / 2)) = Real.exp (-((n : ℝ) * s ^ 2 / 2)) := by
    congr 1
    dsimp [r]
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  have hcorrection (s : ℝ) :
      prawitzKernel ((r * s) / (r * T)) / ((r * T : ℝ) : ℂ) -
          Complex.I / ((2 * Real.pi * (r * s) : ℝ) : ℂ) =
        (prawitzKernel (s / T) / (T : ℂ) -
          Complex.I / ((2 * Real.pi * s : ℝ) : ℂ)) / (r : ℂ) := by
    have hdenT : ((r * T : ℝ) : ℂ) = (T : ℂ) * (r : ℂ) := by push_cast; ring
    have hdenS : ((2 * Real.pi * (r * s) : ℝ) : ℂ) =
        ((2 * Real.pi * s : ℝ) : ℂ) * (r : ℂ) := by push_cast; ring
    rw [hdivide, hdenT, hdenS, div_mul_eq_div_div, div_mul_eq_div_div, sub_div]
  let L : ℝ → ℝ := fun t => ‖prawitzKernel (t / (r * T))‖ *
    ‖charFun (μ : Measure ℝ) (t / Real.sqrt n) ^ n - (Real.exp (-(t ^ 2 / 2)) : ℂ)‖
  let Lraw : ℝ → ℝ := fun s => ‖prawitzKernel (s / T)‖ *
    ‖charFun (μ : Measure ℝ) s ^ n - (Real.exp (-((n : ℝ) * s ^ 2 / 2)) : ℂ)‖
  let Q : ℝ → ℝ := fun t => ‖prawitzKernel (t / (r * T))‖ *
    ‖charFun (μ : Measure ℝ) (t / Real.sqrt n) ^ n‖
  let Qraw : ℝ → ℝ := fun s => ‖prawitzKernel (s / T)‖ * ‖charFun (μ : Measure ℝ) s ^ n‖
  let P : ℝ → ℝ := fun t =>
    ‖prawitzKernel (t / (r * T)) / ((r * T : ℝ) : ℂ) -
      Complex.I / ((2 * Real.pi * t : ℝ) : ℂ)‖ * Real.exp (-(t ^ 2 / 2))
  let Praw : ℝ → ℝ := fun s =>
    ‖prawitzKernel (s / T) / (T : ℂ) - Complex.I / ((2 * Real.pi * s : ℝ) : ℂ)‖ *
      Real.exp (-((n : ℝ) * s ^ 2 / 2))
  let G : ℝ → ℝ := fun t => Real.exp (-(t ^ 2 / 2)) / t
  let Graw : ℝ → ℝ := fun s => Real.exp (-((n : ℝ) * s ^ 2 / 2)) / s
  have hL (s : ℝ) : L (r * s) = Lraw s := by
    dsimp [L, Lraw]
    rw [hdivide, hfreq, hgauss]
  have hQ (s : ℝ) : Q (r * s) = Qraw s := by
    dsimp [Q, Qraw]
    rw [hdivide, hfreq]
  have hP (s : ℝ) : P (r * s) = Praw s / r := by
    dsimp [P, Praw]
    rw [hcorrection, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, hgauss]
    ring
  have hG (s : ℝ) : G (r * s) = Graw s / r := by
    dsimp [G, Graw]
    rw [hgauss, mul_comm r s, div_mul_eq_div_div]
  have hLint : (∫ t in (0 : ℝ)..r * T0, L t) = r * ∫ s in (0 : ℝ)..T0, Lraw s := by
    calc
      _ = r * ∫ s in (0 : ℝ)..T0, L (r * s) := by
        simpa only [mul_zero] using intervalIntegral_dilate L r 0 T0
      _ = _ := by simp_rw [hL]
  have hQint : (∫ t in r * T0..r * T, Q t) = r * ∫ s in T0..T, Qraw s := by
    rw [intervalIntegral_dilate Q r T0 T]
    simp_rw [hQ]
  have hPint : (∫ t in (0 : ℝ)..r * T0, P t) = ∫ s in (0 : ℝ)..T0, Praw s := by
    calc
      _ = r * ∫ s in (0 : ℝ)..T0, P (r * s) := by
        simpa only [mul_zero] using intervalIntegral_dilate P r 0 T0
      _ = r * ((∫ s in (0 : ℝ)..T0, Praw s) / r) := by
        simp_rw [hP, intervalIntegral.integral_div]
      _ = _ := by field_simp [hr.ne']
  have hGint : (∫ t in Ioi (r * T0), G t) = ∫ s in Ioi T0, Graw s := by
    calc
      _ = r * ∫ s in Ioi T0, G (r * s) := tailIntegral_dilate G r T0 hr
      _ = r * ((∫ s in Ioi T0, Graw s) / r) := by simp_rw [hG, integral_div]
      _ = _ := by field_simp [hr.ne']
  have hcoef : (2 / (r * T)) * r = 2 / T := by
    rw [mul_comm r T, div_mul_eq_div_div, div_mul_cancel₀ _ hr.ne']
  have hcoef_mul (z : ℝ) : (2 / (r * T)) * (r * z) = (2 / T) * z := by
    rw [← mul_assoc, hcoef]
  change (2 / (r * T)) * (∫ t in (0 : ℝ)..r * T0, L t) +
      (2 / (r * T)) * (∫ t in r * T0..r * T, Q t) +
      2 * (∫ t in (0 : ℝ)..r * T0, P t) +
      (1 / Real.pi) * (∫ t in Ioi (r * T0), G t) =
    (2 / T) * (∫ s in (0 : ℝ)..T0, Lraw s) +
      (2 / T) * (∫ s in T0..T, Qraw s) +
      2 * (∫ s in (0 : ℝ)..T0, Praw s) +
      (1 / Real.pi) * (∫ s in Ioi T0, Graw s)
  rw [hLint, hQint, hPint, hGint]
  simp only [hcoef_mul]

theorem raw_actual_cdf_le (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (n : ℕ) (hn : 0 < n) (T0 T : ℝ) (hT0 : 0 < T0) (hcut : T0 ≤ T) (H : ℝ) :
    |(MixtureSum.iidSumLaw (μ : Measure ℝ) n).real (Iic H) -
      GaussianTools.Phi (H / Real.sqrt n)| ≤ rawEnvelope μ n T0 T := by
  have hr : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  have h := normalized_actual_cdf_le μ hμ n hn (Real.sqrt n * T0) (Real.sqrt n * T)
    (mul_pos hr hT0) (mul_le_mul_of_nonneg_left hcut hr.le) (H / Real.sqrt n)
  have hphase : Real.sqrt n * (H / Real.sqrt n) = H := by field_simp [hr.ne']
  rw [Extremizer.normalized_closedCDF μ n hn, hphase,
    Extremizer.coe_iidSumProbability, normalizedEnvelope_scale_eq_raw μ n hn] at h
  exact h

end BerryEsseen.PrawitzSmoothing

#print axioms BerryEsseen.PrawitzSmoothing.normalizedIidSumLaw_eq_raw_map
#print axioms BerryEsseen.PrawitzSmoothing.integrable_normalizedIidSumLaw
#print axioms BerryEsseen.PrawitzSmoothing.charFun_normalizedIidSumLaw
#print axioms BerryEsseen.PrawitzSmoothing.normalized_actual_cdf_le
#print axioms BerryEsseen.PrawitzSmoothing.normalizedEnvelope_scale_eq_raw
#print axioms BerryEsseen.PrawitzSmoothing.raw_actual_cdf_le
