module

public import BerryEsseen.Target
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

@[expose] public section

/-! 2026-10-28: Gaussian analysis for the actual standard Gaussian measure in
Target. The CDF is its closed CDF, and the density and truncated moments are
connected to the official Gaussian probability measure by actual integrals. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace BerryEsseen.GaussianTools

/-- The standard density of the same Gaussian measure used by Target. -/
def phi : ℝ → ℝ := gaussianPDFReal 0 1

/-- The real closed CDF of Target's actual standard Gaussian measure. -/
def Phi (t : ℝ) : ℝ := (gaussianReal 0 1).real (Iic t)

lemma phi_formula (t : ℝ) :
    phi t = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(t ^ 2) / 2) := by
  simp [phi, gaussianPDFReal]

lemma phi_pos (t : ℝ) : 0 < phi t := gaussianPDFReal_pos 0 1 t one_ne_zero
lemma phi_nonneg (t : ℝ) : 0 ≤ phi t := le_of_lt (phi_pos t)

/-- The standard density derivative is proved from the exponential formula. -/
theorem hasDerivAt_phi (t : ℝ) : HasDerivAt phi (-t * phi t) t := by
  have hinner : HasDerivAt (fun x : ℝ => -(x ^ 2) / 2) (-t) t := by
    convert (((hasDerivAt_id' t).fun_pow 2).fun_neg.div_const 2) using 1
    ring
  have h := hinner.exp.const_mul (Real.sqrt (2 * Real.pi))⁻¹
  convert h using 1
  · ext x
    exact phi_formula x
  · rw [phi_formula]
    ring

lemma continuous_phi : Continuous phi :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_phi t).continuousAt

lemma integrable_phi : Integrable phi := integrable_gaussianPDFReal 0 1

lemma integral_phi : (∫ u : ℝ, phi u) = 1 :=
  integral_gaussianPDFReal_eq_one 0 one_ne_zero

/-- The official with-density formula identifies the actual closed Gaussian CDF. -/
theorem Phi_eq_integral_Iic (t : ℝ) : Phi t = ∫ u in Iic t, phi u := by
  change ((gaussianReal 0 1) (Iic t)).toReal = ∫ u in Iic t, phi u
  rw [gaussianReal_apply_eq_integral 0 one_ne_zero (Iic t)]
  exact ENNReal.toReal_ofReal (integral_nonneg fun u => gaussianPDFReal_nonneg 0 1 u)

/-- The complementary open upper tail is the integral of the actual density. -/
theorem integral_phi_Ioi (t : ℝ) : (∫ u in Ioi t, phi u) = 1 - Phi t := by
  have h := integral_add_compl (s := Iic t) measurableSet_Iic integrable_phi
  rw [compl_Iic, integral_phi, ← Phi_eq_integral_Iic] at h
  linarith

lemma Phi_eq_const_add_intervalIntegral (t : ℝ) :
    Phi t = Phi 0 + ∫ u in (0 : ℝ)..t, phi u := by
  have h := intervalIntegral.integral_Iic_sub_Iic
    (a := (0 : ℝ)) (b := t) integrable_phi.integrableOn integrable_phi.integrableOn
  rw [← Phi_eq_integral_Iic, ← Phi_eq_integral_Iic] at h
  linarith

/-- The derivative belongs to the actual closed CDF, rather than a formal primitive. -/
theorem hasDerivAt_Phi (t : ℝ) : HasDerivAt Phi (phi t) t := by
  have heq : Phi = (fun x : ℝ => Phi 0 + ∫ u in (0 : ℝ)..x, phi u) :=
    funext Phi_eq_const_add_intervalIntegral
  rw [heq]
  exact ((continuous_phi.integral_hasStrictDerivAt 0 t).hasDerivAt).const_add (Phi 0)

end BerryEsseen.GaussianTools

#print axioms BerryEsseen.GaussianTools.hasDerivAt_phi
#print axioms BerryEsseen.GaussianTools.Phi_eq_integral_Iic
#print axioms BerryEsseen.GaussianTools.hasDerivAt_Phi

namespace BerryEsseen.GaussianTools

/-- Every polynomially weighted density used by the Peano interchanges is integrable. -/
lemma integrable_pow_mul_phi (n : ℕ) : Integrable (fun x : ℝ => x ^ n * phi x) := by
  have hs : (-1 : ℝ) < (n : ℝ) :=
    lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg n)
  have hbase : Integrable (fun x : ℝ => x ^ n * Real.exp (-(1 / 2 : ℝ) * x ^ 2)) := by
    simpa only [Real.rpow_natCast] using
      (integrable_rpow_mul_exp_neg_mul_sq (b := (1 / 2 : ℝ)) (s := (n : ℝ))
        (by norm_num) hs)
  convert hbase.const_mul (Real.sqrt (2 * Real.pi))⁻¹ using 1
  ext x
  rw [phi_formula]
  have he : -(x ^ 2) / 2 = -(1 / 2 : ℝ) * x ^ 2 := by ring
  rw [he]
  ring

lemma integrable_mul_phi : Integrable (fun x : ℝ => x * phi x) := by
  simpa only [pow_one] using integrable_pow_mul_phi 1

lemma integrable_sq_mul_phi : Integrable (fun x : ℝ => x ^ 2 * phi x) :=
  integrable_pow_mul_phi 2

lemma hasDerivAt_mul_phi (t : ℝ) :
    HasDerivAt (fun x : ℝ => x * phi x) (phi t - t ^ 2 * phi t) t := by
  convert (hasDerivAt_id' t).fun_mul (hasDerivAt_phi t) using 1
  ring

/-- Boundary decay follows from actual integrability of the density and its derivative. -/
lemma tendsto_phi_atTop : Tendsto phi atTop (𝓝 (0 : ℝ)) := by
  have hn : Integrable (fun x : ℝ => -(x * phi x)) := integrable_mul_phi.neg
  have hd : Integrable (fun x : ℝ => -x * phi x) := by
    simpa only [neg_mul] using hn
  exact tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi (a := 0)
    (fun x _ => hasDerivAt_phi x) hd.integrableOn integrable_phi.integrableOn

/-- The boundary term in the second truncated moment vanishes at infinity. -/
lemma tendsto_mul_phi_atTop : Tendsto (fun x : ℝ => x * phi x) atTop (𝓝 (0 : ℝ)) := by
  have hd : Integrable (fun x : ℝ => phi x - x ^ 2 * phi x) :=
    integrable_phi.sub integrable_sq_mul_phi
  exact tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi (a := 0)
    (fun x _ => hasDerivAt_mul_phi x) hd.integrableOn integrable_mul_phi.integrableOn

/-- The first truncated moment of the actual standard Gaussian density. -/
theorem integral_mul_phi_Ioi (t : ℝ) : (∫ u in Ioi t, u * phi u) = phi t := by
  have hderiv : ∀ x ∈ Ici t, HasDerivAt (fun u : ℝ => -phi u) (x * phi x) x := by
    intro x _
    convert (hasDerivAt_phi x).fun_neg using 1
    ring
  have hz : Tendsto (fun x : ℝ => -phi x) atTop (𝓝 (0 : ℝ)) := by
    simpa only [neg_zero] using tendsto_phi_atTop.neg
  simpa only [zero_sub, neg_neg] using integral_Ioi_of_hasDerivAt_of_tendsto'
    hderiv integrable_mul_phi.integrableOn hz

/-- The second truncated moment, with the tail expressed using the actual closed CDF. -/
theorem integral_sq_mul_phi_Ioi (t : ℝ) :
    (∫ u in Ioi t, u ^ 2 * phi u) = t * phi t + 1 - Phi t := by
  have hi0 : IntegrableOn phi (Ioi t) := integrable_phi.integrableOn
  have hi2 : IntegrableOn (fun x : ℝ => x ^ 2 * phi x) (Ioi t) :=
    integrable_sq_mul_phi.integrableOn
  have hd : IntegrableOn (fun x : ℝ => phi x - x ^ 2 * phi x) (Ioi t) := hi0.sub hi2
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun x _ => hasDerivAt_mul_phi x) hd tendsto_mul_phi_atTop
  rw [integral_sub hi0 hi2, integral_phi_Ioi] at h
  linarith

lemma deriv_phi (t : ℝ) : deriv phi t = -t * phi t := (hasDerivAt_phi t).deriv
lemma deriv_Phi (t : ℝ) : deriv Phi t = phi t := (hasDerivAt_Phi t).deriv

end BerryEsseen.GaussianTools

#print axioms BerryEsseen.GaussianTools.integrable_pow_mul_phi
#print axioms BerryEsseen.GaussianTools.integral_mul_phi_Ioi
#print axioms BerryEsseen.GaussianTools.integral_sq_mul_phi_Ioi
