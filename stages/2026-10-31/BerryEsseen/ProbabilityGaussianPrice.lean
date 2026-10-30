module

public import BerryEsseen.ConditionalResidual
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp

@[expose] public section

/-! 2026-10-28: probability derivatives of the actual canonical Gaussian price.
The noise s and phase t are fixed along each probability slice. Substituting
one law's canonical noise identifies its price value; no variation of that law
with its noise held artificially fixed is asserted. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace BerryEsseen.ProbabilityGaussianPrice

open GaussianTools

def numerator (n k : ℕ) (t p : ℝ) : ℝ := (k : ℝ) + t - (n : ℝ) * p

def variance (n : ℕ) (s p : ℝ) : ℝ := (n : ℝ) * (p * (1 - p) + s)

def varianceSlope (n : ℕ) (p : ℝ) : ℝ := (n : ℝ) * (1 - 2 * p)

def argument (n k : ℕ) (t s p : ℝ) : ℝ :=
  numerator n k t p / Real.sqrt (variance n s p)

def argumentSlope (n k : ℕ) (t s p : ℝ) : ℝ :=
  -(n : ℝ) / Real.sqrt (variance n s p) -
    numerator n k t p * varianceSlope n p /
      (2 * variance n s p * Real.sqrt (variance n s p))

def argumentCurvature (n k : ℕ) (t s p : ℝ) : ℝ :=
  (n : ℝ) * varianceSlope n p / (variance n s p * Real.sqrt (variance n s p)) +
  (n : ℝ) * numerator n k t p / (variance n s p * Real.sqrt (variance n s p)) +
  3 * numerator n k t p * (varianceSlope n p) ^ 2 /
    (4 * (variance n s p) ^ 2 * Real.sqrt (variance n s p))

def gaussianPrice (n k : ℕ) (t s p : ℝ) : ℝ := Phi (argument n k t s p)

def gaussianPriceSlope (n k : ℕ) (t s p : ℝ) : ℝ :=
  phi (argument n k t s p) * argumentSlope n k t s p

def gaussianPriceCurvature (n k : ℕ) (t s p : ℝ) : ℝ :=
  phi (argument n k t s p) *
    (argumentCurvature n k t s p - argument n k t s p * (argumentSlope n k t s p) ^ 2)

lemma variance_pos {n : ℕ} {s p : ℝ} (hn : 0 < n) (hs : 0 ≤ s) (hp : p ∈ Ioo 0 1) :
    0 < variance n s p := by
  exact mul_pos (Nat.cast_pos.mpr hn) (add_pos_of_pos_of_nonneg (mul_pos hp.1 (sub_pos.mpr hp.2)) hs)

lemma hasDerivAt_numerator (n k : ℕ) (t p : ℝ) :
    HasDerivAt (numerator n k t) (-(n : ℝ)) p := by
  change HasDerivAt (fun q : ℝ => (k : ℝ) + t - (n : ℝ) * q) _ p
  convert (hasDerivAt_const p ((k : ℝ) + t)).fun_sub ((hasDerivAt_id' p).const_mul (n : ℝ)) using 1
  ring

lemma hasDerivAt_variance (n : ℕ) (s p : ℝ) :
    HasDerivAt (variance n s) (varianceSlope n p) p := by
  change HasDerivAt (fun q : ℝ => (n : ℝ) * (q * (1 - q) + s)) _ p
  have h := (((hasDerivAt_id' p).fun_mul
    ((hasDerivAt_const p (1 : ℝ)).fun_sub (hasDerivAt_id' p))).add_const s).const_mul (n : ℝ)
  convert h using 1
  dsimp only [varianceSlope]
  ring

lemma hasDerivAt_varianceSlope (n : ℕ) (p : ℝ) :
    HasDerivAt (varianceSlope n) (-2 * (n : ℝ)) p := by
  change HasDerivAt (fun q : ℝ => (n : ℝ) * (1 - 2 * q)) _ p
  convert ((hasDerivAt_const p (1 : ℝ)).fun_sub
    ((hasDerivAt_id' p).const_mul 2)).const_mul (n : ℝ) using 1
  ring

/-- The first threshold derivative is for the same N/sqrt(V) function. -/
theorem argument_hasDerivAt {n k : ℕ} {t s p : ℝ}
    (hn : 0 < n) (hs : 0 ≤ s) (hp : p ∈ Ioo 0 1) :
    HasDerivAt (argument n k t s) (argumentSlope n k t s p) p := by
  have hv := variance_pos hn hs hp
  have hr := (Real.sqrt_pos.mpr hv).ne'
  have h := (hasDerivAt_numerator n k t p).fun_div
    ((hasDerivAt_variance n s p).sqrt hv.ne') hr
  change HasDerivAt (fun q => numerator n k t q / Real.sqrt (variance n s q)) _ p
  convert h using 1
  dsimp only [argumentSlope]
  generalize hveq : variance n s p = v
  generalize hreq : Real.sqrt v = r
  have hrne : r ≠ 0 := by rw [← hreq, ← hveq]; exact hr
  have hsq : r ^ 2 = v := by
    rw [← hreq]
    exact Real.sq_sqrt (by rw [← hveq]; exact hv.le)
  rw [← hsq]
  field_simp [hrne]

/-- All denominators stay positive on the whole probability interval. -/
theorem argument_contDiffOn {n k : ℕ} {t s : ℝ} (hn : 0 < n) (hs : 0 ≤ s) :
    ContDiffOn ℝ 2 (argument n k t s) (Ioo 0 1) := by
  have hN : ContDiffOn ℝ 2 (numerator n k t) (Ioo 0 1) := by unfold numerator; fun_prop
  have hV : ContDiffOn ℝ 2 (variance n s) (Ioo 0 1) := by unfold variance; fun_prop
  exact hN.div (hV.sqrt (fun p hp => (variance_pos hn hs hp).ne'))
    (fun p hp => (Real.sqrt_pos.mpr (variance_pos hn hs hp)).ne')

/-- The explicit first derivative itself has the stated second derivative. -/
theorem argumentSlope_hasDerivAt {n k : ℕ} {t s p : ℝ}
    (hn : 0 < n) (hs : 0 ≤ s) (hp : p ∈ Ioo 0 1) :
    HasDerivAt (argumentSlope n k t s) (argumentCurvature n k t s p) p := by
  have hv := variance_pos hn hs hp
  have hr := (Real.sqrt_pos.mpr hv).ne'
  have hV := hasDerivAt_variance n s p
  have hR := hV.sqrt hv.ne'
  have hN := hasDerivAt_numerator n k t p
  have hVp := hasDerivAt_varianceSlope n p
  have hfirst := (hasDerivAt_const p (-(n : ℝ))).fun_div hR hr
  have hsecond := (hN.fun_mul hVp).fun_div ((hV.const_mul 2).fun_mul hR)
    (mul_ne_zero (mul_ne_zero (by norm_num) hv.ne') hr)
  change HasDerivAt (fun q => -(n : ℝ) / Real.sqrt (variance n s q) -
    numerator n k t q * varianceSlope n q / (2 * variance n s q * Real.sqrt (variance n s q))) _ p
  convert hfirst.fun_sub hsecond using 1
  dsimp only [argumentCurvature]
  generalize hveq : variance n s p = v
  generalize hreq : Real.sqrt v = r
  have hrne : r ≠ 0 := by rw [← hreq, ← hveq]; exact hr
  have hsq : r ^ 2 = v := by
    rw [← hreq]
    exact Real.sq_sqrt (by rw [← hveq]; exact hv.le)
  rw [← hsq]
  field_simp [hrne]
  ring

/-- Native second derivative existence, rather than a default derivative value. -/
theorem argument_hasDerivAt_deriv {n k : ℕ} {t s p : ℝ}
    (hn : 0 < n) (hs : 0 ≤ s) (hp : p ∈ Ioo 0 1) :
    HasDerivAt (deriv (argument n k t s)) (argumentCurvature n k t s p) p := by
  have heq : deriv (argument n k t s) =ᶠ[𝓝 p] argumentSlope n k t s := by
    filter_upwards [isOpen_Ioo.mem_nhds hp] with q hq
    exact (argument_hasDerivAt hn hs hq).deriv
  exact (argumentSlope_hasDerivAt hn hs hp).congr_of_eventuallyEq heq

private lemma phi_contDiff_one : ContDiff ℝ 1 phi := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun x => (hasDerivAt_phi x).differentiableAt, ?_⟩
  have heq : deriv phi = (fun x => -x * phi x) := funext (fun x => (hasDerivAt_phi x).deriv)
  rw [heq]
  exact continuous_id.neg.mul continuous_phi

private lemma Phi_contDiff_two : ContDiff ℝ 2 Phi := by
  apply (contDiff_succ_iff_deriv (n := 1)).mpr
  refine ⟨fun x => (hasDerivAt_Phi x).differentiableAt, by simp, ?_⟩
  have heq : deriv Phi = phi := funext (fun x => (hasDerivAt_Phi x).deriv)
  rw [heq]
  exact phi_contDiff_one

/-- C² for the actual Gaussian measure's closed CDF price on (0,1). -/
theorem gaussianPrice_contDiffOn {n k : ℕ} {t s : ℝ} (hn : 0 < n) (hs : 0 ≤ s) :
    ContDiffOn ℝ 2 (gaussianPrice n k t s) (Ioo 0 1) :=
  Phi_contDiff_two.fun_comp_contDiffOn (argument_contDiffOn hn hs)

theorem gaussianPrice_hasDerivAt {n k : ℕ} {t s p : ℝ}
    (hn : 0 < n) (hs : 0 ≤ s) (hp : p ∈ Ioo 0 1) :
    HasDerivAt (gaussianPrice n k t s) (gaussianPriceSlope n k t s p) p :=
  (hasDerivAt_Phi (argument n k t s p)).comp p (argument_hasDerivAt hn hs hp)

theorem gaussianPriceSlope_hasDerivAt {n k : ℕ} {t s p : ℝ}
    (hn : 0 < n) (hs : 0 ≤ s) (hp : p ∈ Ioo 0 1) :
    HasDerivAt (gaussianPriceSlope n k t s) (gaussianPriceCurvature n k t s p) p := by
  have hphi := (hasDerivAt_phi (argument n k t s p)).comp p (argument_hasDerivAt hn hs hp)
  have h := hphi.fun_mul (argumentSlope_hasDerivAt (k := k) (t := t) hn hs hp)
  change HasDerivAt (fun q => phi (argument n k t s q) * argumentSlope n k t s q) _ p
  convert h using 1 <;> simp only [gaussianPriceCurvature, Function.comp_apply] <;> ring

theorem gaussianPrice_hasDerivAt_deriv {n k : ℕ} {t s p : ℝ}
    (hn : 0 < n) (hs : 0 ≤ s) (hp : p ∈ Ioo 0 1) :
    HasDerivAt (deriv (gaussianPrice n k t s)) (gaussianPriceCurvature n k t s p) p := by
  have heq : deriv (gaussianPrice n k t s) =ᶠ[𝓝 p] gaussianPriceSlope n k t s := by
    filter_upwards [isOpen_Ioo.mem_nhds hp] with q hq
    exact (gaussianPrice_hasDerivAt hn hs hq).deriv
  exact (gaussianPriceSlope_hasDerivAt hn hs hp).congr_of_eventuallyEq heq

/-- The original canonical threshold uses exactly this variance, since its
canonical scale is sqrt(p*q+s), not an independently supplied adapter. -/
theorem canonicalThreshold_eq_argument (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (n k : ℕ) (t : ℝ) :
    ConditionalResidual.canonicalThreshold μ hμ n k t =
      argument n k t (CanonicalSign.noiseVariance μ hμ) (CanonicalSign.p μ) := by
  unfold ConditionalResidual.canonicalThreshold argument numerator variance
  rw [CanonicalSign.scale_eq_sqrt]
  simp only [CanonicalSign.q]
  rw [Real.sqrt_mul (Nat.cast_nonneg n)]
  congr 1
  ring

/-- Fixing μ here selects its actual noise level. The variable is only p. -/
def actualNoiseSlice (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (n k : ℕ) (t : ℝ) : ℝ → ℝ :=
  gaussianPrice n k t (CanonicalSign.noiseVariance μ hμ)

theorem actualNoiseSlice_at_actualp (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (n k : ℕ) (t : ℝ) :
    actualNoiseSlice μ hμ n k t (CanonicalSign.p μ) =
      Phi (ConditionalResidual.canonicalThreshold μ hμ n k t) := by
  unfold actualNoiseSlice gaussianPrice
  rw [canonicalThreshold_eq_argument]

theorem actualNoiseSlice_contDiffOn (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (n k : ℕ) (hn : 0 < n) (t : ℝ) :
    ContDiffOn ℝ 2 (actualNoiseSlice μ hμ n k t) (Ioo 0 1) :=
  gaussianPrice_contDiffOn hn (CanonicalSign.noiseVariance_nonneg μ hμ)

theorem actualNoiseSlice_hasDerivAt (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (n k : ℕ) (hn : 0 < n) (t : ℝ) :
    HasDerivAt (actualNoiseSlice μ hμ n k t)
      (gaussianPriceSlope n k t (CanonicalSign.noiseVariance μ hμ) (CanonicalSign.p μ))
      (CanonicalSign.p μ) :=
  gaussianPrice_hasDerivAt hn (CanonicalSign.noiseVariance_nonneg μ hμ)
    ⟨CanonicalSign.p_pos μ hμ, CanonicalSign.p_lt_one μ hμ⟩

theorem actualNoiseSlice_hasDerivAt_deriv (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (n k : ℕ) (hn : 0 < n) (t : ℝ) :
    HasDerivAt (deriv (actualNoiseSlice μ hμ n k t))
      (gaussianPriceCurvature n k t (CanonicalSign.noiseVariance μ hμ) (CanonicalSign.p μ))
      (CanonicalSign.p μ) :=
  gaussianPrice_hasDerivAt_deriv hn (CanonicalSign.noiseVariance_nonneg μ hμ)
    ⟨CanonicalSign.p_pos μ hμ, CanonicalSign.p_lt_one μ hμ⟩

end BerryEsseen.ProbabilityGaussianPrice

#print axioms BerryEsseen.ProbabilityGaussianPrice.argument_hasDerivAt
#print axioms BerryEsseen.ProbabilityGaussianPrice.argument_hasDerivAt_deriv
#print axioms BerryEsseen.ProbabilityGaussianPrice.gaussianPrice_contDiffOn
#print axioms BerryEsseen.ProbabilityGaussianPrice.gaussianPrice_hasDerivAt_deriv
#print axioms BerryEsseen.ProbabilityGaussianPrice.canonicalThreshold_eq_argument
#print axioms BerryEsseen.ProbabilityGaussianPrice.actualNoiseSlice_at_actualp
#print axioms BerryEsseen.ProbabilityGaussianPrice.actualNoiseSlice_hasDerivAt_deriv



