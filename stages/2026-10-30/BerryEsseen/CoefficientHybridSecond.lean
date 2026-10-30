module

public import BerryEsseen.CoefficientRaySpectral
public import BerryEsseen.ClassicalThreeHalvesCosine

@[expose] public section

/-! 2026-10-29: strengthen only the second Prawitz term for the same actual
iid law. The first coarse error price, its residual-power loss, the kernel
correction and the Gaussian tail are unchanged. The new second term is a
positive p=1/2 power-exponential kernel in fixed spectral coordinates. All
four terms use common interpolation weights, so the endpoint maximum is
taken over this hybrid profile's own endpoints. No numerical profile value
or finite-grid argument is an input. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Interval Topology

namespace BerryEsseen.CoefficientHybridSecond

open HighMomentRayDamping
open RaySpectralCurvature (powerExp powerExp_half_scale spectralKernelWeight
  thirdSpectralIntegrand fourthSpectralIntegrand KernelEndpointBound kernelEndpointBound_log_chord
  actualFirstSpectralIntegrand actualSecondSpectralIntegrand actualSpectralProfile
  normalizedEnvelope_div_beta_eq_actualSpectralProfile)
open Causalean.Stat.CLT.BerryEsseen (prawitzKernel)

def spectralExponent2 (c v : ℝ) : ℝ :=
  min (CoefficientRaySpectral.spectralExponent c v)
    (CoefficientRayPrice.exponent c ClassicalThreeHalvesCosine.a ClassicalThreeHalvesCosine.b 1 v)

def physicalQ (c β t : ℝ) : ℝ :=
  min (CoefficientRayPrice.envelope c β t)
    (Real.exp (CoefficientRayPrice.exponent c ClassicalThreeHalvesCosine.a ClassicalThreeHalvesCosine.b β t))

private lemma exp_min (x y : ℝ) : Real.exp (min x y) = min (Real.exp x) (Real.exp y) := by
  rcases le_total x y with h | h
  · rw [min_eq_left h, min_eq_left (Real.exp_le_exp.mpr h)]
  · rw [min_eq_right h, min_eq_right (Real.exp_le_exp.mpr h)]

private lemma new_branch_power (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (hn : 0 < n) (c : ℝ)
    (hC : thirdAbsoluteMoment μ + 1 ≤ c * thirdAbsoluteMoment μ) (t : ℝ) :
    ‖charFun (μ : Measure ℝ) (t / Real.sqrt n)‖ ^ n ≤
      Real.exp (CoefficientRayPrice.exponent c ClassicalThreeHalvesCosine.a
        ClassicalThreeHalvesCosine.b (beta μ n) t) := by
  let r : ℝ := Real.sqrt n
  let e : ℝ := -ClassicalThreeHalvesCosine.a * (t / r) ^ 2 +
    ClassicalThreeHalvesCosine.b * (thirdAbsoluteMoment μ + 1) * |t / r| ^ 3
  have hr : 0 < r := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  have hr2 : r ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
  have hq : ‖charFun (μ : Measure ℝ) (t / r)‖ ≤ Real.exp e := by
    apply (sq_le_sq₀ (norm_nonneg _) (Real.exp_nonneg e)).mp
    rw [← Real.exp_nat_mul]
    norm_num only [Nat.cast_ofNat]
    have hh := ClassicalThreeHalvesCosine.charFun_norm_sq_le μ h (t / r)
    have hp : ‖charFun (μ : Measure ℝ) (t / r)‖ ^ 2 ≤ 1 + 2 * e := by
      dsimp [e, ClassicalThreeHalvesCosine.polynomial] at *
      nlinarith only [hh]
    exact hp.trans (by linarith [Real.add_one_le_exp (2 * e)])
  have heq : (n : ℝ) * e = -ClassicalThreeHalvesCosine.a * t ^ 2 +
      ClassicalThreeHalvesCosine.b * ((thirdAbsoluteMoment μ + 1) / r) * |t| ^ 3 := by
    dsimp [e]
    rw [abs_div, abs_of_pos hr, div_pow, div_pow, ← hr2]
    field_simp [hr.ne']
  have hd := div_le_div_of_nonneg_right hC hr.le
  have hm := mul_le_mul_of_nonneg_left hd
    (mul_nonneg ClassicalThreeHalvesCosine.b_nonneg (by positivity : 0 ≤ |t| ^ 3))
  have hE : (n : ℝ) * e ≤ CoefficientRayPrice.exponent c ClassicalThreeHalvesCosine.a
      ClassicalThreeHalvesCosine.b (beta μ n) t := by
    rw [heq]
    dsimp [CoefficientRayPrice.exponent, beta]
    convert add_le_add_left hm (-ClassicalThreeHalvesCosine.a * t ^ 2) using 1 <;> ring
  have hp := pow_le_pow_left₀ (norm_nonneg _) hq n
  rw [← Real.exp_nat_mul] at hp
  exact hp.trans (Real.exp_le_exp.mpr hE)

/-- Both alternatives bound the same original CF at the same frequency. -/
theorem normalized_power_le_physicalQ (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (hn : 0 < n) (c : ℝ)
    (hC : thirdAbsoluteMoment μ + 1 ≤ c * thirdAbsoluteMoment μ) (t : ℝ) :
    ‖charFun (μ : Measure ℝ) (t / Real.sqrt n)‖ ^ n ≤ physicalQ c (beta μ n) t :=
  le_min (CoefficientRayPrice.normalized_power_le_envelope μ h n hn c hC t)
    (new_branch_power μ h n hn c hC t)

lemma continuous_spectralExponent2 (c : ℝ) : Continuous (spectralExponent2 c) := by
  exact (CoefficientRaySpectral.continuous_spectralExponent c).min (by
    unfold CoefficientRayPrice.exponent
    fun_prop)

lemma spectralExponent2_nonpos (c v : ℝ) : spectralExponent2 c v ≤ 0 :=
  (min_le_left _ _).trans (CoefficientRaySpectral.spectralExponent_nonpos c v)

private lemma exponent_scale (c a b β v : ℝ) (hβ : 0 < β) :
    CoefficientRayPrice.exponent c a b β (v / β) =
      (1 / β ^ 2) * CoefficientRayPrice.exponent c a b 1 v := by
  unfold CoefficientRayPrice.exponent
  rw [abs_div, abs_of_pos hβ, div_pow, div_pow]
  field_simp [hβ.ne']

theorem physicalQ_spectral_eq (c β v : ℝ) (hβ : 0 < β) :
    physicalQ c β (v / β) = Real.exp ((1 / β ^ 2) * spectralExponent2 c v) := by
  unfold physicalQ spectralExponent2
  rw [CoefficientRaySpectral.envelope_spectral_eq c β v hβ, exponent_scale _ _ _ _ _ hβ,
    mul_min_of_nonneg _ _ (by positivity : 0 ≤ 1 / β ^ 2)]
  exact (exp_min _ _).symm

def secondSpectralIntegrand (c V s v : ℝ) : ℝ :=
  spectralKernelWeight V v * powerExp (1 / 2) (-spectralExponent2 c v) s

def physicalSecond (c β U t : ℝ) : ℝ := ‖prawitzKernel (t / U)‖ * physicalQ c β t

theorem physicalSecond_scale (c β V v : ℝ) (hβ : 0 < β) :
    physicalSecond c β (V / β) (v / β) = β * secondSpectralIntegrand c V (1 / β ^ 2) v := by
  have hratio : (v / β) / (V / β) = v / V := by field_simp [hβ.ne']
  unfold physicalSecond secondSpectralIntegrand spectralKernelWeight
  rw [hratio, physicalQ_spectral_eq c β v hβ, powerExp_half_scale β _ hβ]
  have he : -(1 / β ^ 2) * (-spectralExponent2 c v) =
      (1 / β ^ 2) * spectralExponent2 c v := by ring
  rw [he]
  field_simp [hβ.ne']

/-- Exact oriented-integral substitution for the replaced term. K(1) and
all assigned endpoint values remain the original ones. -/
theorem physicalSecond_integral_scale (c β A V : ℝ) (hβ : 0 < β) :
    (∫ t in A / β..V / β, physicalSecond c β (V / β) t) =
      ∫ v in A..V, secondSpectralIntegrand c V (1 / β ^ 2) v := by
  have hh := intervalIntegral.integral_comp_div (a := A) (b := V)
    (physicalSecond c β (V / β)) hβ.ne'
  simp only [smul_eq_mul] at hh
  simp_rw [physicalSecond_scale c β V _ hβ] at hh
  rw [intervalIntegral.integral_const_mul] at hh
  exact (mul_left_cancel₀ hβ.ne' hh).symm

def hybridProfile (N : ℕ) (c A V s : ℝ) : ℝ :=
  (2 / V) * (∫ v in Ioc 0 A, CoefficientRaySpectral.firstSpectralIntegrand N c V s v) +
  (2 / V) * (∫ v in Ioc A V, secondSpectralIntegrand c V s v) +
  (2 / V) * (∫ v in Ioc 0 A, thirdSpectralIntegrand V s v) +
  (1 / Real.pi) * (∫ v in Ioi A, fourthSpectralIntegrand s v)

private lemma measurable_kernel (V : ℝ) : Measurable (spectralKernelWeight V) := by
  have heq : spectralKernelWeight V = CoefficientRaySpectral.secondSpectralIntegrand 0 V 0 := by
    funext v
    simp only [CoefficientRaySpectral.secondSpectralIntegrand, powerExp, Real.log_zero,
      mul_zero, zero_mul, sub_zero, Real.exp_zero, mul_one]
  rw [heq]
  exact CoefficientRaySpectral.measurable_secondSpectralIntegrand 0 V 0

lemma measurable_secondSpectralIntegrand (c V s : ℝ) : Measurable (secondSpectralIntegrand c V s) := by
  have hk := measurable_kernel V
  have hg := continuous_spectralExponent2 c
  unfold secondSpectralIntegrand powerExp
  fun_prop

lemma secondSpectralIntegrand_nonneg (c V s v : ℝ) : 0 ≤ secondSpectralIntegrand c V s v := by
  unfold secondSpectralIntegrand spectralKernelWeight
  exact mul_nonneg (norm_nonneg _) (RaySpectralCurvature.powerExp_pos _ _ _).le

private lemma second_le_old (c V s v : ℝ) (hs : 0 ≤ s) :
    secondSpectralIntegrand c V s v ≤ CoefficientRaySpectral.secondSpectralIntegrand c V s v := by
  unfold secondSpectralIntegrand CoefficientRaySpectral.secondSpectralIntegrand powerExp
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg (prawitzKernel (v / V)))
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left (min_le_left
    (CoefficientRaySpectral.spectralExponent c v)
    (CoefficientRayPrice.exponent c ClassicalThreeHalvesCosine.a ClassicalThreeHalvesCosine.b 1 v)) hs
  dsimp [spectralExponent2]
  nlinarith only [hh]

theorem second_integrable (N : ℕ) (hN : 0 < N) (c A V s : ℝ)
    (hA : 0 < A) (hAV : A ≤ V) (hs : 0 < s) :
    IntegrableOn (secondSpectralIntegrand c V s) (Ioc A V) := by
  have hI := CoefficientRaySpectral.profileIntegrable N hN c A V s hA hAV hs
  apply hI.second.mono' (measurable_secondSpectralIntegrand c V s).aestronglyMeasurable
  exact ae_of_all _ (fun v => by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (secondSpectralIntegrand_nonneg c V s v)] using
      second_le_old c V s v hs.le)

private lemma integral_le_of_domination {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f g : α → ℝ) (hf : AEStronglyMeasurable f μ) (hg : Integrable g μ)
    (hn : ∀ x, 0 ≤ f x) (hle : ∀ᵐ x ∂μ, f x ≤ g x) : (∫ x, f x ∂μ) ≤ ∫ x, g x ∂μ := by
  have hfi : Integrable f μ := hg.mono' hf (hle.mono (fun x hx => by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hn x)] using hx))
  exact integral_mono_ae hfi hg hle

theorem actualSpectralProfile_le_hybridProfile (μ : ProbabilityMeasure ℝ)
    (h : StandardizedLaw μ) (n N : ℕ) (hN : 0 < N) (hNn : N ≤ n)
    (hρ : rho0 ≤ thirdAbsoluteMoment μ) (c : ℝ)
    (hC : thirdAbsoluteMoment μ + 1 ≤ c * thirdAbsoluteMoment μ)
    (A V : ℝ) (hA : 0 < A) (hAV : A ≤ V) :
    actualSpectralProfile μ n (beta μ n) A V ≤ hybridProfile N c A V (1 / beta μ n ^ 2) := by
  let β := beta μ n
  have hn : 0 < n := lt_of_lt_of_le hN hNn
  have hβ : 0 < β := CoarseHighMomentRayPrice.beta_pos μ n hn hρ
  have hV : 0 < V := hA.trans_le hAV
  have hI := CoefficientRaySpectral.profileIntegrable N hN c A V (1 / β ^ 2) hA hAV (by positivity)
  have hI2 := second_integrable N hN c A V (1 / β ^ 2) hA hAV (by positivity)
  have hk := measurable_kernel V
  have h1meas : Measurable (actualFirstSpectralIntegrand μ n β V) := by
    unfold actualFirstSpectralIntegrand
    fun_prop
  have h2meas : Measurable (actualSecondSpectralIntegrand μ n β V) := by
    unfold actualSecondSpectralIntegrand
    fun_prop
  have h1 := integral_le_of_domination (volume.restrict (Ioc 0 A))
    (actualFirstSpectralIntegrand μ n β V) _ h1meas.aestronglyMeasurable hI.first
    (fun v => by unfold actualFirstSpectralIntegrand spectralKernelWeight; positivity) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
      have hh := CoefficientRayPrice.normalized_power_error_div_beta_le_coarsePrice
        μ h n N hN hNn hρ c hC (v / β) (div_nonneg hv.1.le hβ.le)
      rw [CoefficientRaySpectral.coarsePrice_spectral_eq N hN c β v hβ] at hh
      exact mul_le_mul_of_nonneg_left hh (norm_nonneg (prawitzKernel (v / V))))
  have h2 := integral_le_of_domination (volume.restrict (Ioc A V))
    (actualSecondSpectralIntegrand μ n β V) _ h2meas.aestronglyMeasurable hI2
    (fun v => by unfold actualSecondSpectralIntegrand spectralKernelWeight; positivity) (ae_of_all _ (fun v => by
      have hh := div_le_div_of_nonneg_right (normalized_power_le_physicalQ μ h n hn c hC (v / β)) hβ.le
      rw [physicalQ_spectral_eq c β v hβ] at hh
      have he : powerExp (1 / 2) (-spectralExponent2 c v) (1 / β ^ 2) =
          Real.exp ((1 / β ^ 2) * spectralExponent2 c v) / β := by
        rw [powerExp_half_scale β _ hβ]
        congr 2
        ring
      unfold actualSecondSpectralIntegrand secondSpectralIntegrand
      rw [he, norm_pow]
      exact mul_le_mul_of_nonneg_left hh (norm_nonneg (prawitzKernel (v / V)))))
  have h1' := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 2 / V)
  have h2' := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ 2 / V)
  change actualSpectralProfile μ n β A V ≤ hybridProfile N c A V (1 / β ^ 2)
  unfold actualSpectralProfile hybridProfile
  linarith only [h1', h2']

theorem normalized_actual_cdf_le_beta_hybridProfile (μ : ProbabilityMeasure ℝ)
    (h : StandardizedLaw μ) (n N : ℕ) (hN : 0 < N) (hNn : N ≤ n)
    (hρ : rho0 ≤ thirdAbsoluteMoment μ) (c : ℝ)
    (hC : thirdAbsoluteMoment μ + 1 ≤ c * thirdAbsoluteMoment μ)
    (A V : ℝ) (hA : 0 < A) (hAV : A ≤ V) (x : ℝ) :
    |(normalizedIidSumLaw μ n).real (Iic x) - GaussianTools.Phi x| ≤
      beta μ n * hybridProfile N c A V (1 / beta μ n ^ 2) := by
  have hn : 0 < n := lt_of_lt_of_le hN hNn
  have hβ := CoarseHighMomentRayPrice.beta_pos μ n hn hρ
  have hh := div_le_div_of_nonneg_right
    (PrawitzSmoothing.normalized_actual_cdf_le μ h n hn (A / beta μ n) (V / beta μ n)
      (div_pos hA hβ) (div_le_div_of_nonneg_right hAV hβ.le) x) hβ.le
  rw [normalizedEnvelope_div_beta_eq_actualSpectralProfile μ n (beta μ n) A V hβ hA hAV] at hh
  have hm := hh.trans (actualSpectralProfile_le_hybridProfile μ h n N hN hNn hρ c hC A V hA hAV)
  simpa only [mul_comm] using (div_le_iff₀ hβ).mp hm

private lemma integral_endpoint_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f fa fb : α → ℝ) (E l r : ℝ) (hfs : Integrable f μ) (hfa : Integrable fa μ) (hfb : Integrable fb μ)
    (hle : ∀ᵐ x ∂μ, f x ≤ E * (l * fa x + r * fb x)) :
    (∫ x, f x ∂μ) ≤ E * (l * (∫ x, fa x ∂μ) + r * (∫ x, fb x ∂μ)) := by
  have hd : Integrable (fun x => E * (l * fa x + r * fb x)) μ :=
    ((hfa.const_mul l).add (hfb.const_mul r)).const_mul E
  have hh := integral_mono_ae hfs hd hle
  simpa only [Pi.add_apply, integral_const_mul, integral_add (hfa.const_mul l) (hfb.const_mul r)] using hh

/-- One common positive-Laplace bound controls T2/T3/T4 and the original
T1 core. Endpoints on the right belong to this same hybrid profile. -/
theorem hybridProfile_endpoint_of_core (N : ℕ) (hN : 0 < N)
    (c A V a b s E l r : ℝ) (hA : 0 < A) (hAV : A ≤ V) (ha : 0 < a) (hb : 0 < b) (hs : 0 < s)
    (hc : ∀ v w : ℝ, 0 ≤ v → 0 ≤ w → w ≤ v → CoefficientRaySpectral.coarseSpectralCore N c s v w ≤
      E * (l * CoefficientRaySpectral.coarseSpectralCore N c a v w + r * CoefficientRaySpectral.coarseSpectralCore N c b v w))
    (hk : ∀ R : ℝ, powerExp (1 / 2) R s ≤ E * (l * powerExp (1 / 2) R a + r * powerExp (1 / 2) R b)) :
    hybridProfile N c A V s ≤ E * (l * hybridProfile N c A V a + r * hybridProfile N c A V b) := by
  have hV : 0 < V := hA.trans_le hAV
  have hIa := CoefficientRaySpectral.profileIntegrable N hN c A V a hA hAV ha
  have hIb := CoefficientRaySpectral.profileIntegrable N hN c A V b hA hAV hb
  have hIs := CoefficientRaySpectral.profileIntegrable N hN c A V s hA hAV hs
  have h1 := integral_endpoint_le (volume.restrict (Ioc 0 A)) _ _ _ E l r hIs.first hIa.first hIb.first (by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    have hh := CoefficientRaySpectral.coarseSpectralSlice_endpoint N c a b s E l r v hv.1.le
      (fun w hw hwv => hc v w hv.1.le hw hwv)
    have hm := mul_le_mul_of_nonneg_left hh (norm_nonneg (prawitzKernel (v / V)))
    unfold CoefficientRaySpectral.firstSpectralIntegrand spectralKernelWeight
    convert hm using 1
    ring)
  have h2 := integral_endpoint_le (volume.restrict (Ioc A V)) _ _ _ E l r
    (second_integrable N hN c A V s hA hAV hs) (second_integrable N hN c A V a hA hAV ha)
    (second_integrable N hN c A V b hA hAV hb) (ae_of_all _ (fun v => by
      have hh := mul_le_mul_of_nonneg_left (hk (-spectralExponent2 c v)) (norm_nonneg (prawitzKernel (v / V)))
      unfold secondSpectralIntegrand spectralKernelWeight
      convert hh using 1
      ring))
  have h3 := integral_endpoint_le (volume.restrict (Ioc 0 A)) _ _ _ E l r hIs.third hIa.third hIb.third (ae_of_all _ (fun v => by
    have hh := mul_le_mul_of_nonneg_left (hk (v ^ 2 / 2)) (norm_nonneg (prawitzKernel (v / V) - Complex.I / ((2 * Real.pi * (v / V) : ℝ) : ℂ)))
    unfold thirdSpectralIntegrand RaySpectralCurvature.spectralCorrectionWeight
    convert hh using 1
    ring))
  have h4 := integral_endpoint_le (volume.restrict (Ioi A)) _ _ _ E l r hIs.fourth hIa.fourth hIb.fourth (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    have hh := div_le_div_of_nonneg_right (hk (v ^ 2 / 2)) (hA.trans hv).le
    unfold fourthSpectralIntegrand
    convert hh using 1
    ring)
  have h1' := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 2 / V)
  have h2' := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ 2 / V)
  have h3' := mul_le_mul_of_nonneg_left h3 (by positivity : 0 ≤ 2 / V)
  have h4' := mul_le_mul_of_nonneg_left h4 (by positivity : 0 ≤ 1 / Real.pi)
  unfold hybridProfile
  nlinarith only [h1', h2', h3', h4']

private lemma mixture_le_max (a b s x y : ℝ) (hab : a < b) (hs : s ∈ Icc a b) :
    ((b - s) / (b - a)) * x + ((s - a) / (b - a)) * y ≤ max x y := by
  have hl := div_nonneg (sub_nonneg.mpr hs.2) (sub_pos.mpr hab).le
  have hr := div_nonneg (sub_nonneg.mpr hs.1) (sub_pos.mpr hab).le
  calc
    _ ≤ ((b - s) / (b - a)) * max x y + ((s - a) / (b - a)) * max x y :=
      add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) hl) (mul_le_mul_of_nonneg_left (le_max_right _ _) hr)
    _ = _ := by field_simp [(sub_pos.mpr hab).ne']; ring

theorem hybridProfile_le_const_endpoint_max (N : ℕ) (hN : 0 < N)
    (c A V a b s : ℝ) (hA : 0 < A) (hAV : A ≤ V) (ha : 0 < a) (hab : a < b)
    (hs : s ∈ Icc a b) (hbranch : (N : ℝ) / rho0 ^ 2 ≤ a) :
    hybridProfile N c A V s ≤ Real.exp ((3 / 2) * ((b - a) ^ 2 / (8 * a ^ 2))) *
      max (hybridProfile N c A V a) (hybridProfile N c A V b) := by
  have hk := kernelEndpointBound_log_chord a b s (3 / 2) ha hab hs
  have hh := hybridProfile_endpoint_of_core N hN c A V a b s _ _ _ hA hAV ha (ha.trans hab) (ha.trans_le hs.1)
    (fun v w _ hw _ => CoefficientRaySpectral.coarseSpectralCore_endpoint_const N hN c a b s _ _ _ v w
      ha (ha.trans hab) (ha.trans_le hs.1) hw hbranch (hbranch.trans hab.le) (hbranch.trans hs.1) hk)
    (fun R => hk (1 / 2) R (by norm_num) (by norm_num))
  exact hh.trans (mul_le_mul_of_nonneg_left (mixture_le_max a b s _ _ hab hs) (Real.exp_pos _).le)

theorem hybridProfile_le_linear_endpoint_max (N : ℕ) (hN : 0 < N)
    (c A V a b s : ℝ) (hA : 0 < A) (hAV : A ≤ V) (ha : 0 < a) (hab : a < b)
    (hs : s ∈ Icc a b) (hbranch : b ≤ (N : ℝ) / rho0 ^ 2) :
    hybridProfile N c A V s ≤ Real.exp ((5 / 2) * ((b - a) ^ 2 / (8 * a ^ 2))) *
      max (hybridProfile N c A V a) (hybridProfile N c A V b) := by
  have hk := kernelEndpointBound_log_chord a b s (5 / 2) ha hab hs
  have hh := hybridProfile_endpoint_of_core N hN c A V a b s _ _ _ hA hAV ha (ha.trans hab) (ha.trans_le hs.1)
    (fun v w _ hw _ => CoefficientRaySpectral.coarseSpectralCore_endpoint_linear N hN c a b s _ _ _ v w
      ha (ha.trans hab) (ha.trans_le hs.1) hw (hab.le.trans hbranch) hbranch (hs.2.trans hbranch) hk)
    (fun R => hk (1 / 2) R (by norm_num) (by norm_num))
  exact hh.trans (mul_le_mul_of_nonneg_left (mixture_le_max a b s _ _ hab hs) (Real.exp_pos _).le)

theorem normalized_actual_cdf_le_node_linear_endpoints (μ : ProbabilityMeasure ℝ)
    (h : StandardizedLaw μ) (n N : ℕ) (hN : 0 < N) (hNn : N ≤ n) (hρ : rho0 ≤ thirdAbsoluteMoment μ)
    (c A V a b : ℝ) (hc : CoefficientRaySpectral.nodeCoefficient N b ≤ c) (hA : 0 < A) (hAV : A ≤ V)
    (ha : 0 < a) (hab : a < b) (hs : 1 / beta μ n ^ 2 ∈ Icc a b) (hbranch : b ≤ (N : ℝ) / rho0 ^ 2) (x : ℝ) :
    |(normalizedIidSumLaw μ n).real (Iic x) - GaussianTools.Phi x| ≤
      beta μ n * (Real.exp ((5 / 2) * ((b - a) ^ 2 / (8 * a ^ 2))) *
        max (hybridProfile N c A V a) (hybridProfile N c A V b)) := by
  have hC := CoefficientRayPrice.node_coefficient_qualifies μ n N hN hNn hρ a b c ha hs.1 hs.2 hc
  apply (normalized_actual_cdf_le_beta_hybridProfile μ h n N hN hNn hρ c hC A V hA hAV x).trans
  exact mul_le_mul_of_nonneg_left (hybridProfile_le_linear_endpoint_max N hN c A V a b _ hA hAV ha hab hs hbranch)
    (CoarseHighMomentRayPrice.beta_pos μ n (lt_of_lt_of_le hN hNn) hρ).le

theorem normalized_actual_cdf_le_node_const_endpoints (μ : ProbabilityMeasure ℝ)
    (h : StandardizedLaw μ) (n N : ℕ) (hN : 0 < N) (hNn : N ≤ n) (hρ : rho0 ≤ thirdAbsoluteMoment μ)
    (c A V a b : ℝ) (hc : CoefficientRaySpectral.nodeCoefficient N b ≤ c) (hA : 0 < A) (hAV : A ≤ V)
    (ha : 0 < a) (hab : a < b) (hs : 1 / beta μ n ^ 2 ∈ Icc a b) (hbranch : (N : ℝ) / rho0 ^ 2 ≤ a) (x : ℝ) :
    |(normalizedIidSumLaw μ n).real (Iic x) - GaussianTools.Phi x| ≤
      beta μ n * (Real.exp ((3 / 2) * ((b - a) ^ 2 / (8 * a ^ 2))) *
        max (hybridProfile N c A V a) (hybridProfile N c A V b)) := by
  have hC := CoefficientRayPrice.node_coefficient_qualifies μ n N hN hNn hρ a b c ha hs.1 hs.2 hc
  apply (normalized_actual_cdf_le_beta_hybridProfile μ h n N hN hNn hρ c hC A V hA hAV x).trans
  exact mul_le_mul_of_nonneg_left (hybridProfile_le_const_endpoint_max N hN c A V a b _ hA hAV ha hab hs hbranch)
    (CoarseHighMomentRayPrice.beta_pos μ n (lt_of_lt_of_le hN hNn) hρ).le

end BerryEsseen.CoefficientHybridSecond

#print axioms BerryEsseen.CoefficientHybridSecond.normalized_power_le_physicalQ
#print axioms BerryEsseen.CoefficientHybridSecond.physicalQ_spectral_eq
#print axioms BerryEsseen.CoefficientHybridSecond.physicalSecond_integral_scale
#print axioms BerryEsseen.CoefficientHybridSecond.normalized_actual_cdf_le_beta_hybridProfile
#print axioms BerryEsseen.CoefficientHybridSecond.hybridProfile_le_const_endpoint_max
#print axioms BerryEsseen.CoefficientHybridSecond.hybridProfile_le_linear_endpoint_max
#print axioms BerryEsseen.CoefficientHybridSecond.normalized_actual_cdf_le_node_const_endpoints
#print axioms BerryEsseen.CoefficientHybridSecond.normalized_actual_cdf_le_node_linear_endpoints
