module

public import BerryEsseen.GenericRayPrice
public import BerryEsseen.RaySpectralCurvature

@[expose] public section

/-! 2026-10-29: fixed continuous nonpositive spectral rates, with an actual
same-law CF input. The generic predecessor-power theorem licenses the ODE
price. Exact spectral substitution and genuine integrability then give the
original four-term Prawitz CDF bound and a common positive-Laplace endpoint
bound. No CF-error estimate or numerical profile value is assumed. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Interval Topology

namespace BerryEsseen.FixedSpectrumPrice

open HighMomentRayDamping
open RaySpectralCurvature (powerExp powerExp_eq_rpow powerExp_half_scale scaled_one_half
  spectralLoss spectralLoss_eq_scaled_loss spectralLoss_eq_const spectralLoss_eq_linear
  spectralLoss_nonneg spectralLoss_le_self spectralKernelWeight spectralKernelWeight_le
  thirdSpectralIntegrand fourthSpectralIntegrand sliceCoefficient linearCoreWeights_nonneg
  KernelEndpointBound kernelEndpointBound_log_chord actualFirstSpectralIntegrand
  actualSecondSpectralIntegrand actualSpectralProfile normalizedEnvelope_div_beta_eq_actualSpectralProfile)
open Causalean.Stat.CLT.BerryEsseen (prawitzKernel)

def exponent (β : ℝ) (G : ℝ → ℝ) (t : ℝ) : ℝ := (1 / β ^ 2) * G (β * t)
def physicalQ (β : ℝ) (G : ℝ → ℝ) (t : ℝ) : ℝ := Real.exp (exponent β G t)
def physicalLoss (N : ℕ) (β : ℝ) (G : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp ((1 - loss N β) * exponent β G t)
def coarsePrice (N : ℕ) (β : ℝ) (G : ℝ → ℝ) (t : ℝ) : ℝ :=
  GenericRayPrice.price N β (physicalLoss N β G) t

lemma continuous_physicalLoss (N : ℕ) (β : ℝ) (G : ℝ → ℝ) (hG : Continuous G) :
    Continuous (physicalLoss N β G) := by unfold physicalLoss exponent; fun_prop

lemma continuous_coarsePrice (N : ℕ) (β : ℝ) (G : ℝ → ℝ) (hG : Continuous G) :
    Continuous (coarsePrice N β G) :=
  GenericRayPrice.continuous_price N β _ (continuous_physicalLoss N β G hG)

theorem normalized_pred_power_le_physicalLoss (μ : ProbabilityMeasure ℝ) (_h : StandardizedLaw μ)
    (n N : ℕ) (hN : 0 < N) (hNn : N ≤ n) (hρ : rho0 ≤ thirdAbsoluteMoment μ) (G : ℝ → ℝ)
    (hQ : ∀ u, 0 ≤ u → ‖charFun (μ : Measure ℝ) (u / Real.sqrt n)‖ ^ n ≤ physicalQ (beta μ n) G u)
    (t : ℝ) (ht : 0 ≤ t) :
    ‖charFun (μ : Measure ℝ) (t / Real.sqrt n)‖ ^ (n - 1) ≤ physicalLoss N (beta μ n) G t := by
  exact GenericRayPrice.pred_power_from_normalized_bound _ _ _ n (norm_nonneg _) (norm_charFun_le_one _)
    (lt_of_lt_of_le hN hNn) (inv_n_le_loss μ n N hN hNn hρ) (loss_le_one N hN _) (hQ t ht)

theorem normalized_error_div_beta_le_coarsePrice (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n N : ℕ) (hN : 0 < N) (hNn : N ≤ n) (hρ : rho0 ≤ thirdAbsoluteMoment μ)
    (G : ℝ → ℝ) (hG : Continuous G)
    (hQ : ∀ u, 0 ≤ u → ‖charFun (μ : Measure ℝ) (u / Real.sqrt n)‖ ^ n ≤ physicalQ (beta μ n) G u)
    (t : ℝ) (ht : 0 ≤ t) :
    ‖charFun (μ : Measure ℝ) (t / Real.sqrt n) ^ n - (Real.exp (-(t ^ 2 / 2)) : ℂ)‖ / beta μ n ≤
      coarsePrice N (beta μ n) G t :=
  GenericRayPrice.normalized_power_error_div_beta_le_price μ h n N hN hNn hρ _
    (continuous_physicalLoss N _ G hG)
    (fun u hu => normalized_pred_power_le_physicalLoss μ h n N hN hNn hρ G hQ u hu) t ht

theorem physicalQ_spectral_eq (β : ℝ) (G : ℝ → ℝ) (v : ℝ) (hβ : 0 < β) :
    physicalQ β G (v / β) = Real.exp ((1 / β ^ 2) * G v) := by
  have hv : β * (v / β) = v := by field_simp [hβ.ne']
  simp only [physicalQ, exponent, hv]

theorem physicalLoss_spectral_eq (N : ℕ) (β : ℝ) (G : ℝ → ℝ) (v : ℝ) (hβ : 0 < β) :
    physicalLoss N β G (v / β) =
      Real.exp (((1 / β ^ 2) - spectralLoss N (1 / β ^ 2)) * G v) := by
  have hv : β * (v / β) = v := by field_simp [hβ.ne']
  unfold physicalLoss exponent
  rw [hv, spectralLoss_eq_scaled_loss N β hβ]
  congr 1
  ring

def spectralRate (G : ℝ → ℝ) (v w : ℝ) : ℝ := (v ^ 2 - w ^ 2) / 2 - G w
def linearSpectralRate (N : ℕ) (G : ℝ → ℝ) (v w : ℝ) : ℝ :=
  (v ^ 2 - w ^ 2) / 2 - (1 - 1 / (N : ℝ)) * G w
def coarseSpectralCore (N : ℕ) (G : ℝ → ℝ) (s v w : ℝ) : ℝ :=
  s ^ (3 / 2 : ℝ) * Real.exp (-s * (v ^ 2 - w ^ 2) / 2 + (s - spectralLoss N s) * G w) *
    (w ^ 2 / 2 + spectralLoss N s * w ^ 3 / 3)
def coarseSpectralSlice (N : ℕ) (G : ℝ → ℝ) (s v : ℝ) : ℝ :=
  ∫ w in (0 : ℝ)..v, coarseSpectralCore N G s v w
def firstSpectralIntegrand (N : ℕ) (G : ℝ → ℝ) (V s v : ℝ) : ℝ :=
  spectralKernelWeight V v * coarseSpectralSlice N G s v
def secondSpectralIntegrand (G : ℝ → ℝ) (V s v : ℝ) : ℝ :=
  spectralKernelWeight V v * powerExp (1 / 2) (-G v) s
def spectralProfile (N : ℕ) (G : ℝ → ℝ) (A V s : ℝ) : ℝ :=
  (2 / V) * (∫ v in Ioc 0 A, firstSpectralIntegrand N G V s v) +
  (2 / V) * (∫ v in Ioc A V, secondSpectralIntegrand G V s v) +
  (2 / V) * (∫ v in Ioc 0 A, thirdSpectralIntegrand V s v) +
  (1 / Real.pi) * (∫ v in Ioi A, fourthSpectralIntegrand s v)

structure ProfileIntegrable (N : ℕ) (G : ℝ → ℝ) (A V s : ℝ) : Prop where
  first : IntegrableOn (firstSpectralIntegrand N G V s) (Ioc 0 A)
  second : IntegrableOn (secondSpectralIntegrand G V s) (Ioc A V)
  third : IntegrableOn (thirdSpectralIntegrand V s) (Ioc 0 A)
  fourth : IntegrableOn (fourthSpectralIntegrand s) (Ioi A)

private lemma scaled_three_halves (β : ℝ) (hβ : 0 < β) :
    (1 / β ^ 2) ^ (3 / 2 : ℝ) = 1 / β ^ 3 := by
  have hh := Real.rpow_mul_natCast (by positivity : 0 ≤ 1 / β ^ 2) (1 / 2) 3
  norm_num only [Nat.cast_ofNat] at hh
  convert hh.trans (by rw [scaled_one_half β hβ, div_pow, one_pow]) using 1

private lemma lambda_spectral (N : ℕ) (β : ℝ) (hβ : 0 < β) :
    CoarseHighMomentRayPrice.lambda N β = β * spectralLoss N (1 / β ^ 2) := by
  rw [spectralLoss_eq_scaled_loss N β hβ, ← CoarseHighMomentRayPrice.loss_div_eq_lambda N β hβ]
  field_simp [hβ.ne']

/-- Exact change of variables for the actual licensed generic price. -/
theorem coarsePrice_spectral_eq (N : ℕ) (β : ℝ) (G : ℝ → ℝ) (v : ℝ) (hβ : 0 < β) :
    coarsePrice N β G (v / β) = coarseSpectralSlice N G (1 / β ^ 2) v := by
  have hsub := intervalIntegral.integral_comp_div (a := (0 : ℝ)) (b := v)
    (GenericRayPrice.integrand N β (physicalLoss N β G)) hβ.ne'
  simp only [zero_div, smul_eq_mul] at hsub
  have hchange : (∫ u in (0 : ℝ)..v / β, GenericRayPrice.integrand N β (physicalLoss N β G) u) =
      (1 / β) * ∫ w in (0 : ℝ)..v, GenericRayPrice.integrand N β (physicalLoss N β G) (w / β) := by
    rw [hsub]
    field_simp [hβ.ne']
  unfold coarsePrice GenericRayPrice.price coarseSpectralSlice
  rw [hchange, ← mul_assoc, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro w _
  unfold GenericRayPrice.integrand coarseSpectralCore
  dsimp only
  rw [physicalLoss_spectral_eq N β G w hβ, lambda_spectral N β hβ, scaled_three_halves β hβ]
  have he : Real.exp (-((v / β) ^ 2 / 2)) * Real.exp ((w / β) ^ 2 / 2) *
      Real.exp ((1 / β ^ 2 - spectralLoss N (1 / β ^ 2)) * G w) =
      Real.exp (-(1 / β ^ 2) * (v ^ 2 - w ^ 2) / 2 +
        (1 / β ^ 2 - spectralLoss N (1 / β ^ 2)) * G w) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    field_simp [hβ.ne']
    ring
  calc
    _ = (1 / β ^ 3) * (Real.exp (-((v / β) ^ 2 / 2)) * Real.exp ((w / β) ^ 2 / 2) *
        Real.exp ((1 / β ^ 2 - spectralLoss N (1 / β ^ 2)) * G w)) *
        (w ^ 2 / 2 + spectralLoss N (1 / β ^ 2) * w ^ 3 / 3) := by field_simp [hβ.ne']
    _ = _ := by rw [he]

lemma continuous_core (N : ℕ) (G : ℝ → ℝ) (hG : Continuous G) (s v : ℝ) :
    Continuous (coarseSpectralCore N G s v) := by unfold coarseSpectralCore; fun_prop

lemma core_nonneg (N : ℕ) (G : ℝ → ℝ) (s v w : ℝ) (hs : 0 ≤ s) (hw : 0 ≤ w) :
    0 ≤ coarseSpectralCore N G s v w := by unfold coarseSpectralCore spectralLoss; positivity

lemma slice_nonneg (N : ℕ) (G : ℝ → ℝ) (s v : ℝ) (hs : 0 ≤ s) (hv : 0 ≤ v) :
    0 ≤ coarseSpectralSlice N G s v :=
  intervalIntegral.integral_nonneg hv (fun w hw => core_nonneg N G s v w hs hw.1)

lemma continuous_slice (N : ℕ) (G : ℝ → ℝ) (hG : Continuous G) (s : ℝ) (hs : 0 < s) :
    Continuous (coarseSpectralSlice N G s) := by
  let β : ℝ := 1 / Real.sqrt s
  have hβ : 0 < β := div_pos zero_lt_one (Real.sqrt_pos.mpr hs)
  have hid : 1 / β ^ 2 = s := by
    dsimp [β]
    rw [div_pow, one_pow, one_div_div, Real.sq_sqrt hs.le, div_one]
  have heq : coarseSpectralSlice N G s = (fun v => coarsePrice N β G (v / β)) := by
    funext v
    rw [coarsePrice_spectral_eq N β G v hβ, hid]
  rw [heq]
  exact (continuous_coarsePrice N β G hG).comp (by fun_prop)

private lemma measurable_kernel (V : ℝ) : Measurable (spectralKernelWeight V) := by
  have heq : spectralKernelWeight V = RaySpectralCurvature.secondSpectralIntegrand V 0 := by
    funext v
    simp only [RaySpectralCurvature.secondSpectralIntegrand, powerExp, Real.log_zero,
      mul_zero, zero_mul, sub_zero, Real.exp_zero, mul_one]
  rw [heq]
  exact RaySpectralCurvature.measurable_secondSpectralIntegrand V 0

lemma core_le_quadratic (N : ℕ) (hN : 0 < N) (G : ℝ → ℝ) (hG0 : ∀ w, G w ≤ 0)
    (A s v w : ℝ) (hs : 0 ≤ s) (hw : 0 ≤ w) (hwv : w ≤ v) (hvA : v ≤ A) :
    coarseSpectralCore N G s v w ≤ sliceCoefficient N A s * w ^ 2 := by
  have hd := spectralLoss_nonneg N s hs
  have hds := spectralLoss_le_self N hN s hs
  have harg : -s * (v ^ 2 - w ^ 2) / 2 + (s - spectralLoss N s) * G w ≤ 0 := by
    have h1 := mul_nonneg hs (show 0 ≤ v ^ 2 - w ^ 2 by nlinarith)
    have h2 := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hds) (hG0 w)
    nlinarith only [h1, h2]
  have he := Real.exp_le_one_iff.mpr harg
  have hp := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (hwv.trans hvA) (sq_nonneg w)) hd
  have hpow : 0 ≤ s ^ (3 / 2 : ℝ) := Real.rpow_nonneg hs _
  have hp' := mul_le_mul_of_nonneg_left hp hpow
  unfold coarseSpectralCore sliceCoefficient
  calc
    _ ≤ s ^ (3 / 2 : ℝ) * 1 * (w ^ 2 / 2 + spectralLoss N s * w ^ 3 / 3) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he hpow) (by positivity)
    _ ≤ _ := by nlinarith only [hp']

lemma slice_le_cubic (N : ℕ) (hN : 0 < N) (G : ℝ → ℝ) (hG : Continuous G) (hG0 : ∀ w, G w ≤ 0)
    (A s v : ℝ) (hs : 0 ≤ s) (hv : 0 ≤ v) (hvA : v ≤ A) :
    coarseSpectralSlice N G s v ≤ sliceCoefficient N A s * v ^ 3 / 3 := by
  have hh := intervalIntegral.integral_mono_on (μ := volume) hv ((continuous_core N G hG s v).intervalIntegrable 0 v)
    ((by fun_prop : Continuous (fun w => sliceCoefficient N A s * w ^ 2)).intervalIntegrable 0 v)
    (fun w hw => core_le_quadratic N hN G hG0 A s v w hs hw.1 hw.2 hvA)
  unfold coarseSpectralSlice
  convert hh using 1
  rw [intervalIntegral.integral_const_mul, integral_pow]
  norm_num
  ring

theorem profileIntegrable (N : ℕ) (hN : 0 < N) (G : ℝ → ℝ) (hG : Continuous G) (hG0 : ∀ w, G w ≤ 0)
    (A V s : ℝ) (hA : 0 < A) (hAV : A ≤ V) (hs : 0 < s) : ProfileIntegrable N G A V s := by
  have hV : 0 < V := hA.trans_le hAV
  have hOld := RaySpectralCurvature.profileIntegrable N hN A V s hA hAV hs
  have hk := measurable_kernel V
  have h1m : Measurable (firstSpectralIntegrand N G V s) :=
    hk.mul (continuous_slice N G hG s hs).measurable
  have h2m : Measurable (secondSpectralIntegrand G V s) := by unfold secondSpectralIntegrand powerExp; fun_prop
  refine ⟨?_, ?_, hOld.third, hOld.fourth⟩
  · have hp : Continuous (fun v => (sliceCoefficient N A s / 3) * (V / (2 * Real.pi) * v ^ 2 + v ^ 3 / 2)) := by fun_prop
    apply (hp.intervalIntegrable 0 A).1.mono' h1m.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    have hn := mul_nonneg (norm_nonneg (prawitzKernel (v / V))) (slice_nonneg N G s v hs.le hv.1.le)
    unfold firstSpectralIntegrand spectralKernelWeight
    rw [Real.norm_eq_abs, abs_of_nonneg hn]
    have hvpos : 0 < v := hv.1
    have hh := mul_le_mul (spectralKernelWeight_le V v hV hv.1 (hv.2.trans hAV))
      (slice_le_cubic N hN G hG hG0 A s v hs.le hv.1.le hv.2) (slice_nonneg N G s v hs.le hv.1.le) (by positivity)
    calc
      _ ≤ (V / (2 * Real.pi) / v + 1 / 2) * (sliceCoefficient N A s * v ^ 3 / 3) := by simpa only [spectralKernelWeight] using hh
      _ = _ := by field_simp [hv.1.ne']
  · have hkI : IntegrableOn (spectralKernelWeight V) (Ioc A V) := by
      apply (intervalIntegrable_const (c := V / (2 * Real.pi) / A + 1 / 2) (a := A) (b := V) (μ := volume)).1.mono' hk.aestronglyMeasurable
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
      rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ spectralKernelWeight V v from norm_nonneg _)]
      exact (spectralKernelWeight_le V v hV (hA.trans hv.1) hv.2).trans (by gcongr; exact hv.1.le)
    have hp : Continuous (fun v => powerExp (1 / 2) (-G v) s) := by unfold powerExp; fun_prop
    exact hkI.mul_continuousOn_of_subset hp.continuousOn measurableSet_Ioc isCompact_Icc Ioc_subset_Icc_self

theorem core_const (N : ℕ) (hN : 0 < N) (G : ℝ → ℝ) (s v w : ℝ) (hs : 0 < s)
    (hb : (N : ℝ) / rho0 ^ 2 ≤ s) :
    coarseSpectralCore N G s v w = (Real.exp (-(1 / rho0 ^ 2) * G w) *
      (w ^ 2 / 2 + (1 / rho0 ^ 2) * w ^ 3 / 3)) * powerExp (3 / 2) (spectralRate G v w) s := by
  unfold coarseSpectralCore
  rw [spectralLoss_eq_const N hN s hb, powerExp_eq_rpow _ _ _ hs]
  have he : -s * (v ^ 2 - w ^ 2) / 2 + (s - 1 / rho0 ^ 2) * G w =
      -(1 / rho0 ^ 2) * G w + -s * spectralRate G v w := by unfold spectralRate; ring
  rw [he, Real.exp_add]
  ring

theorem core_linear (N : ℕ) (hN : 0 < N) (G : ℝ → ℝ) (s v w : ℝ) (hs : 0 < s)
    (hb : s ≤ (N : ℝ) / rho0 ^ 2) :
    coarseSpectralCore N G s v w = (w ^ 2 / 2) * powerExp (3 / 2) (linearSpectralRate N G v w) s +
      (w ^ 3 / (3 * (N : ℝ))) * powerExp (5 / 2) (linearSpectralRate N G v w) s := by
  unfold coarseSpectralCore
  rw [spectralLoss_eq_linear N hN s hb, powerExp_eq_rpow _ _ _ hs, powerExp_eq_rpow _ _ _ hs]
  have he : -s * (v ^ 2 - w ^ 2) / 2 + (s - s / (N : ℝ)) * G w =
      -s * linearSpectralRate N G v w := by unfold linearSpectralRate; ring
  have hp : s ^ (5 / 2 : ℝ) = s ^ (3 / 2 : ℝ) * s := by
    convert Real.rpow_add_one hs.ne' (3 / 2) using 1
    norm_num
  rw [he, hp]
  ring

theorem core_endpoint_const (N : ℕ) (hN : 0 < N) (G : ℝ → ℝ) (a b s E l r v w : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hs : 0 < s) (hw : 0 ≤ w)
    (hba : (N : ℝ) / rho0 ^ 2 ≤ a) (hbb : (N : ℝ) / rho0 ^ 2 ≤ b) (hbs : (N : ℝ) / rho0 ^ 2 ≤ s)
    (hk : KernelEndpointBound a b s E l r (3 / 2)) :
    coarseSpectralCore N G s v w ≤ E * (l * coarseSpectralCore N G a v w + r * coarseSpectralCore N G b v w) := by
  rw [core_const N hN G s v w hs hbs, core_const N hN G a v w ha hba, core_const N hN G b v w hb hbb]
  have hc : 0 ≤ Real.exp (-(1 / rho0 ^ 2) * G w) * (w ^ 2 / 2 + (1 / rho0 ^ 2) * w ^ 3 / 3) := by positivity
  have hh := mul_le_mul_of_nonneg_left (hk (3 / 2) (spectralRate G v w) (by norm_num) le_rfl) hc
  convert hh using 1
  ring

theorem core_endpoint_linear (N : ℕ) (hN : 0 < N) (G : ℝ → ℝ) (a b s E l r v w : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hs : 0 < s) (hw : 0 ≤ w)
    (hba : a ≤ (N : ℝ) / rho0 ^ 2) (hbb : b ≤ (N : ℝ) / rho0 ^ 2) (hbs : s ≤ (N : ℝ) / rho0 ^ 2)
    (hk : KernelEndpointBound a b s E l r (5 / 2)) :
    coarseSpectralCore N G s v w ≤ E * (l * coarseSpectralCore N G a v w + r * coarseSpectralCore N G b v w) := by
  rw [core_linear N hN G s v w hs hbs, core_linear N hN G a v w ha hba, core_linear N hN G b v w hb hbb]
  obtain ⟨hc1, hc2⟩ := linearCoreWeights_nonneg N w hw
  have h1 := mul_le_mul_of_nonneg_left (hk (3 / 2) (linearSpectralRate N G v w) (by norm_num) (by norm_num)) hc1
  have h2 := mul_le_mul_of_nonneg_left (hk (5 / 2) (linearSpectralRate N G v w) (by norm_num) le_rfl) hc2
  convert add_le_add h1 h2 using 1
  ring

private lemma integral_endpoint_le {α : Type*} [MeasurableSpace α] (μ : Measure α) (f fa fb : α → ℝ)
    (E l r : ℝ) (hf : Integrable f μ) (ha : Integrable fa μ) (hb : Integrable fb μ)
    (hle : ∀ᵐ x ∂μ, f x ≤ E * (l * fa x + r * fb x)) :
    (∫ x, f x ∂μ) ≤ E * (l * (∫ x, fa x ∂μ) + r * (∫ x, fb x ∂μ)) := by
  have hd : Integrable (fun x => E * (l * fa x + r * fb x)) μ := ((ha.const_mul l).add (hb.const_mul r)).const_mul E
  have hh := integral_mono_ae hf hd hle
  simpa only [integral_const_mul, integral_add (ha.const_mul l) (hb.const_mul r)] using hh

theorem profile_endpoint_of_core (N : ℕ) (hN : 0 < N) (G : ℝ → ℝ) (hG : Continuous G) (hG0 : ∀ w, G w ≤ 0)
    (A V a b s E l r : ℝ) (hA : 0 < A) (hAV : A ≤ V) (ha : 0 < a) (hb : 0 < b) (hs : 0 < s)
    (hc : ∀ v w, 0 ≤ v → 0 ≤ w → w ≤ v → coarseSpectralCore N G s v w ≤
      E * (l * coarseSpectralCore N G a v w + r * coarseSpectralCore N G b v w))
    (hk : ∀ R, powerExp (1 / 2) R s ≤ E * (l * powerExp (1 / 2) R a + r * powerExp (1 / 2) R b)) :
    spectralProfile N G A V s ≤ E * (l * spectralProfile N G A V a + r * spectralProfile N G A V b) := by
  have hV : 0 < V := hA.trans_le hAV
  have hIa := profileIntegrable N hN G hG hG0 A V a hA hAV ha
  have hIb := profileIntegrable N hN G hG hG0 A V b hA hAV hb
  have hIs := profileIntegrable N hN G hG hG0 A V s hA hAV hs
  have h1 := integral_endpoint_le (volume.restrict (Ioc 0 A)) _ _ _ E l r hIs.first hIa.first hIb.first (by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    have hca := continuous_core N G hG a v
    have hcb := continuous_core N G hG b v
    have hcs := continuous_core N G hG s v
    have hh := intervalIntegral.integral_mono_on (μ := volume) hv.1.le (hcs.intervalIntegrable 0 v)
      ((((hca.const_mul l).add (hcb.const_mul r)).const_mul E).intervalIntegrable 0 v)
      (fun w hw => hc v w hv.1.le hw.1 hw.2)
    have hslice : coarseSpectralSlice N G s v ≤ E * (l * coarseSpectralSlice N G a v + r * coarseSpectralSlice N G b v) := by
      unfold coarseSpectralSlice
      convert hh using 1
      simp only [Pi.add_apply]
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
        ((hca.const_mul l).intervalIntegrable 0 v) ((hcb.const_mul r).intervalIntegrable 0 v),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    have hm := mul_le_mul_of_nonneg_left hslice (norm_nonneg (prawitzKernel (v / V)))
    unfold firstSpectralIntegrand spectralKernelWeight
    convert hm using 1
    ring)
  have h2 := integral_endpoint_le (volume.restrict (Ioc A V)) _ _ _ E l r hIs.second hIa.second hIb.second (ae_of_all _ (fun v => by
    have hh := mul_le_mul_of_nonneg_left (hk (-G v)) (norm_nonneg (prawitzKernel (v / V)))
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
  unfold spectralProfile
  nlinarith only [h1', h2', h3', h4']

private lemma mixture_le_max (a b s x y : ℝ) (hab : a < b) (hs : s ∈ Icc a b) :
    ((b - s) / (b - a)) * x + ((s - a) / (b - a)) * y ≤ max x y := by
  have hl := div_nonneg (sub_nonneg.mpr hs.2) (sub_pos.mpr hab).le
  have hr := div_nonneg (sub_nonneg.mpr hs.1) (sub_pos.mpr hab).le
  calc
    _ ≤ ((b - s) / (b - a)) * max x y + ((s - a) / (b - a)) * max x y :=
      add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) hl) (mul_le_mul_of_nonneg_left (le_max_right _ _) hr)
    _ = _ := by field_simp [(sub_pos.mpr hab).ne']; ring

theorem spectralProfile_le_const_endpoint_max (N : ℕ) (hN : 0 < N) (G : ℝ → ℝ) (hG : Continuous G) (hG0 : ∀ w, G w ≤ 0)
    (A V a b s : ℝ) (hA : 0 < A) (hAV : A ≤ V) (ha : 0 < a) (hab : a < b) (hs : s ∈ Icc a b)
    (hb : (N : ℝ) / rho0 ^ 2 ≤ a) : spectralProfile N G A V s ≤
    Real.exp ((3 / 2) * ((b - a) ^ 2 / (8 * a ^ 2))) * max (spectralProfile N G A V a) (spectralProfile N G A V b) := by
  have hk := kernelEndpointBound_log_chord a b s (3 / 2) ha hab hs
  have hh := profile_endpoint_of_core N hN G hG hG0 A V a b s _ _ _ hA hAV ha (ha.trans hab) (ha.trans_le hs.1)
    (fun v w _ hw _ => core_endpoint_const N hN G a b s _ _ _ v w ha (ha.trans hab) (ha.trans_le hs.1) hw hb (hb.trans hab.le) (hb.trans hs.1) hk)
    (fun R => hk (1 / 2) R (by norm_num) (by norm_num))
  exact hh.trans (mul_le_mul_of_nonneg_left (mixture_le_max a b s _ _ hab hs) (Real.exp_pos _).le)

theorem spectralProfile_le_linear_endpoint_max (N : ℕ) (hN : 0 < N) (G : ℝ → ℝ) (hG : Continuous G) (hG0 : ∀ w, G w ≤ 0)
    (A V a b s : ℝ) (hA : 0 < A) (hAV : A ≤ V) (ha : 0 < a) (hab : a < b) (hs : s ∈ Icc a b)
    (hb : b ≤ (N : ℝ) / rho0 ^ 2) : spectralProfile N G A V s ≤
    Real.exp ((5 / 2) * ((b - a) ^ 2 / (8 * a ^ 2))) * max (spectralProfile N G A V a) (spectralProfile N G A V b) := by
  have hk := kernelEndpointBound_log_chord a b s (5 / 2) ha hab hs
  have hh := profile_endpoint_of_core N hN G hG hG0 A V a b s _ _ _ hA hAV ha (ha.trans hab) (ha.trans_le hs.1)
    (fun v w _ hw _ => core_endpoint_linear N hN G a b s _ _ _ v w ha (ha.trans hab) (ha.trans_le hs.1) hw (hab.le.trans hb) hb (hs.2.trans hb) hk)
    (fun R => hk (1 / 2) R (by norm_num) (by norm_num))
  exact hh.trans (mul_le_mul_of_nonneg_left (mixture_le_max a b s _ _ hab hs) (Real.exp_pos _).le)

private theorem actual_comparison (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (n N : ℕ)
    (hN : 0 < N) (hNn : N ≤ n) (hρ : rho0 ≤ thirdAbsoluteMoment μ)
    (G : ℝ → ℝ) (hG : Continuous G) (hG0 : ∀ w, G w ≤ 0)
    (hQ : ∀ u, 0 ≤ u → ‖charFun (μ : Measure ℝ) (u / Real.sqrt n)‖ ^ n ≤ physicalQ (beta μ n) G u)
    (A V : ℝ) (hA : 0 < A) (hAV : A ≤ V) :
    (IntegrableOn (actualFirstSpectralIntegrand μ n (beta μ n) V) (Ioc 0 A) ∧
      IntegrableOn (actualSecondSpectralIntegrand μ n (beta μ n) V) (Ioc A V) ∧
      IntegrableOn (thirdSpectralIntegrand V (1 / beta μ n ^ 2)) (Ioc 0 A) ∧
      IntegrableOn (fourthSpectralIntegrand (1 / beta μ n ^ 2)) (Ioi A)) ∧
    actualSpectralProfile μ n (beta μ n) A V ≤ spectralProfile N G A V (1 / beta μ n ^ 2) := by
  let β := beta μ n
  have hβ : 0 < β := CoarseHighMomentRayPrice.beta_pos μ n (lt_of_lt_of_le hN hNn) hρ
  have hV : 0 < V := hA.trans_le hAV
  have hI := profileIntegrable N hN G hG hG0 A V (1 / β ^ 2) hA hAV (by positivity)
  have hk := measurable_kernel V
  have h1point (v : ℝ) (hv : 0 ≤ v) : actualFirstSpectralIntegrand μ n β V v ≤ firstSpectralIntegrand N G V (1 / β ^ 2) v := by
    have hh := normalized_error_div_beta_le_coarsePrice μ h n N hN hNn hρ G hG hQ (v / β) (div_nonneg hv hβ.le)
    rw [coarsePrice_spectral_eq N β G v hβ] at hh
    exact mul_le_mul_of_nonneg_left hh (norm_nonneg (prawitzKernel (v / V)))
  have h2point (v : ℝ) (hv : 0 ≤ v) : actualSecondSpectralIntegrand μ n β V v ≤ secondSpectralIntegrand G V (1 / β ^ 2) v := by
    have hh := div_le_div_of_nonneg_right (hQ (v / β) (div_nonneg hv hβ.le)) hβ.le
    rw [physicalQ_spectral_eq β G v hβ] at hh
    have he : powerExp (1 / 2) (-G v) (1 / β ^ 2) = Real.exp ((1 / β ^ 2) * G v) / β := by
      rw [powerExp_half_scale β _ hβ]
      congr 2
      ring
    unfold actualSecondSpectralIntegrand secondSpectralIntegrand
    rw [he, norm_pow]
    exact mul_le_mul_of_nonneg_left hh (norm_nonneg (prawitzKernel (v / V)))
  have h1m : Measurable (actualFirstSpectralIntegrand μ n β V) := by unfold actualFirstSpectralIntegrand; fun_prop
  have h2m : Measurable (actualSecondSpectralIntegrand μ n β V) := by unfold actualSecondSpectralIntegrand; fun_prop
  have h1I : IntegrableOn (actualFirstSpectralIntegrand μ n β V) (Ioc 0 A) := by
    apply hI.first.mono' h1m.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    have hn : 0 ≤ actualFirstSpectralIntegrand μ n β V v := by unfold actualFirstSpectralIntegrand spectralKernelWeight; positivity
    simpa only [Real.norm_eq_abs, abs_of_nonneg hn] using h1point v hv.1.le
  have h2I : IntegrableOn (actualSecondSpectralIntegrand μ n β V) (Ioc A V) := by
    apply hI.second.mono' h2m.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    have hn : 0 ≤ actualSecondSpectralIntegrand μ n β V v := by unfold actualSecondSpectralIntegrand spectralKernelWeight; positivity
    simpa only [Real.norm_eq_abs, abs_of_nonneg hn] using h2point v (hA.trans hv.1).le
  refine ⟨⟨h1I, h2I, hI.third, hI.fourth⟩, ?_⟩
  have h1 := integral_mono_ae h1I hI.first (by filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv; exact h1point v hv.1.le)
  have h2 := integral_mono_ae h2I hI.second (by filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv; exact h2point v (hA.trans hv.1).le)
  have h1' := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 2 / V)
  have h2' := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ 2 / V)
  change actualSpectralProfile μ n β A V ≤ spectralProfile N G A V (1 / β ^ 2)
  unfold actualSpectralProfile spectralProfile
  linarith only [h1', h2']

theorem actual_four_integrands_integrable (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (n N : ℕ)
    (hN : 0 < N) (hNn : N ≤ n) (hρ : rho0 ≤ thirdAbsoluteMoment μ)
    (G : ℝ → ℝ) (hG : Continuous G) (hG0 : ∀ w, G w ≤ 0)
    (hQ : ∀ u, 0 ≤ u → ‖charFun (μ : Measure ℝ) (u / Real.sqrt n)‖ ^ n ≤ physicalQ (beta μ n) G u)
    (A V : ℝ) (hA : 0 < A) (hAV : A ≤ V) :
    IntegrableOn (actualFirstSpectralIntegrand μ n (beta μ n) V) (Ioc 0 A) ∧
      IntegrableOn (actualSecondSpectralIntegrand μ n (beta μ n) V) (Ioc A V) ∧
      IntegrableOn (thirdSpectralIntegrand V (1 / beta μ n ^ 2)) (Ioc 0 A) ∧
      IntegrableOn (fourthSpectralIntegrand (1 / beta μ n ^ 2)) (Ioi A) :=
  (actual_comparison μ h n N hN hNn hρ G hG hG0 hQ A V hA hAV).1

theorem normalized_actual_cdf_le_beta_spectralProfile (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (n N : ℕ)
    (hN : 0 < N) (hNn : N ≤ n) (hρ : rho0 ≤ thirdAbsoluteMoment μ)
    (G : ℝ → ℝ) (hG : Continuous G) (hG0 : ∀ w, G w ≤ 0)
    (hQ : ∀ u, 0 ≤ u → ‖charFun (μ : Measure ℝ) (u / Real.sqrt n)‖ ^ n ≤ physicalQ (beta μ n) G u)
    (A V : ℝ) (hA : 0 < A) (hAV : A ≤ V) (x : ℝ) :
    |(normalizedIidSumLaw μ n).real (Iic x) - GaussianTools.Phi x| ≤
      beta μ n * spectralProfile N G A V (1 / beta μ n ^ 2) := by
  have hn : 0 < n := lt_of_lt_of_le hN hNn
  have hβ := CoarseHighMomentRayPrice.beta_pos μ n hn hρ
  have hh := div_le_div_of_nonneg_right (PrawitzSmoothing.normalized_actual_cdf_le μ h n hn
    (A / beta μ n) (V / beta μ n) (div_pos hA hβ) (div_le_div_of_nonneg_right hAV hβ.le) x) hβ.le
  rw [normalizedEnvelope_div_beta_eq_actualSpectralProfile μ n (beta μ n) A V hβ hA hAV] at hh
  have hm := hh.trans (actual_comparison μ h n N hN hNn hρ G hG hG0 hQ A V hA hAV).2
  simpa only [mul_comm] using (div_le_iff₀ hβ).mp hm

theorem normalized_actual_cdf_le_const_endpoints (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (n N : ℕ)
    (hN : 0 < N) (hNn : N ≤ n) (hρ : rho0 ≤ thirdAbsoluteMoment μ)
    (G : ℝ → ℝ) (hG : Continuous G) (hG0 : ∀ w, G w ≤ 0)
    (hQ : ∀ u, 0 ≤ u → ‖charFun (μ : Measure ℝ) (u / Real.sqrt n)‖ ^ n ≤ physicalQ (beta μ n) G u)
    (A V a b : ℝ) (hA : 0 < A) (hAV : A ≤ V) (ha : 0 < a) (hab : a < b)
    (hs : 1 / beta μ n ^ 2 ∈ Icc a b) (hb : (N : ℝ) / rho0 ^ 2 ≤ a) (x : ℝ) :
    |(normalizedIidSumLaw μ n).real (Iic x) - GaussianTools.Phi x| ≤ beta μ n *
      (Real.exp ((3 / 2) * ((b - a) ^ 2 / (8 * a ^ 2))) * max (spectralProfile N G A V a) (spectralProfile N G A V b)) := by
  apply (normalized_actual_cdf_le_beta_spectralProfile μ h n N hN hNn hρ G hG hG0 hQ A V hA hAV x).trans
  exact mul_le_mul_of_nonneg_left (spectralProfile_le_const_endpoint_max N hN G hG hG0 A V a b _ hA hAV ha hab hs hb)
    (CoarseHighMomentRayPrice.beta_pos μ n (lt_of_lt_of_le hN hNn) hρ).le

theorem normalized_actual_cdf_le_linear_endpoints (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (n N : ℕ)
    (hN : 0 < N) (hNn : N ≤ n) (hρ : rho0 ≤ thirdAbsoluteMoment μ)
    (G : ℝ → ℝ) (hG : Continuous G) (hG0 : ∀ w, G w ≤ 0)
    (hQ : ∀ u, 0 ≤ u → ‖charFun (μ : Measure ℝ) (u / Real.sqrt n)‖ ^ n ≤ physicalQ (beta μ n) G u)
    (A V a b : ℝ) (hA : 0 < A) (hAV : A ≤ V) (ha : 0 < a) (hab : a < b)
    (hs : 1 / beta μ n ^ 2 ∈ Icc a b) (hb : b ≤ (N : ℝ) / rho0 ^ 2) (x : ℝ) :
    |(normalizedIidSumLaw μ n).real (Iic x) - GaussianTools.Phi x| ≤ beta μ n *
      (Real.exp ((5 / 2) * ((b - a) ^ 2 / (8 * a ^ 2))) * max (spectralProfile N G A V a) (spectralProfile N G A V b)) := by
  apply (normalized_actual_cdf_le_beta_spectralProfile μ h n N hN hNn hρ G hG hG0 hQ A V hA hAV x).trans
  exact mul_le_mul_of_nonneg_left (spectralProfile_le_linear_endpoint_max N hN G hG hG0 A V a b _ hA hAV ha hab hs hb)
    (CoarseHighMomentRayPrice.beta_pos μ n (lt_of_lt_of_le hN hNn) hρ).le

end BerryEsseen.FixedSpectrumPrice

#print axioms BerryEsseen.FixedSpectrumPrice.normalized_pred_power_le_physicalLoss
#print axioms BerryEsseen.FixedSpectrumPrice.coarsePrice_spectral_eq
#print axioms BerryEsseen.FixedSpectrumPrice.profileIntegrable
#print axioms BerryEsseen.FixedSpectrumPrice.spectralProfile_le_const_endpoint_max
#print axioms BerryEsseen.FixedSpectrumPrice.spectralProfile_le_linear_endpoint_max
#print axioms BerryEsseen.FixedSpectrumPrice.actual_four_integrands_integrable
#print axioms BerryEsseen.FixedSpectrumPrice.normalized_actual_cdf_le_beta_spectralProfile
#print axioms BerryEsseen.FixedSpectrumPrice.normalized_actual_cdf_le_const_endpoints
#print axioms BerryEsseen.FixedSpectrumPrice.normalized_actual_cdf_le_linear_endpoints
