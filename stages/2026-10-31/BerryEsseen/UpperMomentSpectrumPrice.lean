module

public import BerryEsseen.FixedSpectrumPrice
public import BerryEsseen.WeightedRayPrice
public import BerryEsseen.UpperMomentDamping

@[expose] public section

/-! 2026-10-30: full sine forcing at the fixed upper-moment scale U.
The positive Laplace representation has a single maximal power 3/2.
The actual-law client derives damping and forcing from the same moment
upper bound; neither a CF envelope nor a predecessor bound is assumed. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Interval Topology

namespace BerryEsseen.UpperMomentSpectrumPrice

open HighMomentRayDamping
open RaySpectralCurvature (powerExp powerExp_eq_rpow powerExp_half_scale scaled_one_half
  spectralKernelWeight spectralKernelWeight_le thirdSpectralIntegrand fourthSpectralIntegrand
  KernelEndpointBound kernelEndpointBound_log_chord actualFirstSpectralIntegrand
  actualSecondSpectralIntegrand actualSpectralProfile normalizedEnvelope_div_beta_eq_actualSpectralProfile)
open Causalean.Stat.CLT.BerryEsseen (prawitzKernel)

def d (U : ℝ) : ℝ := 1 / U ^ 2
def W (U v : ℝ) : ℝ := U * FiniteRhoSinePrice.H U (v / U)

lemma continuous_W (U : ℝ) : Continuous (W U) :=
  continuous_const.mul ((FiniteRhoSinePrice.continuous_H U).comp (continuous_id.div_const U))

lemma W_nonneg (U v : ℝ) (hU : 0 < U) (hv : 0 ≤ v) : 0 ≤ W U v :=
  mul_nonneg hU.le (FiniteRhoSinePrice.H_nonneg U _ hU (div_nonneg hv hU.le))

lemma kernel_le (U t : ℝ) (hU : 0 < U) (ht : 0 ≤ t) :
    FiniteRhoSinePrice.kernel U t ≤ U * t + t ^ 2 := by
  have h1 : 0 ≤ min (U * t / 2) (Real.pi / 2) := le_min (by positivity) (by positivity)
  have h2 : 0 ≤ min t (Real.pi / 2) := le_min ht (by positivity)
  have hs1 := (Real.sin_le h1).trans (min_le_left _ _)
  have hs2 := mul_le_mul_of_nonneg_left ((Real.sin_le h2).trans (min_le_left _ _)) ht
  unfold FiniteRhoSinePrice.kernel FiniteRhoSinePrice.firstKernel FiniteRhoSinePrice.secondKernel
  nlinarith only [hs1, hs2]

lemma H_le (U t : ℝ) (hU : 0 < U) (ht : 0 ≤ t) :
    FiniteRhoSinePrice.H U t ≤ U * t ^ 2 / 2 + t ^ 3 / 3 := by
  have hh := intervalIntegral.integral_mono_on (μ := volume) ht
    ((FiniteRhoSinePrice.continuous_kernel U).intervalIntegrable 0 t)
    ((by fun_prop : Continuous (fun v : ℝ => U * v + v ^ 2)).intervalIntegrable 0 t)
    (fun v hv => kernel_le U v hU hv.1)
  unfold FiniteRhoSinePrice.H
  convert hh using 1
  rw [intervalIntegral.integral_add
    ((by fun_prop : Continuous (fun v : ℝ => U * v)).intervalIntegrable 0 t)
    ((by fun_prop : Continuous (fun v : ℝ => v ^ 2)).intervalIntegrable 0 t),
    intervalIntegral.integral_const_mul, integral_id, integral_pow]
  norm_num
  ring

lemma W_le (U v : ℝ) (hU : 0 < U) (hv : 0 ≤ v) :
    W U v ≤ v ^ 2 / 2 + d U * v ^ 3 / 3 := by
  have hh := mul_le_mul_of_nonneg_left (H_le U (v / U) hU (div_nonneg hv hU.le)) hU.le
  unfold W d
  convert hh using 1
  field_simp [hU.ne']

def physicalLoss (U β : ℝ) (G : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (((1 / β ^ 2) - d U) * G (β * t))
def forcing (U β t : ℝ) : ℝ := (1 / β ^ 2) * W U (β * t)
def physicalPrice (U β : ℝ) (G : ℝ → ℝ) (t : ℝ) : ℝ :=
  WeightedRayPrice.price (physicalLoss U β G) (forcing U β) t

lemma continuous_physicalLoss (U β : ℝ) (G : ℝ → ℝ) (hG : Continuous G) :
    Continuous (physicalLoss U β G) := by unfold physicalLoss; fun_prop
lemma continuous_forcing (U β : ℝ) : Continuous (forcing U β) :=
  continuous_const.mul ((continuous_W U).comp (continuous_const.mul continuous_id))

def core (U : ℝ) (G : ℝ → ℝ) (s v w : ℝ) : ℝ :=
  s ^ (3 / 2 : ℝ) * Real.exp (-s * (v ^ 2 - w ^ 2) / 2 + (s - d U) * G w) * W U w
def firstSlice (U : ℝ) (G : ℝ → ℝ) (s v : ℝ) : ℝ := ∫ w in (0 : ℝ)..v, core U G s v w
def firstSpectralIntegrand (U : ℝ) (G : ℝ → ℝ) (V s v : ℝ) : ℝ :=
  spectralKernelWeight V v * firstSlice U G s v
def spectralProfile (U : ℝ) (G : ℝ → ℝ) (A V s : ℝ) : ℝ :=
  (2 / V) * (∫ v in Ioc 0 A, firstSpectralIntegrand U G V s v) +
  (2 / V) * (∫ v in Ioc A V, FixedSpectrumPrice.secondSpectralIntegrand G V s v) +
  (2 / V) * (∫ v in Ioc 0 A, thirdSpectralIntegrand V s v) +
  (1 / Real.pi) * (∫ v in Ioi A, fourthSpectralIntegrand s v)

structure ProfileIntegrable (U : ℝ) (G : ℝ → ℝ) (A V s : ℝ) : Prop where
  first : IntegrableOn (firstSpectralIntegrand U G V s) (Ioc 0 A)
  second : IntegrableOn (FixedSpectrumPrice.secondSpectralIntegrand G V s) (Ioc A V)
  third : IntegrableOn (thirdSpectralIntegrand V s) (Ioc 0 A)
  fourth : IntegrableOn (fourthSpectralIntegrand s) (Ioi A)

lemma continuous_core (U : ℝ) (G : ℝ → ℝ) (hG : Continuous G) (s v : ℝ) :
    Continuous (core U G s v) := by
  exact ((by fun_prop : Continuous (fun w : ℝ =>
    s ^ (3 / 2 : ℝ) * Real.exp (-s * (v ^ 2 - w ^ 2) / 2 + (s - d U) * G w)))).mul (continuous_W U)

lemma continuous_slice (U : ℝ) (G : ℝ → ℝ) (hG : Continuous G) (s : ℝ) :
    Continuous (firstSlice U G s) := by
  change Continuous (fun v : ℝ => ∫ w in (0 : ℝ)..v, core U G s v w)
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous (μ := volume) (a₀ := 0) _ continuous_id
  unfold Function.uncurry core
  exact (by fun_prop : Continuous (fun p : ℝ × ℝ =>
    s ^ (3 / 2 : ℝ) * Real.exp (-s * (p.1 ^ 2 - p.2 ^ 2) / 2 + (s - d U) * G p.2))).mul
    ((continuous_W U).comp continuous_snd)

lemma core_nonneg (U : ℝ) (G : ℝ → ℝ) (s v w : ℝ) (hU : 0 < U) (hs : 0 ≤ s) (hw : 0 ≤ w) :
    0 ≤ core U G s v w := by
  have hW := W_nonneg U w hU hw
  unfold core
  positivity

lemma slice_nonneg (U : ℝ) (G : ℝ → ℝ) (s v : ℝ) (hU : 0 < U) (hs : 0 ≤ s) (hv : 0 ≤ v) :
    0 ≤ firstSlice U G s v :=
  intervalIntegral.integral_nonneg hv (fun w hw => core_nonneg U G s v w hU hs hw.1)

def sliceCoefficient (U A s : ℝ) : ℝ := s ^ (3 / 2 : ℝ) * (1 / 2 + d U * A / 3)

lemma core_le_quadratic (U : ℝ) (hU : 0 < U) (G : ℝ → ℝ) (hG0 : ∀ w, G w ≤ 0)
    (A s v w : ℝ) (hs : 0 ≤ s) (hds : d U ≤ s) (hw : 0 ≤ w) (hwv : w ≤ v) (hvA : v ≤ A) :
    core U G s v w ≤ sliceCoefficient U A s * w ^ 2 := by
  have hd : 0 ≤ d U := by unfold d; positivity
  have harg : -s * (v ^ 2 - w ^ 2) / 2 + (s - d U) * G w ≤ 0 := by
    have h1 := mul_nonneg hs (show 0 ≤ v ^ 2 - w ^ 2 by nlinarith)
    have h2 := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hds) (hG0 w)
    nlinarith only [h1, h2]
  have he := Real.exp_le_one_iff.mpr harg
  have hW := W_le U w hU hw
  have hW0 := W_nonneg U w hU hw
  have hp := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (hwv.trans hvA) (sq_nonneg w)) hd
  have hpow : 0 ≤ s ^ (3 / 2 : ℝ) := Real.rpow_nonneg hs _
  unfold core sliceCoefficient
  calc
    _ ≤ s ^ (3 / 2 : ℝ) * 1 * W U w :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he hpow) hW0
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hW hpow,
      mul_le_mul_of_nonneg_left hp hpow]

lemma slice_le_cubic (U : ℝ) (hU : 0 < U) (G : ℝ → ℝ) (hG : Continuous G) (hG0 : ∀ w, G w ≤ 0)
    (A s v : ℝ) (hs : 0 ≤ s) (hds : d U ≤ s) (hv : 0 ≤ v) (hvA : v ≤ A) :
    firstSlice U G s v ≤ sliceCoefficient U A s * v ^ 3 / 3 := by
  have hh := intervalIntegral.integral_mono_on (μ := volume) hv ((continuous_core U G hG s v).intervalIntegrable 0 v)
    ((by fun_prop : Continuous (fun w => sliceCoefficient U A s * w ^ 2)).intervalIntegrable 0 v)
    (fun w hw => core_le_quadratic U hU G hG0 A s v w hs hds hw.1 hw.2 hvA)
  unfold firstSlice
  convert hh using 1
  rw [intervalIntegral.integral_const_mul, integral_pow]
  norm_num
  ring

private lemma measurable_kernel (V : ℝ) : Measurable (spectralKernelWeight V) := by
  have heq : spectralKernelWeight V = RaySpectralCurvature.secondSpectralIntegrand V 0 := by
    funext v
    simp only [RaySpectralCurvature.secondSpectralIntegrand, powerExp, Real.log_zero,
      mul_zero, zero_mul, sub_zero, Real.exp_zero, mul_one]
  rw [heq]
  exact RaySpectralCurvature.measurable_secondSpectralIntegrand V 0

theorem profileIntegrable (U : ℝ) (hU : 0 < U) (G : ℝ → ℝ) (hG : Continuous G) (hG0 : ∀ w, G w ≤ 0)
    (A V s : ℝ) (hA : 0 < A) (hAV : A ≤ V) (hs : 0 < s) (hds : d U ≤ s) : ProfileIntegrable U G A V s := by
  have hV : 0 < V := hA.trans_le hAV
  have hOld := FixedSpectrumPrice.profileIntegrable 1 (by norm_num) G hG hG0 A V s hA hAV hs
  have hk := measurable_kernel V
  have h1m : Measurable (firstSpectralIntegrand U G V s) := hk.mul (continuous_slice U G hG s).measurable
  refine ⟨?_, hOld.second, hOld.third, hOld.fourth⟩
  have hp : Continuous (fun v => (sliceCoefficient U A s / 3) * (V / (2 * Real.pi) * v ^ 2 + v ^ 3 / 2)) := by fun_prop
  apply (hp.intervalIntegrable 0 A).1.mono' h1m.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
  have hn := mul_nonneg (norm_nonneg (prawitzKernel (v / V))) (slice_nonneg U G s v hU hs.le hv.1.le)
  unfold firstSpectralIntegrand spectralKernelWeight
  rw [Real.norm_eq_abs, abs_of_nonneg hn]
  have hvpos : 0 < v := hv.1
  have hh := mul_le_mul (spectralKernelWeight_le V v hV hv.1 (hv.2.trans hAV))
    (slice_le_cubic U hU G hG hG0 A s v hs.le hds hv.1.le hv.2)
    (slice_nonneg U G s v hU hs.le hv.1.le) (by positivity)
  calc
    _ ≤ (V / (2 * Real.pi) / v + 1 / 2) * (sliceCoefficient U A s * v ^ 3 / 3) := by simpa only [spectralKernelWeight] using hh
    _ = _ := by field_simp [hv.1.ne']

theorem core_laplace (U : ℝ) (G : ℝ → ℝ) (s v w : ℝ) (hs : 0 < s) :
    core U G s v w = (Real.exp (-d U * G w) * W U w) *
      powerExp (3 / 2) (FixedSpectrumPrice.spectralRate G v w) s := by
  unfold core
  rw [powerExp_eq_rpow _ _ _ hs]
  have he : -s * (v ^ 2 - w ^ 2) / 2 + (s - d U) * G w =
      -d U * G w + -s * FixedSpectrumPrice.spectralRate G v w := by unfold FixedSpectrumPrice.spectralRate; ring
  rw [he, Real.exp_add]
  ring

theorem core_endpoint (U : ℝ) (hU : 0 < U) (G : ℝ → ℝ) (a b s E l r v w : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hs : 0 < s) (hw : 0 ≤ w)
    (hk : KernelEndpointBound a b s E l r (3 / 2)) :
    core U G s v w ≤ E * (l * core U G a v w + r * core U G b v w) := by
  rw [core_laplace U G s v w hs, core_laplace U G a v w ha, core_laplace U G b v w hb]
  have hc := mul_nonneg (Real.exp_nonneg (-d U * G w)) (W_nonneg U w hU hw)
  have hh := mul_le_mul_of_nonneg_left (hk (3 / 2) (FixedSpectrumPrice.spectralRate G v w) (by norm_num) le_rfl) hc
  convert hh using 1
  ring

private lemma integral_endpoint_le {α : Type*} [MeasurableSpace α] (μ : Measure α) (f fa fb : α → ℝ)
    (E l r : ℝ) (hf : Integrable f μ) (ha : Integrable fa μ) (hb : Integrable fb μ)
    (hle : ∀ᵐ x ∂μ, f x ≤ E * (l * fa x + r * fb x)) :
    (∫ x, f x ∂μ) ≤ E * (l * (∫ x, fa x ∂μ) + r * (∫ x, fb x ∂μ)) := by
  have hd : Integrable (fun x => E * (l * fa x + r * fb x)) μ := ((ha.const_mul l).add (hb.const_mul r)).const_mul E
  have hh := integral_mono_ae hf hd hle
  simpa only [integral_const_mul, integral_add (ha.const_mul l) (hb.const_mul r)] using hh

theorem profile_endpoint_of_core (U : ℝ) (hU : 0 < U) (G : ℝ → ℝ) (hG : Continuous G) (hG0 : ∀ w, G w ≤ 0)
    (A V a b s E l r : ℝ) (hA : 0 < A) (hAV : A ≤ V) (ha : 0 < a) (hb : 0 < b) (hs : 0 < s)
    (hda : d U ≤ a) (hdb : d U ≤ b) (hds : d U ≤ s)
    (hc : ∀ v w, 0 ≤ v → 0 ≤ w → w ≤ v → core U G s v w ≤
      E * (l * core U G a v w + r * core U G b v w))
    (hk : ∀ R, powerExp (1 / 2) R s ≤ E * (l * powerExp (1 / 2) R a + r * powerExp (1 / 2) R b)) :
    spectralProfile U G A V s ≤ E * (l * spectralProfile U G A V a + r * spectralProfile U G A V b) := by
  have hV : 0 < V := hA.trans_le hAV
  have hIa := profileIntegrable U hU G hG hG0 A V a hA hAV ha hda
  have hIb := profileIntegrable U hU G hG hG0 A V b hA hAV hb hdb
  have hIs := profileIntegrable U hU G hG hG0 A V s hA hAV hs hds
  have h1 := integral_endpoint_le (volume.restrict (Ioc 0 A)) _ _ _ E l r hIs.first hIa.first hIb.first (by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    have hca := continuous_core U G hG a v
    have hcb := continuous_core U G hG b v
    have hcs := continuous_core U G hG s v
    have hh := intervalIntegral.integral_mono_on (μ := volume) hv.1.le (hcs.intervalIntegrable 0 v)
      ((((hca.const_mul l).add (hcb.const_mul r)).const_mul E).intervalIntegrable 0 v)
      (fun w hw => hc v w hv.1.le hw.1 hw.2)
    have hslice : firstSlice U G s v ≤ E * (l * firstSlice U G a v + r * firstSlice U G b v) := by
      unfold firstSlice
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
    unfold FixedSpectrumPrice.secondSpectralIntegrand spectralKernelWeight
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

theorem spectralProfile_le_endpoint_max (U : ℝ) (hU : 0 < U) (G : ℝ → ℝ) (hG : Continuous G) (hG0 : ∀ w, G w ≤ 0)
    (A V a b s : ℝ) (hA : 0 < A) (hAV : A ≤ V) (ha : 0 < a) (hab : a < b) (hs : s ∈ Icc a b)
    (hda : d U ≤ a) : spectralProfile U G A V s ≤
    Real.exp ((3 / 2) * ((b - a) ^ 2 / (8 * a ^ 2))) * max (spectralProfile U G A V a) (spectralProfile U G A V b) := by
  have hk := kernelEndpointBound_log_chord a b s (3 / 2) ha hab hs
  have hh := profile_endpoint_of_core U hU G hG hG0 A V a b s _ _ _ hA hAV ha (ha.trans hab) (ha.trans_le hs.1)
    hda (hda.trans hab.le) (hda.trans hs.1)
    (fun v w _ hw _ => core_endpoint U hU G a b s _ _ _ v w ha (ha.trans hab) (ha.trans_le hs.1) hw hk)
    (fun R => hk (1 / 2) R (by norm_num) (by norm_num))
  exact hh.trans (mul_le_mul_of_nonneg_left (mixture_le_max a b s _ _ hab hs) (Real.exp_pos _).le)

private lemma scaled_three_halves (β : ℝ) (hβ : 0 < β) :
    (1 / β ^ 2) ^ (3 / 2 : ℝ) = 1 / β ^ 3 := by
  have hh := Real.rpow_mul_natCast (by positivity : 0 ≤ 1 / β ^ 2) (1 / 2) 3
  norm_num only [Nat.cast_ofNat] at hh
  convert hh.trans (by rw [scaled_one_half β hβ, div_pow, one_pow]) using 1

theorem physicalPrice_spectral_eq (U β : ℝ) (G : ℝ → ℝ) (v : ℝ) (hβ : 0 < β) :
    physicalPrice U β G (v / β) = firstSlice U G (1 / β ^ 2) v := by
  have hsub := intervalIntegral.integral_comp_div (a := (0 : ℝ)) (b := v)
    (WeightedRayPrice.integrand (physicalLoss U β G) (forcing U β)) hβ.ne'
  simp only [zero_div, smul_eq_mul] at hsub
  have hchange : (∫ u in (0 : ℝ)..v / β, WeightedRayPrice.integrand (physicalLoss U β G) (forcing U β) u) =
      (1 / β) * ∫ w in (0 : ℝ)..v, WeightedRayPrice.integrand (physicalLoss U β G) (forcing U β) (w / β) := by
    rw [hsub]
    field_simp [hβ.ne']
  unfold physicalPrice WeightedRayPrice.price firstSlice
  rw [hchange, ← mul_assoc, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro w _
  have hv : β * (w / β) = w := by field_simp [hβ.ne']
  unfold WeightedRayPrice.integrand physicalLoss forcing core
  dsimp only
  rw [hv, scaled_three_halves β hβ]
  have he : Real.exp (-((v / β) ^ 2 / 2)) * Real.exp ((w / β) ^ 2 / 2) *
      Real.exp ((1 / β ^ 2 - d U) * G w) =
      Real.exp (-(1 / β ^ 2) * (v ^ 2 - w ^ 2) / 2 + (1 / β ^ 2 - d U) * G w) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    field_simp [hβ.ne']
    ring
  calc
    _ = (1 / β ^ 3) * (Real.exp (-((v / β) ^ 2 / 2)) * Real.exp ((w / β) ^ 2 / 2) *
        Real.exp ((1 / β ^ 2 - d U) * G w)) * W U w := by field_simp [hβ.ne']
    _ = _ := by rw [he]

lemma betaScale_pos (U : ℝ) (n : ℕ) (hU : 0 < U) (hn : 0 < n) :
    0 < UpperMomentDamping.betaScale U n :=
  div_pos hU (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn))

lemma d_le_sScale (U : ℝ) (n : ℕ) (hn : 0 < n) : d U ≤ UpperMomentDamping.sScale U n := by
  unfold d UpperMomentDamping.sScale
  exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.succ_le_of_lt hn) (sq_nonneg U)

lemma scaled_sinePrimitive_le_forcing (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (U : ℝ) (hU : 0 < U) (hρ : thirdAbsoluteMoment μ ≤ U)
    (n : ℕ) (hn : 0 < n) (t : ℝ) (ht : 0 ≤ t) :
    Real.sqrt n * IidSmoothingPrice.sinePrimitive μ (t / Real.sqrt n) ≤
      UpperMomentDamping.betaScale U n * forcing U (UpperMomentDamping.betaScale U n) t := by
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  have hh := mul_le_mul_of_nonneg_left
    (FiniteRhoSinePrice.sinePrimitive_le_H μ h U (t / Real.sqrt n) hρ (div_nonneg ht hs.le)) hs.le
  have harg : UpperMomentDamping.betaScale U n * t / U = t / Real.sqrt n := by
    unfold UpperMomentDamping.betaScale
    field_simp [hU.ne', hs.ne']
  have he : UpperMomentDamping.betaScale U n * forcing U (UpperMomentDamping.betaScale U n) t =
      Real.sqrt n * FiniteRhoSinePrice.H U (t / Real.sqrt n) := by
    unfold forcing W
    rw [harg]
    dsimp only [UpperMomentDamping.betaScale]
    field_simp [hU.ne', hs.ne']
  exact hh.trans_eq he.symm

lemma price_const_forcing (L F : ℝ → ℝ) (c t : ℝ) :
    WeightedRayPrice.price L (fun u => c * F u) t = c * WeightedRayPrice.price L F t := by
  have hf : WeightedRayPrice.integrand L (fun u => c * F u) =
      (fun u => c * WeightedRayPrice.integrand L F u) := by
    funext u
    unfold WeightedRayPrice.integrand
    ring
  unfold WeightedRayPrice.price
  rw [hf, intervalIntegral.integral_const_mul]
  ring

/-- The actual-beta VoC theorem is rescaled by its exact constant ratio.
The forcing is the complete two-cap sine primitive at the upper scale. -/
theorem normalized_error_div_scale_le_price (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (U : ℝ) (hU : 0 < U) (hρ : thirdAbsoluteMoment μ ≤ U)
    (n : ℕ) (hn : 0 < n) (t : ℝ) (ht : 0 ≤ t) :
    ‖charFun (μ : Measure ℝ) (t / Real.sqrt n) ^ n -
      (Real.exp (-(t ^ 2 / 2)) : ℂ)‖ / UpperMomentDamping.betaScale U n ≤
      physicalPrice U (UpperMomentDamping.betaScale U n) (UpperMomentDamping.G U U) t := by
  let β := UpperMomentDamping.betaScale U n
  let B := beta μ n
  have hβ : 0 < β := betaScale_pos U n hU hn
  have hB : 0 < B := div_pos
    (lt_of_lt_of_le zero_lt_one (ThirdMomentRegion.one_le_third μ h))
    (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn))
  have hs : UpperMomentDamping.sScale U n = 1 / β ^ 2 :=
    UpperMomentDamping.sScale_eq_inv_betaScale_sq U n hU hn
  have hPred (u : ℝ) (_hu : 0 ≤ u) :
      ‖charFun (μ : Measure ℝ) (u / Real.sqrt n)‖ ^ (n - 1) ≤
        physicalLoss U β (UpperMomentDamping.G U U) u := by
    simpa only [physicalLoss, ← hs, d] using
      UpperMomentDamping.normalized_pred_power_le_exp μ h U U hU hρ n hn u
  have hF : Continuous (fun u => (β / B) * forcing U β u) :=
    continuous_const.mul (continuous_forcing U β)
  have hh := WeightedRayPrice.normalized_error_div_beta_le_price μ h n hn
    (physicalLoss U β (UpperMomentDamping.G U U)) (fun u => (β / B) * forcing U β u)
    (continuous_physicalLoss U β _ (UpperMomentDamping.continuous_G U U)) hF hPred t ht (by
      intro u hu
      have hf := scaled_sinePrimitive_le_forcing μ h U hU hρ n hn u hu.1
      change Real.sqrt n * IidSmoothingPrice.sinePrimitive μ (u / Real.sqrt n) ≤ B * ((β / B) * forcing U β u)
      apply hf.trans_eq
      change β * forcing U β u = B * ((β / B) * forcing U β u)
      field_simp [hB.ne'])
  rw [price_const_forcing] at hh
  have hh' := (div_le_iff₀ hB).mp hh
  have he : ((β / B) * WeightedRayPrice.price (physicalLoss U β (UpperMomentDamping.G U U))
      (forcing U β) t) * B = β * physicalPrice U β (UpperMomentDamping.G U U) t := by
    unfold physicalPrice
    field_simp [hB.ne']
  rw [he] at hh'
  exact (div_le_iff₀ hβ).mpr (by simpa only [mul_comm] using hh')

private theorem actual_comparison (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (U : ℝ) (hU : 0 < U) (hρ : thirdAbsoluteMoment μ ≤ U) (n : ℕ) (hn : 0 < n)
    (A V : ℝ) (hA : 0 < A) (hAV : A ≤ V) :
    (IntegrableOn (actualFirstSpectralIntegrand μ n (UpperMomentDamping.betaScale U n) V) (Ioc 0 A) ∧
      IntegrableOn (actualSecondSpectralIntegrand μ n (UpperMomentDamping.betaScale U n) V) (Ioc A V) ∧
      IntegrableOn (thirdSpectralIntegrand V (UpperMomentDamping.sScale U n)) (Ioc 0 A) ∧
      IntegrableOn (fourthSpectralIntegrand (UpperMomentDamping.sScale U n)) (Ioi A)) ∧
    actualSpectralProfile μ n (UpperMomentDamping.betaScale U n) A V ≤
      spectralProfile U (UpperMomentDamping.G U U) A V (UpperMomentDamping.sScale U n) := by
  let β := UpperMomentDamping.betaScale U n
  let G := UpperMomentDamping.G U U
  have hβ : 0 < β := betaScale_pos U n hU hn
  have hs : UpperMomentDamping.sScale U n = 1 / β ^ 2 :=
    UpperMomentDamping.sScale_eq_inv_betaScale_sq U n hU hn
  have hds : d U ≤ 1 / β ^ 2 := hs ▸ d_le_sScale U n hn
  have hV : 0 < V := hA.trans_le hAV
  have hI := profileIntegrable U hU G (UpperMomentDamping.continuous_G U U)
    (UpperMomentDamping.G_nonpos U U) A V (1 / β ^ 2) hA hAV (by positivity) hds
  have h1point (v : ℝ) (hv : 0 ≤ v) : actualFirstSpectralIntegrand μ n β V v ≤ firstSpectralIntegrand U G V (1 / β ^ 2) v := by
    have hh := normalized_error_div_scale_le_price μ h U hU hρ n hn (v / β) (div_nonneg hv hβ.le)
    rw [physicalPrice_spectral_eq U β G v hβ] at hh
    exact mul_le_mul_of_nonneg_left hh (norm_nonneg (prawitzKernel (v / V)))
  have h2point (v : ℝ) (hv : 0 ≤ v) : actualSecondSpectralIntegrand μ n β V v ≤ FixedSpectrumPrice.secondSpectralIntegrand G V (1 / β ^ 2) v := by
    have hh := div_le_div_of_nonneg_right
      (UpperMomentDamping.normalized_power_le_exp μ h U U hU hρ n hn (v / β)) hβ.le
    have harg : β * (v / β) = v := by field_simp [hβ.ne']
    change _ ≤ Real.exp (UpperMomentDamping.sScale U n * G (β * (v / β))) / β at hh
    rw [harg, hs] at hh
    have he : powerExp (1 / 2) (-G v) (1 / β ^ 2) = Real.exp ((1 / β ^ 2) * G v) / β := by
      rw [powerExp_half_scale β _ hβ]
      congr 2
      ring
    unfold actualSecondSpectralIntegrand FixedSpectrumPrice.secondSpectralIntegrand
    rw [he, norm_pow]
    exact mul_le_mul_of_nonneg_left hh (norm_nonneg (prawitzKernel (v / V)))
  have h1m : Measurable (actualFirstSpectralIntegrand μ n β V) := by
    unfold actualFirstSpectralIntegrand
    exact (measurable_kernel V).mul (by fun_prop)
  have h2m : Measurable (actualSecondSpectralIntegrand μ n β V) := by
    unfold actualSecondSpectralIntegrand
    exact (measurable_kernel V).mul (by fun_prop)
  have h1I : IntegrableOn (actualFirstSpectralIntegrand μ n β V) (Ioc 0 A) := by
    apply hI.first.mono' h1m.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    have hnn : 0 ≤ actualFirstSpectralIntegrand μ n β V v := by unfold actualFirstSpectralIntegrand spectralKernelWeight; positivity
    simpa only [Real.norm_eq_abs, abs_of_nonneg hnn] using h1point v hv.1.le
  have h2I : IntegrableOn (actualSecondSpectralIntegrand μ n β V) (Ioc A V) := by
    apply hI.second.mono' h2m.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    have hnn : 0 ≤ actualSecondSpectralIntegrand μ n β V v := by unfold actualSecondSpectralIntegrand spectralKernelWeight; positivity
    simpa only [Real.norm_eq_abs, abs_of_nonneg hnn] using h2point v (hA.trans hv.1).le
  refine ⟨⟨h1I, h2I, hs ▸ hI.third, hs ▸ hI.fourth⟩, ?_⟩
  have h1 := integral_mono_ae h1I hI.first (by filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv; exact h1point v hv.1.le)
  have h2 := integral_mono_ae h2I hI.second (by filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv; exact h2point v (hA.trans hv.1).le)
  have h1' := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 2 / V)
  have h2' := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ 2 / V)
  rw [hs]
  change actualSpectralProfile μ n β A V ≤ spectralProfile U G A V (1 / β ^ 2)
  unfold actualSpectralProfile spectralProfile
  linarith only [h1', h2']

theorem actual_four_integrands_integrable (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (U : ℝ) (hU : 0 < U) (hρ : thirdAbsoluteMoment μ ≤ U) (n : ℕ) (hn : 0 < n)
    (A V : ℝ) (hA : 0 < A) (hAV : A ≤ V) :
    IntegrableOn (actualFirstSpectralIntegrand μ n (UpperMomentDamping.betaScale U n) V) (Ioc 0 A) ∧
      IntegrableOn (actualSecondSpectralIntegrand μ n (UpperMomentDamping.betaScale U n) V) (Ioc A V) ∧
      IntegrableOn (thirdSpectralIntegrand V (UpperMomentDamping.sScale U n)) (Ioc 0 A) ∧
      IntegrableOn (fourthSpectralIntegrand (UpperMomentDamping.sScale U n)) (Ioi A) :=
  (actual_comparison μ h U hU hρ n hn A V hA hAV).1

/-- Every threshold of the original iid law, with arbitrary positive U
above its actual third absolute moment. The profile has no rho lower bound. -/
theorem normalized_actual_cdf_le_scale_spectralProfile (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (U : ℝ) (hU : 0 < U) (hρ : thirdAbsoluteMoment μ ≤ U) (n : ℕ) (hn : 0 < n)
    (A V : ℝ) (hA : 0 < A) (hAV : A ≤ V) (x : ℝ) :
    |(normalizedIidSumLaw μ n).real (Iic x) - GaussianTools.Phi x| ≤
      UpperMomentDamping.betaScale U n *
        spectralProfile U (UpperMomentDamping.G U U) A V (UpperMomentDamping.sScale U n) := by
  have hβ := betaScale_pos U n hU hn
  have hh := div_le_div_of_nonneg_right (PrawitzSmoothing.normalized_actual_cdf_le μ h n hn
    (A / UpperMomentDamping.betaScale U n) (V / UpperMomentDamping.betaScale U n)
    (div_pos hA hβ) (div_le_div_of_nonneg_right hAV hβ.le) x) hβ.le
  rw [normalizedEnvelope_div_beta_eq_actualSpectralProfile μ n (UpperMomentDamping.betaScale U n) A V hβ hA hAV] at hh
  have hm := hh.trans (actual_comparison μ h U hU hρ n hn A V hA hAV).2
  simpa only [mul_comm] using (div_le_iff₀ hβ).mp hm

theorem normalized_actual_cdf_le_endpoints (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (U : ℝ) (hU : 0 < U) (hρ : thirdAbsoluteMoment μ ≤ U) (n : ℕ) (hn : 0 < n)
    (A V a b : ℝ) (hA : 0 < A) (hAV : A ≤ V) (ha : 0 < a) (hab : a < b)
    (hs : UpperMomentDamping.sScale U n ∈ Icc a b) (hda : d U ≤ a) (x : ℝ) :
    |(normalizedIidSumLaw μ n).real (Iic x) - GaussianTools.Phi x| ≤
      UpperMomentDamping.betaScale U n *
        (Real.exp ((3 / 2) * ((b - a) ^ 2 / (8 * a ^ 2))) *
          max (spectralProfile U (UpperMomentDamping.G U U) A V a)
            (spectralProfile U (UpperMomentDamping.G U U) A V b)) := by
  apply (normalized_actual_cdf_le_scale_spectralProfile μ h U hU hρ n hn A V hA hAV x).trans
  exact mul_le_mul_of_nonneg_left
    (spectralProfile_le_endpoint_max U hU (UpperMomentDamping.G U U)
      (UpperMomentDamping.continuous_G U U) (UpperMomentDamping.G_nonpos U U)
      A V a b _ hA hAV ha hab hs hda) (betaScale_pos U n hU hn).le

/-- A whole sample-size slab is located by n/U²; its price uses only the
two fixed scale nodes N/U² and M/U². -/
theorem normalized_actual_cdf_le_sample_endpoints (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (U : ℝ) (hU : 0 < U) (hρ : thirdAbsoluteMoment μ ≤ U) (n N M : ℕ)
    (hN : 0 < N) (hNM : N < M) (hNn : N ≤ n) (hnM : n ≤ M)
    (A V : ℝ) (hA : 0 < A) (hAV : A ≤ V) (x : ℝ) :
    |(normalizedIidSumLaw μ n).real (Iic x) - GaussianTools.Phi x| ≤
      UpperMomentDamping.betaScale U n *
        (Real.exp ((3 / 2) *
            ((UpperMomentDamping.sScale U M - UpperMomentDamping.sScale U N) ^ 2 /
              (8 * UpperMomentDamping.sScale U N ^ 2))) *
          max (spectralProfile U (UpperMomentDamping.G U U) A V (UpperMomentDamping.sScale U N))
            (spectralProfile U (UpperMomentDamping.G U U) A V (UpperMomentDamping.sScale U M))) := by
  have hn : 0 < n := hN.trans_le hNn
  have hU2 : 0 < U ^ 2 := sq_pos_of_pos hU
  have ha : 0 < UpperMomentDamping.sScale U N :=
    div_pos (Nat.cast_pos.mpr hN) hU2
  have hab : UpperMomentDamping.sScale U N < UpperMomentDamping.sScale U M :=
    (div_lt_div_iff_of_pos_right hU2).mpr (Nat.cast_lt.mpr hNM)
  have hs : UpperMomentDamping.sScale U n ∈
      Icc (UpperMomentDamping.sScale U N) (UpperMomentDamping.sScale U M) :=
    ⟨div_le_div_of_nonneg_right (Nat.cast_le.mpr hNn) hU2.le,
      div_le_div_of_nonneg_right (Nat.cast_le.mpr hnM) hU2.le⟩
  exact normalized_actual_cdf_le_endpoints μ h U hU hρ n hn A V _ _ hA hAV ha hab hs
    (d_le_sScale U N hN) x

/-- A moment lower bound enters only when converting the proved CDF bound
to the customary sqrt(n)/rho ratio, after the profile is fully fixed. -/
theorem normalized_actual_cdf_ratio_le_endpoints (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (U L : ℝ) (hU : 0 < U) (hL : 0 < L)
    (hρ : thirdAbsoluteMoment μ ≤ U) (hLρ : L ≤ thirdAbsoluteMoment μ) (n : ℕ) (hn : 0 < n)
    (A V a b : ℝ) (hA : 0 < A) (hAV : A ≤ V) (ha : 0 < a) (hab : a < b)
    (hs : UpperMomentDamping.sScale U n ∈ Icc a b) (hda : d U ≤ a) (x : ℝ) :
    Real.sqrt n * |(normalizedIidSumLaw μ n).real (Iic x) - GaussianTools.Phi x| /
      thirdAbsoluteMoment μ ≤ (U / L) *
        (Real.exp ((3 / 2) * ((b - a) ^ 2 / (8 * a ^ 2))) *
          max (spectralProfile U (UpperMomentDamping.G U U) A V a)
            (spectralProfile U (UpperMomentDamping.G U U) A V b)) := by
  let C := Real.exp ((3 / 2) * ((b - a) ^ 2 / (8 * a ^ 2))) *
    max (spectralProfile U (UpperMomentDamping.G U U) A V a)
      (spectralProfile U (UpperMomentDamping.G U U) A V b)
  have hh := normalized_actual_cdf_le_endpoints μ h U hU hρ n hn A V a b hA hAV ha hab hs hda x
  change |(normalizedIidSumLaw μ n).real (Iic x) - GaussianTools.Phi x| ≤
    UpperMomentDamping.betaScale U n * C at hh
  have hβ := betaScale_pos U n hU hn
  have hC : 0 ≤ C := nonneg_of_mul_nonneg_right ((abs_nonneg _).trans hh) hβ
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  have hmul := mul_le_mul_of_nonneg_left hh hsqrt.le
  have he : Real.sqrt n * (UpperMomentDamping.betaScale U n * C) = U * C := by
    unfold UpperMomentDamping.betaScale
    field_simp [hsqrt.ne']
  rw [he] at hmul
  calc
    _ ≤ (U * C) / thirdAbsoluteMoment μ :=
      div_le_div_of_nonneg_right hmul (hL.trans_le hLρ).le
    _ ≤ (U * C) / L := div_le_div_of_nonneg_left (mul_nonneg hU.le hC) hL hLρ
    _ = _ := by dsimp [C]; ring

end BerryEsseen.UpperMomentSpectrumPrice

#print axioms BerryEsseen.UpperMomentSpectrumPrice.W_le
#print axioms BerryEsseen.UpperMomentSpectrumPrice.profileIntegrable
#print axioms BerryEsseen.UpperMomentSpectrumPrice.core_laplace
#print axioms BerryEsseen.UpperMomentSpectrumPrice.spectralProfile_le_endpoint_max
#print axioms BerryEsseen.UpperMomentSpectrumPrice.physicalPrice_spectral_eq
#print axioms BerryEsseen.UpperMomentSpectrumPrice.scaled_sinePrimitive_le_forcing
#print axioms BerryEsseen.UpperMomentSpectrumPrice.normalized_error_div_scale_le_price
#print axioms BerryEsseen.UpperMomentSpectrumPrice.actual_four_integrands_integrable
#print axioms BerryEsseen.UpperMomentSpectrumPrice.normalized_actual_cdf_le_scale_spectralProfile
#print axioms BerryEsseen.UpperMomentSpectrumPrice.normalized_actual_cdf_le_endpoints
#print axioms BerryEsseen.UpperMomentSpectrumPrice.normalized_actual_cdf_le_sample_endpoints
#print axioms BerryEsseen.UpperMomentSpectrumPrice.normalized_actual_cdf_ratio_le_endpoints
