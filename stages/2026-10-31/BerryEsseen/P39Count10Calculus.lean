module

public import BerryEsseen.P39Count11Face
public import BerryEsseen.BinomialPrefixGate
public import BerryEsseen.ConvexPriceComposition

@[expose] public section

/-! 2026-10-29: native calculus and signed coarse bounds for the literal
count-10 coefficients on P39 and phase [-1/8,0]. These fixed coefficients
are joined to the actual reference law in P39Count10Coarse. -/

namespace BerryEsseen.P39Count10Calculus

open MeasureTheory Set Filter
open GaussianTools BinomialWeights P39Count11Face
open scoped Topology ContDiff

noncomputable section

def phaseStrip : Set ℝ := Icc (-1 / 8) 0
def ci : ℝ := 803 / 10000
def K : ℝ := (1 - delta) * (11 / 16)
def eta (p : ℝ) : ℝ := mass 26 11 p / (1 - delta)
def etaSlope (p : ℝ) : ℝ := massSlope 26 11 p / (1 - delta)
def etaCurvature (p : ℝ) : ℝ := massCurvature 26 11 p / (1 - delta)
def A (p : ℝ) : ℝ := K * (1 - p) / p
def ASlope (p : ℝ) : ℝ := -K / p ^ 2
def ACurvature (p : ℝ) : ℝ := 2 * K / p ^ 3
def arg (t p : ℝ) : ℝ := ProbabilityGaussianPrice.argument 26 10 t 0 p
def gaussian (t p : ℝ) : ℝ := ProbabilityGaussianPrice.gaussianPrice 26 10 t 0 p
def baseline (t p : ℝ) : ℝ := lowerPrefix 26 10 p - gaussian t p - ci * P39Reference.rho0 p
def smoothBase (t p : ℝ) : ℝ := baseline t p + eta p * t

lemma K_bounds : 0 ≤ K ∧ K ≤ (13 : ℝ) / 20 := by
  norm_num [K, delta, N26P39Price.inward]

lemma eta_contDiff : ContDiff ℝ 2 eta := (contDiff_two_mass 26 11).div_const (1 - delta)

lemma rho_contDiffOn : ContDiffOn ℝ 2 P39Reference.rho0 (Ioo (0 : ℝ) 1) := by
  have hv : ContDiffOn ℝ 2 P39Reference.v (Ioo (0 : ℝ) 1) := by unfold P39Reference.v; fun_prop
  exact (contDiffOn_const.sub (contDiffOn_const.mul hv)).div
    (hv.sqrt (fun p hp => (P39Reference.v_pos hp.1 hp.2).ne'))
    (fun p hp => (Real.sqrt_pos.mpr (P39Reference.v_pos hp.1 hp.2)).ne')

lemma A_contDiffOn : ContDiffOn ℝ 2 A (Ioo (0 : ℝ) 1) := by
  unfold A
  exact (contDiffOn_const.mul (contDiffOn_const.sub contDiffOn_id)).div contDiffOn_id (fun p hp => hp.1.ne')

lemma baseline_contDiffOn (t : ℝ) : ContDiffOn ℝ 2 (baseline t) (Ioo (0 : ℝ) 1) :=
  ((contDiff_two_prefix 26 10).contDiffOn.sub
    (ProbabilityGaussianPrice.gaussianPrice_contDiffOn (by norm_num) (by norm_num))).sub
      (contDiffOn_const.mul rho_contDiffOn)

lemma smoothBase_contDiffOn (t : ℝ) : ContDiffOn ℝ 2 (smoothBase t) (Ioo (0 : ℝ) 1) :=
  (baseline_contDiffOn t).add (eta_contDiff.contDiffOn.mul contDiffOn_const)

lemma eta_nonneg {p : ℝ} (hp : p ∈ strip) : 0 ≤ eta p :=
  div_nonneg (mass_nonneg 26 11 p (domain hp).1.le (domain hp).2.le) (sub_nonneg.mpr delta_lt_one.le)

lemma eta_upper {p : ℝ} (hp : p ∈ strip) : eta p ≤ (9 : ℝ) / 50 := by
  have hδ : delta = (5769 : ℝ) / 100000 := by norm_num [delta, N26P39Price.inward]
  unfold eta
  apply (div_le_iff₀ (sub_pos.mpr delta_lt_one)).mpr
  rw [hδ]
  linarith only [mass11_upper hp]

theorem hasDerivAt_eta {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) : HasDerivAt eta (etaSlope p) p :=
  (hasDerivAt_mass 26 11 p hp.1 hp.2 (by norm_num)).div_const (1 - delta)

theorem hasDerivAt_deriv_eta {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (deriv eta) (etaCurvature p) p := by
  have heq : deriv eta =ᶠ[𝓝 p] (fun x => deriv (mass 26 11) x / (1 - delta)) := by
    filter_upwards [Ioo_mem_nhds hp.1 hp.2] with x hx
    rw [(hasDerivAt_eta hx).deriv, (hasDerivAt_mass 26 11 x hx.1 hx.2 (by norm_num)).deriv]
    rfl
  exact ((hasDerivAt_deriv_mass 26 11 p hp.1 hp.2 (by norm_num)).div_const
    (1 - delta)).congr_of_eventuallyEq heq

lemma etaSlope_eq {p : ℝ} (hp : p ∈ strip) : etaSlope p = eta p * (11 - 26 * p) / P39Reference.v p := by
  unfold etaSlope eta massSlope P39Reference.v
  norm_num only [Nat.cast_ofNat]
  field_simp [(domain hp).1.ne', (sub_pos.mpr (domain hp).2).ne', (sub_pos.mpr delta_lt_one).ne']

lemma etaCurvature_eq {p : ℝ} (hp : p ∈ strip) :
    etaCurvature p = eta p * ((11 - 26 * p) ^ 2 - 11 * (1 - p) ^ 2 - 15 * p ^ 2) / (P39Reference.v p) ^ 2 := by
  unfold etaCurvature eta massCurvature P39Reference.v
  norm_num only [Nat.cast_ofNat, Nat.reduceSub]
  field_simp [(domain hp).1.ne', (sub_pos.mpr (domain hp).2).ne', (sub_pos.mpr delta_lt_one).ne']

lemma etaSlope_nonneg {p : ℝ} (hp : p ∈ strip) : 0 ≤ etaSlope p := by
  rw [etaSlope_eq hp]
  exact div_nonneg (mul_nonneg (eta_nonneg hp) (by linarith only [hp.2]))
    (P39Reference.v_pos (domain hp).1 (domain hp).2).le

lemma etaCurvature_bounds {p : ℝ} (hp : p ∈ strip) : -30 ≤ etaCurvature p ∧ etaCurvature p ≤ 0 := by
  have hq : (3 : ℝ) / 5 ≤ 1 - p ∧ 1 - p ≤ 61 / 100 := by constructor <;> linarith only [hp.1, hp.2]
  have hq0 : 0 ≤ 1 - p := by linarith only [hq.1]
  have hp0 : 0 ≤ p := (domain hp).1.le
  have hp2 := (sq_le_sq₀ hp0 (by norm_num : (0 : ℝ) ≤ 2 / 5)).mpr hp.2
  have hq2 := (sq_le_sq₀ hq0 (by norm_num : (0 : ℝ) ≤ 61 / 100)).mpr hq.2
  have hq2lo := (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 3 / 5) hq0).mpr hq.1
  have hN := numerator_bounds hp
  have hN0 : 0 ≤ 11 - 26 * p := by linarith only [hN.1]
  have hN2 := (sq_le_sq₀ hN0 (by norm_num : (0 : ℝ) ≤ 43 / 50)).mpr hN.2
  let D := (11 - 26 * p) ^ 2 - 11 * (1 - p) ^ 2 - 15 * p ^ 2
  have hDlo : -(13 : ℝ) / 2 ≤ D := by dsimp only [D]; nlinarith only [sq_nonneg (11 - 26 * p), hp2, hq2]
  have hDhi : D ≤ 0 := by dsimp only [D]; nlinarith only [hN2, hq2lo, sq_nonneg p]
  have hv := P39NoiseGate.variance_bounds hp
  have hv0 : 0 < P39Reference.v p := P39Reference.v_pos (domain hp).1 (domain hp).2
  have hv2 := (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 7 / 30) hv0.le).mpr hv.1
  have hprod : -(117 : ℝ) / 100 ≤ eta p * D := by
    calc
      _ = (9 / 50 : ℝ) * (-13 / 2) := by norm_num
      _ ≤ eta p * (-13 / 2) := mul_le_mul_of_nonpos_right (eta_upper hp) (by norm_num)
      _ ≤ eta p * D := mul_le_mul_of_nonneg_left hDlo (eta_nonneg hp)
  rw [etaCurvature_eq hp]
  change -30 ≤ eta p * D / (P39Reference.v p) ^ 2 ∧ eta p * D / (P39Reference.v p) ^ 2 ≤ 0
  constructor
  · apply (le_div_iff₀ (sq_pos_of_pos hv0)).mpr
    nlinarith only [hprod, hv2]
  · exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (eta_nonneg hp) hDhi) (sq_nonneg _)

theorem hasDerivAt_A {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) : HasDerivAt A (ASlope p) p := by
  have h := ((HasDerivAt.const_sub 1 (hasDerivAt_id' p)).const_mul K).fun_div (hasDerivAt_id' p) hp.1.ne'
  convert h using 1
  · rfl
  · unfold ASlope
    field_simp [hp.1.ne']
    ring

theorem hasDerivAt_deriv_A {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (deriv A) (ACurvature p) p := by
  have heq : deriv A =ᶠ[𝓝 p] (fun x => -K / x ^ 2) := by
    filter_upwards [Ioo_mem_nhds hp.1 hp.2] with x hx
    exact (hasDerivAt_A hx).deriv
  have h := (hasDerivAt_const p (-K)).fun_div ((hasDerivAt_id' p).fun_pow 2) (pow_ne_zero _ hp.1.ne')
  convert h.congr_of_eventuallyEq heq using 1
  unfold ACurvature
  field_simp [hp.1.ne']
  ring

lemma ASlope_nonpos {p : ℝ} (_hp : p ∈ strip) : ASlope p ≤ 0 :=
  div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr K_bounds.1) (sq_nonneg p)

lemma ACurvature_bounds {p : ℝ} (hp : p ∈ strip) : 0 ≤ ACurvature p ∧ ACurvature p ≤ 25 := by
  have hp0 := (domain hp).1
  have hp3 : ((39 : ℝ) / 100) ^ 3 ≤ p ^ 3 := pow_le_pow_left₀ (by norm_num) hp.1 3
  unfold ACurvature
  constructor
  · exact div_nonneg (mul_nonneg (by norm_num) K_bounds.1) (pow_nonneg hp0.le _)
  · apply (div_le_iff₀ (pow_pos hp0 3)).mpr
    nlinarith only [K_bounds.2, hp3]

lemma A_antitone : AntitoneOn A strip := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
  · intro p hp; exact (hasDerivAt_A (domain hp)).continuousAt.continuousWithinAt
  · intro p hp; exact (hasDerivAt_A (domain (interior_subset hp))).differentiableAt.differentiableWithinAt
  · intro p hp
    rw [(hasDerivAt_A (domain (interior_subset hp))).deriv]
    exact ASlope_nonpos (interior_subset hp)

lemma mass10_upper {p : ℝ} (hp : p ∈ strip) : mass 26 10 p ≤ (17 : ℝ) / 100 := by
  have hflux := BinomialPrefixGate.adjacent_mass_flux 26 10 p (by norm_num)
  norm_num only [Nat.reduceAdd, Nat.reduceSub, Nat.cast_ofNat] at hflux
  have hq : 1 - p ≤ (61 : ℝ) / 100 := by linarith only [hp.1]
  have hp0 := (domain hp).1
  have hq0 : 0 ≤ 1 - p := sub_nonneg.mpr (domain hp).2.le
  have hm0 := mass_nonneg 26 10 p hp0.le (domain hp).2.le
  have hm1 := mass_nonneg 26 11 p hp0.le (domain hp).2.le
  have hright := mul_le_mul hq (mass11_upper hp) hm1 (by norm_num : (0 : ℝ) ≤ 61 / 100)
  have hleft := mul_le_mul_of_nonneg_right hp.1 hm0
  nlinarith only [hflux, hright, hleft]

lemma prefixCurvature_lower {p : ℝ} (hp : p ∈ strip) : -5 ≤ prefixCurvature 26 10 p := by
  have hp0 := (domain hp).1
  have hq : (3 : ℝ) / 5 ≤ 1 - p := by linarith only [hp.2]
  have hq0 : 0 < 1 - p := sub_pos.mpr (domain hp).2
  have hq2 := (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 3 / 5) hq0.le).mpr hq
  have hden := mul_le_mul hp.1 hq2 (by norm_num : (0 : ℝ) ≤ (3 / 5) ^ 2) hp0.le
  have hN0 : 0 ≤ 10 - 25 * p := by linarith only [hp.2]
  have hN : 10 - 25 * p ≤ (1 : ℝ) / 4 := by linarith only [hp.1]
  have hprod := mul_le_mul (mass10_upper hp) hN hN0 (by norm_num : (0 : ℝ) ≤ 17 / 100)
  change -5 ≤ -16 * mass 26 10 p * (10 - 25 * p) / (p * (1 - p) ^ 2)
  apply (le_div_iff₀ (mul_pos hp0 (sq_pos_of_pos hq0))).mpr
  nlinarith only [hden, hprod]

lemma numerator_bounds {p t : ℝ} (hp : p ∈ strip) (ht : t ∈ phaseStrip) :
    (-21 : ℝ) / 40 ≤ 10 + t - 26 * p ∧ 10 + t - 26 * p ≤ -7 / 50 := by
  constructor <;> linarith only [hp.1, hp.2, ht.1, ht.2]

lemma arg_eq (t p : ℝ) : arg t p = (10 + t - 26 * p) / Real.sqrt (26 * P39Reference.v p) := by
  simp only [arg, ProbabilityGaussianPrice.argument, ProbabilityGaussianPrice.numerator,
    ProbabilityGaussianPrice.variance, Nat.cast_ofNat, add_zero, P39Reference.v]

lemma arg_bounds {p t : ℝ} (hp : p ∈ strip) (ht : t ∈ phaseStrip) : (-7 : ℝ) / 32 ≤ arg t p ∧ arg t p ≤ 0 := by
  have hs := zero_sqrt_bounds hp
  have hslo : (12 : ℝ) / 5 ≤ Real.sqrt (26 * P39Reference.v p) := by linarith only [hs.1]
  have hs0 : 0 < Real.sqrt (26 * P39Reference.v p) := by linarith only [hslo]
  have hN := numerator_bounds hp ht
  rw [arg_eq]
  constructor
  · apply (le_div_iff₀ hs0).mpr
    linarith only [hslo, hN.1]
  · exact div_nonpos_of_nonpos_of_nonneg (by linarith only [hN.2]) hs0.le

lemma varianceSlope_bounds {p : ℝ} (hp : p ∈ strip) :
    0 ≤ 26 * (1 - 2 * p) ∧ 26 * (1 - 2 * p) ≤ (143 : ℝ) / 25 := by
  constructor <;> linarith only [hp.1, hp.2]

lemma argumentSlope_bounds {p t : ℝ} (hp : p ∈ strip) (ht : t ∈ phaseStrip) :
    (-65 : ℝ) / 6 ≤ ProbabilityGaussianPrice.argumentSlope 26 10 t 0 p ∧
      ProbabilityGaussianPrice.argumentSlope 26 10 t 0 p < 0 := by
  let V := 26 * P39Reference.v p
  let R := Real.sqrt V
  let N := 10 + t - 26 * p
  let D := 26 * (1 - 2 * p)
  have hV : 6 ≤ V := by dsimp only [V]; linarith only [(zero_variance_bounds hp).1]
  have hV0 : 0 < V := by linarith only [hV]
  have hR : (12 : ℝ) / 5 ≤ R := by dsimp only [R]; apply Real.le_sqrt_of_sq_le; norm_num; linarith only [hV]
  have hR0 : 0 < R := by linarith only [hR]
  have hN := numerator_bounds hp ht
  have hD := varianceSlope_bounds hp
  have hNDhi : N * D ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by dsimp only [N]; linarith only [hN.2]) hD.1
  have hNDlo : (-63 : ℝ) / 20 ≤ N * D := by
    calc
      _ = (-21 / 40 : ℝ) * 6 := by norm_num
      _ ≤ (-21 / 40 : ℝ) * D := mul_le_mul_of_nonpos_left (by dsimp only [D]; linarith only [hD.2]) (by norm_num)
      _ ≤ N * D := mul_le_mul_of_nonneg_right hN.1 hD.1
  have heq : ProbabilityGaussianPrice.argumentSlope 26 10 t 0 p = -26 / R - N * D / (2 * V * R) := by
    simp only [ProbabilityGaussianPrice.argumentSlope, ProbabilityGaussianPrice.numerator,
      ProbabilityGaussianPrice.variance, ProbabilityGaussianPrice.varianceSlope,
      Nat.cast_ofNat, add_zero, N, D, V, R, P39Reference.v]
  rw [heq]
  constructor
  · have hfirst : (26 : ℝ) / R ≤ 65 / 6 := by apply (div_le_iff₀ hR0).mpr; linarith only [hR]
    have hsecond : N * D / (2 * V * R) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hNDhi (by positivity)
    simp only [neg_div]
    linarith only [hfirst, hsecond]
  · have hnum : 0 < 52 * V + N * D := by linarith only [hV, hNDlo]
    have heq2 : -26 / R - N * D / (2 * V * R) = -(52 * V + N * D) / (2 * V * R) := by
      field_simp [hR0.ne', hV0.ne']
      ring
    rw [heq2]
    exact div_neg_of_neg_of_pos (neg_neg_of_pos hnum) (by positivity)

lemma argumentCurvature_upper {p t : ℝ} (hp : p ∈ strip) (ht : t ∈ phaseStrip) :
    ProbabilityGaussianPrice.argumentCurvature 26 10 t 0 p ≤ (1859 : ℝ) / 180 := by
  let V := 26 * P39Reference.v p
  let R := Real.sqrt V
  let N := 10 + t - 26 * p
  let D := 26 * (1 - 2 * p)
  have hV : 6 ≤ V := by dsimp only [V]; linarith only [(zero_variance_bounds hp).1]
  have hV0 : 0 < V := by linarith only [hV]
  have hR : (12 : ℝ) / 5 ≤ R := by dsimp only [R]; apply Real.le_sqrt_of_sq_le; norm_num; linarith only [hV]
  have hR0 : 0 < R := by linarith only [hR]
  have hVR : (72 : ℝ) / 5 ≤ V * R := by
    have h := mul_le_mul hV hR (by norm_num : (0 : ℝ) ≤ 12 / 5) hV0.le
    nlinarith only [h]
  have hN : N ≤ 0 := by dsimp only [N]; linarith only [(numerator_bounds hp ht).2]
  have hD := (varianceSlope_bounds hp).2
  have hfirst : 26 * D / (V * R) ≤ (1859 : ℝ) / 180 := by
    apply (div_le_iff₀ (mul_pos hV0 hR0)).mpr
    nlinarith only [hVR, hD]
  have hsecond : 26 * N / (V * R) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by norm_num) hN) (by positivity)
  have hthird : 3 * N * D ^ 2 / (4 * V ^ 2 * R) ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg
    · exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by norm_num) hN) (sq_nonneg _)
    · positivity
  have heq : ProbabilityGaussianPrice.argumentCurvature 26 10 t 0 p =
      26 * D / (V * R) + 26 * N / (V * R) + 3 * N * D ^ 2 / (4 * V ^ 2 * R) := by
    simp only [ProbabilityGaussianPrice.argumentCurvature, ProbabilityGaussianPrice.numerator,
      ProbabilityGaussianPrice.variance, ProbabilityGaussianPrice.varianceSlope,
      Nat.cast_ofNat, add_zero, N, D, V, R, P39Reference.v]
  rw [heq]
  linarith only [hfirst, hsecond, hthird]

lemma gaussianCurvature_upper {p t : ℝ} (hp : p ∈ strip) (ht : t ∈ phaseStrip) :
    ProbabilityGaussianPrice.gaussianPriceCurvature 26 10 t 0 p ≤ 15 := by
  have hz := arg_bounds hp ht
  have hs := argumentSlope_bounds hp ht
  have hsq : (ProbabilityGaussianPrice.argumentSlope 26 10 t 0 p) ^ 2 ≤ ((65 : ℝ) / 6) ^ 2 := by
    nlinarith only [hs.1, hs.2, sq_nonneg (ProbabilityGaussianPrice.argumentSlope 26 10 t 0 p + 65 / 6)]
  have hprod := mul_le_mul (show -arg t p ≤ (7 : ℝ) / 32 by linarith only [hz.1]) hsq
    (sq_nonneg _) (by norm_num : (0 : ℝ) ≤ 7 / 32)
  have hterm : ProbabilityGaussianPrice.argumentCurvature 26 10 t 0 p -
      arg t p * (ProbabilityGaussianPrice.argumentSlope 26 10 t 0 p) ^ 2 ≤
        (1859 : ℝ) / 180 + (7 : ℝ) / 32 * (65 / 6) ^ 2 := by
    nlinarith only [hprod, argumentCurvature_upper hp ht]
  unfold ProbabilityGaussianPrice.gaussianPriceCurvature
  change phi (arg t p) * (ProbabilityGaussianPrice.argumentCurvature 26 10 t 0 p -
    arg t p * (ProbabilityGaussianPrice.argumentSlope 26 10 t 0 p) ^ 2) ≤ 15
  calc
    _ ≤ phi (arg t p) * ((1859 : ℝ) / 180 + (7 : ℝ) / 32 * (65 / 6) ^ 2) :=
      mul_le_mul_of_nonneg_left hterm (phi_nonneg _)
    _ ≤ (2 / 5 : ℝ) * ((1859 : ℝ) / 180 + (7 : ℝ) / 32 * (65 / 6) ^ 2) :=
      mul_le_mul_of_nonneg_right (phi_upper _) (by norm_num)
    _ ≤ 15 := by norm_num

def baselineSlope (t p : ℝ) : ℝ := prefixSlope 26 10 p -
  ProbabilityGaussianPrice.gaussianPriceSlope 26 10 t 0 p - ci * P39Reference.e1 p
def baselineCurvature (t p : ℝ) : ℝ := prefixCurvature 26 10 p -
  ProbabilityGaussianPrice.gaussianPriceCurvature 26 10 t 0 p - ci * P39Reference.e2 p

theorem hasDerivAt_baseline {p t : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (baseline t) (baselineSlope t p) p := by
  have hF := hasDerivAt_prefix 26 10 p hp.1 hp.2 (by norm_num)
  have hG := ProbabilityGaussianPrice.gaussianPrice_hasDerivAt (n := 26) (k := 10) (t := t) (s := 0)
    (by norm_num) (by norm_num) hp
  have hR := (P39Reference.hasDerivAt_rho0 hp.1 hp.2).const_mul ci
  exact (hF.fun_sub hG).fun_sub hR

theorem hasDerivAt_deriv_baseline {p t : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (deriv (baseline t)) (baselineCurvature t p) p := by
  have heq : deriv (baseline t) =ᶠ[𝓝 p] (fun x => deriv (lowerPrefix 26 10) x -
      deriv (gaussian t) x - ci * deriv P39Reference.rho0 x) := by
    filter_upwards [Ioo_mem_nhds hp.1 hp.2] with x hx
    unfold gaussian
    rw [(hasDerivAt_baseline hx).deriv, (hasDerivAt_prefix 26 10 x hx.1 hx.2 (by norm_num)).deriv,
      (ProbabilityGaussianPrice.gaussianPrice_hasDerivAt (n := 26) (k := 10) (t := t) (s := 0)
        (by norm_num) (by norm_num) hx).deriv, (P39Reference.hasDerivAt_rho0 hx.1 hx.2).deriv]
    rfl
  have hF := hasDerivAt_deriv_prefix 26 10 p hp.1 hp.2 (by norm_num)
  have hG := ProbabilityGaussianPrice.gaussianPrice_hasDerivAt_deriv (n := 26) (k := 10) (t := t) (s := 0)
    (by norm_num) (by norm_num) hp
  have hR := (P39Reference.hasDerivAt_deriv_rho0 hp.1 hp.2).const_mul ci
  exact ((hF.fun_sub hG).fun_sub hR).congr_of_eventuallyEq heq

lemma baselineCurvature_lower {p t : ℝ} (hp : p ∈ strip) (ht : t ∈ phaseStrip) : -22 ≤ baselineCurvature t p := by
  have hF := prefixCurvature_lower hp
  have hG := gaussianCurvature_upper hp ht
  have hR := (P39Reference.e2_bounds hp).2
  unfold baselineCurvature ci
  linarith only [hF, hG, hR]

lemma deriv2_smoothBase {p t : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    deriv (deriv (smoothBase t)) p = baselineCurvature t p + etaCurvature p * t := by
  have hb := (baseline_contDiffOn t).contDiffAt (isOpen_Ioo.mem_nhds hp)
  have he := eta_contDiff.contDiffAt (x := p)
  have hprod : deriv (deriv (fun q => eta q * t)) p = etaCurvature p * t := by
    rw [ConvexPriceComposition.deriv2_mul he (by fun_prop)]
    simp only [deriv_const', deriv_const, mul_zero, add_zero, (hasDerivAt_deriv_eta hp).deriv]
  change deriv (deriv (fun q => baseline t q + eta q * t)) p = _
  rw [ConvexPriceComposition.deriv2_add hb (he.mul (by fun_prop)), hprod,
    (hasDerivAt_deriv_baseline hp).deriv]

lemma smoothBaseCurvature_lower {p t : ℝ} (hp : p ∈ strip) (ht : t ∈ phaseStrip) :
    -22 ≤ deriv (deriv (smoothBase t)) p := by
  rw [deriv2_smoothBase (domain hp)]
  have hterm := mul_nonneg_of_nonpos_of_nonpos (etaCurvature_bounds hp).2 ht.2
  linarith only [baselineCurvature_lower hp ht, hterm]

private lemma phi_contDiff_one : ContDiff ℝ 1 phi := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun x => (hasDerivAt_phi x).differentiableAt, ?_⟩
  have heq : deriv phi = (fun x => -x * phi x) := funext (fun x => (hasDerivAt_phi x).deriv)
  rw [heq]
  exact continuous_id.neg.mul continuous_phi

lemma Phi_contDiff_two : ContDiff ℝ 2 Phi := by
  apply (contDiff_succ_iff_deriv (n := 1)).mpr
  refine ⟨fun x => (hasDerivAt_Phi x).differentiableAt, by simp, ?_⟩
  have heq : deriv Phi = phi := funext (fun x => (hasDerivAt_Phi x).deriv)
  rw [heq]
  exact phi_contDiff_one

def phaseSmooth (p t : ℝ) : ℝ := smoothBase t p
def phaseSlope (p t : ℝ) : ℝ := eta p - phi (arg t p) / Real.sqrt (26 * P39Reference.v p)
def phaseCurvature (p t : ℝ) : ℝ := arg t p * phi (arg t p) / (26 * P39Reference.v p)

lemma phaseSmooth_contDiff (p : ℝ) : ContDiff ℝ 2 (phaseSmooth p) := by
  have harg : ContDiff ℝ 2 (fun t => arg t p) := by
    have heq : (fun t => arg t p) = (fun t => (10 + t - 26 * p) / Real.sqrt (26 * P39Reference.v p)) :=
      funext (fun t => arg_eq t p)
    rw [heq]
    fun_prop
  exact ((contDiff_const.sub (Phi_contDiff_two.comp harg)).sub contDiff_const).add
    (contDiff_const.mul contDiff_id)

lemma hasDerivAt_phaseArg (p t : ℝ) :
    HasDerivAt (fun u => arg u p) (1 / Real.sqrt (26 * P39Reference.v p)) t := by
  have h := (((hasDerivAt_id' t).const_add 10).sub_const (26 * p)).div_const (Real.sqrt (26 * P39Reference.v p))
  convert h using 1
  funext u
  exact arg_eq u p

theorem hasDerivAt_phaseSmooth (p t : ℝ) : HasDerivAt (phaseSmooth p) (phaseSlope p t) t := by
  have hG := (hasDerivAt_Phi (arg t p)).comp t (hasDerivAt_phaseArg p t)
  have h := (((hasDerivAt_const t (lowerPrefix 26 10 p)).fun_sub hG).sub_const
    (ci * P39Reference.rho0 p)).fun_add ((hasDerivAt_id' t).const_mul (eta p))
  convert h using 1
  · funext u; rfl
  · unfold phaseSlope
    ring

theorem hasDerivAt_phaseSlope {p : ℝ} (hp : p ∈ strip) (t : ℝ) :
    HasDerivAt (phaseSlope p) (phaseCurvature p t) t := by
  have hv : 0 < 26 * P39Reference.v p := by linarith only [(zero_variance_bounds hp).1]
  have hr := (Real.sqrt_pos.mpr hv).ne'
  have hG := (hasDerivAt_phi (arg t p)).comp t (hasDerivAt_phaseArg p t)
  have h := (hasDerivAt_const t (eta p)).fun_sub (hG.div_const (Real.sqrt (26 * P39Reference.v p)))
  convert h using 1
  · funext u; rfl
  · unfold phaseCurvature
    have hs := Real.sq_sqrt hv.le
    have hvp := (P39Reference.v_pos (domain hp).1 (domain hp).2).ne'
    generalize heq : Real.sqrt (26 * P39Reference.v p) = r at *
    field_simp [hr, hvp]
    rw [hs]
    ring

lemma phaseCurvature_lower {p t : ℝ} (hp : p ∈ strip) (ht : t ∈ phaseStrip) :
    -(1 : ℝ) / 64 ≤ phaseCurvature p t := by
  have hz := arg_bounds hp ht
  have hprod : -(7 : ℝ) / 80 ≤ arg t p * phi (arg t p) := by
    calc
      _ = (-7 / 32 : ℝ) * (2 / 5) := by norm_num
      _ ≤ (-7 / 32 : ℝ) * phi (arg t p) := mul_le_mul_of_nonpos_left (phi_upper _) (by norm_num)
      _ ≤ arg t p * phi (arg t p) := mul_le_mul_of_nonneg_right hz.1 (phi_nonneg _)
  have hV : 6 ≤ 26 * P39Reference.v p := by linarith only [(zero_variance_bounds hp).1]
  unfold phaseCurvature
  apply (le_div_iff₀ (by linarith only [hV] : 0 < 26 * P39Reference.v p)).mpr
  linarith only [hprod, hV]

lemma deriv2_phaseSmooth {p : ℝ} (hp : p ∈ strip) (t : ℝ) :
    deriv (deriv (phaseSmooth p)) t = phaseCurvature p t := by
  have heq : deriv (phaseSmooth p) = phaseSlope p := funext (fun u => (hasDerivAt_phaseSmooth p u).deriv)
  rw [heq]
  exact (hasDerivAt_phaseSlope hp t).deriv

end

end BerryEsseen.P39Count10Calculus

#print axioms BerryEsseen.P39Count10Calculus.etaCurvature_bounds
#print axioms BerryEsseen.P39Count10Calculus.ACurvature_bounds
#print axioms BerryEsseen.P39Count10Calculus.gaussianCurvature_upper
#print axioms BerryEsseen.P39Count10Calculus.smoothBaseCurvature_lower
#print axioms BerryEsseen.P39Count10Calculus.deriv2_phaseSmooth
#print axioms BerryEsseen.P39Count10Calculus.phaseCurvature_lower
