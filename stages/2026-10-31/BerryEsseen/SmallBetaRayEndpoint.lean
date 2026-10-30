module

public import BerryEsseen.HighMomentRayPrice
public import BerryEsseen.GaussianEnclosures
public import BerryEsseen.GaussianCancellationPrice
public import Causalean.Stat.CLT.BerryEsseen.PrawitzKernelBounds
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

@[expose] public section

/-! 2026-10-29: effective estimates on the entire small-beta ray.
The logarithmic cutoff and damping bounds below hold for every
0 < beta <= 3/1000. They are not a finite grid or a limiting assertion.
All four Prawitz integral comparisons are proved and applied to the actual
normalized iid law. -/

noncomputable section

open MeasureTheory Set
open scoped Interval Topology

namespace BerryEsseen.SmallBetaRayEndpoint

open HighMomentRayDamping HighMomentRayPrice

def betaMax : ℝ := 3 / 1000
def logScale (β : ℝ) : ℝ := Real.log (1 / β)
def cutoff (β : ℝ) : ℝ := Real.sqrt (8 * logScale β)
def band (β : ℝ) : ℝ := 4 / β

lemma betaMax_pos : 0 < betaMax := by norm_num [betaMax]

lemma logScale_eq (β : ℝ) : logScale β = -Real.log β := by
  simp [logScale]

lemma five_le_logScale (β : ℝ) (hβ : 0 < β) (hmax : β ≤ betaMax) :
    5 ≤ logScale β := by
  apply (Real.le_log_iff_exp_le (one_div_pos.mpr hβ)).mpr
  have he : Real.exp (5 : ℝ) ≤ 3 ^ (5 : ℕ) := by
    rw [show (5 : ℝ) = (5 : ℕ) * (1 : ℝ) by norm_num, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.exp_nonneg _) Real.exp_one_lt_three.le 5
  apply he.trans
  apply (le_div_iff₀ hβ).mpr
  norm_num [betaMax] at hmax ⊢
  linarith

lemma logScale_betaMax_lt_six : logScale betaMax < 6 := by
  apply (Real.log_lt_iff_lt_exp (one_div_pos.mpr betaMax_pos)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 6) 9
  have hn : 1 / betaMax < ∑ k ∈ Finset.range 9, (6 : ℝ) ^ k / (k.factorial : ℝ) := by
    norm_num [betaMax, Finset.sum_range_succ]
  exact hn.trans_le he

private lemma cubicLog_deriv (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => y ^ 2 * logScale y ^ 3)
      (x * logScale x ^ 2 * (2 * logScale x - 3)) x := by
  have hl : HasDerivAt logScale (-x⁻¹) x := by
    convert (Real.hasDerivAt_log hx.ne').neg using 1
    ext y
    exact logScale_eq y
  convert ((hasDerivAt_id' x).pow 2).mul (hl.pow 3) using 1
  simp only [Nat.cast_ofNat, Pi.pow_apply]
  field_simp [hx.ne']
  ring

/-- The product that controls the cubic damping correction increases all
the way to the explicit endpoint, despite the unbounded logarithm. -/
lemma sq_logScale_cube_le_endpoint (β : ℝ) (hβ : 0 < β) (hmax : β ≤ betaMax) :
    β ^ 2 * logScale β ^ 3 ≤ betaMax ^ 2 * logScale betaMax ^ 3 := by
  let f : ℝ → ℝ := fun x => x ^ 2 * logScale x ^ 3
  have hc : ContinuousOn f (Icc β betaMax) := by
    intro x hx
    exact (cubicLog_deriv x (hβ.trans_le hx.1)).continuousAt.continuousWithinAt
  have hm : MonotoneOn f (Icc β betaMax) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc β betaMax) hc
      (f' := fun x => x * logScale x ^ 2 * (2 * logScale x - 3))
    · intro x hx
      have hi := interior_subset hx
      exact (cubicLog_deriv x (hβ.trans_le hi.1)).hasDerivWithinAt
    · intro x hx
      have hi := interior_subset hx
      have hl := five_le_logScale x (hβ.trans_le hi.1) hi.2
      exact mul_nonneg (mul_nonneg (hβ.trans_le hi.1).le (sq_nonneg _)) (by linarith)
  exact hm ⟨le_rfl, hmax⟩ ⟨hmax, le_rfl⟩ hmax

lemma cutoff_sq (β : ℝ) (hβ : 0 < β) (hmax : β ≤ betaMax) :
    cutoff β ^ 2 = 8 * logScale β := by
  exact Real.sq_sqrt (by linarith [five_le_logScale β hβ hmax])

lemma cutoff_sq_ge_forty (β : ℝ) (hβ : 0 < β) (hmax : β ≤ betaMax) :
    40 ≤ cutoff β ^ 2 := by
  rw [cutoff_sq β hβ hmax]
  linarith [five_le_logScale β hβ hmax]

lemma cutoff_pos (β : ℝ) (hβ : 0 < β) (hmax : β ≤ betaMax) :
    0 < cutoff β := by
  apply Real.sqrt_pos.mpr
  linarith [five_le_logScale β hβ hmax]

lemma sq_mul_cutoff_six_le_one (β : ℝ) (hβ : 0 < β) (hmax : β ≤ betaMax) :
    β ^ 2 * cutoff β ^ 6 ≤ 1 := by
  have hm := sq_logScale_cube_le_endpoint β hβ hmax
  have hl := logScale_betaMax_lt_six
  have hl0 := five_le_logScale betaMax betaMax_pos le_rfl
  have hc : logScale betaMax ^ 3 ≤ (6 : ℝ) ^ 3 :=
    pow_le_pow_left₀ (by linarith) hl.le 3
  have hm2 := mul_le_mul_of_nonneg_left hc (sq_nonneg betaMax)
  have hsq := cutoff_sq β hβ hmax
  have heq : cutoff β ^ 6 = 512 * logScale β ^ 3 := by
    calc
      _ = (cutoff β ^ 2) ^ 3 := by ring
      _ = _ := by rw [hsq]; ring
  rw [heq]
  norm_num [betaMax] at hm hm2
  nlinarith only [hm, hm2]

lemma mul_cutoff_cube_le_one (β : ℝ) (hβ : 0 < β) (hmax : β ≤ betaMax) :
    β * cutoff β ^ 3 ≤ 1 := by
  have h := sq_mul_cutoff_six_le_one β hβ hmax
  have hs : (β * cutoff β ^ 3) ^ 2 ≤ 1 := by nlinarith only [h]
  nlinarith [sq_nonneg (β * cutoff β ^ 3 - 1)]

lemma sq_mul_cutoff_sq_le (β : ℝ) (hβ : 0 < β) (hmax : β ≤ betaMax) :
    β ^ 2 * cutoff β ^ 2 ≤ 1 / 1600 := by
  have h := sq_mul_cutoff_six_le_one β hβ hmax
  have hu := cutoff_sq_ge_forty β hβ hmax
  have h4 : (1600 : ℝ) ≤ cutoff β ^ 4 := by
    nlinarith [sq_nonneg (cutoff β ^ 2 - 40)]
  have hm := mul_le_mul_of_nonneg_left h4
    (mul_nonneg (sq_nonneg β) (sq_nonneg (cutoff β)))
  nlinarith only [hm, h]

lemma loss_le_beta_sq_third (N : ℕ) (β : ℝ) : loss N β ≤ β ^ 2 / 3 := by
  apply (min_le_left _ _).trans
  exact div_le_div_of_nonneg_left (sq_nonneg β) (by norm_num)
    (by norm_num [rho0])

lemma cubicCoefficient_le : (1 + 1 / rho0) / 10 ≤ (7 : ℝ) / 45 := by
  norm_num [rho0]

lemma local_exponent_le (N : ℕ) (β : ℝ) (hβ : 0 < β) (hmax : β ≤ betaMax)
    (t : ℝ) (ht : 0 ≤ t) (htu : t ≤ cutoff β) :
    (1 - loss N β) * exponent (1 / 2) (1 / 10) β t ≤ -t ^ 2 / 2 + 1 / 5 := by
  have he0 := loss_nonneg N β
  have he := loss_le_beta_sq_third N β
  have hc0 : 0 ≤ (1 + 1 / rho0) / 10 := by norm_num [rho0]
  have htsq := pow_le_pow_left₀ ht htu 2
  have htcu := pow_le_pow_left₀ ht htu 3
  have heterm : loss N β * t ^ 2 / 2 ≤ 1 / 9600 := by
    have hm := mul_le_mul he htsq (sq_nonneg t) (by positivity : 0 ≤ β ^ 2 / 3)
    have hb := sq_mul_cutoff_sq_le β hβ hmax
    nlinarith only [hm, hb]
  have hcterm : (1 + 1 / rho0) / 10 * β * t ^ 3 ≤ 7 / 45 := by
    have hβt : β * t ^ 3 ≤ 1 :=
      (mul_le_mul_of_nonneg_left htcu hβ.le).trans (mul_cutoff_cube_le_one β hβ hmax)
    have hm := mul_le_mul cubicCoefficient_le hβt
      (mul_nonneg hβ.le (pow_nonneg ht 3)) (by norm_num : (0 : ℝ) ≤ 7 / 45)
    nlinarith only [hm]
  have hnon := mul_nonneg he0
    (mul_nonneg (mul_nonneg hc0 hβ.le) (pow_nonneg ht 3))
  unfold exponent
  rw [abs_of_nonneg ht]
  nlinarith only [heterm, hcterm, hnon]

lemma exp_one_fifth_le : Real.exp ((1 : ℝ) / 5) ≤ 5 / 4 := by
  have h := Real.exp_bound_div_one_sub_of_interval
    (by norm_num : (0 : ℝ) ≤ 1 / 5) (by norm_num : (1 : ℝ) / 5 < 1)
  norm_num at h ⊢
  exact h

/-- A uniform Gaussian comparison for the actual residual-power envelope. -/
theorem lossEnvelope_le_local_gaussian (N : ℕ) (β : ℝ) (hβ : 0 < β)
    (hmax : β ≤ betaMax) (t : ℝ) (ht : 0 ≤ t) (htu : t ≤ cutoff β) :
    lossEnvelope N β t ≤ (5 / 4) * Real.exp (-t ^ 2 / 2) := by
  have henv : lossEnvelope N β t ≤
      Real.exp ((1 - loss N β) * exponent (1 / 2) (1 / 10) β t) :=
    (min_le_right _ _).trans (min_le_left _ _)
  apply henv.trans
  apply (Real.exp_le_exp.mpr (local_exponent_le N β hβ hmax t ht htu)).trans
  rw [Real.exp_add]
  nlinarith [mul_le_mul_of_nonneg_left exp_one_fifth_le
    (Real.exp_nonneg (-t ^ 2 / 2))]

lemma sineKernel_le_linear (β v : ℝ) (hβ : 0 ≤ β) (hv : 0 ≤ v) :
    sineKernel β v ≤ β * v := by
  have hn : 0 ≤ min (β * v / 2) (Real.pi / 2) := by positivity
  have hs := (Real.sin_le hn).trans (min_le_left (β * v / 2) (Real.pi / 2))
  unfold sineKernel
  linarith

lemma B_le_quadratic (β t : ℝ) (hβ : 0 ≤ β) (ht : 0 ≤ t) :
    B β t ≤ β * t ^ 2 / 2 := by
  have hc : Continuous (fun v : ℝ => β * v) := by fun_prop
  have hm := intervalIntegral.integral_mono_on (μ := volume) ht
    ((continuous_sineKernel β).intervalIntegrable 0 t) (hc.intervalIntegrable 0 t)
    (fun v hv => sineKernel_le_linear β v hβ hv.1)
  unfold B
  apply hm.trans_eq
  rw [intervalIntegral.integral_const_mul, integral_id]
  ring

private lemma local_integrand_le (N : ℕ) (β : ℝ) (hβ : 0 < β)
    (hmax : β ≤ betaMax) (t : ℝ) (ht : 0 ≤ t) (htu : t ≤ cutoff β) :
    integrand N β t ≤ (5 / 4) * (β * t ^ 2 / 2 + β ^ 2 * t ^ 3 / 9) := by
  have hp : 0 ≤ β * t ^ 2 / 2 + β ^ 2 * t ^ 3 / 9 := by positivity
  have hf : B β t + loss N β * t ^ 3 / 3 ≤
      β * t ^ 2 / 2 + β ^ 2 * t ^ 3 / 9 := by
    have hm := mul_le_mul_of_nonneg_right (loss_le_beta_sq_third N β)
      (by positivity : 0 ≤ t ^ 3 / 3)
    nlinarith only [B_le_quadratic β t hβ.le ht, hm]
  have hforcing : forcing N β t ≤
      ((5 / 4) * Real.exp (-t ^ 2 / 2)) *
        (β * t ^ 2 / 2 + β ^ 2 * t ^ 3 / 9) := by
    unfold forcing
    calc
      _ ≤ lossEnvelope N β t * (β * t ^ 2 / 2 + β ^ 2 * t ^ 3 / 9) :=
        mul_le_mul_of_nonneg_left hf (lossEnvelope_nonneg N β t)
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (lossEnvelope_le_local_gaussian N β hβ hmax t ht htu) hp
  have he : Real.exp (t ^ 2 / 2) * Real.exp (-t ^ 2 / 2) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1 <;> ring
  unfold integrand
  apply (mul_le_mul_of_nonneg_left hforcing (Real.exp_nonneg _)).trans_eq
  calc
    _ = (Real.exp (t ^ 2 / 2) * Real.exp (-t ^ 2 / 2)) *
      ((5 / 4) * (β * t ^ 2 / 2 + β ^ 2 * t ^ 3 / 9)) := by ring
    _ = _ := by rw [he, one_mul]

/-- The actual one-parameter CF price has an explicit polynomial times
Gaussian bound on the complete logarithmic low-frequency interval. -/
theorem price_le_local_gaussian (N : ℕ) (β : ℝ) (hβ : 0 < β)
    (hmax : β ≤ betaMax) (t : ℝ) (ht : 0 ≤ t) (htu : t ≤ cutoff β) :
    price N β t ≤ (5 / 4) * Real.exp (-t ^ 2 / 2) *
      (β * t ^ 3 / 6 + β ^ 2 * t ^ 4 / 36) := by
  have hc : Continuous (fun u : ℝ =>
      (5 / 4) * (β * u ^ 2 / 2 + β ^ 2 * u ^ 3 / 9)) := by fun_prop
  have hm := intervalIntegral.integral_mono_on (μ := volume) ht
    ((continuous_integrand N β).intervalIntegrable 0 t) (hc.intervalIntegrable 0 t)
    (fun u hu => local_integrand_le N β hβ hmax u hu.1 (hu.2.trans htu))
  have hi : (∫ u in (0 : ℝ)..t,
      (5 / 4) * (β * u ^ 2 / 2 + β ^ 2 * u ^ 3 / 9)) =
      (5 / 4) * (β * t ^ 3 / 6 + β ^ 2 * t ^ 4 / 36) := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add
        ((by fun_prop : Continuous (fun u : ℝ => β * u ^ 2 / 2)).intervalIntegrable 0 t)
        ((by fun_prop : Continuous (fun u : ℝ => β ^ 2 * u ^ 3 / 9)).intervalIntegrable 0 t)]
    simp_rw [div_eq_mul_inv]
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul,
      integral_pow, integral_pow]
    norm_num
    ring
  rw [hi] at hm
  unfold price
  convert mul_le_mul_of_nonneg_left hm (Real.exp_nonneg (-(t ^ 2 / 2))) using 1 <;> ring

lemma envelope_le_near_gaussian (β : ℝ) (hβ : 0 < β) (t : ℝ)
    (ht : 0 ≤ t) (htu : t ≤ 1 / β) :
    envelope β t ≤ Real.exp (-t ^ 2 / 3) := by
  have hbt : β * t ≤ 1 := by
    have hh := (le_div_iff₀ hβ).mp htu
    nlinarith only [hh]
  have hm := mul_le_mul_of_nonneg_right hbt (sq_nonneg t)
  have hc := mul_le_mul_of_nonneg_right cubicCoefficient_le
    (mul_nonneg hβ.le (pow_nonneg ht 3))
  have he : exponent (1 / 2) (1 / 10) β t ≤ -t ^ 2 / 3 := by
    unfold exponent
    rw [abs_of_nonneg ht]
    nlinarith only [hm, hc, sq_nonneg t]
  exact ((min_le_right _ _).trans (min_le_left _ _)).trans (Real.exp_le_exp.mpr he)

def farDelta : ℝ := 2249 / 18402500

lemma farDelta_pos : 0 < farDelta := by norm_num [farDelta]

lemma farDelta_ge : (3 : ℝ) / 25000 ≤ farDelta := by norm_num [farDelta]

lemma envelope_le_far_constant (β : ℝ) (hβ : 0 < β) (t : ℝ)
    (htl : 1 / β ≤ t) (htu : t ≤ band β) :
    envelope β t ≤ Real.exp (-farDelta / β ^ 2) := by
  have ht : 0 ≤ t := (one_div_pos.mpr hβ).le.trans htl
  have hbt : β * t ≤ 4 := by
    have hh := (le_div_iff₀ hβ).mp htu
    nlinarith only [hh]
  have hc0 : 0 ≤ (1 + 1 / rho0) / 625 := by norm_num [rho0]
  have hcoef : -1 / 100 + ((1 + 1 / rho0) / 625) * (β * t) ≤ -farDelta := by
    have hm := mul_le_mul_of_nonneg_left hbt hc0
    norm_num [rho0, farDelta] at hm ⊢
    linarith only [hm]
  have hsq : (1 / β) ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ (one_div_pos.mpr hβ).le htl 2
  have hm := mul_le_mul_of_nonneg_right hcoef (sq_nonneg t)
  have hm2 := mul_le_mul_of_nonpos_left hsq (neg_nonpos.mpr farDelta_pos.le)
  have he : exponent ClassicalRationalCosine.a ClassicalRationalCosine.b β t ≤
      -farDelta / β ^ 2 := by
    unfold exponent ClassicalRationalCosine.a ClassicalRationalCosine.b
    rw [abs_of_nonneg ht]
    calc
      _ = (-1 / 100 + (1 + 1 / rho0) / 625 * (β * t)) * t ^ 2 := by ring
      _ ≤ -farDelta * t ^ 2 := hm
      _ ≤ -farDelta * (1 / β) ^ 2 := hm2
      _ = _ := by ring
  apply (show envelope β t ≤
    Real.exp (exponent ClassicalRationalCosine.a ClassicalRationalCosine.b β t) from
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))).trans
  exact Real.exp_le_exp.mpr he

lemma exp_neg_forty_thirds_le : Real.exp (-(40 : ℝ) / 3) ≤ 1 / 500000 := by
  have ht := GaussianEnclosures.exp_neg_taylor_upper 4 (by decide)
    (5 / 6) (by norm_num)
  have hp := pow_le_pow_left₀ (Real.exp_nonneg (-(5 / 6 : ℝ))) ht 16
  have he : (Real.exp (-(5 / 6 : ℝ))) ^ 16 = Real.exp (-(40 : ℝ) / 3) := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [he] at hp
  norm_num [GaussianEnclosures.expTaylor, Finset.sum_range_succ] at hp ⊢
  exact hp.trans (by norm_num)

private def farRatio (β : ℝ) : ℝ := Real.exp (-(3 / 25000 : ℝ) / β ^ 2) / β

private lemma farRatio_deriv (x : ℝ) (hx : 0 < x) :
    HasDerivAt farRatio
      (Real.exp (-(3 / 25000 : ℝ) / x ^ 2) * (2 * (3 / 25000 : ℝ) - x ^ 2) / x ^ 4) x := by
  unfold farRatio
  convert ((((hasDerivAt_const x (-(3 / 25000 : ℝ))).div
    ((hasDerivAt_id' x).pow 2) (pow_ne_zero 2 hx.ne')).exp).div
      (hasDerivAt_id' x) hx.ne') using 1
  simp only [Nat.cast_ofNat, Pi.pow_apply, Pi.div_apply]
  field_simp [hx.ne']
  ring

/-- The exponentially small far band has a uniform effective price;
the division by beta is included in the monotonicity proof. -/
theorem far_exponential_ratio_le (β : ℝ) (hβ : 0 < β) (hmax : β ≤ betaMax) :
    Real.exp (-farDelta / β ^ 2) / β ≤ 1 / 1500 := by
  have hc : ContinuousOn farRatio (Icc β betaMax) := by
    intro x hx
    exact (farRatio_deriv x (hβ.trans_le hx.1)).continuousAt.continuousWithinAt
  have hm : MonotoneOn farRatio (Icc β betaMax) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc β betaMax) hc
      (f' := fun x => Real.exp (-(3 / 25000 : ℝ) / x ^ 2) *
        (2 * (3 / 25000 : ℝ) - x ^ 2) / x ^ 4)
    · intro x hx
      exact (farRatio_deriv x (hβ.trans_le (interior_subset hx).1)).hasDerivWithinAt
    · intro x hx
      have hi := interior_subset hx
      have hp : 0 ≤ x := (hβ.trans_le hi.1).le
      have hs := pow_le_pow_left₀ hp hi.2 2
      have hn : 0 ≤ 2 * (3 / 25000 : ℝ) - x ^ 2 := by
        norm_num [betaMax] at hs
        linarith
      exact div_nonneg (mul_nonneg (Real.exp_nonneg _) hn) (pow_nonneg hp 4)
  have hmono := hm ⟨le_rfl, hmax⟩ ⟨hmax, le_rfl⟩ hmax
  have he : Real.exp (-farDelta / β ^ 2) / β ≤ farRatio β := by
    apply div_le_div_of_nonneg_right _ hβ.le
    apply Real.exp_le_exp.mpr
    exact div_le_div_of_nonneg_right (neg_le_neg farDelta_ge) (sq_nonneg β)
  apply he.trans (hmono.trans _)
  unfold farRatio
  norm_num [betaMax]
  have hh := exp_neg_forty_thirds_le
  linarith only [hh]

/-- Rational budget after the four analytic integral bounds. This lemma
does not assert those integral comparisons or a CDF estimate. -/
theorem four_term_rational_budget (β : ℝ) (hβ : 0 ≤ β) (hmax : β ≤ betaMax) :
    (5 / 4 : ℝ) * ((2 / 5 : ℝ) / 6 + β / 12 + β / (18 * (25 / 8 : ℝ)) +
      β ^ 2 * (63 / 50 : ℝ) / 48) + (63 / 50 : ℝ) / 4 +
      1 / 1000 + 1 / 10 ^ (9 : ℕ) < 2 / 5 := by
  have hs := pow_le_pow_left₀ hβ hmax 2
  norm_num [betaMax] at hs hmax
  norm_num
  nlinarith only [hs, hmax]

lemma six_le_cutoff (β : ℝ) (hβ : 0 < β) (hmax : β ≤ betaMax) :
    6 ≤ cutoff β := by
  nlinarith [cutoff_sq_ge_forty β hβ hmax, (cutoff_pos β hβ hmax).le]

lemma cutoff_le_inv (β : ℝ) (hβ : 0 < β) (hmax : β ≤ betaMax) :
    cutoff β ≤ 1 / β := by
  apply (le_div_iff₀ hβ).mpr
  have hh := sq_mul_cutoff_sq_le β hβ hmax
  nlinarith [sq_nonneg (β * cutoff β - 1)]

lemma cutoff_le_band (β : ℝ) (hβ : 0 < β) (hmax : β ≤ betaMax) :
    cutoff β ≤ band β := by
  exact (cutoff_le_inv β hβ hmax).trans
    (div_le_div_of_nonneg_right (by norm_num) hβ.le)

lemma exp_cutoff_eq_fourth (β : ℝ) (hβ : 0 < β) (hmax : β ≤ betaMax) :
    Real.exp (-cutoff β ^ 2 / 2) = β ^ 4 := by
  rw [cutoff_sq β hβ hmax, logScale_eq]
  have he : -(8 * -Real.log β) / 2 = (4 : ℕ) * Real.log β := by norm_num; ring
  rw [he, Real.exp_nat_mul, Real.exp_log hβ]

lemma exp_cutoff_third_le_sq (β : ℝ) (hβ : 0 < β) (hmax : β ≤ betaMax) :
    Real.exp (-cutoff β ^ 2 / 3) ≤ β ^ 2 := by
  have he : Real.exp (-cutoff β ^ 2 / 4) = β ^ 2 := by
    rw [cutoff_sq β hβ hmax, logScale_eq]
    have hh : -(8 * -Real.log β) / 4 = (2 : ℕ) * Real.log β := by norm_num; ring
    rw [hh, Real.exp_nat_mul, Real.exp_log hβ]
  rw [← he]
  exact Real.exp_le_exp.mpr (by nlinarith [sq_nonneg (cutoff β)])

lemma near_rational_budget (β : ℝ) (hβ : 0 ≤ β) (hmax : β ≤ betaMax) :
    β ^ 2 / 16 + β / 80 < 1 / 25000 := by
  have hs := pow_le_pow_left₀ hβ hmax 2
  norm_num [betaMax] at hs hmax
  nlinarith only [hs, hmax]

lemma pi_ge_twentyfive_eighths : (25 : ℝ) / 8 ≤ Real.pi := by
  linarith [Real.pi_gt_d2]

lemma sqrt_pi_half_le : Real.sqrt (Real.pi / 2) ≤ (63 : ℝ) / 50 := by
  have hs := Real.sq_sqrt (show 0 ≤ Real.pi / 2 by positivity)
  nlinarith [Real.pi_lt_d2, Real.sqrt_nonneg (Real.pi / 2)]

private lemma gaussian_deriv (a x : ℝ) :
    HasDerivAt (fun u : ℝ => Real.exp (-a * u ^ 2))
      (-2 * a * x * Real.exp (-a * x ^ 2)) x := by
  convert (((hasDerivAt_id' x).fun_pow 2).const_mul (-a)).exp using 1
  ring

private lemma gaussian_tendsto_zero (a : ℝ) (ha : 0 < a) :
    Filter.Tendsto (fun x : ℝ => Real.exp (-a * x ^ 2)) Filter.atTop (𝓝 0) := by
  have hd : Integrable (fun x : ℝ => -2 * a * x * Real.exp (-a * x ^ 2)) := by
    convert (integrable_mul_exp_neg_mul_sq ha).const_mul (-2 * a) using 1
    ext x
    ring
  exact tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi (a := 0)
    (fun x _ => gaussian_deriv a x) hd.integrableOn
      (integrable_exp_neg_mul_sq ha).integrableOn

lemma integral_mul_gaussian_Ioi (a c : ℝ) (ha : 0 < a) :
    (∫ x in Ioi c, x * Real.exp (-a * x ^ 2)) = Real.exp (-a * c ^ 2) / (2 * a) := by
  have hd : ∀ x ∈ Ici c, HasDerivAt
      (fun u : ℝ => -Real.exp (-a * u ^ 2) / (2 * a))
      (x * Real.exp (-a * x ^ 2)) x := by
    intro x _
    convert ((gaussian_deriv a x).neg.div_const (2 * a)) using 1
    field_simp [ha.ne']
  have hz : Filter.Tendsto (fun x : ℝ => -Real.exp (-a * x ^ 2) / (2 * a))
      Filter.atTop (𝓝 0) := by
    simpa using (gaussian_tendsto_zero a ha).neg.div_const (2 * a)
  simpa only [zero_sub, neg_div, neg_neg] using
    integral_Ioi_of_hasDerivAt_of_tendsto' hd
      (integrable_mul_exp_neg_mul_sq ha).integrableOn hz

/-- A real Gaussian reciprocal tail comparison, including its improper
integral. No integrability assumption on a freely chosen envelope is used. -/
theorem gaussian_reciprocal_tail_le (a c : ℝ) (ha : 0 < a) (hc : 0 < c) :
    (∫ x in Ioi c, Real.exp (-a * x ^ 2) / x) ≤
      Real.exp (-a * c ^ 2) / (2 * a * c ^ 2) := by
  have hnon : 0 ≤ᵐ[volume.restrict (Ioi c)]
      (fun x : ℝ => Real.exp (-a * x ^ 2) / x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact div_nonneg (Real.exp_nonneg _) (hc.trans hx).le
  have hle : (fun x : ℝ => Real.exp (-a * x ^ 2) / x) ≤ᵐ[volume.restrict (Ioi c)]
      (fun x : ℝ => (x * Real.exp (-a * x ^ 2)) / c ^ 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hp : 0 < x := hc.trans hx
    apply (div_le_div_iff₀ hp (sq_pos_of_pos hc)).mpr
    have hs := pow_le_pow_left₀ hc.le hx.le 2
    nlinarith only [mul_le_mul_of_nonneg_right hs (Real.exp_nonneg (-a * x ^ 2))]
  have hm := integral_mono_of_nonneg hnon
    ((integrable_mul_exp_neg_mul_sq ha).integrableOn.div_const (c ^ 2)) hle
  apply hm.trans_eq
  rw [integral_div, integral_mul_gaussian_Ioi a c ha]
  ring

/-- The actual fourth Prawitz term, divided by beta, has the claimed
uniform tiny tail price on the complete small-beta ray. -/
theorem fourth_term_le (β : ℝ) (hβ : 0 < β) (hmax : β ≤ betaMax) :
    ((1 / Real.pi) * (∫ t in Ioi (cutoff β), Real.exp (-(t ^ 2 / 2)) / t)) / β <
      1 / 10 ^ (9 : ℕ) := by
  have hc := cutoff_pos β hβ hmax
  have hm := gaussian_reciprocal_tail_le (1 / 2) (cutoff β) (by norm_num) hc
  have he : (fun t : ℝ => Real.exp (-(1 / 2 : ℝ) * t ^ 2) / t) =
      (fun t : ℝ => Real.exp (-(t ^ 2 / 2)) / t) := by
    ext t
    congr 2
    ring
  rw [he] at hm
  have hh : Real.exp (-(1 / 2 : ℝ) * cutoff β ^ 2) = β ^ 4 := by
    convert exp_cutoff_eq_fourth β hβ hmax using 1 <;> ring
  rw [hh] at hm
  norm_num only [mul_one, one_mul] at hm
  have hcoef : 0 ≤ (1 / Real.pi) / β := by positivity
  have hmul := mul_le_mul_of_nonneg_left hm hcoef
  have hgoal : ((1 / Real.pi) *
      (∫ t in Ioi (cutoff β), Real.exp (-(t ^ 2 / 2)) / t)) / β ≤
      β ^ 3 / (Real.pi * cutoff β ^ 2) := by
    convert hmul using 1 <;> field_simp [hβ.ne', Real.pi_ne_zero] <;> ring
  apply hgoal.trans_lt
  have hu := cutoff_sq_ge_forty β hβ hmax
  have hs := pow_le_pow_left₀ hβ.le hmax 3
  have hden : 120 ≤ Real.pi * cutoff β ^ 2 := by
    nlinarith only [mul_le_mul pi_ge_twentyfive_eighths hu
      (by norm_num : (0 : ℝ) ≤ 40) (by positivity : 0 ≤ Real.pi)]
  apply (div_lt_iff₀ (by positivity : 0 < Real.pi * cutoff β ^ 2)).mpr
  norm_num [betaMax] at hs
  norm_num
  nlinarith only [hs, hden]

open Causalean.Stat.CLT.BerryEsseen (prawitzKernel)
open GaussianCancellationPrice LowFrequencyLeading

lemma scaled_kernel_le (U t : ℝ) (hU : 0 < U) (ht : 0 < t) (htU : t ≤ U) :
    (2 / U) * ‖prawitzKernel (t / U)‖ ≤ 1 / (Real.pi * t) + 1 / U := by
  have harg : 0 < t / U := div_pos ht hU
  have hband : |t / U| ≤ 1 := by
    rw [abs_of_pos harg]
    exact (div_le_one hU).mpr htU
  have hk := Causalean.Stat.CLT.BerryEsseen.prawitzKernel_norm_le
    (t / U) (abs_pos.mpr harg.ne') hband
  have hm := mul_le_mul_of_nonneg_left hk (by positivity : 0 ≤ 2 / U)
  apply hm.trans_eq
  rw [abs_of_pos harg]
  field_simp [hU.ne', ht.ne', Real.pi_ne_zero]

lemma scaled_correction_le (U t : ℝ) (hU : 0 < U) (ht : 0 < t) (htU : t ≤ U) :
    ‖prawitzKernel (t / U) / (U : ℂ) - Complex.I / ((2 * Real.pi * t : ℝ) : ℂ)‖ ≤
      1 / (2 * U) := by
  have harg : 0 < t / U := div_pos ht hU
  have hband : |t / U| ≤ 1 := by
    rw [abs_of_pos harg]
    exact (div_le_one hU).mpr htU
  have hk := Causalean.Stat.CLT.BerryEsseen.prawitzKernel_principal_correction_norm_le
    (t / U) (abs_pos.mpr harg.ne') hband
  have hcU : (U : ℂ) ≠ 0 := by exact_mod_cast hU.ne'
  have hct : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hcp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hid : prawitzKernel (t / U) / (U : ℂ) - Complex.I / ((2 * Real.pi * t : ℝ) : ℂ) =
      (prawitzKernel (t / U) - Complex.I / ((2 * Real.pi * (t / U) : ℝ) : ℂ)) /
        (U : ℂ) := by
    push_cast
    field_simp [hcU, hct, hcp]
  rw [hid, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hU]
  have hm := div_le_div_of_nonneg_right hk hU.le
  convert hm using 1 <;> ring

private lemma thirdWeight_primitive_deriv (x : ℝ) :
    HasDerivAt (fun t : ℝ => -(t ^ 2 + 2) * weight t) (x ^ 3 * weight x) x := by
  unfold weight
  have he : HasDerivAt (fun t : ℝ => Real.exp (-(t ^ 2) / 2))
      (-x * Real.exp (-(x ^ 2) / 2)) x := by
    convert gaussian_deriv (1 / 2) x using 1 <;> ring
  convert ((((hasDerivAt_id' x).fun_pow 2).add_const 2).neg.mul he) using 1
  simp only [Pi.neg_apply, Pi.add_apply]
  ring

lemma integral_weight_three_zero : (∫ x in Ioi (0 : ℝ), x ^ 3 * weight x) = 2 := by
  have hf : Integrable (fun t : ℝ => -(t ^ 2 + 2) * weight t) := by
    convert ((integrable_pow_weight 2).add (integrable_weight.const_mul 2)).neg using 1
    ext t
    simp only [Pi.neg_apply, Pi.add_apply]
    ring
  have hz : Filter.Tendsto (fun t : ℝ => -(t ^ 2 + 2) * weight t)
      Filter.atTop (𝓝 0) :=
    tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi (a := 0)
      (fun x _ => thirdWeight_primitive_deriv x)
      (integrable_pow_weight 3).integrableOn hf.integrableOn
  have hi := integral_Ioi_of_hasDerivAt_of_tendsto' (a := (0 : ℝ))
    (fun x _ => thirdWeight_primitive_deriv x) (integrable_pow_weight 3).integrableOn hz
  norm_num [weight] at hi
  exact hi

def thirdTerm (β : ℝ) : ℝ :=
  2 * (∫ t in (0 : ℝ)..cutoff β,
    ‖prawitzKernel (t / band β) / (band β : ℂ) -
      Complex.I / ((2 * Real.pi * t : ℝ) : ℂ)‖ * weight t)

theorem third_term_le (β : ℝ) (hβ : 0 < β) (hmax : β ≤ betaMax) :
    thirdTerm β / β ≤ (63 / 50 : ℝ) / 4 := by
  have hU : 0 < band β := div_pos (by norm_num) hβ
  have hc := cutoff_pos β hβ hmax
  have hcut := cutoff_le_band β hβ hmax
  have hi : Integrable (fun t : ℝ => (1 / band β) * weight t) :=
    integrable_weight.const_mul _
  have hm : thirdTerm β ≤
      ∫ t in Ioc (0 : ℝ) (cutoff β), (1 / band β) * weight t := by
    unfold thirdTerm
    rw [← intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le hc.le]
    apply setIntegral_mono_of_nonneg (μ := volume)
    · intro t ht
      exact mul_nonneg (by norm_num) (mul_nonneg (norm_nonneg _) (weight_pos t).le)
    · intro t ht
      have hh := scaled_correction_le (band β) t hU ht.1 (ht.2.trans hcut)
      have hmul := mul_le_mul_of_nonneg_right hh (weight_pos t).le
      calc
        _ ≤ 2 * (1 / (2 * band β) * weight t) :=
          mul_le_mul_of_nonneg_left hmul (by norm_num)
        _ = _ := by field_simp [hU.ne']
    · exact hi.integrableOn
  have hsub : (∫ t in Ioc (0 : ℝ) (cutoff β), (1 / band β) * weight t) ≤
      ∫ t in Ioi (0 : ℝ), (1 / band β) * weight t := by
    apply setIntegral_mono_set hi.integrableOn
    · exact Filter.Eventually.of_forall (fun t => by positivity [weight_pos t])
    · exact Filter.Eventually.of_forall (fun t ht => ht.1)
  have hmass : (∫ t in Ioi (0 : ℝ), (1 / band β) * weight t) =
      β * gaussianMass / 4 := by
    rw [integral_const_mul]
    change (1 / band β) * tailWeight 0 = _
    rw [tailWeight_zero]
    unfold band
    field_simp [hβ.ne']
  have hprice : thirdTerm β / β ≤ gaussianMass / 4 := by
    apply (div_le_iff₀ hβ).mpr
    have hh := hm.trans (hsub.trans_eq hmass)
    nlinarith only [hh]
  exact hprice.trans (div_le_div_of_nonneg_right sqrt_pi_half_le (by norm_num))

def lowMajorant (β t : ℝ) : ℝ :=
  (5 / 4) * (β / (6 * Real.pi) * (t ^ 2 * weight t) +
    (β ^ 2 / 24 + β ^ 2 / (36 * Real.pi)) * (t ^ 3 * weight t) +
    β ^ 3 / 144 * (t ^ 4 * weight t))

lemma integrable_lowMajorant (β : ℝ) : Integrable (lowMajorant β) := by
  exact ((((integrable_pow_weight 2).const_mul _).add
    ((integrable_pow_weight 3).const_mul _)).add
      ((integrable_pow_weight 4).const_mul _)).const_mul _

lemma lowMajorant_nonneg (β : ℝ) (hβ : 0 ≤ β) (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ lowMajorant β t := by
  unfold lowMajorant
  positivity [weight_pos t]

lemma integral_lowMajorant (β : ℝ) :
    (∫ t in Ioi (0 : ℝ), lowMajorant β t) =
      β * (5 / 4) * (gaussianMass / (6 * Real.pi) + β / 12 +
        β / (18 * Real.pi) + β ^ 2 * gaussianMass / 48) := by
  have h2 : IntegrableOn (fun t : ℝ => β / (6 * Real.pi) * (t ^ 2 * weight t))
      (Ioi (0 : ℝ)) := (integrable_pow_weight 2).const_mul _ |>.integrableOn
  have h3 : IntegrableOn (fun t : ℝ =>
      (β ^ 2 / 24 + β ^ 2 / (36 * Real.pi)) * (t ^ 3 * weight t))
      (Ioi (0 : ℝ)) := (integrable_pow_weight 3).const_mul _ |>.integrableOn
  have h4 : IntegrableOn (fun t : ℝ => β ^ 3 / 144 * (t ^ 4 * weight t))
      (Ioi (0 : ℝ)) := (integrable_pow_weight 4).const_mul _ |>.integrableOn
  have h23 : IntegrableOn (fun t : ℝ => β / (6 * Real.pi) * (t ^ 2 * weight t) +
      (β ^ 2 / 24 + β ^ 2 / (36 * Real.pi)) * (t ^ 3 * weight t)) (Ioi (0 : ℝ)) := by
    exact h2.fun_add h3
  unfold lowMajorant
  rw [integral_const_mul]
  rw [integral_add (μ := volume.restrict (Ioi (0 : ℝ)))
    (f := fun t : ℝ => β / (6 * Real.pi) * (t ^ 2 * weight t) +
      (β ^ 2 / 24 + β ^ 2 / (36 * Real.pi)) * (t ^ 3 * weight t))
    (g := fun t : ℝ => β ^ 3 / 144 * (t ^ 4 * weight t))
    h23 h4]
  rw [integral_add (μ := volume.restrict (Ioi (0 : ℝ)))
    (f := fun t : ℝ => β / (6 * Real.pi) * (t ^ 2 * weight t))
    (g := fun t : ℝ => (β ^ 2 / 24 + β ^ 2 / (36 * Real.pi)) * (t ^ 3 * weight t))
    h2 h3]
  simp_rw [integral_const_mul]
  rw [integral_weight_two_zero, integral_weight_three_zero, integral_weight_four_zero]
  ring

def firstTerm (β : ℝ) (f : ℝ → ℝ) : ℝ :=
  (2 / band β) * ∫ t in (0 : ℝ)..cutoff β, ‖prawitzKernel (t / band β)‖ * f t

theorem first_term_le_moments (β : ℝ) (hβ : 0 < β) (hmax : β ≤ betaMax)
    (f : ℝ → ℝ) (hf : ∀ t ∈ Ioc (0 : ℝ) (cutoff β), 0 ≤ f t)
    (hprice : ∀ t ∈ Ioc (0 : ℝ) (cutoff β), f t ≤
      (5 / 4) * weight t * (β * t ^ 3 / 6 + β ^ 2 * t ^ 4 / 36)) :
    firstTerm β f / β ≤ (5 / 4) * (gaussianMass / (6 * Real.pi) + β / 12 +
      β / (18 * Real.pi) + β ^ 2 * gaussianMass / 48) := by
  have hU : 0 < band β := div_pos (by norm_num) hβ
  have hc := cutoff_pos β hβ hmax
  have hcut := cutoff_le_band β hβ hmax
  have hm : firstTerm β f ≤ ∫ t in Ioc (0 : ℝ) (cutoff β), lowMajorant β t := by
    unfold firstTerm
    rw [← intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le hc.le]
    apply setIntegral_mono_of_nonneg (μ := volume)
    · intro t ht
      exact mul_nonneg (by positivity) (mul_nonneg (norm_nonneg _) (hf t ht))
    · intro t ht
      have hk := scaled_kernel_le (band β) t hU ht.1 (ht.2.trans hcut)
      have hr := hprice t ht
      have htp : 0 < t := ht.1
      have hspec : 0 ≤ 1 / (Real.pi * t) + 1 / band β := by positivity
      have hh := mul_le_mul hk hr (hf t ht) hspec
      calc
        _ = ((2 / band β) * ‖prawitzKernel (t / band β)‖) * f t := by ring
        _ ≤ _ := hh
        _ = lowMajorant β t := by
          unfold lowMajorant band
          field_simp [hβ.ne', ht.1.ne', Real.pi_ne_zero]
          ring
    · exact (integrable_lowMajorant β).integrableOn
  have hs : (∫ t in Ioc (0 : ℝ) (cutoff β), lowMajorant β t) ≤
      ∫ t in Ioi (0 : ℝ), lowMajorant β t := by
    apply setIntegral_mono_set (integrable_lowMajorant β).integrableOn
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact lowMajorant_nonneg β hβ.le t ht.le
    · exact Filter.Eventually.of_forall (fun t ht => ht.1)
  apply (div_le_iff₀ hβ).mpr
  rw [integral_lowMajorant] at hs
  nlinarith only [hm, hs]

lemma gaussianMass_div_pi_le : gaussianMass / Real.pi ≤ (2 : ℝ) / 5 := by
  have hs := Real.sq_sqrt (show 0 ≤ Real.pi / 2 by positivity)
  have hn : 0 ≤ (4 / 25 : ℝ) * Real.pi - 1 / 2 := by
    linarith only [pi_ge_twentyfive_eighths]
  have hh := mul_nonneg Real.pi_pos.le hn
  apply (div_le_iff₀ Real.pi_pos).mpr
  unfold gaussianMass
  nlinarith only [hs, hh, Real.sqrt_nonneg (Real.pi / 2), Real.pi_pos]

theorem first_term_le (β : ℝ) (hβ : 0 < β) (hmax : β ≤ betaMax)
    (f : ℝ → ℝ) (hf : ∀ t ∈ Ioc (0 : ℝ) (cutoff β), 0 ≤ f t)
    (hprice : ∀ t ∈ Ioc (0 : ℝ) (cutoff β), f t ≤
      (5 / 4) * weight t * (β * t ^ 3 / 6 + β ^ 2 * t ^ 4 / 36)) :
    firstTerm β f / β ≤ (5 / 4) * ((2 / 5 : ℝ) / 6 + β / 12 +
      β / (18 * (25 / 8 : ℝ)) + β ^ 2 * (63 / 50 : ℝ) / 48) := by
  apply (first_term_le_moments β hβ hmax f hf hprice).trans
  have hm1 : gaussianMass / (6 * Real.pi) ≤ ((2 / 5 : ℝ) / 6) := by
    convert div_le_div_of_nonneg_right gaussianMass_div_pi_le (by norm_num : (0 : ℝ) ≤ 6)
      using 1 <;> ring
  have hm2 : β / (18 * Real.pi) ≤ β / (18 * (25 / 8 : ℝ)) := by
    apply div_le_div_of_nonneg_left hβ.le (by positivity)
    nlinarith only [pi_ge_twentyfive_eighths]
  have hm3 := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left sqrt_pi_half_le (sq_nonneg β))
    (by norm_num : (0 : ℝ) ≤ 48)
  change β ^ 2 * gaussianMass / 48 ≤ β ^ 2 * (63 / 50 : ℝ) / 48 at hm3
  nlinarith only [hm1, hm2, hm3]

def secondNear (β : ℝ) (f : ℝ → ℝ) : ℝ :=
  (2 / band β) * ∫ t in cutoff β..1 / β, ‖prawitzKernel (t / band β)‖ * f t

theorem second_near_le (β : ℝ) (hβ : 0 < β) (hmax : β ≤ betaMax)
    (f : ℝ → ℝ) (hf : ∀ t ∈ Ioc (cutoff β) (1 / β), 0 ≤ f t)
    (hq : ∀ t ∈ Ioc (cutoff β) (1 / β), f t ≤ Real.exp (-t ^ 2 / 3)) :
    secondNear β f / β < 1 / 25000 := by
  let M : ℝ := 1 / (Real.pi * cutoff β ^ 2) + β / (4 * cutoff β)
  have hc := cutoff_pos β hβ hmax
  have hU : 0 < band β := div_pos (by norm_num) hβ
  have hcu := cutoff_le_inv β hβ hmax
  have hiU : 1 / β ≤ band β := div_le_div_of_nonneg_right (by norm_num) hβ.le
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hi : Integrable (fun t : ℝ => M * (t * Real.exp (-(1 / 3 : ℝ) * t ^ 2))) :=
    (integrable_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 3)).const_mul M
  have hm : secondNear β f ≤ ∫ t in Ioc (cutoff β) (1 / β),
      M * (t * Real.exp (-(1 / 3 : ℝ) * t ^ 2)) := by
    unfold secondNear
    rw [← intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le hcu]
    apply setIntegral_mono_of_nonneg (μ := volume)
    · intro t ht
      exact mul_nonneg (by positivity) (mul_nonneg (norm_nonneg _) (hf t ht))
    · intro t ht
      have htp : 0 < t := hc.trans ht.1
      have hk := scaled_kernel_le (band β) t hU htp (ht.2.trans hiU)
      have hr : f t ≤ Real.exp (-(1 / 3 : ℝ) * t ^ 2) := by
        convert hq t ht using 1 <;> congr 1 <;> ring
      have hs : 0 ≤ 1 / (Real.pi * t) + 1 / band β := by positivity
      have hh := mul_le_mul hk hr (hf t ht) hs
      have hsq := pow_le_pow_left₀ hc.le ht.1.le 2
      have hrecip : 1 / (Real.pi * t) ≤ t / (Real.pi * cutoff β ^ 2) := by
        apply (div_le_div_iff₀ (mul_pos Real.pi_pos htp)
          (mul_pos Real.pi_pos (sq_pos_of_pos hc))).mpr
        nlinarith only [mul_le_mul_of_nonneg_left hsq Real.pi_pos.le]
      have hconst : β / 4 ≤ β * t / (4 * cutoff β) := by
        apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 4) (by positivity)).mpr
        nlinarith only [mul_le_mul_of_nonneg_left ht.1.le hβ.le]
      have hband : 1 / band β = β / 4 := by
        unfold band
        field_simp [hβ.ne']
      have hcoef : 1 / (Real.pi * t) + 1 / band β ≤ M * t := by
        rw [hband]
        calc
          _ ≤ t / (Real.pi * cutoff β ^ 2) + β * t / (4 * cutoff β) :=
            add_le_add hrecip hconst
          _ = _ := by dsimp [M]; ring
      calc
        _ = ((2 / band β) * ‖prawitzKernel (t / band β)‖) * f t := by ring
        _ ≤ _ := hh
        _ ≤ (M * t) * Real.exp (-(1 / 3 : ℝ) * t ^ 2) :=
          mul_le_mul_of_nonneg_right hcoef (Real.exp_nonneg _)
        _ = _ := by ring
    · exact hi.integrableOn
  have hsub : (∫ t in Ioc (cutoff β) (1 / β),
      M * (t * Real.exp (-(1 / 3 : ℝ) * t ^ 2))) ≤
      ∫ t in Ioi (cutoff β), M * (t * Real.exp (-(1 / 3 : ℝ) * t ^ 2)) := by
    apply setIntegral_mono_set hi.integrableOn
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact mul_nonneg hM (mul_nonneg (hc.trans ht).le (Real.exp_nonneg _))
    · exact Filter.Eventually.of_forall (fun t ht => ht.1)
  have htotal := hm.trans hsub
  rw [integral_const_mul, integral_mul_gaussian_Ioi (1 / 3) (cutoff β) (by norm_num)] at htotal
  have he : Real.exp (-(1 / 3 : ℝ) * cutoff β ^ 2) ≤ β ^ 2 := by
    convert exp_cutoff_third_le_sq β hβ hmax using 1 <;> congr 1 <;> ring
  have hraw : secondNear β f ≤ M * (3 / 2) * β ^ 2 := by
    apply htotal.trans
    have hh := mul_le_mul_of_nonneg_left he (mul_nonneg hM (by norm_num : (0 : ℝ) ≤ 3 / 2))
    convert hh using 1 <;> ring
  have hdiv : secondNear β f / β ≤ β * (3 / 2) * M := by
    apply (div_le_iff₀ hβ).mpr
    convert hraw using 1 <;> ring
  have hden : (120 : ℝ) ≤ Real.pi * cutoff β ^ 2 := by
    have hh := mul_le_mul pi_ge_twentyfive_eighths (cutoff_sq_ge_forty β hβ hmax)
      (by norm_num : (0 : ℝ) ≤ 40) Real.pi_pos.le
    nlinarith only [hh]
  have hM1 : 1 / (Real.pi * cutoff β ^ 2) ≤ (1 : ℝ) / 120 :=
    one_div_le_one_div_of_le (by norm_num) hden
  have hM2 : β / (4 * cutoff β) ≤ β / 24 := by
    apply div_le_div_of_nonneg_left hβ.le (by norm_num)
    nlinarith only [six_le_cutoff β hβ hmax]
  have hMsmall : (3 / 2 : ℝ) * M ≤ 1 / 80 + β / 16 := by
    dsimp [M]
    nlinarith only [hM1, hM2]
  apply (hdiv.trans _).trans_lt (near_rational_budget β hβ.le hmax)
  have hh := mul_le_mul_of_nonneg_left hMsmall hβ.le
  nlinarith only [hh]

private lemma spectral_intervalIntegrable (β : ℝ) (hβ : 0 < β) :
    IntervalIntegrable (fun t : ℝ => 1 / (Real.pi * t) + 1 / band β)
      volume (1 / β) (band β) := by
  have hi : 1 / β ≤ band β := div_le_div_of_nonneg_right (by norm_num) hβ.le
  apply ContinuousOn.intervalIntegrable_of_Icc hi
  apply ContinuousOn.add _ continuousOn_const
  exact continuousOn_const.div (continuousOn_const.mul continuousOn_id)
    (fun t ht => mul_ne_zero Real.pi_ne_zero ((one_div_pos.mpr hβ).trans_le ht.1).ne')

lemma far_spectral_integral (β : ℝ) (hβ : 0 < β) :
    (∫ t in (1 / β)..band β, (1 / (Real.pi * t) + 1 / band β)) =
      Real.log 4 / Real.pi + 3 / 4 := by
  have hi : 1 / β ≤ band β := div_le_div_of_nonneg_right (by norm_num) hβ.le
  have hinv : IntervalIntegrable (fun t : ℝ => 1 / t) volume (1 / β) (band β) := by
    apply ContinuousOn.intervalIntegrable_of_Icc hi
    exact continuousOn_const.div continuousOn_id
      (fun t ht => ((one_div_pos.mpr hβ).trans_le ht.1).ne')
  have hfun : (fun t : ℝ => 1 / (Real.pi * t) + 1 / band β) =
      (fun t : ℝ => (1 / Real.pi) * (1 / t) + 1 / band β) := by
    ext t
    ring
  rw [hfun, intervalIntegral.integral_add (hinv.const_mul _) intervalIntegrable_const,
    intervalIntegral.integral_const_mul,
    integral_one_div_of_pos (one_div_pos.mpr hβ) (by dsimp [band]; positivity),
    intervalIntegral.integral_const]
  have he : band β / (1 / β) = 4 := by dsimp [band]; field_simp [hβ.ne']
  rw [he]
  dsimp [band]
  field_simp [hβ.ne']
  ring

lemma far_spectral_integral_le : Real.log (4 : ℝ) / Real.pi + 3 / 4 ≤ 5 / 4 := by
  have hl : Real.log (4 : ℝ) ≤ 3 / 2 := by
    apply (Real.log_le_iff_le_exp (by norm_num)).mpr
    have hh := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 2) 6
    have hn : (4 : ℝ) ≤ ∑ k ∈ Finset.range 6,
        (3 / 2 : ℝ) ^ k / (k.factorial : ℝ) := by
      norm_num [Finset.sum_range_succ]
    exact hn.trans hh
  have hh : Real.log (4 : ℝ) / Real.pi ≤ 1 / 2 := by
    apply (div_le_iff₀ Real.pi_pos).mpr
    linarith only [hl, pi_ge_twentyfive_eighths]
  linarith only [hh]

def secondFar (β : ℝ) (f : ℝ → ℝ) : ℝ :=
  (2 / band β) * ∫ t in (1 / β)..band β, ‖prawitzKernel (t / band β)‖ * f t

theorem second_far_le (β : ℝ) (hβ : 0 < β) (hmax : β ≤ betaMax)
    (f : ℝ → ℝ) (hf : ∀ t ∈ Ioc (1 / β) (band β), 0 ≤ f t)
    (hq : ∀ t ∈ Ioc (1 / β) (band β), f t ≤ Real.exp (-farDelta / β ^ 2)) :
    secondFar β f / β ≤ 1 / 1200 := by
  have hU : 0 < band β := div_pos (by norm_num) hβ
  have hi : 1 / β ≤ band β := div_le_div_of_nonneg_right (by norm_num) hβ.le
  have hm : secondFar β f ≤ ∫ t in Ioc (1 / β) (band β),
      (1 / (Real.pi * t) + 1 / band β) * Real.exp (-farDelta / β ^ 2) := by
    unfold secondFar
    rw [← intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le hi]
    apply setIntegral_mono_of_nonneg (μ := volume)
    · intro t ht
      exact mul_nonneg (by positivity) (mul_nonneg (norm_nonneg _) (hf t ht))
    · intro t ht
      have htp : 0 < t := (one_div_pos.mpr hβ).trans ht.1
      have hk := scaled_kernel_le (band β) t hU htp ht.2
      have hs : 0 ≤ 1 / (Real.pi * t) + 1 / band β := by positivity
      have hh := mul_le_mul hk (hq t ht) (hf t ht) hs
      nlinarith only [hh]
    · exact ((spectral_intervalIntegrable β hβ).mul_const _).1
  rw [← intervalIntegral.integral_of_le hi, intervalIntegral.integral_mul_const,
    far_spectral_integral β hβ] at hm
  have hdiv : secondFar β f / β ≤
      (Real.log 4 / Real.pi + 3 / 4) * (Real.exp (-farDelta / β ^ 2) / β) := by
    convert div_le_div_of_nonneg_right hm hβ.le using 1 <;> ring
  apply hdiv.trans
  have hh := mul_le_mul far_spectral_integral_le (far_exponential_ratio_le β hβ hmax)
    (by positivity : 0 ≤ Real.exp (-farDelta / β ^ 2) / β) (by norm_num : (0 : ℝ) ≤ 5 / 4)
  norm_num at hh ⊢
  exact hh

def secondTerm (β : ℝ) (f : ℝ → ℝ) : ℝ :=
  (2 / band β) * ∫ t in cutoff β..band β, ‖prawitzKernel (t / band β)‖ * f t

theorem second_term_le (β : ℝ) (hβ : 0 < β) (hmax : β ≤ betaMax)
    (f : ℝ → ℝ) (hf : ∀ t ∈ Ioc (cutoff β) (band β), 0 ≤ f t)
    (hq : ∀ t ∈ Ioc (cutoff β) (band β), f t ≤ envelope β t) :
    secondTerm β f / β < 1 / 1000 := by
  have hci := cutoff_le_inv β hβ hmax
  have hiU : 1 / β ≤ band β := div_le_div_of_nonneg_right (by norm_num) hβ.le
  have hcU := cutoff_le_band β hβ hmax
  have hc := cutoff_pos β hβ hmax
  by_cases hint : IntervalIntegrable (fun t : ℝ => ‖prawitzKernel (t / band β)‖ * f t)
      volume (cutoff β) (band β)
  · have hnear := second_near_le β hβ hmax f
      (fun t ht => hf t ⟨ht.1, ht.2.trans hiU⟩) (fun t ht =>
        (hq t ⟨ht.1, ht.2.trans hiU⟩).trans
          (envelope_le_near_gaussian β hβ t (hc.trans ht.1).le ht.2))
    have hfar := second_far_le β hβ hmax f
      (fun t ht => hf t ⟨hci.trans_lt ht.1, ht.2⟩) (fun t ht =>
        (hq t ⟨hci.trans_lt ht.1, ht.2⟩).trans
          (envelope_le_far_constant β hβ t ht.1.le ht.2))
    have hin : IntervalIntegrable (fun t : ℝ => ‖prawitzKernel (t / band β)‖ * f t)
        volume (cutoff β) (1 / β) := by
      apply hint.mono_set
      rw [uIcc_of_le hci, uIcc_of_le hcU]
      exact Icc_subset_Icc le_rfl hiU
    have hif : IntervalIntegrable (fun t : ℝ => ‖prawitzKernel (t / band β)‖ * f t)
        volume (1 / β) (band β) := by
      apply hint.mono_set
      rw [uIcc_of_le hiU, uIcc_of_le hcU]
      exact Icc_subset_Icc hci le_rfl
    have he : secondTerm β f = secondNear β f + secondFar β f := by
      unfold secondTerm secondNear secondFar
      rw [← intervalIntegral.integral_add_adjacent_intervals hin hif]
      ring
    rw [he, add_div]
    nlinarith only [hnear, hfar]
  · rw [secondTerm, intervalIntegral.integral_undef hint, mul_zero, zero_div]
    norm_num

open ProbabilityTheory

/-- The four actual Prawitz integrals, including both infinite-beta-ray
and improper-tail endpoints, have a strict effective bound. -/
theorem normalizedEnvelope_lt_two_fifths (μ : ProbabilityMeasure ℝ)
    (h : StandardizedLaw μ) (n N : ℕ) (hN : 0 < N) (hNn : N ≤ n)
    (hρ : rho0 ≤ thirdAbsoluteMoment μ) (hsmall : beta μ n ≤ betaMax) :
    PrawitzSmoothing.normalizedEnvelope μ n (cutoff (beta μ n)) (band (beta μ n)) /
      beta μ n < 2 / 5 := by
  have hn : 0 < n := lt_of_lt_of_le hN hNn
  have hβ : 0 < beta μ n :=
    div_pos (rho0_pos.trans_le hρ) (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn))
  let f : ℝ → ℝ := fun t => ‖charFun (μ : Measure ℝ) (t / Real.sqrt n) ^ n -
    (Real.exp (-(t ^ 2 / 2)) : ℂ)‖
  let q : ℝ → ℝ := fun t => ‖charFun (μ : Measure ℝ) (t / Real.sqrt n) ^ n‖
  have hfirst := first_term_le (beta μ n) hβ hsmall f
    (fun t _ => norm_nonneg _) (fun t ht => by
      have hh := normalized_power_sub_gaussian_le_price μ h n N hN hNn hρ t ht.1.le
      have hp := price_le_local_gaussian N (beta μ n) hβ hsmall t ht.1.le ht.2
      exact hh.trans hp)
  have hsecond := second_term_le (beta μ n) hβ hsmall q
    (fun t _ => norm_nonneg _) (fun t _ => by
      dsimp [q]
      rw [norm_pow]
      exact normalized_power_le_envelope μ h n hn hρ t)
  have hthird := third_term_le (beta μ n) hβ hsmall
  have hfourth := fourth_term_le (beta μ n) hβ hsmall
  have hbudget := four_term_rational_budget (beta μ n) hβ.le hsmall
  have he : PrawitzSmoothing.normalizedEnvelope μ n (cutoff (beta μ n))
      (band (beta μ n)) / beta μ n = firstTerm (beta μ n) f / beta μ n +
      secondTerm (beta μ n) q / beta μ n + thirdTerm (beta μ n) / beta μ n +
      ((1 / Real.pi) * (∫ t in Ioi (cutoff (beta μ n)),
        Real.exp (-(t ^ 2 / 2)) / t)) / beta μ n := by
    unfold PrawitzSmoothing.normalizedEnvelope firstTerm secondTerm thirdTerm
    dsimp [f, q, weight]
    simp only [add_div, neg_div]
  rw [he]
  linarith only [hfirst, hsecond, hthird, hfourth, hbudget]

/-- A genuine uniform CDF estimate on the whole effective small-beta ray.
The original standardized law needs only the proved third absolute moment. -/
theorem normalized_actual_cdf_lt_two_fifths (μ : ProbabilityMeasure ℝ)
    (h : StandardizedLaw μ) (n N : ℕ) (hN : 0 < N) (hNn : N ≤ n)
    (hρ : rho0 ≤ thirdAbsoluteMoment μ) (hsmall : beta μ n ≤ betaMax) (x : ℝ) :
    |(normalizedIidSumLaw μ n).real (Iic x) - GaussianTools.Phi x| <
      (2 / 5) * beta μ n := by
  have hn : 0 < n := lt_of_lt_of_le hN hNn
  have hβ : 0 < beta μ n :=
    div_pos (rho0_pos.trans_le hρ) (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn))
  have hs := PrawitzSmoothing.normalized_actual_cdf_le μ h n hn
    (cutoff (beta μ n)) (band (beta μ n)) (cutoff_pos _ hβ hsmall)
      (cutoff_le_band _ hβ hsmall) x
  exact hs.trans_lt ((div_lt_iff₀ hβ).mp
    (normalizedEnvelope_lt_two_fifths μ h n N hN hNn hρ hsmall))

end BerryEsseen.SmallBetaRayEndpoint

#print axioms BerryEsseen.SmallBetaRayEndpoint.sq_logScale_cube_le_endpoint
#print axioms BerryEsseen.SmallBetaRayEndpoint.mul_cutoff_cube_le_one
#print axioms BerryEsseen.SmallBetaRayEndpoint.lossEnvelope_le_local_gaussian
#print axioms BerryEsseen.SmallBetaRayEndpoint.price_le_local_gaussian
#print axioms BerryEsseen.SmallBetaRayEndpoint.first_term_le
#print axioms BerryEsseen.SmallBetaRayEndpoint.second_term_le
#print axioms BerryEsseen.SmallBetaRayEndpoint.third_term_le
#print axioms BerryEsseen.SmallBetaRayEndpoint.fourth_term_le
#print axioms BerryEsseen.SmallBetaRayEndpoint.normalizedEnvelope_lt_two_fifths
#print axioms BerryEsseen.SmallBetaRayEndpoint.normalized_actual_cdf_lt_two_fifths
