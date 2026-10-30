module

public import BerryEsseen.SecondOrderDamping
public import BerryEsseen.FixedSpectrumPrice

@[expose] public section

/-! 2026-10-30: connect the finite-index second-order spectrum directly
to the original iid CDF.  A whole spectral node uses eta=a/M once at
both endpoints.  The original rho0 loss and actual law's coefficient
condition are retained.  No numerical endpoint value is assumed here. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace BerryEsseen.FiniteBandRayPrice

open HighMomentRayDamping (rho0 beta beta_sq_mul_n)

def profile (N M : ℕ) (c R A V a s : ℝ) : ℝ :=
  FixedSpectrumPrice.spectralProfile N
    (SecondOrderDamping.spectrum (a / (M : ℝ)) c R) A V s

/-- A fixed lower moment bound licenses the coefficient for the same law. -/
theorem coefficient_qualifies (ρ c R : ℝ) (hR : 0 < R) (hρ : R ≤ ρ)
    (hc : 1 ≤ (c - 1) * R) : ρ + 1 ≤ c * ρ := by
  have hc0 : 0 ≤ c - 1 := by
    by_contra hh
    have hn : (c - 1) * R < 0 := mul_neg_of_neg_of_pos (lt_of_not_ge hh) hR
    linarith only [hc, hn]
  have hm := mul_le_mul_of_nonneg_left hρ hc0
  nlinarith only [hc, hm]

/-- The upper spectral cutoff follows from the same actual rho and n. -/
theorem spectral_upper (μ : ProbabilityMeasure ℝ) (n M : ℕ)
    (hn : 0 < n) (hnM : n ≤ M) (R : ℝ) (hR : 0 < R)
    (hρ : R ≤ thirdAbsoluteMoment μ) :
    1 / beta μ n ^ 2 ≤ (M : ℝ) / R ^ 2 := by
  have hβ : 0 < beta μ n := div_pos (hR.trans_le hρ)
    (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn))
  have hsq := pow_le_pow_left₀ hR.le hρ 2
  have hm := mul_le_mul_of_nonneg_left hsq (show 0 ≤ 1 / beta μ n ^ 2 by positivity)
  have he : (1 / beta μ n ^ 2) * thirdAbsoluteMoment μ ^ 2 = (n : ℝ) := by
    rw [← beta_sq_mul_n μ n hn]
    field_simp
  rw [he] at hm
  exact (le_div_iff₀ (sq_pos_of_pos hR)).mpr (hm.trans (Nat.cast_le.mpr hnM))

/-- Integer n retains the lower-bound information in n=s*rho^2.
In particular, the same node can use N=ceil(a*R^2), independently of its
upper endpoint.  This changes no actual-law domain. -/
theorem cutoff_qualifies (μ : ProbabilityMeasure ℝ) (n N : ℕ) (hn : 0 < n)
    (a R : ℝ) (hR : 0 < R) (hρ : R ≤ thirdAbsoluteMoment μ)
    (hs : a ≤ 1 / beta μ n ^ 2) (hN : (N : ℝ) - 1 < a * R ^ 2) : N ≤ n := by
  have hβ : 0 < beta μ n := div_pos (hR.trans_le hρ)
    (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn))
  have hsq := pow_le_pow_left₀ hR.le hρ 2
  have h1 := mul_le_mul_of_nonneg_right hs (sq_nonneg R)
  have h2 := mul_le_mul_of_nonneg_left hsq (show 0 ≤ 1 / beta μ n ^ 2 by positivity)
  have he : (1 / beta μ n ^ 2) * thirdAbsoluteMoment μ ^ 2 = (n : ℝ) := by
    rw [← beta_sq_mul_n μ n hn]
    field_simp
  rw [he] at h2
  have hreal : a * R ^ 2 ≤ (n : ℝ) := h1.trans h2
  by_contra hh
  have hnN : n + 1 ≤ N := Nat.succ_le_of_lt (lt_of_not_ge hh)
  have hnR : (n : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast hnN
  linarith only [hN, hreal, hnR]

/-- The original lower index and a node's upper spectral endpoint jointly
license a stronger reference moment. No law is discarded by using this R. -/
theorem node_moment_lower (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n N : ℕ) (hN : 0 < N) (hNn : N ≤ n) (b R : ℝ) (hb : 0 < b)
    (hR : 0 ≤ R) (hs : 1 / beta μ n ^ 2 ≤ b)
    (hbudget : b * R ^ 2 ≤ (N : ℝ)) : R ≤ thirdAbsoluteMoment μ := by
  have hn : 0 < n := lt_of_lt_of_le hN hNn
  have hρ : 0 < thirdAbsoluteMoment μ :=
    lt_of_lt_of_le zero_lt_one (ThirdMomentRegion.one_le_third μ h)
  have hβ : 0 < beta μ n := div_pos hρ (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn))
  have he : (1 / beta μ n ^ 2) * thirdAbsoluteMoment μ ^ 2 = (n : ℝ) := by
    rw [← beta_sq_mul_n μ n hn]
    field_simp
  have hm := mul_le_mul_of_nonneg_right hs (sq_nonneg (thirdAbsoluteMoment μ))
  rw [he] at hm
  have hp : b * R ^ 2 ≤ b * thirdAbsoluteMoment μ ^ 2 :=
    (hbudget.trans (Nat.cast_le.mpr hNn)).trans hm
  exact (sq_le_sq₀ hR hρ.le).mp ((mul_le_mul_iff_left₀ hb).mp
    (by simpa only [mul_comm] using hp))

private theorem actualQ (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n M : ℕ) (hn : 0 < n) (hnM : n ≤ M) (a : ℝ) (ha : 0 < a)
    (hs : a ≤ 1 / beta μ n ^ 2) (c R : ℝ) (hR : 0 < R)
    (hρ : R ≤ thirdAbsoluteMoment μ)
    (hC : thirdAbsoluteMoment μ + 1 ≤ c * thirdAbsoluteMoment μ) :
    ∀ u, 0 ≤ u → ‖charFun (μ : Measure ℝ) (u / Real.sqrt n)‖ ^ n ≤
      FixedSpectrumPrice.physicalQ (beta μ n)
        (SecondOrderDamping.spectrum (a / (M : ℝ)) c R) u := by
  intro u _
  exact SecondOrderDamping.normalized_power_le_finite_band μ h n M hn hnM a ha hs c R hR hρ hC u

theorem normalized_actual_cdf_le_profile (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n N M : ℕ) (hN : 0 < N) (hNn : N ≤ n) (hnM : n ≤ M)
    (hρ0 : rho0 ≤ thirdAbsoluteMoment μ) (c R A V a : ℝ)
    (hR : 0 < R) (hρR : R ≤ thirdAbsoluteMoment μ)
    (hC : thirdAbsoluteMoment μ + 1 ≤ c * thirdAbsoluteMoment μ)
    (hA : 0 < A) (hAV : A ≤ V) (ha : 0 < a)
    (hs : a ≤ 1 / beta μ n ^ 2) (x : ℝ) :
    |(normalizedIidSumLaw μ n).real (Iic x) - GaussianTools.Phi x| ≤
      beta μ n * profile N M c R A V a (1 / beta μ n ^ 2) := by
  have hn : 0 < n := lt_of_lt_of_le hN hNn
  have hη := (SecondOrderDamping.finite_band_admissible μ h n M hn hnM a ha hs).1
  exact FixedSpectrumPrice.normalized_actual_cdf_le_beta_spectralProfile μ h n N hN hNn hρ0
    (SecondOrderDamping.spectrum (a / (M : ℝ)) c R)
    (SecondOrderDamping.continuous_spectrum _ _ _)
    (fun v => SecondOrderDamping.spectrum_nonpos _ _ _ v hη)
    (actualQ μ h n M hn hnM a ha hs c R hR hρR hC) A V hA hAV x

theorem normalized_actual_cdf_le_linear_endpoints (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n N M : ℕ) (hN : 0 < N) (hNn : N ≤ n) (hnM : n ≤ M)
    (hρ0 : rho0 ≤ thirdAbsoluteMoment μ) (c R A V a b : ℝ)
    (hR : 0 < R) (hρR : R ≤ thirdAbsoluteMoment μ)
    (hC : thirdAbsoluteMoment μ + 1 ≤ c * thirdAbsoluteMoment μ)
    (hA : 0 < A) (hAV : A ≤ V) (ha : 0 < a) (hab : a < b)
    (hs : 1 / beta μ n ^ 2 ∈ Icc a b) (hb : b ≤ (N : ℝ) / rho0 ^ 2) (x : ℝ) :
    |(normalizedIidSumLaw μ n).real (Iic x) - GaussianTools.Phi x| ≤ beta μ n *
      (Real.exp ((5 / 2) * ((b - a) ^ 2 / (8 * a ^ 2))) *
        max (profile N M c R A V a a) (profile N M c R A V a b)) := by
  have hn : 0 < n := lt_of_lt_of_le hN hNn
  have hη := (SecondOrderDamping.finite_band_admissible μ h n M hn hnM a ha hs.1).1
  exact FixedSpectrumPrice.normalized_actual_cdf_le_linear_endpoints μ h n N hN hNn hρ0
    (SecondOrderDamping.spectrum (a / (M : ℝ)) c R)
    (SecondOrderDamping.continuous_spectrum _ _ _)
    (fun v => SecondOrderDamping.spectrum_nonpos _ _ _ v hη)
    (actualQ μ h n M hn hnM a ha hs.1 c R hR hρR hC) A V a b hA hAV ha hab hs hb x

theorem normalized_actual_cdf_le_const_endpoints (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n N M : ℕ) (hN : 0 < N) (hNn : N ≤ n) (hnM : n ≤ M)
    (hρ0 : rho0 ≤ thirdAbsoluteMoment μ) (c R A V a b : ℝ)
    (hR : 0 < R) (hρR : R ≤ thirdAbsoluteMoment μ)
    (hC : thirdAbsoluteMoment μ + 1 ≤ c * thirdAbsoluteMoment μ)
    (hA : 0 < A) (hAV : A ≤ V) (ha : 0 < a) (hab : a < b)
    (hs : 1 / beta μ n ^ 2 ∈ Icc a b) (hb : (N : ℝ) / rho0 ^ 2 ≤ a) (x : ℝ) :
    |(normalizedIidSumLaw μ n).real (Iic x) - GaussianTools.Phi x| ≤ beta μ n *
      (Real.exp ((3 / 2) * ((b - a) ^ 2 / (8 * a ^ 2))) *
        max (profile N M c R A V a a) (profile N M c R A V a b)) := by
  have hn : 0 < n := lt_of_lt_of_le hN hNn
  have hη := (SecondOrderDamping.finite_band_admissible μ h n M hn hnM a ha hs.1).1
  exact FixedSpectrumPrice.normalized_actual_cdf_le_const_endpoints μ h n N hN hNn hρ0
    (SecondOrderDamping.spectrum (a / (M : ℝ)) c R)
    (SecondOrderDamping.continuous_spectrum _ _ _)
    (fun v => SecondOrderDamping.spectrum_nonpos _ _ _ v hη)
    (actualQ μ h n M hn hnM a ha hs.1 c R hR hρR hC) A V a b hA hAV ha hab hs hb x

/-- Both reference moment and numerical cutoff can be acquired from the
same original spectral node. These licenses preserve the original law
domain rather than introducing extra moment or index hypotheses. -/
theorem normalized_actual_cdf_le_correlated_linear_endpoints
    (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (n Nbase N M : ℕ)
    (hbase : 0 < Nbase) (hbasen : Nbase ≤ n) (hnM : n ≤ M) (hN : 0 < N)
    (Rbase : ℝ) (hbaseρ0 : rho0 ≤ Rbase) (hρbase : Rbase ≤ thirdAbsoluteMoment μ)
    (c R A V a b : ℝ) (hR : 0 < R) (hA : 0 < A) (hAV : A ≤ V)
    (ha : 0 < a) (hab : a < b) (hs : 1 / beta μ n ^ 2 ∈ Icc a b)
    (hRlicense : R ≤ Rbase ∨ b * R ^ 2 ≤ (Nbase : ℝ))
    (hNlicense : N ≤ Nbase ∨ (N : ℝ) - 1 < a * R ^ 2)
    (hcoefficient : 1 ≤ (c - 1) * R) (hb : b ≤ (N : ℝ) / rho0 ^ 2) (x : ℝ) :
    |(normalizedIidSumLaw μ n).real (Iic x) - GaussianTools.Phi x| ≤ beta μ n *
      (Real.exp ((5 / 2) * ((b - a) ^ 2 / (8 * a ^ 2))) *
        max (profile N M c R A V a a) (profile N M c R A V a b)) := by
  have hn : 0 < n := lt_of_lt_of_le hbase hbasen
  have hρR : R ≤ thirdAbsoluteMoment μ := by
    rcases hRlicense with hsmall | hbudget
    · exact hsmall.trans hρbase
    · exact node_moment_lower μ h n Nbase hbase hbasen b R (ha.trans hab) hR.le hs.2 hbudget
  have hNn : N ≤ n := by
    rcases hNlicense with hsmall | hinteger
    · exact hsmall.trans hbasen
    · exact cutoff_qualifies μ n N hn a R hR hρR hs.1 hinteger
  exact normalized_actual_cdf_le_linear_endpoints μ h n N M hN hNn hnM
    (hbaseρ0.trans hρbase) c R A V a b hR hρR
    (coefficient_qualifies _ c R hR hρR hcoefficient) hA hAV ha hab hs hb x

end BerryEsseen.FiniteBandRayPrice

#print axioms BerryEsseen.FiniteBandRayPrice.coefficient_qualifies
#print axioms BerryEsseen.FiniteBandRayPrice.spectral_upper
#print axioms BerryEsseen.FiniteBandRayPrice.cutoff_qualifies
#print axioms BerryEsseen.FiniteBandRayPrice.node_moment_lower
#print axioms BerryEsseen.FiniteBandRayPrice.normalized_actual_cdf_le_profile
#print axioms BerryEsseen.FiniteBandRayPrice.normalized_actual_cdf_le_linear_endpoints
#print axioms BerryEsseen.FiniteBandRayPrice.normalized_actual_cdf_le_const_endpoints
#print axioms BerryEsseen.FiniteBandRayPrice.normalized_actual_cdf_le_correlated_linear_endpoints
