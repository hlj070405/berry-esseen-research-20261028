module

public import BerryEsseen.SignedMoment
public import BerryEsseen.GaussianTools
public import BerryEsseen.GaussianMills
public import BerryEsseen.CommonProductMoments
public import BerryEsseen.ContactVariation
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
public import Mathlib.MeasureTheory.Measure.DiracProba
public import Mathlib.Tactic.FieldSimp

@[expose] public section

/-!
The original all-law fixed-index positive closed-CDF score and the
compactness prerequisites for an extremizer. These definitions retain
every standardized law with finite absolute third moment.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ENNReal BoundedContinuousFunction

namespace BerryEsseen.Extremizer

def iidSumProbability (μ : ProbabilityMeasure ℝ) (n : ℕ) : ProbabilityMeasure ℝ :=
  ⟨MixtureSum.iidSumLaw (μ : Measure ℝ) n, by
    rw [MixtureSum.iidSumLaw_eq_convPower]
    infer_instance⟩

@[simp] lemma coe_iidSumProbability (μ : ProbabilityMeasure ℝ) (n : ℕ) :
    (iidSumProbability μ n : Measure ℝ) = MixtureSum.iidSumLaw (μ : Measure ℝ) n := rfl

def positiveClosedScore (μ : ProbabilityMeasure ℝ) (n : ℕ) (H : ℝ) : ℝ :=
  Real.sqrt n * ((iidSumProbability μ n : Measure ℝ).real (Iic H) -
    GaussianTools.Phi (H / Real.sqrt n)) / thirdAbsoluteMoment μ

def scoreSet (n : ℕ) : Set ℝ :=
  {c | ∃ μ : ProbabilityMeasure ℝ, ∃ _ : StandardizedLaw μ, ∃ H : ℝ,
    c = positiveClosedScore μ n H}

/-- The supremum over the full original law and real-threshold domain. -/
def fixedNSup (n : ℕ) : ℝ := sSup (scoreSet n)

theorem thirdAbsoluteMoment_ge_one (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    1 ≤ thirdAbsoluteMoment μ := by
  have ha := SignedMoment.firstAbsoluteMoment_pos μ h
  have hfirst := SignedMoment.first_mul_third_ge_one_add_signed_sq μ h
  have hsecond := SignedMoment.first_sq_add_signed_sq_le_one μ h
  have ha1 : SignedMoment.firstAbsoluteMoment μ ≤ 1 := by nlinarith
  have hρ : 0 ≤ thirdAbsoluteMoment μ :=
    integral_nonneg (fun x => pow_nonneg (abs_nonneg x) 3)
  have hprod := mul_le_mul_of_nonneg_right ha1 hρ
  nlinarith [sq_nonneg (SignedMoment.signedSecondMoment μ)]

lemma thirdAbsoluteMoment_pos (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) :
    0 < thirdAbsoluteMoment μ := lt_of_lt_of_le zero_lt_one (thirdAbsoluteMoment_ge_one μ h)

theorem positiveClosedScore_le_inverse_moment (μ : ProbabilityMeasure ℝ)
    (h : StandardizedLaw μ) (n : ℕ) (H : ℝ) :
    positiveClosedScore μ n H ≤ Real.sqrt n / thirdAbsoluteMoment μ := by
  have hF : (iidSumProbability μ n : Measure ℝ).real (Iic H) ≤ 1 := measureReal_le_one
  have hPhi : 0 ≤ GaussianTools.Phi (H / Real.sqrt n) := ENNReal.toReal_nonneg
  have hdiff : (iidSumProbability μ n : Measure ℝ).real (Iic H) -
      GaussianTools.Phi (H / Real.sqrt n) ≤ 1 := by linarith
  have hnum := mul_le_mul_of_nonneg_left hdiff (Real.sqrt_nonneg (n : ℝ))
  simpa only [positiveClosedScore, mul_one] using
    div_le_div_of_nonneg_right hnum (le_of_lt (thirdAbsoluteMoment_pos μ h))

theorem positiveClosedScore_le_sqrt (μ : ProbabilityMeasure ℝ)
    (h : StandardizedLaw μ) (n : ℕ) (H : ℝ) :
    positiveClosedScore μ n H ≤ Real.sqrt n := by
  apply (positiveClosedScore_le_inverse_moment μ h n H).trans
  apply (div_le_iff₀ (thirdAbsoluteMoment_pos μ h)).mpr
  simpa only [one_mul, mul_comm] using
    mul_le_mul_of_nonneg_right (thirdAbsoluteMoment_ge_one μ h) (Real.sqrt_nonneg (n : ℝ))

theorem scoreSet_bddAbove (n : ℕ) : BddAbove (scoreSet n) := by
  refine ⟨Real.sqrt n, ?_⟩
  rintro c ⟨μ, hμ, H, rfl⟩
  exact positiveClosedScore_le_sqrt μ hμ n H

theorem positiveClosedScore_le_fixedNSup (μ : ProbabilityMeasure ℝ)
    (h : StandardizedLaw μ) (n : ℕ) (H : ℝ) :
    positiveClosedScore μ n H ≤ fixedNSup n :=
  le_csSup (scoreSet_bddAbove n) ⟨μ, h, H, rfl⟩

theorem fixedNSup_le_sqrt (n : ℕ) : fixedNSup n ≤ Real.sqrt n := by
  by_cases hne : (scoreSet n).Nonempty
  · apply csSup_le hne
    rintro c ⟨μ, hμ, H, rfl⟩
    exact positiveClosedScore_le_sqrt μ hμ n H
  · have hempty : scoreSet n = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    simpa only [fixedNSup, hempty, Real.sSup_empty] using Real.sqrt_nonneg (n : ℝ)

theorem scoreSet_nonempty_of_fixedNSup_pos (n : ℕ) (hC : 0 < fixedNSup n) :
    (scoreSet n).Nonempty := by
  by_contra hne
  have hempty : scoreSet n = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
  simp only [fixedNSup, hempty, Real.sSup_empty, lt_self_iff_false] at hC

/-- A positive score layer already bounds the actual third moment.
No universal Berry--Esseen upper bound is used. -/
theorem thirdAbsoluteMoment_le_of_score_ge_half (μ : ProbabilityMeasure ℝ)
    (h : StandardizedLaw μ) (n : ℕ) (H C : ℝ) (hC : 0 < C)
    (hscore : C / 2 ≤ positiveClosedScore μ n H) :
    thirdAbsoluteMoment μ ≤ 2 * Real.sqrt n / C := by
  have hprod := (le_div_iff₀ (thirdAbsoluteMoment_pos μ h)).mp
    (hscore.trans (positiveClosedScore_le_inverse_moment μ h n H))
  apply (le_div_iff₀ hC).mpr
  nlinarith

/-- A maximizing sequence in the original all-law domain, whose third
moments have the finite bound needed for uniform integrability. -/
theorem exists_maximizing_sequence (n : ℕ) (hC : 0 < fixedNSup n) :
    ∃ μ : ℕ → ProbabilityMeasure ℝ, ∃ H : ℕ → ℝ,
      (∀ m, StandardizedLaw (μ m)) ∧
      Tendsto (fun m => positiveClosedScore (μ m) n (H m)) atTop (𝓝 (fixedNSup n)) ∧
      (∀ m, fixedNSup n / 2 < positiveClosedScore (μ m) n (H m)) ∧
      (∀ m, thirdAbsoluteMoment (μ m) ≤ 2 * Real.sqrt n / fixedNSup n) := by
  let C := fixedNSup n
  have hne := scoreSet_nonempty_of_fixedNSup_pos n hC
  have hex : ∀ m : ℕ, ∃ μ : ProbabilityMeasure ℝ, StandardizedLaw μ ∧ ∃ H : ℝ,
      C - (C / 2) * (1 / ((m : ℝ) + 1)) < positiveClosedScore μ n H := by
    intro m
    have hden : 0 < (m : ℝ) + 1 := add_pos_of_nonneg_of_pos (Nat.cast_nonneg m) zero_lt_one
    have hfrac : 0 < 1 / ((m : ℝ) + 1) := one_div_pos.mpr hden
    have hlt : C - (C / 2) * (1 / ((m : ℝ) + 1)) < fixedNSup n := by
      have hp := mul_pos (show 0 < C / 2 by dsimp [C]; linarith) hfrac
      dsimp [C] at hp ⊢
      linarith
    obtain ⟨c, ⟨μ, hμ, H, rfl⟩, hc⟩ := exists_lt_of_lt_csSup hne hlt
    exact ⟨μ, hμ, H, hc⟩
  choose μ hμ H hclose using hex
  have hlower : ∀ m : ℕ, C / 2 < positiveClosedScore (μ m) n (H m) := by
    intro m
    have hden : 0 < (m : ℝ) + 1 := add_pos_of_nonneg_of_pos (Nat.cast_nonneg m) zero_lt_one
    have hfrac : 1 / ((m : ℝ) + 1) ≤ 1 :=
      (div_le_one₀ hden).mpr (by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
    have hp := mul_le_mul_of_nonneg_left hfrac (show 0 ≤ C / 2 by dsimp [C]; linarith)
    linarith [hclose m]
  refine ⟨μ, H, hμ, ?_, hlower, ?_⟩
  · have hlowlim : Tendsto (fun m : ℕ => C - (C / 2) * (1 / ((m : ℝ) + 1)))
        atTop (𝓝 C) := by
      have hmul : Tendsto (fun m : ℕ => (C / 2) * (1 / ((m : ℝ) + 1)))
          atTop (𝓝 ((C / 2) * 0)) :=
        tendsto_const_nhds.mul tendsto_one_div_add_atTop_nhds_zero_nat
      have ht := (tendsto_const_nhds : Tendsto (fun _ : ℕ => C) atTop (𝓝 C)).sub hmul
      simpa only [mul_zero, sub_zero] using ht
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlowlim tendsto_const_nhds
      (fun m => (hclose m).le) (fun m => positiveClosedScore_le_fixedNSup (μ m) (hμ m) n (H m))
  · intro m
    exact thirdAbsoluteMoment_le_of_score_ge_half (μ m) (hμ m) n (H m) C hC (hlower m).le

theorem continuous_iidSumProbability (n : ℕ) :
    Continuous (fun μ : ProbabilityMeasure ℝ => iidSumProbability μ n) := by
  have hfun : (fun μ : ProbabilityMeasure ℝ => iidSumProbability μ n) =
      (fun μ : ProbabilityMeasure ℝ =>
        (ProbabilityMeasure.pi (fun _ : Fin n => μ)).map (fun z => ∑ i, z i)) := by
    funext μ
    apply ProbabilityMeasure.toMeasure_injective
    rfl
  rw [hfun]
  have hdiag : Continuous (fun μ : ProbabilityMeasure ℝ => fun _ : Fin n => μ) :=
    continuous_pi (fun _ => continuous_id)
  exact (ProbabilityMeasure.continuous_map (by fun_prop)).comp
    (ProbabilityMeasure.continuous_pi.comp hdiag)

/-- The second moment belongs to the actual independent sum law. -/
theorem iidSum_moments (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ) (n : ℕ) :
    Integrable (fun x : ℝ => x) (iidSumProbability μ n : Measure ℝ) ∧
    Integrable (fun x : ℝ => x ^ 2) (iidSumProbability μ n : Measure ℝ) ∧
    (∫ x : ℝ, x ∂(iidSumProbability μ n : Measure ℝ)) = 0 ∧
    (∫ x : ℝ, x ^ 2 ∂(iidSumProbability μ n : Measure ℝ)) = (n : ℝ) := by
  have hm := CommonProductMoments.convPower_moments (μ : Measure ℝ)
    h.integrable_mean h.integrable_square h.mean_zero n
  have hmeasure : (iidSumProbability μ n : Measure ℝ) =
      MixtureSum.convPower (μ : Measure ℝ) n := MixtureSum.iidSumLaw_eq_convPower _ n
  rw [hmeasure]
  simpa only [h.second_moment_one, mul_one] using hm

/-- A genuine moment-based probability tail bound, in the measure-valued form
needed by Prokhorov's tightness criterion. -/
theorem measure_abs_gt_le_second (ν : ProbabilityMeasure ℝ)
    (h2 : Integrable (fun x : ℝ => x ^ 2) (ν : Measure ℝ)) (R : ℝ) (hR : 0 < R) :
    (ν : Measure ℝ) {x | R < |x|} ≤
      ENNReal.ofReal ((∫ x : ℝ, x ^ 2 ∂(ν : Measure ℝ)) / R ^ 2) := by
  have hi := h2.div_const (R ^ 2)
  have hn : 0 ≤ᵐ[(ν : Measure ℝ)] (fun x : ℝ => x ^ 2 / R ^ 2) :=
    Filter.Eventually.of_forall (fun x => div_nonneg (sq_nonneg x) (sq_nonneg R))
  have hs : ∀ x ∈ {x : ℝ | R < |x|}, 1 ≤ x ^ 2 / R ^ 2 := by
    intro x hx
    apply (one_le_div₀ (sq_pos_of_pos hR)).mpr
    simpa only [sq_abs] using
      (sq_le_sq₀ hR.le (abs_nonneg x)).mpr (le_of_lt hx)
  have hb := hi.measure_le_integral hn hs
  rwa [integral_div] at hb

theorem standardized_measure_abs_gt (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (R : ℝ) (hR : 0 < R) :
    (μ : Measure ℝ) {x | R < |x|} ≤ ENNReal.ofReal (1 / R ^ 2) := by
  simpa only [h.second_moment_one] using measure_abs_gt_le_second μ h.integrable_square R hR

theorem iidSum_measure_abs_gt (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (R : ℝ) (hR : 0 < R) :
    (iidSumProbability μ n : Measure ℝ) {x | R < |x|} ≤
      ENNReal.ofReal ((n : ℝ) / R ^ 2) := by
  have hm := iidSum_moments μ h n
  simpa only [hm.2.2.2] using measure_abs_gt_le_second (iidSumProbability μ n) hm.2.1 R hR

def standardizedFamily : Set (ProbabilityMeasure ℝ) := {μ | StandardizedLaw μ}

theorem standardizedFamily_isTight :
    IsTightMeasureSet {((μ : ProbabilityMeasure ℝ) : Measure ℝ) | μ ∈ standardizedFamily} := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  by_cases htop : ε = ∞
  · exact ⟨∅, isCompact_empty, fun _ _ => by simp [htop]⟩
  have he : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' htop
  let R : ℝ := 1 + 1 / ε.toReal
  have hR1 : 1 ≤ R := by
    dsimp [R]
    linarith [one_div_pos.mpr he]
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one hR1
  have hcancel : ε.toReal * (1 / ε.toReal) = 1 := mul_div_cancel₀ 1 he.ne'
  have heR : 1 ≤ ε.toReal * R := by dsimp [R]; nlinarith
  have hRsq : R ≤ R ^ 2 := by nlinarith [sq_nonneg (R - 1)]
  have hbound : 1 / R ^ 2 ≤ ε.toReal := by
    apply (div_le_iff₀ (sq_pos_of_pos hR)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hRsq he.le]
  have hεbound : ENNReal.ofReal (1 / R ^ 2) ≤ ε := by
    rw [← ENNReal.ofReal_toReal htop]
    exact ENNReal.ofReal_le_ofReal hbound
  refine ⟨Icc (-R) R, isCompact_Icc, ?_⟩
  rintro ν ⟨μ, hμ, rfl⟩
  have hset : (Icc (-R) R)ᶜ = {x : ℝ | R < |x|} := by
    ext x
    simp only [mem_compl_iff, mem_Icc, ← abs_le, not_le, mem_ofPred_eq]
  rw [hset]
  exact (standardized_measure_abs_gt μ hμ R hR).trans hεbound

theorem isCompact_closure_standardizedFamily : IsCompact (closure standardizedFamily) :=
  isCompact_closure_of_isTightMeasureSet standardizedFamily_isTight

/-- This gives a weak probability limit, without asserting that its moments
are preserved. Moment preservation is a separate required step. -/
theorem standardized_sequence_has_weak_subsequence (μ : ℕ → ProbabilityMeasure ℝ)
    (hμ : ∀ k, StandardizedLaw (μ k)) :
    ∃ ν : ProbabilityMeasure ℝ, ∃ σ : ℕ → ℕ, StrictMono σ ∧
      Tendsto (μ ∘ σ) atTop (𝓝 ν) := by
  obtain ⟨ν, hν, σ, hσ, hlim⟩ := isCompact_closure_standardizedFamily.tendsto_subseq
    (fun k => subset_closure (hμ k))
  exact ⟨ν, σ, hσ, hlim⟩

/-- Portmanteau applied to the actual nonnegative continuous cubic
integrand gives both integrability and the third-moment cap at a weak limit. -/
theorem weakLimit_integrable_cube_and_cap (μ : ℕ → ProbabilityMeasure ℝ)
    (ν : ProbabilityMeasure ℝ) (R : ℝ) (hμ : ∀ k, StandardizedLaw (μ k))
    (hcap : ∀ k, thirdAbsoluteMoment (μ k) ≤ R)
    (hlim : Tendsto μ atTop (𝓝 ν)) :
    Integrable (fun x : ℝ => |x| ^ 3) (ν : Measure ℝ) ∧ thirdAbsoluteMoment ν ≤ R := by
  have hc : Continuous (fun x : ℝ => |x| ^ 3) := continuous_abs.pow 3
  have hn : 0 ≤ (fun x : ℝ => |x| ^ 3) := fun x => pow_nonneg (abs_nonneg x) 3
  have hopens : ∀ G : Set ℝ, IsOpen G →
      (ν : Measure ℝ) G ≤ atTop.liminf (fun k => (μ k : Measure ℝ) G) :=
    fun G hG => ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim hG
  have hfatou := lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure
    hc hn hopens
  have hibound : ∀ k, (∫⁻ x : ℝ, ENNReal.ofReal (|x| ^ 3) ∂(μ k : Measure ℝ)) ≤
      ENNReal.ofReal R := by
    intro k
    rw [← ofReal_integral_eq_lintegral_ofReal (hμ k).integrable_cube
      (Filter.Eventually.of_forall hn)]
    exact ENNReal.ofReal_le_ofReal (hcap k)
  have hliminf : (atTop.liminf fun k =>
      ∫⁻ x : ℝ, ENNReal.ofReal (|x| ^ 3) ∂(μ k : Measure ℝ)) ≤ ENNReal.ofReal R := by
    have ht : (atTop.liminf fun k =>
        ∫⁻ x : ℝ, ENNReal.ofReal (|x| ^ 3) ∂(μ k : Measure ℝ)) ≤
        atTop.liminf (fun _ : ℕ => ENNReal.ofReal R) :=
      liminf_le_liminf (Filter.Eventually.of_forall hibound)
    simpa only [liminf_const] using ht
  have hbound : (∫⁻ x : ℝ, ENNReal.ofReal (|x| ^ 3) ∂(ν : Measure ℝ)) ≤
      ENNReal.ofReal R := hfatou.trans hliminf
  have hint : Integrable (fun x : ℝ => |x| ^ 3) (ν : Measure ℝ) := by
    refine ⟨hc.aestronglyMeasurable, ?_⟩
    exact (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hn)).mpr
      (hbound.trans_lt ENNReal.ofReal_lt_top)
  refine ⟨hint, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hn)] at hbound
  have hR : 0 ≤ R := (show 0 ≤ thirdAbsoluteMoment (μ 0) by
    linarith [thirdAbsoluteMoment_ge_one (μ 0) (hμ 0)]).trans (hcap 0)
  exact (ENNReal.ofReal_le_ofReal_iff hR).mp hbound

lemma weakLimit_nonnegative_integral_cap (μ : ℕ → ProbabilityMeasure ℝ)
    (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hc : Continuous f) (hn : 0 ≤ f)
    (hi : ∀ k, Integrable f (μ k : Measure ℝ))
    (hb : ∀ k, (∫ x, f x ∂(μ k : Measure ℝ)) ≤ B)
    (hlim : Tendsto μ atTop (𝓝 ν)) :
    Integrable f (ν : Measure ℝ) ∧ (∫ x, f x ∂(ν : Measure ℝ)) ≤ B := by
  have hopens : ∀ G : Set ℝ, IsOpen G →
      (ν : Measure ℝ) G ≤ atTop.liminf (fun k => (μ k : Measure ℝ) G) :=
    fun G hG => ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim hG
  have hfatou := lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure
    hc hn hopens
  have hibound : ∀ k, (∫⁻ x, ENNReal.ofReal (f x) ∂(μ k : Measure ℝ)) ≤
      ENNReal.ofReal B := by
    intro k
    rw [← ofReal_integral_eq_lintegral_ofReal (hi k) (Filter.Eventually.of_forall hn)]
    exact ENNReal.ofReal_le_ofReal (hb k)
  have hliminf : (atTop.liminf fun k =>
      ∫⁻ x, ENNReal.ofReal (f x) ∂(μ k : Measure ℝ)) ≤ ENNReal.ofReal B := by
    have ht : (atTop.liminf fun k => ∫⁻ x, ENNReal.ofReal (f x) ∂(μ k : Measure ℝ)) ≤
        atTop.liminf (fun _ : ℕ => ENNReal.ofReal B) :=
      liminf_le_liminf (Filter.Eventually.of_forall hibound)
    simpa only [liminf_const] using ht
  have hbound := hfatou.trans hliminf
  have hint : Integrable f (ν : Measure ℝ) :=
    ⟨hc.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hn)).mpr
        (hbound.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hint, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hn)] at hbound
  exact (ENNReal.ofReal_le_ofReal_iff hB).mp hbound

lemma integrable_first_square_of_cube (ν : ProbabilityMeasure ℝ)
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) (ν : Measure ℝ)) :
    Integrable (fun x : ℝ => x) (ν : Measure ℝ) ∧
    Integrable (fun x : ℝ => x ^ 2) (ν : Measure ℝ) := by
  have hm : AEStronglyMeasurable (fun x : ℝ => x) (ν : Measure ℝ) :=
    measurable_id.aestronglyMeasurable
  have h3n : Integrable (fun x : ℝ => ‖x‖ ^ 3) (ν : Measure ℝ) := by
    simpa only [Real.norm_eq_abs] using h3
  refine ⟨(integrable_norm_iff hm).mp ?_, ?_⟩
  · simpa only [pow_one] using integrable_norm_pow_of_le hm (by decide : 1 ≤ 3) h3n
  · simpa only [Real.norm_eq_abs, sq_abs] using
      integrable_norm_pow_of_le hm (by decide : 2 ≤ 3) h3n

lemma integrable_shift_square (ν : ProbabilityMeasure ℝ)
    (h1 : Integrable (fun x : ℝ => x) (ν : Measure ℝ))
    (h2 : Integrable (fun x : ℝ => x ^ 2) (ν : Measure ℝ)) (c : ℝ) :
    Integrable (fun x : ℝ => (x - c) ^ 2) (ν : Measure ℝ) := by
  have hfun : (fun x : ℝ => (x - c) ^ 2) =
      (fun x : ℝ => x ^ 2 - (2 * c) * x + c ^ 2) := by funext x; ring
  rw [hfun]
  exact (h2.sub (h1.const_mul (2 * c))).add (integrable_const (c ^ 2))

lemma integral_shift_square (ν : ProbabilityMeasure ℝ)
    (h1 : Integrable (fun x : ℝ => x) (ν : Measure ℝ))
    (h2 : Integrable (fun x : ℝ => x ^ 2) (ν : Measure ℝ)) (c : ℝ) :
    (∫ x : ℝ, (x - c) ^ 2 ∂(ν : Measure ℝ)) =
      (∫ x : ℝ, x ^ 2 ∂(ν : Measure ℝ)) -
        (2 * c) * (∫ x : ℝ, x ∂(ν : Measure ℝ)) + c ^ 2 := by
  have hfun : (fun x : ℝ => (x - c) ^ 2) =
      (fun x : ℝ => x ^ 2 - (2 * c) * x + c ^ 2) := by funext x; ring
  have hA : Integrable (fun x : ℝ => x ^ 2 - (2 * c) * x) (ν : Measure ℝ) :=
    h2.sub (h1.const_mul (2 * c))
  rw [hfun, integral_add hA (integrable_const (c ^ 2)),
    integral_sub h2 (h1.const_mul (2 * c)), integral_const_mul, integral_const]
  simp only [probReal_univ, one_smul]

def squareTrunc (T : ℝ) : ℝ →ᵇ ℝ where
  toFun x := min (x ^ 2) (T ^ 2)
  continuous_toFun := (continuous_id.pow 2).min continuous_const
  map_bounded' := by
    refine ⟨2 * T ^ 2, ?_⟩
    intro x y
    rw [Real.dist_eq, abs_le]
    have hx0 : 0 ≤ min (x ^ 2) (T ^ 2) := le_min (sq_nonneg x) (sq_nonneg T)
    have hy0 : 0 ≤ min (y ^ 2) (T ^ 2) := le_min (sq_nonneg y) (sq_nonneg T)
    have hxT := min_le_right (x ^ 2) (T ^ 2)
    have hyT := min_le_right (y ^ 2) (T ^ 2)
    constructor <;> linarith

lemma square_le_trunc_add_cube_div (x T : ℝ) (hT : 0 < T) :
    x ^ 2 ≤ squareTrunc T x + |x| ^ 3 / T := by
  change x ^ 2 ≤ min (x ^ 2) (T ^ 2) + |x| ^ 3 / T
  by_cases hx : x ^ 2 ≤ T ^ 2
  · rw [min_eq_left hx]
    exact le_add_of_nonneg_right (div_nonneg (pow_nonneg (abs_nonneg x) 3) hT.le)
  · rw [min_eq_right (le_of_not_ge hx)]
    have hsq : T ^ 2 ≤ |x| ^ 2 := by simpa only [sq_abs] using (le_of_not_ge hx)
    have hTx : T ≤ |x| := (sq_le_sq₀ hT.le (abs_nonneg x)).mp hsq
    have hmul := mul_le_mul_of_nonneg_right hTx (sq_nonneg x)
    have hcube : |x| ^ 3 = |x| * x ^ 2 := by rw [pow_succ, sq_abs]; ring
    have hd : x ^ 2 ≤ |x| ^ 3 / T := (le_div_iff₀ hT).mpr (by rw [hcube]; nlinarith)
    nlinarith [sq_nonneg T]

/-- A bounded cubic moment prevents both loss of centering and loss of
variance at a weak limit. The second-moment lower bound uses the actual
bounded continuous truncations and their explicit cubic tail error. -/
theorem weakLimit_standardizedLaw_of_third_cap (μ : ℕ → ProbabilityMeasure ℝ)
    (ν : ProbabilityMeasure ℝ) (R : ℝ) (hμ : ∀ k, StandardizedLaw (μ k))
    (hcap : ∀ k, thirdAbsoluteMoment (μ k) ≤ R)
    (hlim : Tendsto μ atTop (𝓝 ν)) : StandardizedLaw ν ∧ thirdAbsoluteMoment ν ≤ R := by
  obtain ⟨hν3, hνcap⟩ := weakLimit_integrable_cube_and_cap μ ν R hμ hcap hlim
  obtain ⟨hν1, hν2⟩ := integrable_first_square_of_cube ν hν3
  have hlinear : ∀ c : ℝ, (∫ x : ℝ, x ^ 2 ∂(ν : Measure ℝ)) -
      (2 * c) * (∫ x : ℝ, x ∂(ν : Measure ℝ)) ≤ 1 := by
    intro c
    have hshift : ∀ k, (∫ x : ℝ, (x - c) ^ 2 ∂(μ k : Measure ℝ)) ≤ 1 + c ^ 2 := by
      intro k
      rw [integral_shift_square (μ k) (hμ k).integrable_mean (hμ k).integrable_square c,
        (hμ k).second_moment_one, (hμ k).mean_zero]
      ring_nf
      exact le_rfl
    have hlimc := weakLimit_nonnegative_integral_cap μ ν (fun x : ℝ => (x - c) ^ 2)
      (1 + c ^ 2) (by nlinarith [sq_nonneg c])
      ((continuous_id.sub continuous_const).pow 2) (fun x => sq_nonneg (x - c))
      (fun k => integrable_shift_square (μ k) (hμ k).integrable_mean (hμ k).integrable_square c)
      hshift hlim
    have hc := hlimc.2
    rw [integral_shift_square ν hν1 hν2 c] at hc
    linarith
  have hmean : (∫ x : ℝ, x ∂(ν : Measure ℝ)) = 0 := by
    by_contra hm
    have hc := hlinear (-1 / (∫ x : ℝ, x ∂(ν : Measure ℝ)))
    have hcancel : (-1 / (∫ x : ℝ, x ∂(ν : Measure ℝ))) *
        (∫ x : ℝ, x ∂(ν : Measure ℝ)) = -1 := div_mul_cancel₀ (-1) hm
    have hnon : 0 ≤ (∫ x : ℝ, x ^ 2 ∂(ν : Measure ℝ)) := integral_nonneg (fun x => sq_nonneg x)
    nlinarith
  have hupper : (∫ x : ℝ, x ^ 2 ∂(ν : Measure ℝ)) ≤ 1 := by simpa using hlinear 0
  have hlowerT : ∀ T : ℝ, 0 < T →
      1 ≤ (∫ x : ℝ, x ^ 2 ∂(ν : Measure ℝ)) + R / T := by
    intro T hT
    have htestlow : ∀ k, 1 - R / T ≤ ∫ x, squareTrunc T x ∂(μ k : Measure ℝ) := by
      intro k
      have ht := BoundedContinuousFunction.integrable (μ k : Measure ℝ) (squareTrunc T)
      have hle := integral_mono (hμ k).integrable_square
        (ht.add ((hμ k).integrable_cube.div_const T)) (fun x => square_le_trunc_add_cube_div x T hT)
      simp only [Pi.add_apply] at hle
      rw [(hμ k).second_moment_one, integral_add ht ((hμ k).integrable_cube.div_const T),
        integral_div] at hle
      change 1 ≤ (∫ x, squareTrunc T x ∂(μ k : Measure ℝ)) + thirdAbsoluteMoment (μ k) / T at hle
      have hd := div_le_div_of_nonneg_right (hcap k) hT.le
      change thirdAbsoluteMoment (μ k) / T ≤ R / T at hd
      linarith
    have htestlim := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim (squareTrunc T)
    have htestν : 1 - R / T ≤ ∫ x, squareTrunc T x ∂(ν : Measure ℝ) :=
      le_of_tendsto_of_tendsto tendsto_const_nhds htestlim (Filter.Eventually.of_forall htestlow)
    have hleν := integral_mono (BoundedContinuousFunction.integrable (ν : Measure ℝ) (squareTrunc T))
      hν2 (fun x => min_le_left (x ^ 2) (T ^ 2))
    linarith
  have htail : Tendsto (fun T : ℝ => R / T) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hsum : Tendsto (fun T : ℝ => (∫ x : ℝ, x ^ 2 ∂(ν : Measure ℝ)) + R / T)
      atTop (𝓝 (∫ x : ℝ, x ^ 2 ∂(ν : Measure ℝ))) := by
    have hcst : Tendsto (fun _ : ℝ => (∫ x : ℝ, x ^ 2 ∂(ν : Measure ℝ)))
        atTop (𝓝 (∫ x : ℝ, x ^ 2 ∂(ν : Measure ℝ))) := tendsto_const_nhds
    simpa only [add_zero] using hcst.add htail
  have hlower : 1 ≤ (∫ x : ℝ, x ^ 2 ∂(ν : Measure ℝ)) :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hsum
      ((eventually_gt_atTop 0).mono fun T hT => hlowerT T hT)
  exact ⟨(standardizedLaw_iff ν).mpr ⟨hν3, hmean, le_antisymm hupper hlower⟩, hνcap⟩

lemma gap_ge_of_score_ge_half (μ : ProbabilityMeasure ℝ) (h : StandardizedLaw μ)
    (n : ℕ) (hn : 0 < n) (H C : ℝ) (hC : 0 < C)
    (hscore : C / 2 ≤ positiveClosedScore μ n H) :
    C / (2 * Real.sqrt n) ≤ (iidSumProbability μ n : Measure ℝ).real (Iic H) -
      GaussianTools.Phi (H / Real.sqrt n) := by
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  have hp := (le_div_iff₀ (thirdAbsoluteMoment_pos μ h)).mp hscore
  have hρ := mul_le_mul_of_nonneg_left (thirdAbsoluteMoment_ge_one μ h)
    (show 0 ≤ C / 2 by linarith)
  apply (div_le_iff₀ (mul_pos (by norm_num) hs)).mpr
  dsimp [positiveClosedScore] at hp
  change C / 2 * thirdAbsoluteMoment μ ≤ Real.sqrt n *
    ((iidSumProbability μ n : Measure ℝ).real (Iic H) - GaussianTools.Phi (H / Real.sqrt n)) at hp
  nlinarith

/-- Positive score layers have uniformly bounded real thresholds. The
left tail uses the actual sum's second moment; the right tail uses the
actual Gaussian density decay and Mills comparison. -/
theorem exists_uniform_threshold_bound (n : ℕ) (hn : 0 < n) (C : ℝ) (hC : 0 < C) :
    ∃ K : ℝ, 0 < K ∧ ∀ (μ : ProbabilityMeasure ℝ), StandardizedLaw μ → ∀ H : ℝ,
      C / 2 ≤ positiveClosedScore μ n H → H ∈ Icc (-K) K := by
  let δ := C / (2 * Real.sqrt n)
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  have hδ : 0 < δ := div_pos hC (mul_pos (by norm_num) hs)
  let R := 1 + (n : ℝ) / δ
  have hR1 : 1 ≤ R := by dsimp [R]; exact le_add_of_nonneg_right (div_nonneg (Nat.cast_nonneg n) hδ.le)
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one hR1
  have hcancel : δ * ((n : ℝ) / δ) = (n : ℝ) := mul_div_cancel₀ _ hδ.ne'
  have hδR : (n : ℝ) < δ * R := by dsimp [R]; nlinarith
  have hRsq : R ≤ R ^ 2 := by nlinarith [sq_nonneg (R - 1)]
  have hRtail : (n : ℝ) / R ^ 2 < δ :=
    (div_lt_iff₀ (sq_pos_of_pos hR)).mpr (by nlinarith [mul_le_mul_of_nonneg_left hRsq hδ.le])
  obtain ⟨A, hA⟩ := eventually_atTop.mp (GaussianTools.tendsto_phi_atTop.eventually_lt_const hδ)
  let B := max 1 A
  have hB : 1 ≤ B := le_max_left _ _
  have htail : ∀ y : ℝ, B ≤ y → GaussianMills.tail y < δ := by
    intro y hy
    have hy1 : 1 ≤ y := hB.trans hy
    have hypos : 0 < y := lt_of_lt_of_le zero_lt_one hy1
    have hpdf := hA y ((le_max_right _ _).trans hy)
    have hdiv : GaussianTools.phi y / y ≤ GaussianTools.phi y := by
      apply (div_le_iff₀ hypos).mpr
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hy1 (GaussianTools.phi_nonneg y)
    exact lt_of_le_of_lt (le_trans (GaussianMills.tail_le_phi_div y hypos) hdiv) hpdf
  refine ⟨max R (Real.sqrt n * B), lt_of_lt_of_le hR (le_max_left _ _), ?_⟩
  intro μ hμ H hscore
  have hgap := gap_ge_of_score_ge_half μ hμ n hn H C hC hscore
  change δ ≤ _ at hgap
  have hPhi : 0 ≤ GaussianTools.Phi (H / Real.sqrt n) := ENNReal.toReal_nonneg
  have hHlow : -R ≤ H := by
    by_contra hnot
    have hHR : H < -R := lt_of_not_ge hnot
    have hsub : Iic H ⊆ {x : ℝ | R < |x|} := by
      intro x hx
      change x ≤ H at hx
      change R < |x|
      linarith [neg_le_abs x]
    have hF := measureReal_mono (μ := (iidSumProbability μ n : Measure ℝ)) hsub
    have htailμ := ENNReal.toReal_mono ENNReal.ofReal_ne_top (iidSum_measure_abs_gt μ hμ n R hR)
    have htailμ' : (iidSumProbability μ n : Measure ℝ).real {x | R < |x|} ≤ (n : ℝ) / R ^ 2 := by
      simpa only [Measure.real,
        ENNReal.toReal_ofReal (div_nonneg (Nat.cast_nonneg n) (sq_nonneg R))] using htailμ
    linarith
  have hHup : H ≤ Real.sqrt n * B := by
    by_contra hnot
    have hHB : Real.sqrt n * B < H := lt_of_not_ge hnot
    have hy : B ≤ H / Real.sqrt n := (le_div_iff₀ hs).mpr (by nlinarith)
    have hG := htail (H / Real.sqrt n) hy
    have hF : (iidSumProbability μ n : Measure ℝ).real (Iic H) ≤ 1 := measureReal_le_one
    dsimp [GaussianMills.tail] at hG
    linarith
  exact ⟨by linarith [le_max_left R (Real.sqrt n * B)],
    hHup.trans (le_max_right _ _)⟩

lemma thirdAbsoluteMoment_le_of_weak_and_moment_tendsto
    (μ : ℕ → ProbabilityMeasure ℝ) (ν : ProbabilityMeasure ℝ) (r : ℝ) (hr : 0 ≤ r)
    (hμ : ∀ k, StandardizedLaw (μ k))
    (hν : Integrable (fun x : ℝ => |x| ^ 3) (ν : Measure ℝ))
    (hlim : Tendsto μ atTop (𝓝 ν))
    (hρlim : Tendsto (fun k => thirdAbsoluteMoment (μ k)) atTop (𝓝 r)) :
    thirdAbsoluteMoment ν ≤ r := by
  have hn : 0 ≤ (fun x : ℝ => |x| ^ 3) := fun x => pow_nonneg (abs_nonneg x) 3
  have hopens : ∀ G : Set ℝ, IsOpen G →
      (ν : Measure ℝ) G ≤ atTop.liminf (fun k => (μ k : Measure ℝ) G) :=
    fun G hG => ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim hG
  have hfatou : (∫⁻ x : ℝ, ENNReal.ofReal (|x| ^ 3) ∂(ν : Measure ℝ)) ≤
      atTop.liminf (fun k => ∫⁻ x : ℝ, ENNReal.ofReal (|x| ^ 3) ∂(μ k : Measure ℝ)) :=
    lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure
      (continuous_abs.pow 3) hn hopens
  have heq : (fun k => ∫⁻ x : ℝ, ENNReal.ofReal (|x| ^ 3) ∂(μ k : Measure ℝ)) =
      (fun k => ENNReal.ofReal (thirdAbsoluteMoment (μ k))) := by
    funext k
    exact (ofReal_integral_eq_lintegral_ofReal (hμ k).integrable_cube
      (Filter.Eventually.of_forall hn)).symm
  rw [heq] at hfatou
  have hreal : Tendsto (fun k => ENNReal.ofReal (thirdAbsoluteMoment (μ k)))
      atTop (𝓝 (ENNReal.ofReal r)) := by
    simpa only [Function.comp_def] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp hρlim
  rw [hreal.liminf_eq] at hfatou
  rw [← ofReal_integral_eq_lintegral_ofReal hν (Filter.Eventually.of_forall hn)] at hfatou
  exact (ENNReal.ofReal_le_ofReal_iff hr).mp hfatou

/-- The bounded-third-moment maximizing sequences have actual standardized
weak subsequential limits, not merely limits in the larger probability space. -/
theorem exists_standardized_weak_subsequence_of_third_cap
    (μ : ℕ → ProbabilityMeasure ℝ) (R : ℝ) (hμ : ∀ k, StandardizedLaw (μ k))
    (hcap : ∀ k, thirdAbsoluteMoment (μ k) ≤ R) :
    ∃ ν : ProbabilityMeasure ℝ, StandardizedLaw ν ∧ thirdAbsoluteMoment ν ≤ R ∧
      ∃ σ : ℕ → ℕ, StrictMono σ ∧ Tendsto (μ ∘ σ) atTop (𝓝 ν) := by
  obtain ⟨ν, σ, hσ, hlim⟩ := standardized_sequence_has_weak_subsequence μ hμ
  obtain ⟨hν, hνcap⟩ := weakLimit_standardizedLaw_of_third_cap (μ ∘ σ) ν R
    (fun k => hμ (σ k)) (fun k => hcap (σ k)) hlim
  exact ⟨ν, hν, hνcap, σ, hσ, hlim⟩

lemma joint_order_event (ν : ProbabilityMeasure ℝ) (H : ℝ) :
    (ν.prod (diracProba H) : Measure (ℝ × ℝ)).real {z | z.1 ≤ z.2} =
      (ν : Measure ℝ).real (Iic H) := by
  change ((ν : Measure ℝ).prod (Measure.dirac H)).real {z : ℝ × ℝ | z.1 ≤ z.2} = _
  unfold Measure.real
  rw [Measure.prod_dirac, Measure.map_apply (by fun_prop)
    (isClosed_le continuous_fst continuous_snd).measurableSet]
  rfl

/-- Closed-set Portmanteau for a moving real threshold, obtained from
the fixed closed order set in the product with its actual Dirac law. -/
theorem moving_closedCDF_limsup_le (μ : ℕ → ProbabilityMeasure ℝ)
    (ν : ProbabilityMeasure ℝ) (H : ℕ → ℝ) (h : ℝ) (n : ℕ)
    (hμlim : Tendsto μ atTop (𝓝 ν)) (hHlim : Tendsto H atTop (𝓝 h)) :
    atTop.limsup (fun k => (iidSumProbability (μ k) n : Measure ℝ).real (Iic (H k))) ≤
      (iidSumProbability ν n : Measure ℝ).real (Iic h) := by
  let S : Set (ℝ × ℝ) := {z | z.1 ≤ z.2}
  have hS : IsClosed S := isClosed_le continuous_fst continuous_snd
  have hsumlim : Tendsto (fun k => iidSumProbability (μ k) n) atTop (𝓝 (iidSumProbability ν n)) :=
    ((continuous_iidSumProbability n).tendsto ν).comp hμlim
  have hdiraclim : Tendsto (fun k => diracProba (H k)) atTop (𝓝 (diracProba h)) :=
    (continuous_diracProba.tendsto h).comp hHlim
  have hprodlim : Tendsto (fun k => (iidSumProbability (μ k) n).prod (diracProba (H k)))
      atTop (𝓝 ((iidSumProbability ν n).prod (diracProba h))) :=
    (ProbabilityMeasure.continuous_prod.tendsto (iidSumProbability ν n, diracProba h)).comp
      (hsumlim.prodMk_nhds hdiraclim)
  have hENN := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hprodlim hS
  have hb : ∀ᶠ k : ℕ in atTop,
      ((iidSumProbability (μ k) n).prod (diracProba (H k)) : Measure (ℝ × ℝ)) S ≤ (1 : NNReal) :=
    Filter.Eventually.of_forall (fun _ => prob_le_one)
  rw [← ENNReal.ofReal_limsup_toReal hb] at hENN
  have hr := (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mp hENN
  have hr' : atTop.limsup (fun k =>
      ((iidSumProbability (μ k) n).prod (diracProba (H k)) : Measure (ℝ × ℝ)).real S) ≤
      ((iidSumProbability ν n).prod (diracProba h) : Measure (ℝ × ℝ)).real S := by
    simpa only [Measure.real] using hr
  simpa only [S, joint_order_event] using hr'

lemma cdf_eq_score_formula (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (n : ℕ) (hn : 0 < n) (H : ℝ) :
    (iidSumProbability μ n : Measure ℝ).real (Iic H) =
      positiveClosedScore μ n H * thirdAbsoluteMoment μ / Real.sqrt n +
        GaussianTools.Phi (H / Real.sqrt n) := by
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  unfold positiveClosedScore
  field_simp [(thirdAbsoluteMoment_pos μ hμ).ne', hs.ne']
  ring

/-- The actual positive all-law supremum is attained whenever it is
positive. The law, threshold and moment limit are extracted from the
maximizing sequence; no weak-limit or attainment premise is introduced. -/
theorem exists_positive_closed_maximizer (n : ℕ) (hn : 0 < n)
    (hC : 0 < fixedNSup n) :
    ∃ μ : ProbabilityMeasure ℝ, StandardizedLaw μ ∧ ∃ H : ℝ,
      positiveClosedScore μ n H = fixedNSup n := by
  let C := fixedNSup n
  let R := 2 * Real.sqrt n / C
  obtain ⟨μ, H, hμ, hscorelim, hscorelower, hcap⟩ := exists_maximizing_sequence n hC
  obtain ⟨K, hK, hHbound⟩ := exists_uniform_threshold_bound n hn C hC
  let zseq : ℕ → ProbabilityMeasure ℝ × (ℝ × ℝ) :=
    fun k => (μ k, (H k, thirdAbsoluteMoment (μ k)))
  have hcompact : IsCompact (closure standardizedFamily ×ˢ (Icc (-K) K ×ˢ Icc 1 R)) :=
    isCompact_closure_standardizedFamily.prod (isCompact_Icc.prod isCompact_Icc)
  have hmem : ∀ k, zseq k ∈ closure standardizedFamily ×ˢ (Icc (-K) K ×ˢ Icc 1 R) := by
    intro k
    exact ⟨subset_closure (hμ k), hHbound (μ k) (hμ k) (H k) (hscorelower k).le,
      thirdAbsoluteMoment_ge_one (μ k) (hμ k), hcap k⟩
  obtain ⟨z, hz, σ, hσ, hzlim⟩ := hcompact.tendsto_subseq hmem
  have hμlim : Tendsto (fun k => μ (σ k)) atTop (𝓝 z.1) := hzlim.fst_nhds
  have hHlim : Tendsto (fun k => H (σ k)) atTop (𝓝 z.2.1) := hzlim.snd_nhds.fst_nhds
  have hρlim : Tendsto (fun k => thirdAbsoluteMoment (μ (σ k))) atTop (𝓝 z.2.2) := hzlim.snd_nhds.snd_nhds
  obtain ⟨hν, hνcap⟩ := weakLimit_standardizedLaw_of_third_cap (fun k => μ (σ k)) z.1 R
    (fun k => hμ (σ k)) (fun k => hcap (σ k)) hμlim
  have hr : 0 ≤ z.2.2 := le_trans zero_le_one hz.2.2.1
  have hρν := thirdAbsoluteMoment_le_of_weak_and_moment_tendsto
    (fun k => μ (σ k)) z.1 z.2.2 hr (fun k => hμ (σ k)) hν.integrable_cube hμlim hρlim
  have hsclim : Tendsto (fun k => positiveClosedScore (μ (σ k)) n (H (σ k)))
      atTop (𝓝 C) := hscorelim.comp hσ.tendsto_atTop
  have hnumlim : Tendsto (fun k => positiveClosedScore (μ (σ k)) n (H (σ k)) *
      thirdAbsoluteMoment (μ (σ k)) / Real.sqrt n) atTop (𝓝 (C * z.2.2 / Real.sqrt n)) :=
    (hsclim.mul hρlim).div_const (Real.sqrt n)
  have hcPhi : Continuous GaussianTools.Phi :=
    continuous_iff_continuousAt.mpr (fun t => (GaussianTools.hasDerivAt_Phi t).continuousAt)
  have hPhilim : Tendsto (fun k => GaussianTools.Phi (H (σ k) / Real.sqrt n))
      atTop (𝓝 (GaussianTools.Phi (z.2.1 / Real.sqrt n))) :=
    (hcPhi.tendsto (z.2.1 / Real.sqrt n)).comp (hHlim.div_const (Real.sqrt n))
  have hCDFlim : Tendsto (fun k => (iidSumProbability (μ (σ k)) n : Measure ℝ).real (Iic (H (σ k))))
      atTop (𝓝 (C * z.2.2 / Real.sqrt n + GaussianTools.Phi (z.2.1 / Real.sqrt n))) := by
    have heq : (fun k => (iidSumProbability (μ (σ k)) n : Measure ℝ).real (Iic (H (σ k)))) =
        (fun k => positiveClosedScore (μ (σ k)) n (H (σ k)) *
          thirdAbsoluteMoment (μ (σ k)) / Real.sqrt n +
          GaussianTools.Phi (H (σ k) / Real.sqrt n)) :=
      funext (fun k => cdf_eq_score_formula (μ (σ k)) (hμ (σ k)) n hn (H (σ k)))
    rw [heq]
    exact hnumlim.add hPhilim
  have hUSC := moving_closedCDF_limsup_le (fun k => μ (σ k)) z.1 (fun k => H (σ k)) z.2.1 n hμlim hHlim
  rw [hCDFlim.limsup_eq] at hUSC
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  have hProdLower : C * z.2.2 ≤ Real.sqrt n *
      ((iidSumProbability z.1 n : Measure ℝ).real (Iic z.2.1) -
        GaussianTools.Phi (z.2.1 / Real.sqrt n)) := by
    have hd : C * z.2.2 / Real.sqrt n ≤
        (iidSumProbability z.1 n : Measure ℝ).real (Iic z.2.1) -
          GaussianTools.Phi (z.2.1 / Real.sqrt n) := by linarith
    have hh := (div_le_iff₀ hs).mp hd
    nlinarith
  have hglobal := positiveClosedScore_le_fixedNSup z.1 hν n z.2.1
  change Real.sqrt n * ((iidSumProbability z.1 n : Measure ℝ).real (Iic z.2.1) -
    GaussianTools.Phi (z.2.1 / Real.sqrt n)) / thirdAbsoluteMoment z.1 ≤ C at hglobal
  have hProdUpper := (div_le_iff₀ (thirdAbsoluteMoment_pos z.1 hν)).mp hglobal
  have hNoLoss : z.2.2 = thirdAbsoluteMoment z.1 := by
    have hm : C * z.2.2 ≤ C * thirdAbsoluteMoment z.1 := le_trans hProdLower hProdUpper
    exact le_antisymm ((mul_le_mul_iff_of_pos_left hC).mp hm) hρν
  rw [hNoLoss] at hProdLower
  have hattain : positiveClosedScore z.1 n z.2.1 = C := by
    change Real.sqrt n * ((iidSumProbability z.1 n : Measure ℝ).real (Iic z.2.1) -
      GaussianTools.Phi (z.2.1 / Real.sqrt n)) / thirdAbsoluteMoment z.1 = C
    apply (div_eq_iff (thirdAbsoluteMoment_pos z.1 hν).ne').mpr
    nlinarith
  exact ⟨z.1, hν, z.2.1, hattain⟩

lemma normalized_closedCDF (μ : ProbabilityMeasure ℝ) (n : ℕ) (hn : 0 < n) (y : ℝ) :
    (normalizedIidSumLaw μ n).real (Iic y) =
      (iidSumProbability μ n : Measure ℝ).real (Iic (Real.sqrt n * y)) := by
  have hm : (μ : Measure ℝ) = (μ : Measure ℝ).map (fun u : ℝ => (u - 0) / 1) := by simp
  have h := AffineSum.normalizedIidSumLaw_closedCDF μ (μ : Measure ℝ) 0 1
    (by norm_num) hm n hn y
  simpa only [mul_zero, zero_add, one_mul, coe_iidSumProbability] using h

theorem global_upper_fixedNSup (n : ℕ) (hn : 0 < n) (μ : ProbabilityMeasure ℝ)
    (hμ : StandardizedLaw μ) (y : ℝ) :
    (normalizedIidSumLaw μ n).real (Iic y) - GaussianTools.Phi y ≤
      fixedNSup n * thirdAbsoluteMoment μ / Real.sqrt n := by
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  have hscore := positiveClosedScore_le_fixedNSup μ hμ n (Real.sqrt n * y)
  have hphase : (Real.sqrt n * y) / Real.sqrt n = y := by field_simp [hs.ne']
  change Real.sqrt n * ((iidSumProbability μ n : Measure ℝ).real (Iic (Real.sqrt n * y)) -
    GaussianTools.Phi ((Real.sqrt n * y) / Real.sqrt n)) / thirdAbsoluteMoment μ ≤ fixedNSup n at hscore
  rw [hphase] at hscore
  have hp := (div_le_iff₀ (thirdAbsoluteMoment_pos μ hμ)).mp hscore
  rw [normalized_closedCDF μ n hn y]
  apply (le_div_iff₀ hs).mpr
  nlinarith

/-- The attained original supremum supplies the existing contact-variation
record, with its full standardized-law global quantifier. -/
theorem exists_PositiveClosedMaximum (n : ℕ) (hn : 0 < n) (hC : 0 < fixedNSup n) :
    ∃ μ : ProbabilityMeasure ℝ, StandardizedLaw μ ∧ ∃ H : ℝ,
      ContactVariation.PositiveClosedMaximum μ n H (fixedNSup n) := by
  obtain ⟨μ, hμ, H, hattain⟩ := exists_positive_closed_maximizer n hn hC
  refine ⟨μ, hμ, H, ⟨fun ν hν y => global_upper_fixedNSup n hn ν hν y, ?_⟩⟩
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  change Real.sqrt n * ((MixtureSum.iidSumLaw (μ : Measure ℝ) n).real (Iic H) -
    GaussianTools.Phi (H / Real.sqrt n)) / thirdAbsoluteMoment μ = fixedNSup n at hattain
  have hp := (div_eq_iff (thirdAbsoluteMoment_pos μ hμ).ne').mp hattain
  apply (eq_div_iff hs.ne').mpr
  nlinarith

end BerryEsseen.Extremizer

#print axioms BerryEsseen.Extremizer.thirdAbsoluteMoment_ge_one
#print axioms BerryEsseen.Extremizer.fixedNSup_le_sqrt
#print axioms BerryEsseen.Extremizer.continuous_iidSumProbability
#print axioms BerryEsseen.Extremizer.iidSum_moments
#print axioms BerryEsseen.Extremizer.standardized_sequence_has_weak_subsequence
#print axioms BerryEsseen.Extremizer.exists_maximizing_sequence
#print axioms BerryEsseen.Extremizer.weakLimit_integrable_cube_and_cap
#print axioms BerryEsseen.Extremizer.weakLimit_standardizedLaw_of_third_cap
#print axioms BerryEsseen.Extremizer.exists_uniform_threshold_bound
#print axioms BerryEsseen.Extremizer.exists_standardized_weak_subsequence_of_third_cap
#print axioms BerryEsseen.Extremizer.moving_closedCDF_limsup_le
#print axioms BerryEsseen.Extremizer.exists_positive_closed_maximizer
#print axioms BerryEsseen.Extremizer.exists_PositiveClosedMaximum
