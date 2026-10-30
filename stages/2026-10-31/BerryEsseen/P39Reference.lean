module

public import LeanCert.Core.IntervalRat.Transcendental
public import BerryEsseen.ConditionalResidual
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp

@[expose] public section

/-! 2026-10-28: Actual N26/B0/P39 first-box Bernoulli moment floor helper.
The continuous interval prices are linked below to the original standardized
law when its actual canonical noise vanishes. Positive noise and whole-profile
closure are separate statements.
All finite checks use `decide +kernel`, without a native fallback. -/

open LeanCert.Core MeasureTheory

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace BerryEsseen.P39Reference

noncomputable def v (p : ℝ) : ℝ := p * (1 - p)
noncomputable def rho0 (p : ℝ) : ℝ := (1 - 2 * v p) / Real.sqrt (v p)
noncomputable def e1 (p : ℝ) : ℝ :=
  -(1 - 2 * p) * (v p + 1 / 2) / (v p * Real.sqrt (v p))
noncomputable def e2 (p : ℝ) : ℝ :=
  2 * (v p + 1 / 2) / (v p * Real.sqrt (v p)) +
  (1 - 2 * p) ^ 2 * (v p / 2 + 3 / 4) / ((v p) ^ 2 * Real.sqrt (v p))

lemma v_pos {p : ℝ} (h0 : 0 < p) (h1 : p < 1) : 0 < v p :=
  mul_pos h0 (sub_pos.mpr h1)

theorem hasDerivAt_v (p : ℝ) : HasDerivAt v (1 - 2 * p) p := by
  convert (hasDerivAt_id p).mul ((hasDerivAt_const p 1).sub (hasDerivAt_id p)) using 1
  · funext x
    rfl
  · simp only [Pi.sub_apply, id_eq]
    ring

theorem hasDerivAt_rho0 {p : ℝ} (h0 : 0 < p) (h1 : p < 1) :
    HasDerivAt rho0 (e1 p) p := by
  have hv := v_pos h0 h1
  have hs := Real.sqrt_pos.mpr hv
  have hd := ((hasDerivAt_const p 1).sub ((hasDerivAt_v p).const_mul 2)).div
    ((hasDerivAt_v p).sqrt hv.ne') hs.ne'
  convert hd using 1
  · funext x
    rfl
  · simp only [e1, Pi.sub_apply]
    generalize hz : Real.sqrt (v p) = s
    have hs0 : s ≠ 0 := by simpa [hz] using hs.ne'
    have hsq : s ^ 2 = v p := by rw [← hz, Real.sq_sqrt hv.le]
    rw [← hsq]
    field_simp [hs0]
    ring

theorem hasDerivAt_e1 {p : ℝ} (h0 : 0 < p) (h1 : p < 1) :
    HasDerivAt e1 (e2 p) p := by
  have hv := v_pos h0 h1
  have hs := Real.sqrt_pos.mpr hv
  have hq := (hasDerivAt_const p 1).sub ((hasDerivAt_id p).const_mul 2)
  have hd := (hq.neg.mul ((hasDerivAt_v p).add_const (1 / 2))).div
    ((hasDerivAt_v p).mul ((hasDerivAt_v p).sqrt hv.ne')) (mul_ne_zero hv.ne' hs.ne')
  convert hd using 1
  · funext x
    rfl
  · simp only [e2, Pi.sub_apply, Pi.mul_apply, Pi.neg_apply, id_eq]
    generalize hz : Real.sqrt (v p) = s
    have hs0 : s ≠ 0 := by simpa [hz] using hs.ne'
    have hsq : s ^ 2 = v p := by rw [← hz, Real.sq_sqrt hv.le]
    rw [← hsq]
    field_simp [hs0]
    ring

theorem deriv_rho0 {p : ℝ} (h0 : 0 < p) (h1 : p < 1) :
    deriv rho0 p = e1 p := (hasDerivAt_rho0 h0 h1).deriv

theorem hasDerivAt_deriv_rho0 {p : ℝ} (h0 : 0 < p) (h1 : p < 1) :
    HasDerivAt (deriv rho0) (e2 p) p := by
  apply (hasDerivAt_e1 h0 h1).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds ⟨h0, h1⟩] with q hq
  exact deriv_rho0 hq.1 hq.2

def constI (q : ℚ) : IntervalRat := IntervalRat.singleton q
def pI : IntervalRat := ⟨39 / 100, 2 / 5, by norm_num⟩
def vI (I : IntervalRat) : IntervalRat := I.mul ((constI 1).sub I)
def sI (I : IntervalRat) : IntervalRat := (vI I).sqrtIntervalTightPrec 80
def d1I (I : IntervalRat) : IntervalRat := (vI I).mul (sI I)
def d2I (I : IntervalRat) : IntervalRat := ((vI I).mul (vI I)).mul (sI I)

def posInv (I : IntervalRat) (h : 0 < I.lo) : IntervalRat :=
  IntervalRat.invNonzero {
    toIntervalRat := I
    nonzero := by
      intro hz
      exact (not_le_of_gt h) hz.1 }

lemma mem_posInv {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (h : 0 < I.lo) :
    x⁻¹ ∈ posInv I h := by
  have hp : (0 : ℝ) < I.lo := by exact_mod_cast h
  have hx0 : x ≠ 0 := (hp.trans_le hx.1).ne'
  exact IntervalRat.mem_invNonzero hx hx0

def e1I : IntervalRat :=
  (((constI 1).sub ((constI 2).mul pI)).neg.mul
    ((vI pI).add (constI (1 / 2)))).mul
    (posInv (d1I pI) (by decide +kernel))

def e2I : IntervalRat :=
  (((constI 2).mul ((vI pI).add (constI (1 / 2)))).mul
    (posInv (d1I pI) (by decide +kernel))).add
  (((((constI 1).sub ((constI 2).mul pI)).mul
      ((constI 1).sub ((constI 2).mul pI))).mul
      (((vI pI).mul (constI (1 / 2))).add (constI (3 / 4)))).mul
    (posInv (d2I pI) (by decide +kernel)))

lemma mem_constI (q : ℚ) : (q : ℝ) ∈ constI q := IntervalRat.mem_singleton q

lemma mem_one : (1 : ℝ) ∈ constI 1 := by simpa using mem_constI 1
lemma mem_two : (2 : ℝ) ∈ constI 2 := by simpa using mem_constI 2
lemma mem_half : (1 / 2 : ℝ) ∈ constI (1 / 2) := by simpa using mem_constI (1 / 2)
lemma mem_three_quarters : (3 / 4 : ℝ) ∈ constI (3 / 4) := by
  simpa using mem_constI (3 / 4)

lemma mem_vI {p : ℝ} {I : IntervalRat} (hp : p ∈ I) : v p ∈ vI I := by
  exact IntervalRat.mem_mul hp (IntervalRat.mem_sub mem_one hp)

lemma mem_sI {p : ℝ} {I : IntervalRat} (hp : p ∈ I) : Real.sqrt (v p) ∈ sI I :=
  IntervalRat.mem_sqrtIntervalTightPrec' (mem_vI hp) 80

lemma mem_d1I {p : ℝ} {I : IntervalRat} (hp : p ∈ I) :
    v p * Real.sqrt (v p) ∈ d1I I := IntervalRat.mem_mul (mem_vI hp) (mem_sI hp)

lemma mem_d2I {p : ℝ} {I : IntervalRat} (hp : p ∈ I) :
    (v p) ^ 2 * Real.sqrt (v p) ∈ d2I I := by
  simpa only [pow_two, d2I] using IntervalRat.mem_mul
    (IntervalRat.mem_mul (mem_vI hp) (mem_vI hp)) (mem_sI hp)

theorem e1_mem {p : ℝ} (hp : p ∈ pI) : e1 p ∈ e1I := by
  have hq := IntervalRat.mem_sub mem_one (IntervalRat.mem_mul mem_two hp)
  have hv := IntervalRat.mem_add (mem_vI hp) mem_half
  have h := IntervalRat.mem_mul (IntervalRat.mem_mul (IntervalRat.mem_neg hq) hv)
    (mem_posInv (mem_d1I hp) (by decide +kernel))
  simpa [e1, div_eq_mul_inv, e1I] using h

theorem e2_mem {p : ℝ} (hp : p ∈ pI) : e2 p ∈ e2I := by
  have hq := IntervalRat.mem_sub mem_one (IntervalRat.mem_mul mem_two hp)
  have hv := IntervalRat.mem_add (mem_vI hp) mem_half
  have ha := IntervalRat.mem_mul (IntervalRat.mem_mul mem_two hv)
    (mem_posInv (mem_d1I hp) (by decide +kernel))
  have hb := IntervalRat.mem_mul
    (IntervalRat.mem_mul (IntervalRat.mem_mul hq hq)
      (IntervalRat.mem_add (IntervalRat.mem_mul (mem_vI hp) mem_half)
        mem_three_quarters))
    (mem_posInv (mem_d2I hp) (by decide +kernel))
  simpa [e2, e2I, div_eq_mul_inv, pow_two] using IntervalRat.mem_add ha hb

theorem e1_bounds {p : ℝ} (hp : p ∈ Set.Icc (39 / 100 : ℝ) (2 / 5)) :
    -(3 / 2 : ℝ) ≤ e1 p ∧ e1 p ≤ -(6 / 5 : ℝ) := by
  have hi : p ∈ pI := by simpa [IntervalRat.mem_def, pI] using hp
  have hlo : (-(3 / 2 : ℚ)) ≤ e1I.lo := by decide +kernel
  have hhi : e1I.hi ≤ (-(6 / 5 : ℚ)) := by decide +kernel
  have hlo' := (Rat.cast_le (K := ℝ) (p := -(3 / 2 : ℚ)) (q := e1I.lo)).mpr hlo
  have hhi' := (Rat.cast_le (K := ℝ) (p := e1I.hi) (q := -(6 / 5 : ℚ))).mpr hhi
  norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_ofNat] at hlo' hhi'
  exact ⟨hlo'.trans (e1_mem hi).1, (e1_mem hi).2.trans hhi'⟩

theorem e2_bounds {p : ℝ} (hp : p ∈ Set.Icc (39 / 100 : ℝ) (2 / 5)) :
    (13 : ℝ) ≤ e2 p ∧ e2 p ≤ 15 := by
  have hi : p ∈ pI := by simpa [IntervalRat.mem_def, pI] using hp
  have hlo : (13 : ℚ) ≤ e2I.lo := by decide +kernel
  have hhi : e2I.hi ≤ (15 : ℚ) := by decide +kernel
  have hlo' : (13 : ℝ) ≤ (e2I.lo : ℝ) := by exact_mod_cast hlo
  have hhi' : (e2I.hi : ℝ) ≤ (15 : ℝ) := by exact_mod_cast hhi
  exact ⟨hlo'.trans (e2_mem hi).1, (e2_mem hi).2.trans hhi'⟩

def endpointI : IntervalRat :=
  ((constI 1).sub ((constI 2).mul (vI (constI (2 / 5))))).mul
    (posInv (sI (constI (2 / 5))) (by decide +kernel))

theorem endpoint_mem : rho0 (2 / 5) ∈ endpointI := by
  have hp : (2 / 5 : ℝ) ∈ constI (2 / 5) := by
    simpa using mem_constI (2 / 5)
  have h := IntervalRat.mem_mul
    (IntervalRat.mem_sub mem_one (IntervalRat.mem_mul mem_two (mem_vI hp)))
    (mem_posInv (mem_sI hp) (by decide +kernel))
  simpa [rho0, endpointI, div_eq_mul_inv] using h

theorem endpoint_floor : (530722777603 / 500000000000 : ℝ) ≤ rho0 (2 / 5) := by
  have h : (530722777603 / 500000000000 : ℚ) ≤ endpointI.lo := by decide +kernel
  have h' : (((530722777603 / 500000000000 : ℚ)) : ℝ) ≤ (endpointI.lo : ℝ) :=
    Rat.cast_le.mpr h
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h'
  exact h'.trans endpoint_mem.1

lemma positive_domain {p : ℝ} (hp : p ∈ Set.Icc (39 / 100 : ℝ) (2 / 5)) :
    0 < p ∧ p < 1 := by
  constructor <;> linarith [hp.1, hp.2]

theorem rho0_antitone : AntitoneOn rho0 (Set.Icc (39 / 100 : ℝ) (2 / 5)) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
  · intro p hp
    exact (hasDerivAt_rho0 (positive_domain hp).1 (positive_domain hp).2).continuousAt.continuousWithinAt
  · intro p hp
    have hd := positive_domain (interior_subset hp)
    exact (hasDerivAt_rho0 hd.1 hd.2).differentiableAt.differentiableWithinAt
  · intro p hp
    have hi := interior_subset hp
    rw [(hasDerivAt_rho0 (positive_domain hi).1 (positive_domain hi).2).deriv]
    linarith [(e1_bounds hi).2]

theorem rho0_floor {p : ℝ} (hp : p ∈ Set.Icc (39 / 100 : ℝ) (2 / 5)) :
    (530722777603 / 500000000000 : ℝ) ≤ rho0 p := by
  exact endpoint_floor.trans (rho0_antitone hp (by norm_num) hp.2)

/-- At zero actual canonical noise, this is the original law's actual third
absolute moment, with its own canonical positive weight. -/
theorem thirdAbsoluteMoment_eq_rho0_of_zero_noise
    (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (hs : CanonicalSign.noiseVariance μ hμ = 0) :
    thirdAbsoluteMoment μ = rho0 (CanonicalSign.p μ) := by
  have hv := v_pos (CanonicalSign.p_pos μ hμ) (CanonicalSign.p_lt_one μ hμ)
  calc
    thirdAbsoluteMoment μ =
        (v (CanonicalSign.p μ) * (1 - 2 * v (CanonicalSign.p μ))) /
          (Real.sqrt (v (CanonicalSign.p μ))) ^ 3 := by
      simpa only [v, CanonicalSign.q] using
        ConditionalResidual.canonical_zero_noise_thirdMoment μ hμ hs
    _ = rho0 (CanonicalSign.p μ) := by
      unfold rho0
      rw [pow_succ, Real.sq_sqrt hv.le]
      field_simp [hv.ne', (Real.sqrt_pos.mpr hv).ne'] <;> ring

/-- The original law inherits the certified P39 floor on the zero-noise boundary. -/
theorem thirdAbsoluteMoment_floor_of_zero_noise
    (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ)
    (hs : CanonicalSign.noiseVariance μ hμ = 0)
    (hp : CanonicalSign.p μ ∈ Set.Icc (39 / 100 : ℝ) (2 / 5)) :
    (530722777603 / 500000000000 : ℝ) ≤ thirdAbsoluteMoment μ := by
  rw [thirdAbsoluteMoment_eq_rho0_of_zero_noise μ hμ hs]
  exact rho0_floor hp

#print axioms hasDerivAt_rho0
#print axioms hasDerivAt_e1
#print axioms hasDerivAt_deriv_rho0
#print axioms e1_bounds
#print axioms e2_bounds
#print axioms endpoint_floor
#print axioms rho0_floor
#print axioms thirdAbsoluteMoment_eq_rho0_of_zero_noise
#print axioms thirdAbsoluteMoment_floor_of_zero_noise

end BerryEsseen.P39Reference
