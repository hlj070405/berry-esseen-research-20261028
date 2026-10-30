module

public import BerryEsseen.P39CoupledInwardNoise
public import BerryEsseen.P39LeftAllocationReduction
public import BerryEsseen.FactorialReferencePrice
public import BerryEsseen.P39Count11Face

@[expose] public section

/-! 2026-10-31: continuous-domain licenses for the actual count-10,
phase-zero reference parameters. The coupled inward cap and the same
probability/noise coordinates are retained in every identity below. -/

namespace BerryEsseen.P39FactorialTailDomain

open MeasureTheory Set

noncomputable section

set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

def strip : Set ℝ := Icc (39 / 100) (2 / 5)
def noiseStrip : Set ℝ := Icc 0 (1 / 5)
def B : ℝ := 9 / 16
def w : ℝ := 1 / 4
def g (lambda : ℝ) : ℝ := 1 - P39CoupledInwardNoise.d lambda
def V (p lambda : ℝ) : ℝ := 16 * lambda / (26 * (1 - p))
def A (p lambda : ℝ) : ℝ := g lambda * 11 * (1 - p) / (16 * p)
def eta (p lambda : ℝ) : ℝ := BinomialWeights.mass 26 11 p / g lambda
def reference (p lambda : ℝ) : Measure ℝ := TwoMoment.uniformReferenceSumLaw B 26 (V p lambda)
def h (p lambda : ℝ) : ℝ := FactorialReferencePrice.step B (V p lambda)
def D (p lambda : ℝ) : ℝ := A p lambda - w + V p lambda / B
def gap (p lambda : ℝ) : ℝ := 2 * h p lambda - D p lambda

lemma domain {p : ℝ} (hp : p ∈ strip) : 0 < p ∧ p < 1 := by
  constructor <;> linarith only [hp.1, hp.2]

lemma q_bounds {p : ℝ} (hp : p ∈ strip) : (3 / 5 : ℝ) ≤ 1 - p ∧ 1 - p ≤ 61 / 100 := by
  constructor <;> linarith only [hp.1, hp.2]

lemma g_lower {lambda : ℝ} (hl : lambda ∈ noiseStrip) : (586 / 625 : ℝ) ≤ g lambda := by
  unfold g P39CoupledInwardNoise.d
  linarith only [hl.1]

lemma g_pos {lambda : ℝ} (hl : lambda ∈ noiseStrip) : 0 < g lambda := by
  linarith only [g_lower hl]

lemma d_bounds {lambda : ℝ} (hl : lambda ∈ noiseStrip) :
    0 < P39CoupledInwardNoise.d lambda ∧ P39CoupledInwardNoise.d lambda < 1 := by
  unfold P39CoupledInwardNoise.d
  constructor <;> linarith only [hl.1, hl.2]

theorem eta_pos {p lambda : ℝ} (hp : p ∈ strip) (hl : lambda ∈ noiseStrip) : 0 < eta p lambda :=
  div_pos (BinomialWeights.mass_pos 26 11 p (domain hp).1 (domain hp).2 (by norm_num)) (g_pos hl)

theorem eta_nonneg {p lambda : ℝ} (hp : p ∈ strip) (hl : lambda ∈ noiseStrip) :
    0 ≤ eta p lambda := (eta_pos hp hl).le

private def endpointMassQ : ℚ := ((26 : ℕ).choose 11 : ℚ) * (2 / 5) ^ 11 * (3 / 5) ^ 15

private lemma endpoint_mass_gate : endpointMassQ ≤ (163 / 1000 : ℚ) * (586 / 625) := by
  decide +kernel

private lemma endpoint_mass_cast : (endpointMassQ : ℝ) = BinomialWeights.mass 26 11 (2 / 5) := by
  norm_num only [endpointMassQ, BinomialWeights.mass, Nat.reduceSub,
    Rat.cast_mul, Rat.cast_pow, Rat.cast_div, Rat.cast_ofNat, Rat.cast_natCast]

theorem eta_upper {p lambda : ℝ} (hp : p ∈ strip) (hl : lambda ∈ noiseStrip) :
    eta p lambda ≤ (163 / 1000 : ℝ) := by
  have hm := P39Count11Face.mass_monotone 11 (by norm_num) (by norm_num)
    hp (by norm_num [P39Count11Face.strip]) hp.2
  have he := (Rat.cast_le (K := ℝ)).mpr endpoint_mass_gate
  rw [endpoint_mass_cast] at he
  norm_num only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat] at he
  unfold eta
  apply (div_le_iff₀ (g_pos hl)).mpr
  nlinarith only [hm, he, g_lower hl]

theorem eta_mem {p lambda : ℝ} (hp : p ∈ strip) (hl : lambda ∈ noiseStrip) :
    eta p lambda ∈ Icc (0 : ℝ) (163 / 1000) := ⟨eta_nonneg hp hl, eta_upper hp hl⟩

theorem V_nonneg {p lambda : ℝ} (hp : p ∈ strip) (hl : lambda ∈ noiseStrip) : 0 ≤ V p lambda :=
  div_nonneg (mul_nonneg (by norm_num) hl.1)
    (mul_nonneg (by norm_num) (sub_pos.mpr (domain hp).2).le)

theorem V_upper {p lambda : ℝ} (hp : p ∈ strip) (hl : lambda ∈ noiseStrip) :
    V p lambda ≤ (40 / 39 : ℝ) * lambda := by
  unfold V
  apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 26) (sub_pos.mpr (domain hp).2))).mpr
  nlinarith only [mul_nonneg hl.1 (sub_nonneg.mpr hp.2)]

theorem V_lower {p lambda : ℝ} (hp : p ∈ strip) (hl : lambda ∈ noiseStrip) :
    (800 / 793 : ℝ) * lambda ≤ V p lambda := by
  unfold V
  apply (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 26) (sub_pos.mpr (domain hp).2))).mpr
  nlinarith only [mul_nonneg hl.1 (sub_nonneg.mpr hp.1)]

theorem A_lower {p lambda : ℝ} (hp : p ∈ strip) (hl : lambda ∈ noiseStrip) :
    (19338 / 20000 : ℝ) + (2607 / 16000) * lambda ≤ A p lambda := by
  have hr : (33 / 32 : ℝ) ≤ 11 * (1 - p) / (16 * p) := by
    apply (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 16) (domain hp).1)).mpr
    linarith only [hp.2]
  have hm := mul_le_mul_of_nonneg_left hr (g_pos hl).le
  have heq : A p lambda = g lambda * (11 * (1 - p) / (16 * p)) := by unfold A; ring
  rw [heq]
  have hv : g lambda * (33 / 32) = (19338 / 20000 : ℝ) + (2607 / 16000) * lambda := by
    unfold g P39CoupledInwardNoise.d
    ring
  rw [← hv]
  exact hm

theorem variance_shift_lower {p lambda : ℝ} (hp : p ∈ strip) (hl : lambda ∈ noiseStrip) :
    (51200 / 30927 : ℝ) * lambda ≤ (12 / 13) * V p lambda / B := by
  have hv := V_lower hp hl
  unfold B
  nlinarith only [hv]

theorem h_pos {p lambda : ℝ} (hp : p ∈ strip) (hl : lambda ∈ noiseStrip) : 0 < h p lambda :=
  FactorialReferencePrice.step_pos B (V p lambda) (by norm_num [B]) (V_nonneg hp hl)

theorem gap_formula (p lambda : ℝ) :
    gap p lambda = 11 / 8 - A p lambda - (12 / 13) * V p lambda / B := by
  unfold gap h D FactorialReferencePrice.step B w
  ring

theorem gap_formula_q (p lambda : ℝ) :
    gap p lambda = 11 / 8 - A p lambda - (512 / 507) * lambda / (1 - p) := by
  rw [gap_formula]
  unfold V B
  simp only [div_eq_mul_inv, mul_inv_rev]
  norm_num
  ring

theorem gap_upper {p lambda : ℝ} (hp : p ∈ strip) (hl : lambda ∈ noiseStrip) :
    gap p lambda ≤ (4081 / 10000 : ℝ) - (9 / 5) * lambda := by
  rw [gap_formula]
  have hA := A_lower hp hl
  have hV := variance_shift_lower hp hl
  nlinarith only [hA, hV, hl.1]

lemma gap_noise_endpoint_lower {p lambda : ℝ} (hp : p ∈ strip) (hl : lambda ∈ noiseStrip) :
    gap p (1 / 5) ≤ gap p lambda := by
  have hg : g lambda ≤ g (1 / 5) := by
    unfold g P39CoupledInwardNoise.d
    linarith only [hl.2]
  have hA : A p lambda ≤ A p (1 / 5) := by
    unfold A
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hg (by norm_num))
        (sub_pos.mpr (domain hp).2).le) (mul_nonneg (by norm_num) (domain hp).1.le)
  have hlq : lambda / (1 - p) ≤ (1 / 5 : ℝ) / (1 - p) :=
    div_le_div_of_nonneg_right hl.2 (sub_pos.mpr (domain hp).2).le
  have hshift := mul_le_mul_of_nonneg_left hlq (by norm_num : (0 : ℝ) ≤ 512 / 507)
  rw [gap_formula_q, gap_formula_q]
  simp only [mul_div_assoc]
  linarith only [hA, hshift]

/-- A difference factor preserves the shared p and q=1-p. No independent
endpoint substitution is used for the two reciprocal terms. -/
lemma gap_probability_endpoint_lower {p : ℝ} (hp : p ∈ strip) :
    gap (39 / 100) (1 / 5) ≤ gap p (1 / 5) := by
  have hp0 := (domain hp).1.ne'
  have hq0 := (sub_pos.mpr (domain hp).2).ne'
  have heq : gap p (1 / 5) - gap (39 / 100) (1 / 5) =
      (p - 39 / 100) *
        ((26653 / 40000 : ℝ) * (61 / 100) * (1 - p) - (512 / 2535) * (39 / 100) * p) /
          ((39 / 100) * p * (61 / 100) * (1 - p)) := by
    rw [gap_formula_q, gap_formula_q]
    unfold A g P39CoupledInwardNoise.d
    field_simp [hp0, hq0]
    ring
  have hn : (0 : ℝ) ≤
      (26653 / 40000 : ℝ) * (61 / 100) * (1 - p) - (512 / 2535) * (39 / 100) * p := by
    linarith only [hp.2]
  have hden : (0 : ℝ) ≤ (39 / 100) * p * (61 / 100) * (1 - p) := by
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (domain hp).1.le)
      (by norm_num)) (sub_pos.mpr (domain hp).2).le
  have hz := div_nonneg (mul_nonneg (sub_nonneg.mpr hp.1) hn) hden
  rw [← heq] at hz
  linarith only [hz]

theorem gap_endpoint_value : gap (39 / 100) (1 / 5) = (2099431 / 1237080000 : ℝ) := by
  norm_num [gap, h, D, FactorialReferencePrice.step, A, g, P39CoupledInwardNoise.d, V, B, w]

theorem gap_nonneg {p lambda : ℝ} (hp : p ∈ strip) (hl : lambda ∈ noiseStrip) :
    0 ≤ gap p lambda := by
  have h0 := gap_probability_endpoint_lower hp
  have h1 := gap_noise_endpoint_lower hp hl
  rw [gap_endpoint_value] at h0
  linarith only [h0, h1]

theorem D_ge_h {p lambda : ℝ} (hp : p ∈ strip) (hl : lambda ∈ noiseStrip) :
    h p lambda ≤ D p lambda := by
  have hA := A_lower hp hl
  have hV := V_nonneg hp hl
  unfold h D FactorialReferencePrice.step B w
  norm_num [div_eq_mul_inv]
  nlinarith only [hA, hV, hl.1]

theorem scaledThreshold_mem {p lambda : ℝ} (hp : p ∈ strip) (hl : lambda ∈ noiseStrip) :
    FactorialReferencePrice.scaledThreshold B (V p lambda) (A p lambda) w ∈ Icc (1 : ℝ) 2 := by
  change D p lambda / h p lambda ∈ Icc (1 : ℝ) 2
  constructor
  · apply (le_div_iff₀ (h_pos hp hl)).mpr
    simpa only [one_mul] using D_ge_h hp hl
  · apply (div_le_iff₀ (h_pos hp hl)).mpr
    have hz := gap_nonneg hp hl
    unfold gap at hz
    linarith only [hz]

theorem V_eq_leftVariance (p lambda : ℝ) :
    V p lambda = P39LeftAllocationReduction.leftVariance p lambda 10 := by
  unfold V P39LeftAllocationReduction.leftVariance
  norm_num only [Nat.reduceSub, Nat.cast_ofNat]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem reference_eq_leftReference (p lambda : ℝ) :
    reference p lambda = P39LeftAllocationReduction.leftReference p lambda 10 := by
  unfold reference P39LeftAllocationReduction.leftReference
  rw [V_eq_leftVariance]
  rfl

theorem eta_eq_leftEta (p lambda : ℝ) :
    eta p lambda = P39LeftAllocationReduction.eta p (P39CoupledInwardNoise.d lambda) 10 := by
  rfl

/-- The true adjacent mass flux gives the actual count-10 threshold. -/
theorem mass10_div_eta_eq_A {p lambda : ℝ} (hp : p ∈ strip) (hl : lambda ∈ noiseStrip) :
    BinomialWeights.mass 26 10 p / eta p lambda = A p lambda := by
  have hf := BinomialPrefixGate.adjacent_mass_flux 26 10 p (by norm_num)
  norm_num only [Nat.reduceAdd, Nat.reduceSub, Nat.cast_ofNat] at hf
  have hm := BinomialWeights.mass_pos 26 11 p (domain hp).1 (domain hp).2 (by norm_num)
  unfold eta A
  field_simp [hm.ne', (domain hp).1.ne', (g_pos hl).ne']
  nlinarith only [hf]

theorem threshold_eq_A {p lambda : ℝ} (hp : p ∈ strip) (hl : lambda ∈ noiseStrip) :
    P39LeftAllocationReduction.threshold p (P39CoupledInwardNoise.d lambda) 10 = A p lambda := by
  unfold P39LeftAllocationReduction.threshold
  rw [← eta_eq_leftEta]
  exact mass10_div_eta_eq_A hp hl

end

end BerryEsseen.P39FactorialTailDomain

#print axioms BerryEsseen.P39FactorialTailDomain.eta_upper
#print axioms BerryEsseen.P39FactorialTailDomain.V_upper
#print axioms BerryEsseen.P39FactorialTailDomain.V_lower
#print axioms BerryEsseen.P39FactorialTailDomain.A_lower
#print axioms BerryEsseen.P39FactorialTailDomain.gap_probability_endpoint_lower
#print axioms BerryEsseen.P39FactorialTailDomain.gap_nonneg
#print axioms BerryEsseen.P39FactorialTailDomain.gap_upper
#print axioms BerryEsseen.P39FactorialTailDomain.D_ge_h
#print axioms BerryEsseen.P39FactorialTailDomain.scaledThreshold_mem
#print axioms BerryEsseen.P39FactorialTailDomain.reference_eq_leftReference
#print axioms BerryEsseen.P39FactorialTailDomain.mass10_div_eta_eq_A
#print axioms BerryEsseen.P39FactorialTailDomain.threshold_eq_A
