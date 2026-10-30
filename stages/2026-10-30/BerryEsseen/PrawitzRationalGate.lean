module

public import BerryEsseen.PrawitzRationalKernel
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section

/-! 2026-10-29: explicit integer cross-multiplication gates for the genuine
four-pole Prawitz majorants. Gate evaluation uses integer polynomials and
comparisons only; no fixed-point division is repeated at each table cell.
The real pi lower bound and the open-band kernel qualifications remain
part of the soundness proof, not numerical assumptions. -/

namespace BerryEsseen.PrawitzRationalGate

open Set
open Causalean.Stat.CLT.BerryEsseen

def piNum : ℤ := 314159265358979323846
def piDen : ℤ := 10 ^ 20

lemma pi_lower : (piNum : ℝ) / piDen < Real.pi := by
  convert Real.pi_gt_d20 using 1; norm_num [piNum, piDen]

def d2 (p q : ℤ) : ℤ := 4 * q ^ 2 - p ^ 2
def d3 (p q : ℤ) : ℤ := 9 * q ^ 2 - p ^ 2
def d4 (p q : ℤ) : ℤ := 16 * q ^ 2 - p ^ 2
def tailDen (p q : ℤ) : ℤ := 40 * (d2 p q * d3 p q * d4 p q)
def tailNum (p q : ℤ) : ℤ :=
  40 * q ^ 2 * (d3 p q * d4 p q + d2 p q * d4 p q + d2 p q * d3 p q) +
    9 * (d2 p q * d3 p q * d4 p q)

def kernelNum (p q : ℤ) : ℤ :=
  p ^ 2 * (q ^ 2 * tailDen p q + (q ^ 2 - p ^ 2) * tailNum p q)

def kernelDen (p q : ℤ) : ℤ := q ^ 2 * (q ^ 2 - p ^ 2) * tailDen p q

/-- Common squared-norm gate. reNum/(2q) and (imagNum/imagDen)/L
are the two real majorants, with the proved pi lower bound L. -/
def NormGate (reNum imagNum imagDen q upper cscale : ℤ) : Prop :=
  0 < q ∧ 0 < cscale ∧ 0 ≤ upper ∧ 0 ≤ imagNum ∧ 0 < imagDen ∧
    cscale ^ 2 * (reNum ^ 2 * imagDen ^ 2 * piNum ^ 2 +
      4 * q ^ 2 * imagNum ^ 2 * piDen ^ 2) ≤
      upper ^ 2 * (4 * q ^ 2 * imagDen ^ 2 * piNum ^ 2)

instance (r n d q u s : ℤ) : Decidable (NormGate r n d q u s) := by
  unfold NormGate
  infer_instance

private lemma normGate_sqrt_le {r n d q u s : ℤ} (h : NormGate r n d q u s) :
    Real.sqrt (((r : ℝ) / (2 * q)) ^ 2 +
      (((n : ℝ) / d) / ((piNum : ℝ) / piDen)) ^ 2) ≤ (u : ℝ) / s := by
  obtain ⟨hq, hs, hu, hn, hd, hc⟩ := h
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hN : (0 : ℝ) < piNum := by norm_num [piNum]
  have hD : (0 : ℝ) < piDen := by norm_num [piDen]
  apply (Real.sqrt_le_left (div_nonneg (by exact_mod_cast hu) hsR.le)).mpr
  have heq : ((r : ℝ) / (2 * q)) ^ 2 +
      (((n : ℝ) / d) / ((piNum : ℝ) / piDen)) ^ 2 =
      ((r : ℝ) ^ 2 * d ^ 2 * piNum ^ 2 + 4 * q ^ 2 * n ^ 2 * piDen ^ 2) /
        (4 * q ^ 2 * d ^ 2 * piNum ^ 2) := by
    field_simp [hqR.ne', hdR.ne', hN.ne', hD.ne']
    ring
  rw [heq, div_pow]
  apply (div_le_div_iff₀ (by positivity) (sq_pos_of_pos hsR)).mpr
  have hcR : (s : ℝ) ^ 2 *
      (r ^ 2 * d ^ 2 * piNum ^ 2 + 4 * q ^ 2 * n ^ 2 * piDen ^ 2) ≤
      u ^ 2 * (4 * q ^ 2 * d ^ 2 * piNum ^ 2) := by exact_mod_cast hc
  convert hcR using 1; ring

private lemma poles_pos (p q : ℤ) (hp : 0 ≤ p) (hpq : p < q) (hq : 0 < q) :
    0 < d2 p q ∧ 0 < d3 p q ∧ 0 < d4 p q := by
  have hp2 := (sq_lt_sq₀ hp hq.le).mpr hpq
  have hq2 := sq_pos_of_pos hq
  unfold d2 d3 d4
  constructor
  · nlinarith only [hp2, hq2]
  constructor <;> nlinarith only [hp2, hq2]

private lemma tailDen_pos (p q : ℤ) (hp : 0 ≤ p) (hpq : p < q) (hq : 0 < q) :
    0 < tailDen p q := by
  obtain ⟨h2, h3, h4⟩ := poles_pos p q hp hpq hq
  unfold tailDen
  positivity

private lemma tail_fraction (p q : ℤ) (hp : 0 ≤ p) (hpq : p < q) (hq : 0 < q) :
    PrawitzRationalKernel.tailBound ((p : ℝ) / q) = (tailNum p q : ℝ) / tailDen p q := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  obtain ⟨hd2, hd3, hd4⟩ := poles_pos p q hp hpq hq
  have h2R : (0 : ℝ) < d2 p q := by exact_mod_cast hd2
  have h3R : (0 : ℝ) < d3 p q := by exact_mod_cast hd3
  have h4R : (0 : ℝ) < d4 p q := by exact_mod_cast hd4
  have h2 : 4 - ((p : ℝ) / q) ^ 2 = (d2 p q : ℝ) / (q : ℝ) ^ 2 := by
    unfold d2
    push_cast
    field_simp
  have h3 : 9 - ((p : ℝ) / q) ^ 2 = (d3 p q : ℝ) / (q : ℝ) ^ 2 := by
    unfold d3
    push_cast
    field_simp
  have h4 : 16 - ((p : ℝ) / q) ^ 2 = (d4 p q : ℝ) / (q : ℝ) ^ 2 := by
    unfold d4
    push_cast
    field_simp
  unfold PrawitzRationalKernel.tailBound
  rw [h2, h3, h4]
  simp only [one_div_div]
  unfold tailNum tailDen
  push_cast
  field_simp [h2R.ne', h3R.ne', h4R.ne']

private lemma kernel_fraction (p q : ℤ) (hp : 0 ≤ p) (hpq : p < q) (hq : 0 < q) :
    PrawitzRationalKernel.kernelImagBound ((p : ℝ) / q) =
      ((kernelNum p q : ℝ) / kernelDen p q) / Real.pi := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hgap : (0 : ℝ) < (q : ℝ) ^ 2 - (p : ℝ) ^ 2 := by
    exact_mod_cast sub_pos.mpr ((sq_lt_sq₀ hp hq.le).mpr hpq)
  have hTD : (0 : ℝ) < tailDen p q := by exact_mod_cast tailDen_pos p q hp hpq hq
  have heq : 1 - ((p : ℝ) / q) ^ 2 =
      ((q : ℝ) ^ 2 - (p : ℝ) ^ 2) / (q : ℝ) ^ 2 := by field_simp
  unfold PrawitzRationalKernel.kernelImagBound
  rw [heq, tail_fraction p q hp hpq hq]
  unfold kernelNum kernelDen
  push_cast
  field_simp [hqR.ne', hgap.ne', hTD.ne', Real.pi_ne_zero]

def KernelGate (p q upper cscale : ℤ) : Prop :=
  0 < p ∧ p < q ∧
    NormGate (q - p) (kernelNum (q - p) q) (kernelDen (q - p) q) q upper cscale

instance (p q u s : ℤ) : Decidable (KernelGate p q u s) := by
  unfold KernelGate
  infer_instance

/-- Integer gate for the actual kernel at the rational point p/q.
Both totalized endpoints of the source kernel are excluded. -/
theorem kernel_norm_le {p q upper cscale : ℤ} (h : KernelGate p q upper cscale) :
    ‖prawitzKernel ((p : ℝ) / q)‖ ≤ (upper : ℝ) / cscale := by
  obtain ⟨hp, hpq, hnorm⟩ := h
  obtain ⟨hq, hs, hu, hn, hd, hcross⟩ := hnorm
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hpqR : (p : ℝ) < q := by exact_mod_cast hpq
  have hz : (p : ℝ) / q ∈ Ioo (0 : ℝ) 1 :=
    ⟨div_pos hpR hqR, (div_lt_one hqR).mpr hpqR⟩
  have hw0 : 0 ≤ q - p := by omega
  have hwq : q - p < q := by omega
  have hnum : (0 : ℝ) ≤ kernelNum (q - p) q := by exact_mod_cast hn
  have hden : (0 : ℝ) < kernelDen (q - p) q := by exact_mod_cast hd
  have hL : (0 : ℝ) < (piNum : ℝ) / piDen := by norm_num [piNum, piDen]
  have hformula := kernel_fraction (q - p) q hw0 hwq hq
  have him0 : 0 ≤ PrawitzRationalKernel.kernelImagBound ((q - p : ℤ) / (q : ℝ)) := by
    rw [hformula]
    positivity
  have him : PrawitzRationalKernel.kernelImagBound ((q - p : ℤ) / (q : ℝ)) ≤
      ((kernelNum (q - p) q : ℝ) / kernelDen (q - p) q) / ((piNum : ℝ) / piDen) := by
    rw [hformula]
    exact div_le_div_of_nonneg_left (div_nonneg hnum hden.le) hL pi_lower.le
  have hsq := pow_le_pow_left₀ him0 him 2
  have hreflect : 1 - (p : ℝ) / q = ((q - p : ℤ) : ℝ) / q := by
    push_cast
    field_simp
  have hre : (((q - p : ℤ) : ℝ) / q) / 2 = ((q - p : ℤ) : ℝ) / (2 * q) := by ring
  have hk := PrawitzRationalKernel.kernel_norm_le ((p : ℝ) / q) hz
  rw [hreflect, hre] at hk
  apply hk.trans
  apply le_trans (b := Real.sqrt
    ((((q - p : ℤ) : ℝ) / (2 * q)) ^ 2 +
      (((kernelNum (q - p) q : ℝ) / kernelDen (q - p) q) / ((piNum : ℝ) / piDen)) ^ 2))
  · exact Real.sqrt_le_sqrt (add_le_add le_rfl hsq)
  · exact normGate_sqrt_le ⟨hq, hs, hu, hn, hd, hcross⟩

/-- Four times q² times the exact maximum of z(1-z) on [a/q,b/q]. -/
def maxQuad4 (a b q : ℤ) : ℤ :=
  if 2 * b ≤ q then 4 * b * (q - b)
  else if q ≤ 2 * a then 4 * a * (q - a)
  else q ^ 2

def correctionNum (a b q : ℤ) : ℤ :=
  4 * b * q ^ 2 * tailDen b q + maxQuad4 a b q * (q + b) * tailNum b q

def correctionDen (_a b q : ℤ) : ℤ := 4 * q ^ 2 * (q + b) * tailDen b q

private lemma tail_nonneg (z : ℝ) (hz : 0 ≤ z) (hz1 : z < 1) :
    0 ≤ PrawitzRationalKernel.tailBound z := by
  have hzsq : z ^ 2 < 1 := by
    simpa using (sq_lt_sq₀ hz (show (0 : ℝ) ≤ 1 by norm_num)).mpr hz1
  have h4 : 0 < 4 - z ^ 2 := by linarith only [hzsq]
  have h9 : 0 < 9 - z ^ 2 := by linarith only [hzsq]
  have h16 : 0 < 16 - z ^ 2 := by linarith only [hzsq]
  unfold PrawitzRationalKernel.tailBound
  positivity

private lemma tail_mono (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y < 1) :
    PrawitzRationalKernel.tailBound x ≤ PrawitzRationalKernel.tailBound y := by
  have hy0 := hx.trans hxy
  have hsq := pow_le_pow_left₀ hx hxy 2
  have hysq : y ^ 2 < 1 := by
    simpa using (sq_lt_sq₀ hy0 (show (0 : ℝ) ≤ 1 by norm_num)).mpr hy
  have h4 := one_div_le_one_div_of_le
    (show 0 < 4 - y ^ 2 by linarith only [hysq]) (sub_le_sub_left hsq 4)
  have h9 := one_div_le_one_div_of_le
    (show 0 < 9 - y ^ 2 by linarith only [hysq]) (sub_le_sub_left hsq 9)
  have h16 := one_div_le_one_div_of_le
    (show 0 < 16 - y ^ 2 by linarith only [hysq]) (sub_le_sub_left hsq 16)
  unfold PrawitzRationalKernel.tailBound
  linarith only [h4, h9, h16]

private lemma quadratic_le_max (a b q : ℤ) (hq : 0 < q) (z : ℝ)
    (hz : z ∈ Icc ((a : ℝ) / q) ((b : ℝ) / q)) :
    z * (1 - z) ≤ (maxQuad4 a b q : ℝ) / (4 * (q : ℝ) ^ 2) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  by_cases hleft : 2 * b ≤ q
  · have hhalf : (b : ℝ) / q ≤ 1 / 2 := by
      apply (div_le_iff₀ hqR).mpr
      have hh : 2 * (b : ℝ) ≤ q := by exact_mod_cast hleft
      linarith only [hh]
    have hprod := mul_nonneg (sub_nonneg.mpr hz.2)
      (show 0 ≤ 1 - (b : ℝ) / q - z by linarith only [hhalf, hz.2])
    have hquad : z * (1 - z) ≤ ((b : ℝ) / q) * (1 - (b : ℝ) / q) := by
      nlinarith only [hprod]
    have heq : ((4 * b * (q - b) : ℤ) : ℝ) / (4 * (q : ℝ) ^ 2) =
        ((b : ℝ) / q) * (1 - (b : ℝ) / q) := by
      push_cast
      field_simp
    simpa only [maxQuad4, ite_eq_left hleft, heq] using hquad
  · by_cases hright : q ≤ 2 * a
    · have hhalf : (1 : ℝ) / 2 ≤ (a : ℝ) / q := by
        apply (le_div_iff₀ hqR).mpr
        have hh : (q : ℝ) ≤ 2 * a := by exact_mod_cast hright
        linarith only [hh]
      have hprod := mul_nonneg (sub_nonneg.mpr hz.1)
        (show 0 ≤ z + (a : ℝ) / q - 1 by linarith only [hhalf, hz.1])
      have hquad : z * (1 - z) ≤ ((a : ℝ) / q) * (1 - (a : ℝ) / q) := by
        nlinarith only [hprod]
      have heq : ((4 * a * (q - a) : ℤ) : ℝ) / (4 * (q : ℝ) ^ 2) =
          ((a : ℝ) / q) * (1 - (a : ℝ) / q) := by
        push_cast
        field_simp
      simpa only [maxQuad4, ite_eq_right hleft, ite_eq_left hright, heq] using hquad
    · have hquad : z * (1 - z) ≤ 1 / 4 := by nlinarith only [sq_nonneg (2 * z - 1)]
      have heq : ((q ^ 2 : ℤ) : ℝ) / (4 * (q : ℝ) ^ 2) = 1 / 4 := by
        push_cast
        field_simp
      simpa only [maxQuad4, ite_eq_right hleft, ite_eq_right hright, heq] using hquad

private lemma correction_fraction (a b q : ℤ) (hb : 0 ≤ b) (hbq : b < q) (hq : 0 < q) :
    (b : ℝ) / (q + b) +
      ((maxQuad4 a b q : ℝ) / (4 * (q : ℝ) ^ 2)) *
        PrawitzRationalKernel.tailBound ((b : ℝ) / q) =
      (correctionNum a b q : ℝ) / correctionDen a b q := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hbR : (0 : ℝ) ≤ b := by exact_mod_cast hb
  have hplus : (0 : ℝ) < q + b := by linarith only [hqR, hbR]
  have hTD : (0 : ℝ) < tailDen b q := by exact_mod_cast tailDen_pos b q hb hbq hq
  rw [tail_fraction b q hb hbq hq]
  unfold correctionNum correctionDen
  push_cast
  field_simp [hqR.ne', hplus.ne', hTD.ne']

def CorrectionGate (a b q upper cscale : ℤ) : Prop :=
  0 ≤ a ∧ a ≤ b ∧ b < q ∧
    NormGate (q - a) (correctionNum a b q) (correctionDen a b q) q upper cscale

instance (a b q u s : ℤ) : Decidable (CorrectionGate a b q u s) := by
  unfold CorrectionGate
  infer_instance

/-- One integer gate controls the actual principal correction throughout
the whole interval. The source kernel is still used only at 0<z<1. -/
theorem correction_norm_le {a b q upper cscale : ℤ}
    (h : CorrectionGate a b q upper cscale) {z : ℝ} (hz : z ∈ Ioo (0 : ℝ) 1)
    (hcell : z ∈ Icc ((a : ℝ) / q) ((b : ℝ) / q)) :
    ‖prawitzKernel z - Complex.I / ((2 * Real.pi * z : ℝ) : ℂ)‖ ≤
      (upper : ℝ) / cscale := by
  obtain ⟨ha, hab, hbq, hnorm⟩ := h
  obtain ⟨hq, hs, hu, hn, hd, hcross⟩ := hnorm
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hb : 0 ≤ b := ha.trans hab
  have hbR : (0 : ℝ) ≤ b := by exact_mod_cast hb
  have hbr0 : 0 ≤ (b : ℝ) / q := div_nonneg hbR hqR.le
  have hbr1 : (b : ℝ) / q < 1 := (div_lt_one hqR).mpr (by exact_mod_cast hbq)
  have hplus : (0 : ℝ) < q + b := by linarith only [hqR, hbR]
  have hfirst : z / (1 + z) ≤ (b : ℝ) / (q + b) := by
    apply (div_le_div_iff₀ (by linarith only [hz.1]) hplus).mpr
    have hh := (le_div_iff₀ hqR).mp hcell.2
    nlinarith only [hh]
  have hquad := quadratic_le_max a b q hq z hcell
  have hzquad : 0 ≤ z * (1 - z) := mul_nonneg hz.1.le (sub_nonneg.mpr hz.2.le)
  have hM := hzquad.trans hquad
  have hT := tail_mono z ((b : ℝ) / q) hz.1.le hcell.2 hbr1
  have hT0 := tail_nonneg z hz.1.le hz.2
  have hbar : z / (1 + z) + z * (1 - z) * PrawitzRationalKernel.tailBound z ≤
      (b : ℝ) / (q + b) + ((maxQuad4 a b q : ℝ) / (4 * (q : ℝ) ^ 2)) *
        PrawitzRationalKernel.tailBound ((b : ℝ) / q) :=
    add_le_add hfirst (mul_le_mul hquad hT hT0 hM)
  have hbar0 : 0 ≤ z / (1 + z) + z * (1 - z) * PrawitzRationalKernel.tailBound z := by
    exact add_nonneg (div_nonneg hz.1.le (by linarith only [hz.1])) (mul_nonneg hzquad hT0)
  have hfrac := correction_fraction a b q hb hbq hq
  rw [hfrac] at hbar
  have hfrac0 := hbar0.trans hbar
  have hAeq : PrawitzRationalKernel.correctionImagBound z =
      (z / (1 + z) + z * (1 - z) * PrawitzRationalKernel.tailBound z) / Real.pi := by
    unfold PrawitzRationalKernel.correctionImagBound
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hL : (0 : ℝ) < (piNum : ℝ) / piDen := by norm_num [piNum, piDen]
  have hA : PrawitzRationalKernel.correctionImagBound z ≤
      ((correctionNum a b q : ℝ) / correctionDen a b q) / ((piNum : ℝ) / piDen) := by
    rw [hAeq]
    exact (div_le_div_of_nonneg_right hbar Real.pi_pos.le).trans
      (div_le_div_of_nonneg_left hfrac0 hL pi_lower.le)
  have hA0 : 0 ≤ PrawitzRationalKernel.correctionImagBound z := by
    rw [hAeq]
    exact div_nonneg hbar0 Real.pi_pos.le
  have hAsq := pow_le_pow_left₀ hA0 hA 2
  have hre : (1 - z) / 2 ≤ ((q - a : ℤ) : ℝ) / (2 * q) := by
    have heq : ((q - a : ℤ) : ℝ) / (2 * q) = (1 - (a : ℝ) / q) / 2 := by
      push_cast
      field_simp
    rw [heq]
    linarith only [hcell.1]
  have hresq := pow_le_pow_left₀ (show 0 ≤ (1 - z) / 2 by linarith only [hz.2]) hre 2
  apply (PrawitzRationalKernel.principal_correction_norm_le z hz).trans
  apply le_trans (b := Real.sqrt
    ((((q - a : ℤ) : ℝ) / (2 * q)) ^ 2 +
      (((correctionNum a b q : ℝ) / correctionDen a b q) / ((piNum : ℝ) / piDen)) ^ 2))
  · exact Real.sqrt_le_sqrt (add_le_add hresq hAsq)
  · exact normGate_sqrt_le ⟨hq, hs, hu, hn, hd, hcross⟩

/-- The rational gate and the existing half bound concern the same
actual principal norm, so their minimum is valid on the same whole cell. -/
theorem correction_norm_le_min_half {a b q upper cscale : ℤ}
    (h : CorrectionGate a b q upper cscale) {z : ℝ} (hz : z ∈ Ioo (0 : ℝ) 1)
    (hcell : z ∈ Icc ((a : ℝ) / q) ((b : ℝ) / q)) :
    ‖prawitzKernel z - Complex.I / ((2 * Real.pi * z : ℝ) : ℂ)‖ ≤
      min ((upper : ℝ) / cscale) (1 / 2) := by
  apply le_min (correction_norm_le h hz hcell)
  exact prawitzKernel_principal_correction_norm_le z
    (by simpa only [abs_of_pos hz.1] using hz.1)
    (by simpa only [abs_of_pos hz.1] using hz.2.le)

end BerryEsseen.PrawitzRationalGate

#print axioms BerryEsseen.PrawitzRationalGate.kernel_norm_le
#print axioms BerryEsseen.PrawitzRationalGate.correction_norm_le
#print axioms BerryEsseen.PrawitzRationalGate.correction_norm_le_min_half
