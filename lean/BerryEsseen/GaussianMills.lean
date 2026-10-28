module

public import BerryEsseen.GaussianTools

@[expose] public section

/-! 2026-10-28: Gaussian tail inequalities used in the Peano kernel's
sign argument. The tail and all moments belong to the actual Gaussian CDF.
-/

noncomputable section

open MeasureTheory Set

namespace BerryEsseen.GaussianMills

open GaussianTools

def tail (y : ℝ) : ℝ := 1 - Phi y

lemma tail_nonneg (y : ℝ) : 0 ≤ tail y := by
  rw [tail, ← integral_phi_Ioi]
  exact integral_nonneg fun u => phi_nonneg u

lemma tail_pos (y : ℝ) : 0 < tail y := by
  have hnon := tail_nonneg y
  by_contra hc
  have hz : tail y = 0 := le_antisymm (le_of_not_gt hc) hnon
  have hint : (∫ u in Ioi y, phi u) = 0 := by rw [integral_phi_Ioi]; exact hz
  have hae := (integral_eq_zero_iff_of_nonneg (fun u => phi_nonneg u)
    integrable_phi.integrableOn).mp hint
  have hfirst : (∫ u in Ioi y, u * phi u) = 0 := by
    calc
      _ = ∫ _ : ℝ, (0 : ℝ) ∂(volume.restrict (Ioi y)) :=
        integral_congr_ae (hae.mono fun u hu => by simp [hu])
      _ = 0 := integral_zero _ _
  rw [integral_mul_phi_Ioi] at hfirst
  linarith [phi_pos y]

/-- An integrated square gives the sharp quadratic Mills inequality. -/
theorem tail_quadratic (y : ℝ) :
    phi y ^ 2 ≤ tail y ^ 2 + y * phi y * tail y := by
  let Q := tail y
  let f := phi y
  have h0 : IntegrableOn phi (Ioi y) := integrable_phi.integrableOn
  have h1 : IntegrableOn (fun u : ℝ => u * phi u) (Ioi y) :=
    integrable_mul_phi.integrableOn
  have h2 : IntegrableOn (fun u : ℝ => u ^ 2 * phi u) (Ioi y) :=
    integrable_sq_mul_phi.integrableOn
  have hA : IntegrableOn (fun u : ℝ => Q ^ 2 * (u ^ 2 * phi u)) (Ioi y) :=
    h2.const_mul _
  have hB : IntegrableOn (fun u : ℝ => (2 * Q * f) * (u * phi u)) (Ioi y) :=
    h1.const_mul _
  have hC : IntegrableOn (fun u : ℝ => f ^ 2 * phi u) (Ioi y) := h0.const_mul _
  have hAB : IntegrableOn (fun u : ℝ => Q ^ 2 * (u ^ 2 * phi u) -
      (2 * Q * f) * (u * phi u)) (Ioi y) := hA.sub hB
  have heq : (fun u : ℝ => (Q * u - f) ^ 2 * phi u) =
      (fun u : ℝ => Q ^ 2 * (u ^ 2 * phi u) -
        (2 * Q * f) * (u * phi u) + f ^ 2 * phi u) := by
    funext u
    ring
  have hint : (∫ u in Ioi y, (Q * u - f) ^ 2 * phi u) =
      Q * (Q ^ 2 + y * f * Q - f ^ 2) := by
    rw [heq, integral_add hAB hC, integral_sub hA hB,
      integral_const_mul, integral_const_mul, integral_const_mul,
      integral_sq_mul_phi_Ioi, integral_mul_phi_Ioi, integral_phi_Ioi]
    dsimp [Q, f, tail]
    ring
  have hnon : 0 ≤ Q * (Q ^ 2 + y * f * Q - f ^ 2) := by
    rw [← hint]
    exact integral_nonneg fun u => mul_nonneg (sq_nonneg _) (phi_nonneg u)
  have hQ : 0 < Q := tail_pos y
  have := (mul_nonneg_iff_of_pos_left hQ).mp hnon
  dsimp [Q, f] at this
  linarith

def millsRatio (y : ℝ) : ℝ := tail y / phi y

theorem millsRatio_pos (y : ℝ) : 0 < millsRatio y := div_pos (tail_pos y) (phi_pos y)

theorem millsRatio_quadratic (y : ℝ) :
    1 ≤ millsRatio y ^ 2 + y * millsRatio y := by
  have hp := phi_pos y
  have heq : (millsRatio y ^ 2 + y * millsRatio y - 1) * phi y ^ 2 =
      tail y ^ 2 + y * phi y * tail y - phi y ^ 2 := by
    dsimp [millsRatio]
    field_simp [ne_of_gt hp]
  have hnon : 0 ≤ (millsRatio y ^ 2 + y * millsRatio y - 1) * phi y ^ 2 := by
    rw [heq]
    linarith [tail_quadratic y]
  have hpos : 0 < phi y ^ 2 := sq_pos_of_pos hp
  have := (mul_nonneg_iff_of_pos_right hpos).mp hnon
  linarith

/-- The rational lower bound used for the negative half-line of the kernel. -/
theorem millsRatio_ge_rational (y : ℝ) (hy : 0 ≤ y) :
    (y + 4) / (y + 2) ^ 2 ≤ millsRatio y := by
  let r := (y + 4) / (y + 2) ^ 2
  have hd : 0 < y + 2 := by linarith
  have hr : 0 < r := div_pos (by linarith) (sq_pos_of_pos hd)
  have hpoly : r ^ 2 + y * r ≤ 1 := by
    dsimp [r]
    have heq : ((y + 4) / (y + 2) ^ 2) ^ 2 + y * ((y + 4) / (y + 2) ^ 2) =
        ((y + 4) ^ 2 + y * (y + 4) * (y + 2) ^ 2) / (y + 2) ^ 4 := by
      field_simp [ne_of_gt hd]
    rw [heq]
    apply (div_le_one₀ (pow_pos hd 4)).mpr
    nlinarith [mul_nonneg hy (show 0 ≤ 3 * y + 8 by linarith)]
  have hm := millsRatio_pos y
  have hquad := millsRatio_quadratic y
  by_contra hc
  have hlt : millsRatio y < r := lt_of_not_ge hc
  have hs : millsRatio y ^ 2 < r ^ 2 := (sq_lt_sq₀ hm.le hr.le).mpr hlt
  have hyterm := mul_le_mul_of_nonneg_left (le_of_lt hlt) hy
  linarith

theorem tail_le_phi_div (y : ℝ) (hy : 0 < y) : tail y ≤ phi y / y := by
  have h0 := integrable_phi.integrableOn (s := Ioi y)
  have h1 := integrable_mul_phi.integrableOn (s := Ioi y)
  have hle : (∫ u in Ioi y, y * phi u) ≤ ∫ u in Ioi y, u * phi u := by
    apply integral_mono_ae (h0.const_mul y) h1
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact mul_le_mul_of_nonneg_right (le_of_lt hu) (phi_nonneg u)
  rw [integral_const_mul, integral_phi_Ioi, integral_mul_phi_Ioi] at hle
  apply (le_div_iff₀ hy).mpr
  dsimp [tail]
  nlinarith

theorem phi_neg (y : ℝ) : phi (-y) = phi y := by
  simp only [phi_formula, neg_sq]

theorem Phi_neg (y : ℝ) : Phi (-y) = tail y := by
  let : NullSingletonClass (ProbabilityTheory.gaussianReal 0 1) :=
    ProbabilityTheory.nullSingletonClass_gaussianReal one_ne_zero
  have hmap : (ProbabilityTheory.gaussianReal 0 1).map (fun u : ℝ => -u) =
      ProbabilityTheory.gaussianReal 0 1 := by
    simpa only [neg_zero] using
      (ProbabilityTheory.gaussianReal_map_neg (μ := 0) (v := 1))
  have hset : (fun u : ℝ => -u) ⁻¹' Iic (-y) = Ici y := by
    ext u
    simp
  have heq : (ProbabilityTheory.gaussianReal 0 1).real (Ici y) =
      (ProbabilityTheory.gaussianReal 0 1).real (Ioi y) := by
    exact congrArg ENNReal.toReal (measure_congr Ioi_ae_eq_Ici).symm
  calc
    Phi (-y) = (ProbabilityTheory.gaussianReal 0 1).real (Ici y) := by
      unfold Phi Measure.real
      rw [← hmap, Measure.map_apply (by fun_prop) measurableSet_Iic, hset]
      rw [hmap]
    _ = (ProbabilityTheory.gaussianReal 0 1).real (Ioi y) := heq
    _ = tail y := by
      unfold Measure.real
      rw [ProbabilityTheory.gaussianReal_apply_eq_integral 0 one_ne_zero (Ioi y)]
      change (ENNReal.ofReal (∫ u in Ioi y, phi u)).toReal = tail y
      rw [ENNReal.toReal_ofReal (integral_nonneg fun u => phi_nonneg u)]
      exact integral_phi_Ioi y

/-- This is the division-free Mills comparison needed when the Peano
kernel is evaluated at a nonpositive argument. -/
theorem tail_lower_kernel (x y : ℝ) (hx : 2 ≤ x) (hy : 0 ≤ y) :
    (2 * x + y) * phi y ≤ (x + y) ^ 2 * tail y := by
  have hd : 0 < y + 2 := by linarith
  have hm := millsRatio_ge_rational y hy
  have hbase : (y + 4) * phi y ≤ tail y * (y + 2) ^ 2 :=
    (div_le_div_iff₀ (sq_pos_of_pos hd) (phi_pos y)).mp hm
  have hcompare : (2 * x + y) * (y + 2) ^ 2 ≤ (x + y) ^ 2 * (y + 4) := by
    have hnon : 0 ≤ (x - 2) * (y * (x + 2) + 4 * x) := by
      apply mul_nonneg (by linarith)
      nlinarith [mul_nonneg hy (show 0 ≤ x + 2 by linarith)]
    nlinarith
  apply (mul_le_mul_iff_of_pos_right (sq_pos_of_pos hd)).mp
  calc
    ((2 * x + y) * phi y) * (y + 2) ^ 2 =
        ((2 * x + y) * (y + 2) ^ 2) * phi y := by ring
    _ ≤ ((x + y) ^ 2 * (y + 4)) * phi y :=
      mul_le_mul_of_nonneg_right hcompare (phi_nonneg y)
    _ = (x + y) ^ 2 * ((y + 4) * phi y) := by ring
    _ ≤ (x + y) ^ 2 * (tail y * (y + 2) ^ 2) :=
      mul_le_mul_of_nonneg_left hbase (sq_nonneg _)
    _ = ((x + y) ^ 2 * tail y) * (y + 2) ^ 2 := by ring

end BerryEsseen.GaussianMills

#print axioms BerryEsseen.GaussianMills.tail_quadratic
#print axioms BerryEsseen.GaussianMills.millsRatio_ge_rational
#print axioms BerryEsseen.GaussianMills.tail_le_phi_div
#print axioms BerryEsseen.GaussianMills.Phi_neg
#print axioms BerryEsseen.GaussianMills.tail_lower_kernel
