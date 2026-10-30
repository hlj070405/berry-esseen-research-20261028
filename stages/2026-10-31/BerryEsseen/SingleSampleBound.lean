module

public import BerryEsseen.SingleSampleMajorant
public import BerryEsseen.GaussianPrices
public import BerryEsseen.GlobalReduction

@[expose] public section

/-! The unconditional one-sample Berry--Esseen bound for every real
standardized law with finite third absolute moment. Analytic moment
majorants and Gaussian comparisons replace the old finite table. -/

namespace BerryEsseen.SingleSampleBound

open MeasureTheory Set Filter
open GaussianTools GaussianPrices GaussianMills SingleSampleMajorant
open scoped Topology

noncomputable section

theorem Phi_mono : Monotone Phi := fun _ _ hab => measureReal_mono (Iic_subset_Iic.mpr hab)

theorem phi_le_two_fifths (y : ℝ) : phi y ≤ (2 : ℝ) / 5 := by
  have hexp : Real.exp (-(y ^ 2 / 2)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg y])
  rw [phi_eq_phi_zero_mul_exp]
  have hmul : phi 0 * Real.exp (-(y ^ 2 / 2)) ≤ phi 0 := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hexp (phi_nonneg 0)
  exact hmul.trans phi_zero_lt_2_5.le

theorem Phi_lower_nonpos (b : ℝ) (hb : b ≤ 0) :
    (1 : ℝ) / 2 + (2 : ℝ) / 5 * b ≤ Phi b := by
  have hd : ∀ y, HasDerivAt (fun x : ℝ => Phi x - (2 : ℝ) / 5 * x)
      (phi y - (2 : ℝ) / 5) y := by
    intro y
    convert (hasDerivAt_Phi y).fun_sub ((hasDerivAt_id' y).const_mul ((2 : ℝ) / 5)) using 1
    ring
  have hm := antitone_of_hasDerivAt_nonpos hd (fun y => sub_nonpos.mpr (phi_le_two_fifths y))
  have h := hm hb
  change Phi 0 - (2 : ℝ) / 5 * 0 ≤ Phi b - (2 : ℝ) / 5 * b at h
  rw [Phi_zero] at h
  linarith

/-- One quartic integration supplies the only negative Gaussian point price. -/
theorem Phi_neg_four_fifths_lower : (98839 : ℝ) / 468750 ≤ Phi (-4 / 5) := by
  let P : ℝ → ℝ := fun u => (2 : ℝ) / 5 * (1 - u ^ 2 / 2 + u ^ 4 / 8)
  have hc : Continuous P := by unfold P; fun_prop
  have hd : ∀ u, HasDerivAt (fun v : ℝ => (2 : ℝ) / 5 * (v - v ^ 3 / 6 + v ^ 5 / 40))
      (P u) u := by
    intro u
    convert (((hasDerivAt_id' u).fun_sub (((hasDerivAt_id' u).fun_pow 3).div_const 6)).fun_add
      (((hasDerivAt_id' u).fun_pow 5).div_const 40)).const_mul ((2 : ℝ) / 5) using 1
    unfold P
    ring
  have hInt : (∫ u in (0 : ℝ)..(4 / 5 : ℝ), P u) = (135536 : ℝ) / 468750 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u)
      (hc.intervalIntegrable 0 (4 / 5))]
    norm_num
  have hi := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0 : ℝ) ≤ 4 / 5)
    (continuous_phi.intervalIntegrable 0 (4 / 5)) (hc.intervalIntegrable 0 (4 / 5))
    (fun u _ => phi_le_quartic u)
  change (∫ u in (0 : ℝ)..(4 / 5 : ℝ), phi u) ≤ ∫ u in (0 : ℝ)..(4 / 5 : ℝ), P u at hi
  rw [hInt] at hi
  have hp := Phi_eq_const_add_intervalIntegral (4 / 5 : ℝ)
  rw [Phi_zero] at hp
  have hn := Phi_neg (4 / 5 : ℝ)
  unfold tail at hn
  have heq : (-(4 / 5 : ℝ)) = (-4 / 5 : ℝ) := by ring
  rw [heq] at hn
  linarith only [hi, hp, hn]

theorem Phi_neg_four_fifths_ge : (843 : ℝ) / 4000 ≤ Phi (-4 / 5) :=
  (by norm_num : (843 : ℝ) / 4000 ≤ 98839 / 468750).trans Phi_neg_four_fifths_lower

theorem phi_le_three_tenths (a : ℝ) (ha : (4 : ℝ) / 5 ≤ a) : phi a ≤ (3 : ℝ) / 10 := by
  have ha0 : 0 ≤ a := by linarith
  have hs : ((4 : ℝ) / 5) ^ 2 ≤ a ^ 2 := (sq_le_sq₀ (by norm_num) ha0).mpr ha
  have hmono : phi a ≤ phi (4 / 5) := by
    rw [phi_eq_phi_zero_mul_exp a, phi_eq_phi_zero_mul_exp (4 / 5)]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith only [hs])) (phi_nonneg 0)
  have hquartic := phi_le_quartic (4 / 5 : ℝ)
  norm_num at hquartic
  linarith

def cantelliGap (a : ℝ) : ℝ := 1 / (1 + a ^ 2) - Phi (-a)

theorem hasDerivAt_cantelliGap (a : ℝ) :
    HasDerivAt cantelliGap (phi a - 2 * a / (1 + a ^ 2) ^ 2) a := by
  have hden : HasDerivAt (fun x : ℝ => 1 + x ^ 2) (2 * a) a := by
    convert ((hasDerivAt_id' a).fun_pow 2).const_add 1 using 1
    ring
  have hinv := (hasDerivAt_const a (1 : ℝ)).fun_div hden
    (show (1 + a ^ 2 : ℝ) ≠ 0 by positivity)
  have hPhi : HasDerivAt (fun x : ℝ => Phi (-x)) (-phi (-a)) a := by
    convert (hasDerivAt_Phi (-a)).comp a (hasDerivAt_id' a).fun_neg using 1
    · funext x; rfl
    · ring
  unfold cantelliGap
  convert hinv.fun_sub hPhi using 1
  rw [phi_neg]
  ring

theorem cantelli_density_lower (a : ℝ) (ha : (4 : ℝ) / 5 ≤ a) (ha1 : a ≤ (5 : ℝ) / 4) :
    (3 : ℝ) / 10 ≤ 2 * a / (1 + a ^ 2) ^ 2 := by
  have ha0 : 0 ≤ a := by linarith
  have hs : a ^ 2 ≤ ((5 : ℝ) / 4) ^ 2 := (sq_le_sq₀ ha0 (by norm_num)).mpr ha1
  have h1 : 0 ≤ (25 : ℝ) / 16 - a ^ 2 := by nlinarith only [hs]
  have h2 : 0 ≤ a - (4 : ℝ) / 5 := by linarith
  have h3 : 0 ≤ (5 : ℝ) / 4 - a := by linarith
  have hid : 20 * a - 3 * (1 + a ^ 2) ^ 2 =
      3 * a ^ 2 * (25 / 16 - a ^ 2) +
        (171 : ℝ) / 16 * (a - 4 / 5) * (5 / 4 - a) +
        (611 : ℝ) / 320 * (5 / 4 - a) + 1357 / 256 := by ring
  have hnon : 0 ≤ 3 * a ^ 2 * (25 / 16 - a ^ 2) +
      (171 : ℝ) / 16 * (a - 4 / 5) * (5 / 4 - a) +
      (611 : ℝ) / 320 * (5 / 4 - a) + 1357 / 256 := by positivity
  apply (le_div_iff₀ (sq_pos_of_pos (show (0 : ℝ) < 1 + a ^ 2 by positivity))).mpr
  nlinarith only [hid, hnon]

theorem cantelliGap_antitone : AntitoneOn cantelliGap (Icc ((4 : ℝ) / 5) (5 / 4)) := by
  have hc : Continuous cantelliGap := continuous_iff_continuousAt.mpr
    (fun a => (hasDerivAt_cantelliGap a).continuousAt)
  apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) hc.continuousOn
    (fun a _ => (hasDerivAt_cantelliGap a).differentiableAt.differentiableWithinAt)
  intro a ha
  have hm := interior_subset ha
  rw [(hasDerivAt_cantelliGap a).deriv]
  linarith only [phi_le_three_tenths a hm.1, cantelli_density_lower a hm.1 hm.2]

theorem cantelliGap_le_two_fifths (a : ℝ) (ha : (4 : ℝ) / 5 ≤ a) (ha1 : a ≤ (5 : ℝ) / 4) :
    1 / (1 + a ^ 2) - Phi (-a) ≤ (2 : ℝ) / 5 := by
  have h := cantelliGap_antitone (by norm_num : (4 / 5 : ℝ) ∈ Icc (4 / 5 : ℝ) (5 / 4))
    ⟨ha, ha1⟩ ha
  have hbase : cantelliGap (4 / 5) = (25 : ℝ) / 41 - Phi (-4 / 5) := by
    unfold cantelliGap
    norm_num
  rw [hbase] at h
  change 1 / (1 + a ^ 2) - Phi (-a) ≤ (25 : ℝ) / 41 - Phi (-4 / 5) at h
  linarith only [h, Phi_neg_four_fifths_ge]

theorem negative_family_price_le_Phi (b : ℝ) (hb : b ≤ 0) :
    (1 : ℝ) / 2 + 89 * b / 160 ≤ Phi b := by
  have h := Phi_lower_nonpos b hb
  linarith

theorem positive_family_price_le_Phi (b : ℝ) (hb : 0 ≤ b) (hb1 : b ≤ (1 : ℝ) / 3) :
    (1 : ℝ) / 2 + 253 * b / 800 + 3 * b ^ 2 / 20 + 9 * b ^ 3 / 250 ≤ Phi b := by
  have h := Phi_lower_on_unit b hb (by linarith)
  have hsq : b ^ 2 ≤ (1 : ℝ) / 9 := by
    have := (sq_le_sq₀ hb (by norm_num : (0 : ℝ) ≤ 1 / 3)).mpr hb1
    norm_num at this
    exact this
  have h1 : 0 ≤ (1 : ℝ) / 3 - b := by linarith
  have h2 : 0 ≤ (1 : ℝ) / 9 - b ^ 2 := by linarith
  have hnon : 0 ≤ b * ((451 : ℝ) / 36000 + (3 : ℝ) / 20 * (1 / 3 - b) +
      (101 : ℝ) / 1000 * (1 / 9 - b ^ 2)) := by positivity
  nlinarith only [h, hnon]

theorem Phi_third_ge_three_fifths : (3 : ℝ) / 5 ≤ Phi (1 / 3) := by
  have h := Phi_lower_on_unit (1 / 3 : ℝ) (by norm_num) (by norm_num)
  norm_num at h
  linarith

/-- The five analytic cuts cover every real threshold for the original
law. All moments and all closed events belong to this same μ. -/
theorem positive_closed_error (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ) (t : ℝ) :
    (μ : Measure ℝ).real (Iic t) - Phi t ≤ (2 : ℝ) / 5 * thirdAbsoluteMoment μ := by
  have hρ := Extremizer.thirdAbsoluteMoment_ge_one μ hμ
  have hPhi : 0 ≤ Phi t := measureReal_nonneg
  by_cases ht0 : t ≤ -5 / 4
  · have ha : 0 < -t := by linarith
    have hc := closedCDF_neg_le_cantelli μ hμ (-t) ha
    simp only [neg_neg] at hc
    have hs : ((5 : ℝ) / 4) ^ 2 ≤ (-t) ^ 2 :=
      (sq_le_sq₀ (by norm_num) ha.le).mpr (by linarith)
    have hprice : 1 / (1 + (-t) ^ 2) ≤ (16 : ℝ) / 41 := by
      apply (div_le_iff₀ (show (0 : ℝ) < 1 + (-t) ^ 2 by positivity)).mpr
      nlinarith only [hs]
    linarith only [hc, hprice, hPhi, hρ]
  by_cases ht1 : t ≤ -4 / 5
  · have ha : 0 < -t := by linarith
    have hc := closedCDF_neg_le_cantelli μ hμ (-t) ha
    have hg := cantelliGap_le_two_fifths (-t) (by linarith) (by linarith)
    simp only [neg_neg] at hc hg
    linarith only [hc, hg, hρ]
  by_cases ht2 : t ≤ -13 / 25
  · have hc := negative_family_CDF μ hμ (-13 / 25) (by norm_num)
    rw [show (1 : ℝ) / 2 + 89 * (-13 / 25) / 160 = 843 / 4000 by norm_num] at hc
    have hF : (μ : Measure ℝ).real (Iic t) ≤ (μ : Measure ℝ).real (Iic (-13 / 25)) :=
      measureReal_mono (Iic_subset_Iic.mpr ht2)
    have hP := Phi_mono (show (-4 / 5 : ℝ) ≤ t by linarith)
    linarith only [hc, hF, hP, Phi_neg_four_fifths_ge]
  by_cases ht3 : t ≤ 0
  · have hc := negative_family_CDF μ hμ t (by linarith)
    have hp := negative_family_price_le_Phi t ht3
    linarith only [hc, hp]
  by_cases ht4 : t ≤ (1 : ℝ) / 3
  · have ht : 0 ≤ t := by linarith
    have hc := positive_family_CDF μ hμ t ht
    have hp := positive_family_price_le_Phi t ht ht4
    linarith only [hc, hp]
  · have hF : (μ : Measure ℝ).real (Iic t) ≤ 1 := measureReal_le_one
    have hP := Phi_mono (show (1 : ℝ) / 3 ≤ t by linarith)
    linarith only [hF, hP, Phi_third_ge_three_fifths, hρ]

theorem iidSumLaw_one (μ : ProbabilityMeasure ℝ) : MixtureSum.iidSumLaw (μ : Measure ℝ) 1 = μ := by
  rw [MixtureSum.iidSumLaw_eq_convPower]
  simp only [MixtureSum.convPower, Measure.conv_dirac_zero]

theorem normalizedIidSumLaw_one (μ : ProbabilityMeasure ℝ) : normalizedIidSumLaw μ 1 = μ := by
  have hid : (μ : Measure ℝ) = (μ : Measure ℝ).map (fun u : ℝ => (u - 0) / 1) := by
    simp only [sub_zero, div_one, Measure.map_id']
  rw [AffineSum.normalizedIidSumLaw_eq_map μ (μ : Measure ℝ) 0 1 hid 1, iidSumLaw_one]
  simp only [Nat.cast_one, Real.sqrt_one, one_mul, mul_zero, sub_zero, div_one, Measure.map_id']

theorem positiveRawClosedBound_one : Reflection.PositiveRawClosedBound 1 ((2 : ℝ) / 5) := by
  intro μ hμ t
  simpa only [iidSumLaw_one, Nat.cast_one, Real.sqrt_one, div_one] using positive_closed_error μ hμ t

theorem positiveClosedBound_one : Reflection.PositiveClosedBound 1 ((2 : ℝ) / 5) := by
  intro μ hμ t
  simpa only [normalizedIidSumLaw_one, Nat.cast_one, Real.sqrt_one, div_one] using
    positive_closed_error μ hμ t

theorem absoluteClosedBound_one : Reflection.AbsoluteClosedBound 1 ((2 : ℝ) / 5) :=
  Reflection.absoluteClosedBound_of_positive 1 ((2 : ℝ) / 5) positiveClosedBound_one

/-- Reflection uses event inclusion, so original atoms are preserved. -/
theorem absolute_closed_error (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ) (t : ℝ) :
    |(μ : Measure ℝ).real (Iic t) - Phi t| ≤ (2 : ℝ) / 5 * thirdAbsoluteMoment μ := by
  simpa only [normalizedIidSumLaw_one, Nat.cast_one, Real.sqrt_one, div_one] using
    absoluteClosedBound_one μ hμ t

theorem fixedNSup_one_le_two_fifths : Extremizer.fixedNSup 1 ≤ (2 : ℝ) / 5 :=
  GlobalReduction.sup_le_of_positiveRawClosedBound 1 (by norm_num) ((2 : ℝ) / 5)
    (by norm_num) positiveRawClosedBound_one

theorem two_fifths_lt_esseenConstant : (2 : ℝ) / 5 < esseenConstant := by
  linarith only [AnalyticConstants.esseenConstant_gt_819_2000]

theorem fixedNSup_one_lt_esseenConstant : Extremizer.fixedNSup 1 < esseenConstant :=
  fixedNSup_one_le_two_fifths.trans_lt two_fifths_lt_esseenConstant

theorem sharp_one (μ : ProbabilityMeasure ℝ) (hμ : StandardizedLaw μ) (t : ℝ) :
    |(normalizedIidSumLaw μ 1).real (Iic t) -
      (ProbabilityTheory.gaussianReal 0 1).real (Iic t)| ≤
        esseenConstant * thirdAbsoluteMoment μ / Real.sqrt (1 : ℝ) := by
  have h := absoluteClosedBound_one μ hμ t
  have hρ : 0 ≤ thirdAbsoluteMoment μ := (Extremizer.thirdAbsoluteMoment_ge_one μ hμ).trans' (by norm_num)
  exact h.trans (by
    simpa only [Nat.cast_one, Real.sqrt_one, div_one] using
      mul_le_mul_of_nonneg_right two_fifths_lt_esseenConstant.le hρ)

end

end BerryEsseen.SingleSampleBound

#print axioms BerryEsseen.SingleSampleBound.Phi_neg_four_fifths_lower
#print axioms BerryEsseen.SingleSampleBound.cantelliGap_antitone
#print axioms BerryEsseen.SingleSampleBound.positive_closed_error
#print axioms BerryEsseen.SingleSampleBound.normalizedIidSumLaw_one
#print axioms BerryEsseen.SingleSampleBound.absolute_closed_error
#print axioms BerryEsseen.SingleSampleBound.fixedNSup_one_lt_esseenConstant
#print axioms BerryEsseen.SingleSampleBound.sharp_one
