module

public import BerryEsseen.StaircasePrices
public import BerryEsseen.MomentBudgetShape
public import Mathlib.Topology.MetricSpace.Lipschitz

@[expose] public section

/-! 2026-10-28: the genuine infimum over all positive widths in (mc:Q).
The reference law is any probability law with a finite second moment.
The proofs use a perspective inequality and approximate minimizers; an
optimal positive width is never assumed to exist. -/

noncomputable section

namespace BerryEsseen.StopLossShape

open MeasureTheory Set

def kernel (z A h : ℝ) : ℝ := (max (z - A + h) 0) ^ 2 / (4 * h)

def price (ν : Measure ℝ) (A h : ℝ) : ℝ :=
  (∫ z, (max (z - A + h) 0) ^ 2 ∂ν) / (4 * h)

def prices (ν : Measure ℝ) (A : ℝ) : Set ℝ :=
  (price ν A) '' Ioi 0

def Q (ν : Measure ℝ) (A : ℝ) : ℝ := sInf (prices ν A)

lemma integrable_numerator (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hSq : Integrable (fun z : ℝ => z ^ 2) ν) (A h : ℝ) :
    Integrable (fun z => (max (z - A + h) 0) ^ 2) ν := by
  convert TwoMoment.integrable_squarePositivePart ν id (A - h) measurable_id hSq using 1
  funext z
  simp only [id_eq]
  rw [show z - (A - h) = z - A + h by ring]

lemma integrable_kernel (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hSq : Integrable (fun z : ℝ => z ^ 2) ν) (A h : ℝ) :
    Integrable (fun z => kernel z A h) ν :=
  (integrable_numerator ν hSq A h).div_const (4 * h)

lemma price_eq_integral (ν : Measure ℝ) (A h : ℝ) :
    price ν A h = ∫ z, kernel z A h ∂ν := by
  simp only [price, kernel, integral_div]

lemma price_nonneg (ν : Measure ℝ) (A h : ℝ) (hh : 0 < h) :
    0 ≤ price ν A h := by
  exact div_nonneg (integral_nonneg (fun _ => sq_nonneg _)) (by positivity)

lemma prices_nonempty (ν : Measure ℝ) (A : ℝ) : (prices ν A).Nonempty :=
  ⟨price ν A 1, 1, by norm_num, rfl⟩

lemma prices_bddBelow (ν : Measure ℝ) (A : ℝ) : BddBelow (prices ν A) := by
  refine ⟨0, ?_⟩
  rintro r ⟨h, hh, rfl⟩
  exact price_nonneg ν A h hh

lemma Q_le_price (ν : Measure ℝ) (A h : ℝ) (hh : 0 < h) :
    Q ν A ≤ price ν A h :=
  csInf_le (prices_bddBelow ν A) ⟨h, hh, rfl⟩

lemma le_Q_iff (ν : Measure ℝ) (A c : ℝ) :
    c ≤ Q ν A ↔ ∀ h : ℝ, 0 < h → c ≤ price ν A h := by
  constructor
  · exact fun hc h hh => hc.trans (Q_le_price ν A h hh)
  · intro hc
    exact le_csInf (prices_nonempty ν A) (by rintro r ⟨h, hh, rfl⟩; exact hc h hh)

lemma Q_nonneg (ν : Measure ℝ) (A : ℝ) : 0 ≤ Q ν A :=
  (le_Q_iff ν A 0).mpr (fun h hh => price_nonneg ν A h hh)

/-- In particular the real infimum is bounded between zero and an actual
finite, integrable width-one price. -/
theorem Q_finite (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hSq : Integrable (fun z : ℝ => z ^ 2) ν) (A : ℝ) :
    Integrable (fun z => kernel z A 1) ν ∧ 0 ≤ Q ν A ∧ Q ν A ≤ price ν A 1 :=
  ⟨integrable_kernel ν hSq A 1, Q_nonneg ν A, Q_le_price ν A 1 (by norm_num)⟩

lemma exists_price_lt (ν : Measure ℝ) (A ε : ℝ) (hε : 0 < ε) :
    ∃ h : ℝ, 0 < h ∧ price ν A h < Q ν A + ε := by
  obtain ⟨r, ⟨h, hh, rfl⟩, hr⟩ := exists_lt_of_csInf_lt (prices_nonempty ν A)
    (show Q ν A < Q ν A + ε by linarith)
  exact ⟨h, hh, hr⟩

lemma kernel_antitone (z h : ℝ) (hh : 0 < h) : Antitone (fun A => kernel z A h) := by
  intro A B hAB
  unfold kernel
  apply div_le_div_of_nonneg_right _ (by positivity : 0 ≤ 4 * h)
  exact (sq_le_sq₀ (le_max_right _ _) (le_max_right _ _)).mpr
    (max_le_max (by linarith) le_rfl)

lemma price_antitone (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hSq : Integrable (fun z : ℝ => z ^ 2) ν) (h : ℝ) (hh : 0 < h) :
    Antitone (fun A => price ν A h) := by
  intro A B hAB
  change price ν B h ≤ price ν A h
  rw [price_eq_integral, price_eq_integral]
  exact integral_mono (integrable_kernel ν hSq B h) (integrable_kernel ν hSq A h)
    (fun z => kernel_antitone z h hh hAB)

theorem Q_antitone (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hSq : Integrable (fun z : ℝ => z ^ 2) ν) : Antitone (Q ν) := by
  intro A B hAB
  apply (le_Q_iff ν A (Q ν B)).mpr
  intro h hh
  exact (Q_le_price ν B h hh).trans (price_antitone ν hSq h hh hAB)

lemma kernel_jensen (z A B h k t : ℝ) (hh : 0 < h) (hk : 0 < k)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    kernel z ((1 - t) * A + t * B) ((1 - t) * h + t * k) ≤
      (1 - t) * kernel z A h + t * kernel z B k := by
  have hm := MomentBudgetShape.affine_mix_pos h k t hh hk ht ht1
  have hn : 0 ≤ 1 - t := sub_nonneg.mpr ht1
  have hmax : max (z - ((1 - t) * A + t * B) + ((1 - t) * h + t * k)) 0 ≤
      (1 - t) * max (z - A + h) 0 + t * max (z - B + k) 0 := by
    apply max_le
    · have h0 := mul_le_mul_of_nonneg_left (le_max_left (z - A + h) 0) hn
      have h1 := mul_le_mul_of_nonneg_left (le_max_left (z - B + k) 0) ht
      nlinarith only [h0, h1]
    · positivity
  have hs := (sq_le_sq₀ (le_max_right _ _) (by positivity)).mpr hmax
  have hj := MomentBudgetShape.square_div_jensen_nonneg
    (max (z - A + h) 0) (max (z - B + k) 0) h k t hh hk ht ht1
  unfold kernel
  have hdiv := div_le_div_of_nonneg_right hs (by positivity :
    0 ≤ 4 * ((1 - t) * h + t * k))
  have heq : ((1 - t) * max (z - A + h) 0 + t * max (z - B + k) 0) ^ 2 /
      (4 * ((1 - t) * h + t * k)) =
      (((1 - t) * max (z - A + h) 0 + t * max (z - B + k) 0) ^ 2 /
        ((1 - t) * h + t * k)) / 4 := by field_simp [hm.ne']
  rw [heq] at hdiv
  calc
    _ ≤ _ := hdiv
    _ ≤ _ := by
        convert (div_le_div_of_nonneg_right (by linarith :
        ((1 - t) * max (z - A + h) 0 + t * max (z - B + k) 0) ^ 2 /
          ((1 - t) * h + t * k) ≤
        (1 - t) * ((max (z - A + h) 0) ^ 2 / h) +
          t * ((max (z - B + k) 0) ^ 2 / k)) (by norm_num : (0 : ℝ) ≤ 4)) using 1
        field_simp [hh.ne', hk.ne']

theorem price_joint_jensen (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hSq : Integrable (fun z : ℝ => z ^ 2) ν)
    (A B h k t : ℝ) (hh : 0 < h) (hk : 0 < k) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    price ν ((1 - t) * A + t * B) ((1 - t) * h + t * k) ≤
      (1 - t) * price ν A h + t * price ν B k := by
  simp only [price_eq_integral]
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add
    ((integrable_kernel ν hSq A h).const_mul (1 - t))
    ((integrable_kernel ν hSq B k).const_mul t)]
  exact integral_mono (integrable_kernel ν hSq _ _)
    (((integrable_kernel ν hSq A h).const_mul (1 - t)).add
      ((integrable_kernel ν hSq B k).const_mul t))
    (fun z => kernel_jensen z A B h k t hh hk ht ht1)

theorem Q_jensen (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hSq : Integrable (fun z : ℝ => z ^ 2) ν)
    (A B t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    Q ν ((1 - t) * A + t * B) ≤ (1 - t) * Q ν A + t * Q ν B := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨h, hh, he⟩ := exists_price_lt ν A ε hε
  obtain ⟨k, hk, ke⟩ := exists_price_lt ν B ε hε
  have hq := Q_le_price ν ((1 - t) * A + t * B) ((1 - t) * h + t * k)
    (MomentBudgetShape.affine_mix_pos h k t hh hk ht ht1)
  have hp := price_joint_jensen ν hSq A B h k t hh hk ht ht1
  have h0 := mul_le_mul_of_nonneg_left he.le (sub_nonneg.mpr ht1)
  have h1 := mul_le_mul_of_nonneg_left ke.le ht
  nlinarith only [hq, hp, h0, h1]

theorem Q_convex (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hSq : Integrable (fun z : ℝ => z ^ 2) ν) : ConvexOn ℝ univ (Q ν) := by
  refine ⟨convex_univ, ?_⟩
  intro A _ B _ a b ha hb hab
  have haeq : a = 1 - b := by linarith
  simpa only [smul_eq_mul, haeq] using Q_jensen ν hSq A B b hb (by linarith)

/-- A width increase by `d` pays at most `d`, including `d = 0`.
The square gap is `d / h * (u - 2*h)^2`. -/
lemma positivePart_width_shift (x h d : ℝ) (hh : 0 < h) (hd : 0 ≤ d) :
    (max (x + 2 * d) 0) ^ 2 / (4 * (h + d)) ≤
      (max x 0) ^ 2 / (4 * h) + d := by
  have hhd : 0 < h + d := add_pos_of_pos_of_nonneg hh hd
  have hm : max (x + 2 * d) 0 ≤ max x 0 + 2 * d := by
    apply max_le
    · linarith only [le_max_left x 0]
    · positivity
  have hs := (sq_le_sq₀ (le_max_right _ _) (by positivity)).mpr hm
  have hgap : ((max x 0) ^ 2 / (4 * h) + d) * (4 * (h + d)) -
      (max x 0 + 2 * d) ^ 2 = d / h * (max x 0 - 2 * h) ^ 2 := by
    field_simp [hh.ne']
    ring
  have hn := mul_nonneg (div_nonneg hd hh.le) (sq_nonneg (max x 0 - 2 * h))
  apply (div_le_iff₀ (by positivity : 0 < 4 * (h + d))).mpr
  nlinarith only [hs, hn, hgap]

lemma kernel_width_shift (z A h d : ℝ) (hh : 0 < h) (hd : 0 ≤ d) :
    kernel z (A - d) (h + d) ≤ kernel z A h + d := by
  unfold kernel
  convert positivePart_width_shift (z - A + h) h d hh hd using 1
  congr 3
  ring

theorem price_width_shift (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hSq : Integrable (fun z : ℝ => z ^ 2) ν)
    (A h d : ℝ) (hh : 0 < h) (hd : 0 ≤ d) :
    price ν (A - d) (h + d) ≤ price ν A h + d := by
  rw [price_eq_integral, price_eq_integral]
  have hi := integral_mono (integrable_kernel ν hSq (A - d) (h + d))
    ((integrable_kernel ν hSq A h).add (integrable_const d))
    (fun z => kernel_width_shift z A h d hh hd)
  change (∫ z, kernel z (A - d) (h + d) ∂ν) ≤ ∫ z, kernel z A h + d ∂ν at hi
  rw [integral_add (integrable_kernel ν hSq A h) (integrable_const d), integral_const] at hi
  simpa using hi

theorem Q_width_shift (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hSq : Integrable (fun z : ℝ => z ^ 2) ν) (A d : ℝ) (hd : 0 ≤ d) :
    Q ν (A - d) ≤ Q ν A + d := by
  have hl : Q ν (A - d) - d ≤ Q ν A := by
    apply (le_Q_iff ν A _).mpr
    intro h hh
    have hq := Q_le_price ν (A - d) (h + d) (add_pos_of_pos_of_nonneg hh hd)
    have hp := price_width_shift ν hSq A h d hh hd
    linarith
  linarith

theorem Q_sub_le (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hSq : Integrable (fun z : ℝ => z ^ 2) ν) (A B : ℝ) (hAB : A ≤ B) :
    0 ≤ Q ν A - Q ν B ∧ Q ν A - Q ν B ≤ B - A := by
  have hm := Q_antitone ν hSq hAB
  have hs := Q_width_shift ν hSq B (B - A) (sub_nonneg.mpr hAB)
  rw [show B - (B - A) = A by ring] at hs
  constructor <;> linarith

theorem Q_abs_sub_le (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hSq : Integrable (fun z : ℝ => z ^ 2) ν) (A B : ℝ) :
    |Q ν A - Q ν B| ≤ |A - B| := by
  rcases le_total A B with hAB | hBA
  · have hs := Q_sub_le ν hSq A B hAB
    rw [abs_of_nonneg hs.1, abs_of_nonpos (sub_nonpos.mpr hAB)]
    linarith [hs.2]
  · have hs := Q_sub_le ν hSq B A hBA
    rw [abs_of_nonpos (by linarith [hs.1] : Q ν A - Q ν B ≤ 0),
      abs_of_nonneg (sub_nonneg.mpr hBA)]
    linarith [hs.2]

theorem Q_lipschitz (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hSq : Integrable (fun z : ℝ => z ^ 2) ν) : LipschitzWith 1 (Q ν) := by
  apply LipschitzWith.of_dist_le_mul
  intro A B
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using Q_abs_sub_le ν hSq A B

/-- Any already justified widthwise bound passes to the real infimum.
This lemma does not assume that such a widthwise comparison has been proved. -/
theorem le_Q_of_le_all_prices (ν : Measure ℝ) (A c : ℝ)
    (hc : ∀ h : ℝ, 0 < h → c ≤ price ν A h) : c ≤ Q ν A :=
  (le_Q_iff ν A c).mpr hc

/-- A CDF or other actual quantity can use the infimum after a valid
positive-slope widthwise estimate has been supplied. -/
theorem cdf_le_inf_price (ν : Measure ℝ) (A c base η : ℝ) (hη : 0 < η)
    (hwidth : ∀ h : ℝ, 0 < h → c ≤ base + η * price ν A h) :
    c ≤ base + η * Q ν A := by
  have hq : (c - base) / η ≤ Q ν A := by
    apply (le_Q_iff ν A _).mpr
    intro h hh
    apply (div_le_iff₀ hη).mpr
    have hp := hwidth h hh
    nlinarith only [hp]
  have hm := (div_le_iff₀ hη).mp hq
  nlinarith only [hm]

/-- An established comparison of squared-positive-part expectations gives
the stop-loss bound in (mc:Q). The actual stop-loss is integrable by L2;
reference integrability under L2 is supplied by `integrable_numerator`. -/
theorem integral_stopLoss_le_Q {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → ℝ)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hU : Measurable U) (hSqU : Integrable (fun ω => U ω ^ 2) μ)
    (hdom : ∀ c : ℝ, (∫ ω, (max (U ω - c) 0) ^ 2 ∂μ) ≤
      ∫ z, (max (z - c) 0) ^ 2 ∂ν) (A : ℝ) :
    (∫ ω, max (U ω - A) 0 ∂μ) ≤ Q ν A := by
  apply (le_Q_iff ν A _).mpr
  intro h hh
  have hi := TwoMoment.integrable_of_integrable_sq μ U hU hSqU
  have hlin : Integrable (fun ω => max (U ω - A) 0) μ :=
    (hi.sub (integrable_const A)).pos_part
  have hquad : Integrable (fun ω => (max (U ω - A + h) 0) ^ 2) μ := by
    convert TwoMoment.integrable_squarePositivePart μ U (A - h) hU hSqU using 1
    funext ω
    rw [show U ω - (A - h) = U ω - A + h by ring]
  have hw := integral_mono hlin (hquad.div_const (4 * h))
    (fun ω => StaircasePrices.positivePart_le_square_width (U ω - A) h hh)
  rw [integral_div] at hw
  have hc := hdom (A - h)
  have heq (x : ℝ) : x - (A - h) = x - A + h := by ring
  simp only [heq] at hc
  exact hw.trans (div_le_div_of_nonneg_right hc (by positivity))

/-- The same connection starting directly from the genuine nonnegative
test-function order. L2 on both laws justifies passage from lintegrals
to ordinary expectations; neither law needs finite support. -/
theorem integral_stopLoss_le_Q_of_squarePositiveOrder
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → ℝ)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hU : Measurable U) (hSqU : Integrable (fun ω => U ω ^ 2) μ)
    (hSqν : Integrable (fun z : ℝ => z ^ 2) ν)
    (horder : TwoMoment.SquarePositiveOrder (μ.map U) ν) (A : ℝ) :
    (∫ ω, max (U ω - A) 0 ∂μ) ≤ Q ν A := by
  apply integral_stopLoss_le_Q μ U ν hU hSqU (A := A)
  intro c
  have hI := TwoMoment.integrable_squarePositivePart μ U c hU hSqU
  have hR : Integrable (fun x : ℝ => (max (x - c) 0) ^ 2) ν := by
    simpa only [id_eq] using TwoMoment.integrable_squarePositivePart ν id c measurable_id hSqν
  have hc := horder c
  have hφ : Measurable (fun x : ℝ => ENNReal.ofReal ((max (x - c) 0) ^ 2)) := by
    fun_prop
  rw [lintegral_map hφ hU,
    ← ofReal_integral_eq_lintegral_ofReal hI (Filter.Eventually.of_forall (fun _ => sq_nonneg _)),
    ← ofReal_integral_eq_lintegral_ofReal hR (Filter.Eventually.of_forall (fun _ => sq_nonneg _))] at hc
  exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg (fun _ => sq_nonneg _))).mp hc

lemma price_eq_staircase_widthReferencePrice (ν0 ν1 : Measure ℝ)
    (b0 b1 : ℝ) (n k : ℕ) (A h : ℝ) :
    price (TwoMoment.coupledReferenceLaw ν0 ν1 b0 b1 n k) A h =
      StaircasePrices.widthReferencePrice ν0 ν1 b0 b1 n k A h := rfl

lemma price_dirac (z A h : ℝ) : price (Measure.dirac z) A h = kernel z A h := by
  simp only [price, kernel, integral_dirac]

/-- A point mass includes the nonattained boundary `A = z`: every
positive width has price `h/4`, while its real infimum is zero. -/
theorem Q_dirac (z A : ℝ) : Q (Measure.dirac z) A = max (z - A) 0 := by
  apply le_antisymm
  · by_cases hx : 0 < z - A
    · have hp := Q_le_price (Measure.dirac z) A (z - A) hx
      rw [price_dirac, kernel, max_eq_left (by linarith : 0 ≤ z - A + (z - A))] at hp
      rw [max_eq_left hx.le]
      convert hp using 1
      field_simp [hx.ne']
      ring
    · have hx0 : z - A ≤ 0 := le_of_not_gt hx
      rw [max_eq_right hx0]
      apply le_of_forall_pos_le_add
      intro ε hε
      have hp := Q_le_price (Measure.dirac z) A ε hε
      rw [price_dirac, kernel] at hp
      have hm : max (z - A + ε) 0 ≤ ε := max_le (by linarith) hε.le
      have hs := (sq_le_sq₀ (le_max_right _ _) hε.le).mpr hm
      have hd : (max (z - A + ε) 0) ^ 2 / (4 * ε) ≤ ε := by
        apply (div_le_iff₀ (by positivity : 0 < 4 * ε)).mpr
        nlinarith only [hs, sq_nonneg ε]
      simpa only [zero_add] using hp.trans hd
  · apply (le_Q_iff (Measure.dirac z) A _).mpr
    intro h hh
    rw [price_dirac]
    exact StaircasePrices.positivePart_le_square_width (z - A) h hh

theorem dirac_boundary_not_attained (z h : ℝ) (hh : 0 < h) :
    Q (Measure.dirac z) z < price (Measure.dirac z) z h := by
  rw [Q_dirac, price_dirac, kernel]
  simp only [sub_self, zero_add, max_self, max_eq_left hh.le]
  exact div_pos (sq_pos_of_pos hh) (by positivity)

end BerryEsseen.StopLossShape

#print axioms BerryEsseen.StopLossShape.Q_finite
#print axioms BerryEsseen.StopLossShape.price_joint_jensen
#print axioms BerryEsseen.StopLossShape.Q_convex
#print axioms BerryEsseen.StopLossShape.Q_antitone
#print axioms BerryEsseen.StopLossShape.Q_lipschitz
#print axioms BerryEsseen.StopLossShape.integral_stopLoss_le_Q
#print axioms BerryEsseen.StopLossShape.integral_stopLoss_le_Q_of_squarePositiveOrder
#print axioms BerryEsseen.StopLossShape.cdf_le_inf_price
#print axioms BerryEsseen.StopLossShape.Q_dirac
#print axioms BerryEsseen.StopLossShape.dirac_boundary_not_attained
