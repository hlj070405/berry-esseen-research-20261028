module

public import BerryEsseen.RationalGaussianTail
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

/-! 2026-10-29: scalar floor monotonicity for the high-frequency prices.
This first stage proves the actual real functions and the quarter threshold.
The numerical floor N is independent of any probability-law maximization.
The six-component physical price and fixed alternative selection are not
assembled in this stage. -/

noncomputable section
open Set
open scoped Topology

namespace BerryEsseen.HighFrequencyFloor

open RationalGaussianTail

def sqrtExp (c x : ℝ) : ℝ := Real.sqrt x * Real.exp (-(c * x))
def invSqrtExp (c x : ℝ) : ℝ := Real.exp (-(c * x)) / Real.sqrt x

def rationalNumerator (x : ℝ) : ℝ := 4 - 10 * x - 22 * x ^ 2 - 13 * x ^ 3 - 2 * x ^ 4

def weightedLambda (x : ℝ) : ℝ := Real.sqrt x * Real.exp (-x) * Lambda x

def scaledRational (r x : ℝ) : ℝ := Real.sqrt x * Real.exp (-(r * x)) * Lambda (r * x)

lemma antitoneOn_Ici_of_hasDerivAt_nonpos (N : ℝ) (f f' : ℝ → ℝ)
    (hd : ∀ x, N ≤ x → HasDerivAt f (f' x) x)
    (hsign : ∀ x, N ≤ x → f' x ≤ 0) : AntitoneOn f (Ici N) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici N)
  · exact fun x hx => (hd x hx).continuousAt.continuousWithinAt
  · exact fun x hx => (hd x (interior_subset hx)).hasDerivWithinAt
  · exact fun x hx => hsign x (interior_subset hx)

lemma sqrtExp_nonneg (c x : ℝ) : 0 ≤ sqrtExp c x := by unfold sqrtExp; positivity

lemma hasDerivAt_sqrtExp (c x : ℝ) (hx : 0 < x) :
    HasDerivAt (sqrtExp c)
      (Real.exp (-(c * x)) / (2 * Real.sqrt x) * (1 - 2 * c * x)) x := by
  have he : HasDerivAt (fun y : ℝ => -(c * y)) (-c) x := by
    convert ((hasDerivAt_id' x).const_mul c).neg using 1 <;> ring
  have h := (Real.hasDerivAt_sqrt (ne_of_gt hx)).mul he.exp
  convert h using 1
  · rfl
  · have hs : Real.sqrt x ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hx)
    field_simp [hs]
    ring_nf
    rw [Real.sq_sqrt hx.le] <;> ring

lemma sqrtExp_rate_pos (N c : ℝ) (hN : 0 < N) (hgate : 1 ≤ 2 * N * c) : 0 < c := by
  by_contra hc
  have hm := mul_nonpos_of_nonneg_of_nonpos hN.le (le_of_not_gt hc)
  nlinarith

/-- The exact one-half gate for √x exp(-cx), on the entire real ray x≥N. -/
theorem sqrtExp_antitone (c N : ℝ) (hN : 0 < N) (hgate : 1 ≤ 2 * N * c) :
    AntitoneOn (sqrtExp c) (Ici N) := by
  have hc := sqrtExp_rate_pos N c hN hgate
  apply antitoneOn_Ici_of_hasDerivAt_nonpos N (sqrtExp c)
    (fun x => Real.exp (-(c * x)) / (2 * Real.sqrt x) * (1 - 2 * c * x))
  · exact fun x hx => hasDerivAt_sqrtExp c x (hN.trans_le hx)
  · intro x hx
    have hx0 := hN.trans_le hx
    have hm := mul_le_mul_of_nonneg_right hx hc.le
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by nlinarith [hm])

/-- exp(-cx)/√x decreases on every positive ray when c>0. -/
theorem invSqrtExp_antitone (c : ℝ) (hc : 0 < c) :
    AntitoneOn (invSqrtExp c) (Ioi 0) := by
  intro x hx y hy hxy
  have he : Real.exp (-(c * y)) ≤ Real.exp (-(c * x)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hxy hc.le]
  unfold invSqrtExp
  calc
    _ ≤ Real.exp (-(c * x)) / Real.sqrt y :=
      div_le_div_of_nonneg_right he (Real.sqrt_nonneg y)
    _ ≤ _ := div_le_div_of_nonneg_left (Real.exp_pos _).le (Real.sqrt_pos.mpr hx)
      (Real.sqrt_le_sqrt hxy)

lemma Lambda_pos (x : ℝ) (hx : 0 ≤ x) : 0 < Lambda x :=
  div_pos (by linarith) (denominator_pos x hx)

lemma Lambda_derivative_neg (x : ℝ) (hx : 0 ≤ x) :
    -(x ^ 2 + 4 * x + 6) / denominator x ^ 2 < 0 := by
  apply div_neg_of_neg_of_pos
  · nlinarith [sq_nonneg x]
  · exact sq_pos_of_pos (denominator_pos x hx)

theorem Lambda_antitone : AntitoneOn Lambda (Ici 0) := by
  apply antitoneOn_Ici_of_hasDerivAt_nonpos 0 Lambda
    (fun x => -(x ^ 2 + 4 * x + 6) / denominator x ^ 2)
  · exact fun x hx => hasDerivAt_Lambda x hx
  · exact fun x hx => (Lambda_derivative_neg x hx).le

lemma rationalNumerator_antitone : AntitoneOn rationalNumerator (Ici 0) := by
  intro x hx y hy hxy
  have h2 := pow_le_pow_left₀ hx hxy 2
  have h3 := pow_le_pow_left₀ hx hxy 3
  have h4 := pow_le_pow_left₀ hx hxy 4
  unfold rationalNumerator
  nlinarith only [hxy, h2, h3, h4]

lemma rationalNumerator_quarter : rationalNumerator (1 / 4) = -(11 : ℝ) / 128 := by
  norm_num [rationalNumerator]

lemma rationalNumerator_neg (x : ℝ) (hx : 1 / 4 ≤ x) : rationalNumerator x < 0 := by
  have h := rationalNumerator_antitone (show (1 / 4 : ℝ) ∈ Ici 0 by norm_num)
    (show x ∈ Ici 0 from le_trans (by norm_num : (0 : ℝ) ≤ 1 / 4) hx) hx
  rw [rationalNumerator_quarter] at h
  linarith

/-- The exact numerator after clearing only positive derivative factors. -/
lemma hasDerivAt_weightedLambda (x : ℝ) (hx : 0 < x) :
    HasDerivAt weightedLambda
      (Real.exp (-x) / (2 * Real.sqrt x * denominator x ^ 2) * rationalNumerator x) x := by
  have h := (hasDerivAt_sqrtExp 1 x hx).mul (hasDerivAt_Lambda x hx.le)
  convert h using 1
  · ext y
    simp only [weightedLambda, sqrtExp, Pi.mul_apply, one_mul]
  · dsimp only [sqrtExp, Lambda, Pi.mul_apply]
    simp only [one_mul]
    have hs : Real.sqrt x ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hx)
    field_simp [hs, ne_of_gt (denominator_pos x hx.le)]
    unfold rationalNumerator denominator
    ring_nf
    rw [Real.sq_sqrt hx.le] <;> ring

/-- √x exp(-x)Λ(x) decreases from the exact original quarter threshold. -/
theorem weightedLambda_antitone : AntitoneOn weightedLambda (Ici (1 / 4)) := by
  apply antitoneOn_Ici_of_hasDerivAt_nonpos (1 / 4) weightedLambda
    (fun x => Real.exp (-x) / (2 * Real.sqrt x * denominator x ^ 2) * rationalNumerator x)
  · exact fun x hx => hasDerivAt_weightedLambda x (by linarith)
  · intro x hx
    apply mul_nonpos_of_nonneg_of_nonpos
    · positivity
    · exact (rationalNumerator_neg x hx).le

lemma scaledRational_eq (r x : ℝ) (hr : 0 < r) :
    scaledRational r x = weightedLambda (r * x) / Real.sqrt r := by
  unfold scaledRational weightedLambda
  rw [Real.sqrt_mul hr.le]
  field_simp [ne_of_gt (Real.sqrt_pos.mpr hr)]

/-- Rescaling transports the quarter gate without changing the index or rate. -/
theorem scaledRational_antitone (r N : ℝ) (hr : 0 < r) (hgate : 1 / 4 ≤ r * N) :
    AntitoneOn (scaledRational r) (Ici N) := by
  intro x hx y hy hxy
  have hxq : 1 / 4 ≤ r * x := hgate.trans (mul_le_mul_of_nonneg_left hx hr.le)
  have hyq : 1 / 4 ≤ r * y := hgate.trans (mul_le_mul_of_nonneg_left hy hr.le)
  have h := weightedLambda_antitone hxq hyq (mul_le_mul_of_nonneg_left hxy hr.le)
  rw [scaledRational_eq r y hr, scaledRational_eq r x hr]
  exact div_le_div_of_nonneg_right h (Real.sqrt_nonneg r)

/-- The improved origin factor has both decreasing nonnegative factors. -/
theorem sqrtExp_mul_Lambda_antitone (c r N : ℝ) (hN : 0 < N)
    (hr : 0 < r) (hgate : 1 ≤ 2 * N * c) :
    AntitoneOn (fun x : ℝ => sqrtExp c x * Lambda (r * x)) (Ici N) := by
  intro x hx y hy hxy
  have hx0 : 0 < x := hN.trans_le hx
  have hy0 : 0 < y := hN.trans_le hy
  have hF := sqrtExp_antitone c N hN hgate hx hy hxy
  have hL := Lambda_antitone (show 0 ≤ r * x by positivity) (show 0 ≤ r * y by positivity)
    (mul_le_mul_of_nonneg_left hxy hr.le)
  exact mul_le_mul hF hL (Lambda_nonneg _ (by positivity)) (sqrtExp_nonneg c x)

lemma sqrtExp_gate_persists (N n c : ℝ) (hN : 0 < N) (hn : N ≤ n)
    (hgate : 1 ≤ 2 * N * c) : 1 ≤ 2 * n * c := by
  have hc := sqrtExp_rate_pos N c hN hgate
  have hm := mul_le_mul_of_nonneg_right hn hc.le
  nlinarith

lemma quarter_gate_persists (N n r : ℝ) (hr : 0 < r) (hn : N ≤ n)
    (hgate : 1 / 4 ≤ r * N) : 1 / 4 ≤ r * n :=
  hgate.trans (mul_le_mul_of_nonneg_left hn hr.le)

lemma antitoneOn_min {s : Set ℝ} {f g : ℝ → ℝ} (hf : AntitoneOn f s) (hg : AntitoneOn g s) :
    AntitoneOn (fun x => min (f x) (g x)) s :=
  fun _ hx _ hy hxy => min_le_min (hf hx hy hxy) (hg hx hy hxy)

end BerryEsseen.HighFrequencyFloor

#print axioms BerryEsseen.HighFrequencyFloor.sqrtExp_antitone
#print axioms BerryEsseen.HighFrequencyFloor.invSqrtExp_antitone
#print axioms BerryEsseen.HighFrequencyFloor.Lambda_antitone
#print axioms BerryEsseen.HighFrequencyFloor.hasDerivAt_weightedLambda
#print axioms BerryEsseen.HighFrequencyFloor.weightedLambda_antitone
#print axioms BerryEsseen.HighFrequencyFloor.scaledRational_antitone
#print axioms BerryEsseen.HighFrequencyFloor.sqrtExp_mul_Lambda_antitone
