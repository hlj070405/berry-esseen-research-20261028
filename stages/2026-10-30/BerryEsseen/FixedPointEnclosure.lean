module

public import LeanCert.Core.IntervalRat.Basic
public import LeanCert.Core.IntervalRat.Transcendental

@[expose] public section

/-! 2026-10-29: integer witnesses for outward-rounded fixed-point intervals.
Each Box represents the real interval [lo/S,hi/S], for S>0. Gates are
sufficient integer/rational inequalities for a candidate output; they do not
trust Python floor/ceil/isqrt execution. Ordinary arithmetic consumes the
vendored LeanCert interval soundness. Upper endpoints have a separate
one-sided meaning: Contains I x implies x<=hi/S, not Contains [hi,hi] x. -/

namespace BerryEsseen.FixedPointEnclosure

open LeanCert.Core

structure Box where
  lo : ℤ
  hi : ℤ
  ordered : lo ≤ hi
  deriving DecidableEq

def qval (S z : ℤ) : ℚ := (z : ℚ) / (S : ℚ)

def Contains (S : ℤ) (I : Box) (x : ℝ) : Prop :=
  (qval S I.lo : ℝ) ≤ x ∧ x ≤ (qval S I.hi : ℝ)

lemma scale_pos {S : ℤ} (hS : 0 < S) : (0 : ℚ) < S := by exact_mod_cast hS

lemma qval_mono {S a b : ℤ} (hS : 0 < S) (h : a ≤ b) : qval S a ≤ qval S b := by
  exact div_le_div_of_nonneg_right (by exact_mod_cast h) (scale_pos hS).le

def toIntervalRat (S : ℤ) (hS : 0 < S) (I : Box) : IntervalRat :=
  ⟨qval S I.lo, qval S I.hi, qval_mono hS I.ordered⟩

theorem contains_iff_real (S : ℤ) (I : Box) (x : ℝ) :
    Contains S I x ↔ (I.lo : ℝ) / S ≤ x ∧ x ≤ (I.hi : ℝ) / S := by
  simp only [Contains, qval, Rat.cast_div, Rat.cast_intCast]

theorem contains_iff_mem (S : ℤ) (hS : 0 < S) (I : Box) (x : ℝ) :
    Contains S I x ↔ x ∈ toIntervalRat S hS I := Iff.rfl

def Encloses (S : ℤ) (K : Box) (J : IntervalRat) : Prop :=
  qval S K.lo ≤ J.lo ∧ J.hi ≤ qval S K.hi

instance (S : ℤ) (K : Box) (J : IntervalRat) : Decidable (Encloses S K J) := by
  unfold Encloses
  infer_instance

/-- A rational gate can round any already-proved LeanCert interval. -/
theorem contains_of_intervalRat {S : ℤ} {K : Box} {J : IntervalRat} {x : ℝ}
    (h : Encloses S K J) (hx : x ∈ J) : Contains S K x := by
  constructor
  · exact (show (qval S K.lo : ℝ) ≤ (J.lo : ℝ) by exact_mod_cast h.1).trans hx.1
  · exact hx.2.trans (show (J.hi : ℝ) ≤ (qval S K.hi : ℝ) by exact_mod_cast h.2)

theorem contains_widen {S : ℤ} (hS : 0 < S) {I K : Box} {x : ℝ}
    (hx : Contains S I x) (hlo : K.lo ≤ I.lo) (hhi : I.hi ≤ K.hi) : Contains S K x := by
  have hl : (qval S K.lo : ℝ) ≤ (qval S I.lo : ℝ) := by exact_mod_cast qval_mono hS hlo
  have hh : (qval S I.hi : ℝ) ≤ (qval S K.hi : ℝ) := by exact_mod_cast qval_mono hS hhi
  exact ⟨hl.trans hx.1, hx.2.trans hh⟩

def RatGate (S p d : ℤ) (K : Box) : Prop :=
  K.lo * d ≤ p * S ∧ p * S ≤ K.hi * d

instance (S p d : ℤ) (K : Box) : Decidable (RatGate S p d K) := by
  unfold RatGate
  infer_instance

theorem contains_rat {S p d : ℤ} (hS : 0 < S) (hd : 0 < d) (K : Box)
    (h : RatGate S p d K) : Contains S K ((p : ℝ) / d) := by
  have hs := scale_pos hS
  have hdq : (0 : ℚ) < d := by exact_mod_cast hd
  have hlo : qval S K.lo ≤ (p : ℚ) / d := by
    apply (div_le_div_iff₀ hs hdq).mpr
    exact_mod_cast h.1
  have hhi : (p : ℚ) / d ≤ qval S K.hi := by
    apply (div_le_div_iff₀ hdq hs).mpr
    exact_mod_cast h.2
  have hh := contains_of_intervalRat (J := IntervalRat.singleton ((p : ℚ) / d))
    (K := K) ⟨hlo, hhi⟩ (IntervalRat.mem_singleton ((p : ℚ) / d))
  simpa only [Rat.cast_div, Rat.cast_intCast] using hh

def AddGate (I J K : Box) : Prop := K.lo ≤ I.lo + J.lo ∧ I.hi + J.hi ≤ K.hi

instance (I J K : Box) : Decidable (AddGate I J K) := by unfold AddGate; infer_instance

theorem contains_add {S : ℤ} (hS : 0 < S) {I J K : Box} {x y : ℝ}
    (hx : Contains S I x) (hy : Contains S J y) (h : AddGate I J K) : Contains S K (x + y) := by
  apply contains_of_intervalRat (J := IntervalRat.add (toIntervalRat S hS I) (toIntervalRat S hS J)) _
    (IntervalRat.mem_add hx hy)
  change qval S K.lo ≤ qval S I.lo + qval S J.lo ∧
    qval S I.hi + qval S J.hi ≤ qval S K.hi
  constructor
  · have hh := qval_mono hS h.1
    simpa only [qval, Int.cast_add, add_div] using hh
  · have hh := qval_mono hS h.2
    simpa only [qval, Int.cast_add, add_div] using hh

def NegGate (I K : Box) : Prop := K.lo ≤ -I.hi ∧ -I.lo ≤ K.hi

instance (I K : Box) : Decidable (NegGate I K) := by unfold NegGate; infer_instance

theorem contains_neg {S : ℤ} (hS : 0 < S) {I K : Box} {x : ℝ}
    (hx : Contains S I x) (h : NegGate I K) : Contains S K (-x) := by
  apply contains_of_intervalRat (J := IntervalRat.neg (toIntervalRat S hS I)) _ (IntervalRat.mem_neg hx)
  change qval S K.lo ≤ -qval S I.hi ∧ -qval S I.lo ≤ qval S K.hi
  constructor
  · simpa only [qval, Int.cast_neg, neg_div] using qval_mono hS h.1
  · simpa only [qval, Int.cast_neg, neg_div] using qval_mono hS h.2

def SubGate (I J K : Box) : Prop := K.lo ≤ I.lo - J.hi ∧ I.hi - J.lo ≤ K.hi

instance (I J K : Box) : Decidable (SubGate I J K) := by unfold SubGate; infer_instance

theorem contains_sub {S : ℤ} (hS : 0 < S) {I J K : Box} {x y : ℝ}
    (hx : Contains S I x) (hy : Contains S J y) (h : SubGate I J K) : Contains S K (x - y) := by
  apply contains_of_intervalRat (J := IntervalRat.sub (toIntervalRat S hS I) (toIntervalRat S hS J)) _
    (IntervalRat.mem_sub hx hy)
  change qval S K.lo ≤ qval S I.lo + -qval S J.hi ∧
    qval S I.hi + -qval S J.lo ≤ qval S K.hi
  constructor
  · simpa only [qval, Int.cast_sub, Int.cast_add, Int.cast_neg, sub_div, add_div, neg_div,
      sub_eq_add_neg] using qval_mono hS h.1
  · simpa only [qval, Int.cast_sub, Int.cast_add, Int.cast_neg, sub_div, add_div, neg_div,
      sub_eq_add_neg] using qval_mono hS h.2

def MulLowerGate (S : ℤ) (I J : Box) (lo : ℤ) : Prop :=
  lo * S ≤ I.lo * J.lo ∧ lo * S ≤ I.lo * J.hi ∧
    lo * S ≤ I.hi * J.lo ∧ lo * S ≤ I.hi * J.hi

def MulUpperGate (S : ℤ) (I J : Box) (hi : ℤ) : Prop :=
  I.lo * J.lo ≤ hi * S ∧ I.lo * J.hi ≤ hi * S ∧
    I.hi * J.lo ≤ hi * S ∧ I.hi * J.hi ≤ hi * S

def MulGate (S : ℤ) (I J K : Box) : Prop := MulLowerGate S I J K.lo ∧ MulUpperGate S I J K.hi

instance (S : ℤ) (I J : Box) (lo : ℤ) : Decidable (MulLowerGate S I J lo) := by
  unfold MulLowerGate
  infer_instance

instance (S : ℤ) (I J : Box) (hi : ℤ) : Decidable (MulUpperGate S I J hi) := by
  unfold MulUpperGate
  infer_instance

instance (S : ℤ) (I J K : Box) : Decidable (MulGate S I J K) := by
  unfold MulGate
  infer_instance

private lemma qval_le_product {S k a b : ℤ} (hS : 0 < S) (h : k * S ≤ a * b) :
    qval S k ≤ qval S a * qval S b := by
  have hs := scale_pos hS
  have hq : (k : ℚ) * S ≤ (a : ℚ) * b := by exact_mod_cast h
  unfold qval
  rw [div_mul_div_comm]
  apply (div_le_div_iff₀ hs (mul_pos hs hs)).mpr
  nlinarith only [mul_le_mul_of_nonneg_right hq hs.le]

private lemma product_le_qval {S k a b : ℤ} (hS : 0 < S) (h : a * b ≤ k * S) :
    qval S a * qval S b ≤ qval S k := by
  have hs := scale_pos hS
  have hq : (a : ℚ) * b ≤ (k : ℚ) * S := by exact_mod_cast h
  unfold qval
  rw [div_mul_div_comm]
  apply (div_le_div_iff₀ (mul_pos hs hs) hs).mpr
  nlinarith only [mul_le_mul_of_nonneg_right hq hs.le]

private lemma mul_rat_lower {S : ℤ} (hS : 0 < S) (I J : Box) (lo : ℤ)
    (h : MulLowerGate S I J lo) :
    qval S lo ≤ (IntervalRat.mul (toIntervalRat S hS I) (toIntervalRat S hS J)).lo := by
  apply (IntervalRat.le_min4_iff _ _ _ _ _).mpr
  exact ⟨qval_le_product hS h.1, qval_le_product hS h.2.1,
    qval_le_product hS h.2.2.1, qval_le_product hS h.2.2.2⟩

private lemma mul_rat_upper {S : ℤ} (hS : 0 < S) (I J : Box) (hi : ℤ)
    (h : MulUpperGate S I J hi) :
    (IntervalRat.mul (toIntervalRat S hS I) (toIntervalRat S hS J)).hi ≤ qval S hi := by
  apply (IntervalRat.max4_le_iff _ _ _ _ _).mpr
  exact ⟨product_le_qval hS h.1, product_le_qval hS h.2.1,
    product_le_qval hS h.2.2.1, product_le_qval hS h.2.2.2⟩

theorem contains_mul {S : ℤ} (hS : 0 < S) {I J K : Box} {x y : ℝ}
    (hx : Contains S I x) (hy : Contains S J y) (h : MulGate S I J K) : Contains S K (x * y) :=
  contains_of_intervalRat ⟨mul_rat_lower hS I J K.lo h.1, mul_rat_upper hS I J K.hi h.2⟩
    (IntervalRat.mem_mul hx hy)

theorem mul_le_upper {S : ℤ} (hS : 0 < S) {I J : Box} {x y : ℝ} (hi : ℤ)
    (hx : Contains S I x) (hy : Contains S J y) (h : MulUpperGate S I J hi) :
    x * y ≤ (qval S hi : ℝ) := by
  have hm := IntervalRat.mem_mul (I := toIntervalRat S hS I) (J := toIntervalRat S hS J) hx hy
  exact hm.2.trans (by exact_mod_cast mul_rat_upper hS I J hi h)

private def positiveRat (S : ℤ) (hS : 0 < S) (I : Box) (hI : 0 < I.lo) :
    IntervalRat.IntervalRatNonzero where
  toIntervalRat := toIntervalRat S hS I
  nonzero := by
    intro h
    have hp : (0 : ℚ) < qval S I.lo := div_pos (by exact_mod_cast hI) (scale_pos hS)
    exact (not_le_of_gt hp) h.1

def InvGate (S : ℤ) (I K : Box) : Prop := K.lo * I.hi ≤ S * S ∧ S * S ≤ K.hi * I.lo

instance (S : ℤ) (I K : Box) : Decidable (InvGate S I K) := by unfold InvGate; infer_instance

theorem contains_inv_pos {S : ℤ} (hS : 0 < S) {I K : Box} {x : ℝ}
    (hI : 0 < I.lo) (hx : Contains S I x) (h : InvGate S I K) : Contains S K x⁻¹ := by
  have hs := scale_pos hS
  have hIq : (0 : ℚ) < I.lo := by exact_mod_cast hI
  have hHq : (0 : ℚ) < I.hi := by exact_mod_cast (lt_of_lt_of_le hI I.ordered)
  have hloq : (0 : ℚ) < qval S I.lo := div_pos hIq hs
  have hxr : 0 < x := (show (0 : ℝ) < (qval S I.lo : ℝ) by exact_mod_cast hloq).trans_le hx.1
  have hi := IntervalRat.mem_invNonzero (I := positiveRat S hS I hI) hx hxr.ne'
  apply contains_of_intervalRat _ hi
  have hp : (0 : ℚ) < (positiveRat S hS I hI).lo := hloq
  simp only [Encloses, IntervalRat.invNonzero, hp, ↓reduceDIte]
  change qval S K.lo ≤ (qval S I.hi)⁻¹ ∧ (qval S I.lo)⁻¹ ≤ qval S K.hi
  constructor
  · unfold qval
    rw [inv_div]
    exact (div_le_div_iff₀ hs hHq).mpr (by exact_mod_cast h.1)
  · unfold qval
    rw [inv_div]
    exact (div_le_div_iff₀ hIq hs).mpr (by exact_mod_cast h.2)

/-- Interval division matches Python's reciprocal-then-multiply path. -/
theorem contains_div_pos {S : ℤ} (hS : 0 < S) {I J R K : Box} {x y : ℝ}
    (hJ : 0 < J.lo) (hx : Contains S I x) (hy : Contains S J y)
    (hinv : InvGate S J R) (hmul : MulGate S I R K) : Contains S K (x / y) := by
  rw [div_eq_mul_inv]
  exact contains_mul hS hx (contains_inv_pos hS hJ hy hinv) hmul

def DivIntGate (d : ℤ) (I K : Box) : Prop := K.lo * d ≤ I.lo ∧ I.hi ≤ K.hi * d

instance (d : ℤ) (I K : Box) : Decidable (DivIntGate d I K) := by unfold DivIntGate; infer_instance

theorem contains_div_int {S d : ℤ} (hS : 0 < S) (hd : 0 < d) {I K : Box} {x : ℝ}
    (hx : Contains S I x) (h : DivIntGate d I K) : Contains S K (x / (d : ℝ)) := by
  rw [contains_iff_real] at hx ⊢
  have hs : (0 : ℝ) < S := by exact_mod_cast hS
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  constructor
  · apply (le_div_iff₀ hdr).mpr
    have hh : (K.lo : ℝ) * d ≤ I.lo := by exact_mod_cast h.1
    have hh' := div_le_div_of_nonneg_right hh hs.le
    apply le_trans _ hx.1
    convert hh' using 1
    ring
  · apply (div_le_iff₀ hdr).mpr
    have hh : (I.hi : ℝ) ≤ (K.hi : ℝ) * d := by exact_mod_cast h.2
    have hh' := div_le_div_of_nonneg_right hh hs.le
    apply le_trans hx.2
    convert hh' using 1
    ring

private lemma real_qval_nonneg {S z : ℤ} (hS : 0 < S) (hz : 0 ≤ z) :
    (0 : ℝ) ≤ (qval S z : ℝ) := by
  have hh : (0 : ℚ) ≤ qval S z := div_nonneg (by exact_mod_cast hz) (scale_pos hS).le
  exact Rat.cast_nonneg.mpr hh

private lemma real_qval_nonpos {S z : ℤ} (hS : 0 < S) (hz : z ≤ 0) :
    (qval S z : ℝ) ≤ 0 := by
  have hh : qval S z ≤ (0 : ℚ) := by
    simpa only [qval, Int.cast_zero, zero_div] using qval_mono hS hz
  exact Rat.cast_nonpos.mpr hh

/-- The lower square gate has three valid cases. In particular, an interval
crossing zero may use the zero lower bound; endpoint-square minima alone
would be unsound in that case. -/
def SqGate (S : ℤ) (I K : Box) : Prop :=
  (K.lo ≤ 0 ∨ (0 ≤ I.lo ∧ K.lo * S ≤ I.lo ^ 2) ∨
    (I.hi ≤ 0 ∧ K.lo * S ≤ I.hi ^ 2)) ∧
  I.lo ^ 2 ≤ K.hi * S ∧ I.hi ^ 2 ≤ K.hi * S

instance (S : ℤ) (I K : Box) : Decidable (SqGate S I K) := by unfold SqGate; infer_instance

theorem contains_sq {S : ℤ} (hS : 0 < S) {I K : Box} {x : ℝ}
    (hx : Contains S I x) (h : SqGate S I K) : Contains S K (x ^ 2) := by
  have hcross : I.lo * I.hi ≤ K.hi * S := by
    nlinarith only [h.2.1, h.2.2, sq_nonneg (I.lo - I.hi)]
  have hupper : MulUpperGate S I I K.hi :=
    ⟨by simpa only [pow_two] using h.2.1, hcross,
      by simpa only [mul_comm] using hcross, by simpa only [pow_two] using h.2.2⟩
  refine ⟨?_, ?_⟩
  · rcases h.1 with hzero | hpos | hneg
    · exact (real_qval_nonpos hS hzero).trans (sq_nonneg x)
    · have hLo0 := real_qval_nonneg hS hpos.1
      have hx0 : 0 ≤ x := hLo0.trans hx.1
      have hl : (qval S K.lo : ℝ) ≤ (qval S I.lo : ℝ) ^ 2 := by
        rw [pow_two]
        have hh := qval_le_product hS
          (show K.lo * S ≤ I.lo * I.lo by simpa only [pow_two] using hpos.2)
        exact_mod_cast hh
      exact hl.trans ((sq_le_sq₀ hLo0 hx0).mpr hx.1)
    · have hHi0 := real_qval_nonpos hS hneg.1
      have hx0 : x ≤ 0 := hx.2.trans hHi0
      have hl : (qval S K.lo : ℝ) ≤ (qval S I.hi : ℝ) ^ 2 := by
        rw [pow_two]
        have hh := qval_le_product hS
          (show K.lo * S ≤ I.hi * I.hi by simpa only [pow_two] using hneg.2)
        exact_mod_cast hh
      have hh := (sq_le_sq₀ (neg_nonneg.mpr hHi0) (neg_nonneg.mpr hx0)).mpr (neg_le_neg hx.2)
      exact hl.trans (by simpa only [neg_sq] using hh)
  · simpa only [pow_two] using mul_le_upper hS K.hi hx hx hupper

def SqrtGate (S : ℤ) (I K : Box) : Prop :=
  0 ≤ I.lo ∧ 0 ≤ K.lo ∧ K.lo ^ 2 ≤ I.lo * S ∧ I.hi * S ≤ K.hi ^ 2

instance (S : ℤ) (I K : Box) : Decidable (SqrtGate S I K) := by unfold SqrtGate; infer_instance

/-- Candidate isqrt endpoints are accepted by integer square inequalities;
the proof does not execute or trust the square-root endpoint algorithm. -/
theorem contains_sqrt {S : ℤ} (hS : 0 < S) {I K : Box} {x : ℝ}
    (hx : Contains S I x) (h : SqrtGate S I K) : Contains S K (Real.sqrt x) := by
  rcases h with ⟨hI0, hK0, hl, hu⟩
  have hx0 : 0 ≤ x := (real_qval_nonneg hS hI0).trans hx.1
  have hLo0 := real_qval_nonneg hS hK0
  have hHi0 := real_qval_nonneg hS (hK0.trans K.ordered)
  have hL : (qval S K.lo : ℝ) ^ 2 ≤ (qval S I.lo : ℝ) := by
    rw [pow_two]
    have hh := product_le_qval hS (show K.lo * K.lo ≤ I.lo * S by simpa only [pow_two] using hl)
    exact_mod_cast hh
  have hU : (qval S I.hi : ℝ) ≤ (qval S K.hi : ℝ) ^ 2 := by
    rw [pow_two]
    have hh := qval_le_product hS (show I.hi * S ≤ K.hi * K.hi by simpa only [pow_two] using hu)
    exact_mod_cast hh
  exact ⟨(Real.le_sqrt hLo0 hx0).mpr (hL.trans hx.1),
    (Real.sqrt_le_left hHi0).mpr (hx.2.trans hU)⟩

/-- The same bridge can consume the vendored precision-aware sqrt
soundness when a caller already has a rational enclosure gate for it. -/
theorem contains_sqrt_library {S : ℤ} (hS : 0 < S) {I K : Box} {x : ℝ}
    (hx : Contains S I x) (bits : ℕ)
    (h : Encloses S K (IntervalRat.sqrtIntervalTightPrec (toIntervalRat S hS I) bits)) :
    Contains S K (Real.sqrt x) :=
  contains_of_intervalRat h (IntervalRat.mem_sqrtIntervalTightPrec' hx bits)

def MinGate (I J K : Box) : Prop := K.lo ≤ min I.lo J.lo ∧ min I.hi J.hi ≤ K.hi

instance (I J K : Box) : Decidable (MinGate I J K) := by unfold MinGate; infer_instance

theorem contains_min {S : ℤ} (hS : 0 < S) {I J K : Box} {x y : ℝ}
    (hx : Contains S I x) (hy : Contains S J y) (h : MinGate I J K) : Contains S K (min x y) := by
  have hs := scale_pos hS
  have hl : qval S K.lo ≤ min (qval S I.lo) (qval S J.lo) := by
    unfold qval
    rw [min_div_div_right hs.le]
    exact div_le_div_of_nonneg_right (by exact_mod_cast h.1) hs.le
  have hh : min (qval S I.hi) (qval S J.hi) ≤ qval S K.hi := by
    unfold qval
    rw [min_div_div_right hs.le]
    exact div_le_div_of_nonneg_right (by exact_mod_cast h.2) hs.le
  have hlr : (qval S K.lo : ℝ) ≤ min (qval S I.lo : ℝ) (qval S J.lo : ℝ) := by exact_mod_cast hl
  have hhr : min (qval S I.hi : ℝ) (qval S J.hi : ℝ) ≤ (qval S K.hi : ℝ) := by exact_mod_cast hh
  exact ⟨hlr.trans (min_le_min hx.1 hy.1), (min_le_min hx.2 hy.2).trans hhr⟩

/-- This is the semantics of I.upper(): an inequality for the original x. -/
theorem le_upper {S : ℤ} {I : Box} {x : ℝ} (hx : Contains S I x) : x ≤ (qval S I.hi : ℝ) := hx.2

def sqrtThree40 : Box :=
  ⟨17320508075688772935274463415058723669428,
    17320508075688772935274463415058723669429, by decide⟩

/-- Exact scale and endpoints from I.sqrt() applied to I.rat(3) at S=10^40.
Only integer gate decisions are evaluated by the kernel. -/
theorem contains_sqrt_three_10pow40 : Contains (10 ^ 40) sqrtThree40 (Real.sqrt 3) := by
  let input : Box := ⟨3 * 10 ^ 40, 3 * 10 ^ 40, le_rfl⟩
  have hx : Contains (10 ^ 40) input (3 : ℝ) := by
    have hh := contains_rat (S := 10 ^ 40) (p := 3) (d := 1) (by decide) (by decide) input (by decide)
    simpa only [Int.cast_ofNat, Int.cast_one, div_one] using hh
  exact contains_sqrt (by decide) hx (by decide)

end BerryEsseen.FixedPointEnclosure

#print axioms BerryEsseen.FixedPointEnclosure.contains_mul
#print axioms BerryEsseen.FixedPointEnclosure.contains_inv_pos
#print axioms BerryEsseen.FixedPointEnclosure.contains_div_pos
#print axioms BerryEsseen.FixedPointEnclosure.contains_sq
#print axioms BerryEsseen.FixedPointEnclosure.contains_sqrt
#print axioms BerryEsseen.FixedPointEnclosure.contains_min
#print axioms BerryEsseen.FixedPointEnclosure.contains_sqrt_three_10pow40
