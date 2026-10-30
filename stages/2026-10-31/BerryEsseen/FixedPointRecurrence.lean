module

public import BerryEsseen.FixedPointUpper
public import BerryEsseen.FixedFourierConstants

@[expose] public section

/-! 2026-10-29: checked upper-endpoint recurrence without a quadratic
list-lookup traversal. H and D must separately be licensed by their actual
forcing and exponential bounds; this module checks the arithmetic step. -/

namespace BerryEsseen.FixedPointRecurrence

open FixedPointEnclosure FixedPointArithmetic FixedPointUpper
open FixedFourierConstants (scale scale_positive)

def updateBox (Dt : Box) (r h d : ℤ) : Box :=
  add (mul scale scale_positive (point d) (point r))
    (mul scale scale_positive Dt (point h))

theorem updateBox_contains {Dt : Box} {w : ℝ} (hDt : Contains scale Dt w) (r h d : ℤ) :
    Contains scale (updateBox Dt r h d)
      ((qval scale d : ℝ) * (qval scale r : ℝ) + w * (qval scale h : ℝ)) :=
  add_contains scale_positive
    (mul_contains scale_positive (point_contains scale d) (point_contains scale r))
    (mul_contains scale_positive hDt (point_contains scale h))

def updateCheck (Dt : Box) (r h d next : ℤ) : Bool :=
  decide ((updateBox Dt r h d).hi ≤ next)

theorem updateCheck_sound {Dt : Box} {w : ℝ} (hDt : Contains scale Dt w)
    (r h d next : ℤ) (hcheck : updateCheck Dt r h d next = true) :
    (qval scale d : ℝ) * (qval scale r : ℝ) + w * (qval scale h : ℝ) ≤
      (qval scale next : ℝ) := by
  have hi : (updateBox Dt r h d).hi ≤ next := of_decide_eq_true hcheck
  exact (le_upper (updateBox_contains hDt r h d)).trans
    (by exact_mod_cast qval_mono scale_positive hi)

/-- Simultaneous sequential traversal. The terminal case also checks that
one final R remains and both H,D lists are exhausted. -/
def chainCheck (step : ℤ → ℤ → ℤ → ℤ → Bool) (rs : List ℤ) : List ℤ → List ℤ → Bool
  | [], [] => match rs with | [_] => true | _ => false
  | h :: hs, d :: ds => match rs with
    | r :: next :: rt => step r h d next && chainCheck step (next :: rt) hs ds
    | _ => false
  | _, _ => false

theorem chainCheck_row (step : ℤ → ℤ → ℤ → ℤ → Bool) (rs hs ds : List ℤ)
    (hcheck : chainCheck step rs hs ds = true) (j : ℕ) (hj : j < hs.length) :
    step (rs.getD j 0) (hs.getD j 0) (ds.getD j 0) (rs.getD (j + 1) 0) = true := by
  induction hs generalizing rs ds j with
  | nil => simp at hj
  | cons h hs ih =>
    cases ds with
    | nil => simp [chainCheck] at hcheck
    | cons d ds =>
      cases rs with
      | nil => simp [chainCheck] at hcheck
      | cons r rt =>
        cases rt with
        | nil => simp [chainCheck] at hcheck
        | cons next rt =>
          change (step r h d next && chainCheck step (next :: rt) hs ds) = true at hcheck
          have hpair : step r h d next = true ∧ chainCheck step (next :: rt) hs ds = true := by
            simpa only [Bool.and_eq_true] using hcheck
          obtain ⟨hfirst, hrest⟩ := hpair
          cases j with
          | zero => simpa using hfirst
          | succ j =>
            have hh := ih (next :: rt) ds hrest j (by simpa using hj)
            simpa using hh

end BerryEsseen.FixedPointRecurrence

#print axioms BerryEsseen.FixedPointRecurrence.updateCheck_sound
#print axioms BerryEsseen.FixedPointRecurrence.chainCheck_row
