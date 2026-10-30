module

public import BerryEsseen.ControlEndpointWitnesses
public import BerryEsseen.FixedFourierConstants
public import BerryEsseen.FixedPointUpper
public import BerryEsseen.CoefficientPhysicalProfile

@[expose] public section

/-! 2026-10-29: actual mathematical parameters of the chosen control
endpoint. Its spectral coordinate is a rational square, so its physical
beta and grid scale admit exact rational descriptions. Literal interval
witnesses are checked against these values, never inferred from metadata. -/

namespace BerryEsseen.ControlEndpointParameters

open FixedPointEnclosure FixedPointArithmetic
open FixedFourierConstants (scale scale_positive)



def resolution : ℕ := ControlEndpointWitnesses.resolution

lemma resolution_pos : 0 < resolution := by decide

def betaBox : Box := ⟨ControlEndpointWitnesses.betaLo, ControlEndpointWitnesses.betaHi, by decide⟩
def rootSBox : Box := ⟨ControlEndpointWitnesses.rootSLo, ControlEndpointWitnesses.rootSHi, by decide⟩
def lambdaBox : Box := ⟨ControlEndpointWitnesses.lambdaLo, ControlEndpointWitnesses.lambdaHi, by decide⟩
def cBox : Box := rat scale scale_positive ControlEndpointWitnesses.cNum ControlEndpointWitnesses.cDen (by decide)
def aBox : Box := rat scale scale_positive ControlEndpointWitnesses.aNum ControlEndpointWitnesses.aDen (by decide)
def vBox : Box := rat scale scale_positive 4 1 (by decide)
def alphaBox : Box := rat scale scale_positive 41 42 (by decide)
def u0Box : Box := mul scale scale_positive aBox rootSBox
def uBox : Box := mul scale scale_positive vBox rootSBox

def indexBox (j : ℕ) : Box :=
  rat scale scale_positive (j : ℤ) (resolution : ℤ) (by exact_mod_cast resolution_pos)

def firstGridBox (j : ℕ) : Box := mul scale scale_positive u0Box (indexBox j)

def secondGridBox (j : ℕ) : Box :=
  add u0Box (mul scale scale_positive (sub uBox u0Box) (indexBox j))

def dtBox : Box := divInt u0Box (resolution : ℤ) (by exact_mod_cast resolution_pos)
def dt2Box : Box := divInt (sub uBox u0Box) (resolution : ℤ) (by exact_mod_cast resolution_pos)

noncomputable section

def s : ℝ := (ControlEndpointWitnesses.sNum : ℝ) / ControlEndpointWitnesses.sDen
def c : ℝ := (ControlEndpointWitnesses.cNum : ℝ) / ControlEndpointWitnesses.cDen
def A : ℝ := (ControlEndpointWitnesses.aNum : ℝ) / ControlEndpointWitnesses.aDen
def beta : ℝ := 13500000000000000 / 45949729863572161
def rootS : ℝ := 45949729863572161 / 13500000000000000
def U0 : ℝ := A * rootS
def U : ℝ := 4 * rootS
def firstGrid (j : ℕ) : ℝ := U0 * ((j : ℝ) / resolution)
def secondGrid (j : ℕ) : ℝ := U0 + (U - U0) * ((j : ℝ) / resolution)

theorem beta_pos : 0 < beta := by norm_num [beta]
theorem rootS_pos : 0 < rootS := by norm_num [rootS]
theorem s_pos : 0 < s := by norm_num [s, ControlEndpointWitnesses.sNum, ControlEndpointWitnesses.sDen]
theorem c_pos : 0 < c := by norm_num [c, ControlEndpointWitnesses.cNum, ControlEndpointWitnesses.cDen]
theorem A_pos : 0 < A := by norm_num [A, ControlEndpointWitnesses.aNum, ControlEndpointWitnesses.aDen]
theorem A_lt_four : A < 4 := by norm_num [A, ControlEndpointWitnesses.aNum, ControlEndpointWitnesses.aDen]

theorem beta_mul_rootS : beta * rootS = 1 := by norm_num [beta, rootS]
theorem spectral_eq : 1 / beta ^ 2 = s := by norm_num [beta, s, ControlEndpointWitnesses.sNum, ControlEndpointWitnesses.sDen]
theorem c_eq_old : c = CoefficientRayPrice.oldCoefficient := by
  norm_num [c, ControlEndpointWitnesses.cNum, ControlEndpointWitnesses.cDen, CoefficientRayPrice.oldCoefficient, HighMomentRayDamping.rho0]

theorem U0_eq : U0 = A / beta := by
  apply (eq_div_iff beta_pos.ne').mpr
  unfold U0
  calc
    A * rootS * beta = A * (beta * rootS) := by ring
    _ = A := by rw [beta_mul_rootS, mul_one]

theorem U_eq : U = 4 / beta := by
  apply (eq_div_iff beta_pos.ne').mpr
  unfold U
  nlinarith only [beta_mul_rootS]

theorem U0_pos : 0 < U0 := mul_pos A_pos rootS_pos
theorem U_pos : 0 < U := mul_pos (by norm_num) rootS_pos
theorem U0_le_U : U0 ≤ U := mul_le_mul_of_nonneg_right A_lt_four.le rootS_pos.le

theorem contains_beta : Contains scale betaBox beta := by
  have hh := contains_rat (S := scale) (p := 13500000000000000) (d := 45949729863572161)
    scale_positive (by decide) betaBox (by decide)
  simpa only [beta, Int.cast_ofNat] using hh

theorem contains_rootS : Contains scale rootSBox rootS := by
  have hh := contains_rat (S := scale) (p := 45949729863572161) (d := 13500000000000000)
    scale_positive (by decide) rootSBox (by decide)
  simpa only [rootS, Int.cast_ofNat] using hh

theorem contains_c : Contains scale cBox c :=
  rat_contains scale scale_positive ControlEndpointWitnesses.cNum ControlEndpointWitnesses.cDen (by decide)

theorem contains_A : Contains scale aBox A :=
  rat_contains scale scale_positive ControlEndpointWitnesses.aNum ControlEndpointWitnesses.aDen (by decide)

theorem contains_four : Contains scale vBox (4 : ℝ) := by
  simpa only [vBox, Int.cast_ofNat, Int.cast_one, div_one] using
    rat_contains scale scale_positive 4 1 (by decide)

theorem loss_eq : HighMomentRayDamping.loss 42 beta = 1 / 42 := by
  unfold HighMomentRayDamping.loss
  apply min_eq_right
  norm_num [beta, HighMomentRayDamping.rho0]

theorem contains_alpha : Contains scale alphaBox (1 - HighMomentRayDamping.loss 42 beta) := by
  rw [loss_eq]
  have hh := rat_contains scale scale_positive 41 42 (by decide)
  norm_num only [Int.cast_ofNat] at hh
  convert hh using 1 <;> norm_num [alphaBox]

theorem alpha_lower_eq : alphaBox.lo = ControlEndpointWitnesses.alphaLower := by decide
theorem alpha_lower_nonneg : 0 ≤ alphaBox.lo := by decide

theorem contains_lambda : Contains scale lambdaBox (CoarseHighMomentRayPrice.lambda 42 beta) := by
  rw [← CoarseHighMomentRayPrice.loss_div_eq_lambda 42 beta beta_pos, loss_eq]
  have hh := contains_rat (S := scale) (p := 45949729863572161) (d := 567000000000000000)
    scale_positive (by decide) lambdaBox (by decide)
  convert hh using 1 <;> norm_num [beta]

theorem contains_U0 : Contains scale u0Box U0 := mul_contains scale_positive contains_A contains_rootS
theorem contains_U : Contains scale uBox U := mul_contains scale_positive contains_four contains_rootS

theorem contains_index (j : ℕ) : Contains scale (indexBox j) ((j : ℝ) / resolution) := by
  simpa only [indexBox, Int.cast_natCast] using
    rat_contains scale scale_positive (j : ℤ) (resolution : ℤ) (by exact_mod_cast resolution_pos)

theorem contains_firstGrid (j : ℕ) : Contains scale (firstGridBox j) (firstGrid j) :=
  mul_contains scale_positive contains_U0 (contains_index j)

theorem contains_secondGrid (j : ℕ) : Contains scale (secondGridBox j) (secondGrid j) :=
  add_contains scale_positive contains_U0
    (mul_contains scale_positive (sub_contains scale_positive contains_U contains_U0) (contains_index j))

theorem first_width (j : ℕ) : firstGrid (j + 1) - firstGrid j = U0 / resolution := by
  simp only [firstGrid, Nat.cast_add, Nat.cast_one]
  ring

theorem second_width (j : ℕ) : secondGrid (j + 1) - secondGrid j = (U - U0) / resolution := by
  simp only [secondGrid, Nat.cast_add, Nat.cast_one]
  ring

theorem contains_dt : Contains scale dtBox (U0 / resolution) := by
  simpa only [dtBox, Int.cast_natCast] using
    divInt_contains scale_positive (by exact_mod_cast resolution_pos : (0 : ℤ) < (resolution : ℤ)) contains_U0

theorem contains_dt2 : Contains scale dt2Box ((U - U0) / resolution) := by
  simpa only [dt2Box, Int.cast_natCast] using
    divInt_contains scale_positive (by exact_mod_cast resolution_pos : (0 : ℤ) < (resolution : ℤ))
      (sub_contains scale_positive contains_U contains_U0)

end

end BerryEsseen.ControlEndpointParameters

#print axioms BerryEsseen.ControlEndpointParameters.contains_beta
#print axioms BerryEsseen.ControlEndpointParameters.contains_lambda
#print axioms BerryEsseen.ControlEndpointParameters.contains_firstGrid
#print axioms BerryEsseen.ControlEndpointParameters.spectral_eq
