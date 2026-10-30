module

public import BerryEsseen.N2NeededData

@[expose] public section

/-! 2026-10-29: exact common coefficient/coordinate denominators.
Threshold numerators are tied to the same original Data.upperQ interval. -/

namespace BerryEsseen.N2NeededIntegerData

def D : ℕ := 549755813888000
def S : ℕ := 256
def tNum (i : Fin 65) : ℤ := -44 + (i.val : ℤ)

theorem D_pos : 0 < D := by decide +kernel
theorem S_pos : 0 < S := by decide +kernel

theorem upperQ_eq_tNum (i : Fin 65) :
    N2NeededData.upperQ i = (tNum i : ℚ) / 20 := by
  simp [N2NeededData.upperQ, tNum]

end BerryEsseen.N2NeededIntegerData

#print axioms BerryEsseen.N2NeededIntegerData.D_pos
#print axioms BerryEsseen.N2NeededIntegerData.S_pos
#print axioms BerryEsseen.N2NeededIntegerData.upperQ_eq_tNum
