module

public import BerryEsseen.N2NeededAssembly
public import BerryEsseen.N2NeededIntegerPointwise00
public import BerryEsseen.N2NeededIntegerPointwise01
public import BerryEsseen.N2NeededIntegerPointwise02
public import BerryEsseen.N2NeededIntegerPointwise03
public import BerryEsseen.N2NeededIntegerPointwise04
public import BerryEsseen.N2NeededIntegerPointwise05
public import BerryEsseen.N2NeededIntegerPointwise06
public import BerryEsseen.N2NeededIntegerPointwise07
public import BerryEsseen.N2NeededIntegerPointwise08
public import BerryEsseen.N2NeededIntegerPointwise09
public import BerryEsseen.N2NeededIntegerPointwise10
public import BerryEsseen.N2NeededIntegerPointwise11
public import BerryEsseen.N2NeededIntegerPointwise12

@[expose] public section

/-! 2026-10-29: the complete original 65-row pointwise family and its
actual-law Berry--Esseen conclusion. Every row uses a kernel-checked tree;
the compact support restriction is discharged by the proved extremizer
reduction, and the analytic threshold and third-moment tails are included. -/

namespace BerryEsseen.N2CertifiedBound

theorem pointwiseFamily : N2NeededAssembly.PointwiseFamily := by
  intro i x y hx hy
  fin_cases i
  · exact N2NeededIntegerPointwise00.pointwise 0 x y hx hy
  · exact N2NeededIntegerPointwise00.pointwise 1 x y hx hy
  · exact N2NeededIntegerPointwise00.pointwise 2 x y hx hy
  · exact N2NeededIntegerPointwise00.pointwise 3 x y hx hy
  · exact N2NeededIntegerPointwise00.pointwise 4 x y hx hy
  · exact N2NeededIntegerPointwise01.pointwise 0 x y hx hy
  · exact N2NeededIntegerPointwise01.pointwise 1 x y hx hy
  · exact N2NeededIntegerPointwise01.pointwise 2 x y hx hy
  · exact N2NeededIntegerPointwise01.pointwise 3 x y hx hy
  · exact N2NeededIntegerPointwise01.pointwise 4 x y hx hy
  · exact N2NeededIntegerPointwise02.pointwise 0 x y hx hy
  · exact N2NeededIntegerPointwise02.pointwise 1 x y hx hy
  · exact N2NeededIntegerPointwise02.pointwise 2 x y hx hy
  · exact N2NeededIntegerPointwise02.pointwise 3 x y hx hy
  · exact N2NeededIntegerPointwise02.pointwise 4 x y hx hy
  · exact N2NeededIntegerPointwise03.pointwise 0 x y hx hy
  · exact N2NeededIntegerPointwise03.pointwise 1 x y hx hy
  · exact N2NeededIntegerPointwise03.pointwise 2 x y hx hy
  · exact N2NeededIntegerPointwise03.pointwise 3 x y hx hy
  · exact N2NeededIntegerPointwise03.pointwise 4 x y hx hy
  · exact N2NeededIntegerPointwise04.pointwise 0 x y hx hy
  · exact N2NeededIntegerPointwise04.pointwise 1 x y hx hy
  · exact N2NeededIntegerPointwise04.pointwise 2 x y hx hy
  · exact N2NeededIntegerPointwise04.pointwise 3 x y hx hy
  · exact N2NeededIntegerPointwise04.pointwise 4 x y hx hy
  · exact N2NeededIntegerPointwise05.pointwise 0 x y hx hy
  · exact N2NeededIntegerPointwise05.pointwise 1 x y hx hy
  · exact N2NeededIntegerPointwise05.pointwise 2 x y hx hy
  · exact N2NeededIntegerPointwise05.pointwise 3 x y hx hy
  · exact N2NeededIntegerPointwise05.pointwise 4 x y hx hy
  · exact N2NeededIntegerPointwise06.pointwise 0 x y hx hy
  · exact N2NeededIntegerPointwise06.pointwise 1 x y hx hy
  · exact N2NeededIntegerPointwise06.pointwise 2 x y hx hy
  · exact N2NeededIntegerPointwise06.pointwise 3 x y hx hy
  · exact N2NeededIntegerPointwise06.pointwise 4 x y hx hy
  · exact N2NeededIntegerPointwise07.pointwise 0 x y hx hy
  · exact N2NeededIntegerPointwise07.pointwise 1 x y hx hy
  · exact N2NeededIntegerPointwise07.pointwise 2 x y hx hy
  · exact N2NeededIntegerPointwise07.pointwise 3 x y hx hy
  · exact N2NeededIntegerPointwise07.pointwise 4 x y hx hy
  · exact N2NeededIntegerPointwise08.pointwise 0 x y hx hy
  · exact N2NeededIntegerPointwise08.pointwise 1 x y hx hy
  · exact N2NeededIntegerPointwise08.pointwise 2 x y hx hy
  · exact N2NeededIntegerPointwise08.pointwise 3 x y hx hy
  · exact N2NeededIntegerPointwise08.pointwise 4 x y hx hy
  · exact N2NeededIntegerPointwise09.pointwise 0 x y hx hy
  · exact N2NeededIntegerPointwise09.pointwise 1 x y hx hy
  · exact N2NeededIntegerPointwise09.pointwise 2 x y hx hy
  · exact N2NeededIntegerPointwise09.pointwise 3 x y hx hy
  · exact N2NeededIntegerPointwise09.pointwise 4 x y hx hy
  · exact N2NeededIntegerPointwise10.pointwise 0 x y hx hy
  · exact N2NeededIntegerPointwise10.pointwise 1 x y hx hy
  · exact N2NeededIntegerPointwise10.pointwise 2 x y hx hy
  · exact N2NeededIntegerPointwise10.pointwise 3 x y hx hy
  · exact N2NeededIntegerPointwise10.pointwise 4 x y hx hy
  · exact N2NeededIntegerPointwise11.pointwise 0 x y hx hy
  · exact N2NeededIntegerPointwise11.pointwise 1 x y hx hy
  · exact N2NeededIntegerPointwise11.pointwise 2 x y hx hy
  · exact N2NeededIntegerPointwise11.pointwise 3 x y hx hy
  · exact N2NeededIntegerPointwise11.pointwise 4 x y hx hy
  · exact N2NeededIntegerPointwise12.pointwise 0 x y hx hy
  · exact N2NeededIntegerPointwise12.pointwise 1 x y hx hy
  · exact N2NeededIntegerPointwise12.pointwise 2 x y hx hy
  · exact N2NeededIntegerPointwise12.pointwise 3 x y hx hy
  · exact N2NeededIntegerPointwise12.pointwise 4 x y hx hy

theorem sharp_two : Reflection.AbsoluteClosedBound 2 esseenConstant :=
  N2NeededAssembly.sharp_two_of_pointwise pointwiseFamily

end BerryEsseen.N2CertifiedBound

#print axioms BerryEsseen.N2CertifiedBound.pointwiseFamily
#print axioms BerryEsseen.N2CertifiedBound.sharp_two
