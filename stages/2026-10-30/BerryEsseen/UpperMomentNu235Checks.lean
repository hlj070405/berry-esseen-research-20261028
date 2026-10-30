module

public import BerryEsseen.FixedPointUpperMomentExp
public import BerryEsseen.FixedPointRecurrence
public import BerryEsseen.UpperMomentN47ScalarData
public import BerryEsseen.UpperMomentN47KernelWitnesses
public import BerryEsseen.UpperMomentNu235Data
public import Mathlib.Data.List.Enum

@[expose] public section

/-! 2026-10-30: only new-s gates for the real nu=235/4 endpoint.
The same already-checked old G/W rows are zipped directly with the new
P/H/D data. All numerical traversals are linear, including the recurrence.
Old G/W/Gamma/rate/kernel gates are neither copied nor recomputed here. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BerryEsseen.UpperMomentNu235Checks

open FixedPointEnclosure FixedPointArithmetic FixedPointUpperMomentRate FixedPointUpperMomentExp
open FixedFourierConstants (scale scale_positive)
open UpperMomentNu235Data

def lift18 (z : ℤ) : ℤ := z * factor
def ub : Box := rat scale scale_positive 7361 4000 (by decide)
def sb : Box := rat scale scale_positive 940000000 54184321 (by decide)
abbrev sBox : Box := sb
def dt1 : Box := rat scale scale_positive 1 1280 (by decide)
def dt2 : Box := rat scale scale_positive 1 320 (by decide)
def firstLeft (j : ℕ) : Box := rat scale scale_positive (j : ℤ) 1280 (by decide)
def firstRight (j : ℕ) : Box := rat scale scale_positive ((j + 1 : ℕ) : ℤ) 1280 (by decide)
def firstGridBox (j : ℕ) : Box := firstLeft j
def cutoffBox : Box := rat scale scale_positive 4 5 (by decide)

abbrev ScalarPair := UpperMomentN47ScalarData.FirstRow × FirstExpRow
def scalarPairs : List ScalarPair := UpperMomentN47ScalarData.firstData.zip firstData

def scalarPairCheck (p : ScalarPair) : Bool :=
  decide (p.1.index = p.2.index) &&
    (forcingCheck ub sb (lift18 p.1.G) (lift18 p.1.W) (lift18 p.2.P) (lift18 p.2.H) &&
      decayCheck sb (firstLeft p.2.index) (firstRight p.2.index) (lift18 p.2.D))

def scalarTableCheck : Bool := scalarPairs.all scalarPairCheck

theorem scalarPairs_length : scalarPairs.length = 1024 := by
  simp only [scalarPairs, List.length_zip, UpperMomentN47ScalarData.firstData_length,
    firstData_length, min_self]

theorem scalarPairs_indices : scalarPairs.map (fun p => (p.1.index, p.2.index)) =
    (List.range 1024).map (fun j => (j, j)) := by decide +kernel

theorem scalar_table_checked : scalarTableCheck = true := by decide +kernel

theorem scalar_pair_checked {p : ScalarPair} (hp : p ∈ scalarPairs) :
    scalarPairCheck p = true := List.all_eq_true.mp scalar_table_checked p hp

theorem scalar_pair_aligned {p : ScalarPair} (hp : p ∈ scalarPairs) : p.1.index = p.2.index :=
  of_decide_eq_true (Bool.and_eq_true_iff.mp (scalar_pair_checked hp)).1

theorem forcing_checked {p : ScalarPair} (hp : p ∈ scalarPairs) :
    forcingCheck ub sb (lift18 p.1.G) (lift18 p.1.W) (lift18 p.2.P) (lift18 p.2.H) = true :=
  (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (scalar_pair_checked hp)).2).1

theorem decay_checked {p : ScalarPair} (hp : p ∈ scalarPairs) :
    decayCheck sb (firstLeft p.2.index) (firstRight p.2.index) (lift18 p.2.D) = true :=
  (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (scalar_pair_checked hp)).2).2

def recurrenceTableCheck : Bool := FixedPointRecurrence.chainCheck
  (FixedPointRecurrence.updateCheck dt1) (R18.map lift18)
  (firstData.map (fun r => lift18 r.H)) (firstData.map (fun r => lift18 r.D))

abbrev FirstPair := ((FirstExpRow × ℤ) × ℤ) × ℤ
def firstPairs : List FirstPair :=
  ((firstData.zip R18).zip UpperMomentN47KernelWitnesses.kernel118).zip row118

def firstPairCheck (p : FirstPair) (j : ℕ) : Bool :=
  decide (p.1.1.1.index = j) &&
    (if j = 0 then true else firstRowCheck dt1 (lift18 p.1.2) (lift18 p.1.1.2)
      (lift18 p.1.1.1.H) (lift18 p.2))

def firstTableCheck : Bool := firstPairs.zipIdx.all (fun p => firstPairCheck p.1 p.2)

abbrev PowerPair := UpperMomentN47ScalarData.T2Row × ℤ
def secondPowerPairs : List PowerPair := UpperMomentN47ScalarData.T2data.zip Q218
def secondPowerPairCheck (p : PowerPair) : Bool := powerCheck sb (lift18 p.1.G) (lift18 p.2)
def secondPowerTableCheck : Bool := secondPowerPairs.all secondPowerPairCheck

abbrev ProductPair := (ℤ × ℤ) × ℤ
def secondPairs : List ProductPair := (UpperMomentN47KernelWitnesses.kernel218.zip Q218).zip row218
def productPairCheck (dt : Box) (p : ProductPair) : Bool :=
  productCheck dt (lift18 p.1.1) (lift18 p.1.2) (lift18 p.2)
def secondTableCheck : Bool := secondPairs.all (productPairCheck dt2)

def gaussianTableCheck : Bool := E318.zipIdx.all (fun p =>
  gaussianCheck sb (firstGridBox p.2) (lift18 p.1))

def thirdPairs : List ProductPair := (UpperMomentN47KernelWitnesses.correction18.zip E318).zip row318
def thirdTableCheck : Bool := thirdPairs.all (productPairCheck dt1)

theorem firstPairs_length : firstPairs.length = 1024 := by
  simp only [firstPairs, List.length_zip, firstData_length, R18_length,
    UpperMomentN47KernelWitnesses.kernel118_length, row118_length,
    min_eq_left (by decide : 1024 ≤ 1025), min_self]

theorem secondPowerPairs_length : secondPowerPairs.length = 1024 := by
  simp only [secondPowerPairs, List.length_zip, UpperMomentN47ScalarData.T2data_length,
    Q218_length, min_self]

theorem secondPairs_length : secondPairs.length = 1024 := by
  simp only [secondPairs, List.length_zip, UpperMomentN47KernelWitnesses.kernel218_length,
    Q218_length, row218_length, min_self]

theorem thirdPairs_length : thirdPairs.length = 1024 := by
  simp only [thirdPairs, List.length_zip, UpperMomentN47KernelWitnesses.correction18_length,
    E318_length, row318_length, min_self]

theorem recurrence_table_checked : recurrenceTableCheck = true := by decide +kernel
theorem first_table_checked : firstTableCheck = true := by decide +kernel
theorem second_power_table_checked : secondPowerTableCheck = true := by decide +kernel
theorem second_table_checked : secondTableCheck = true := by decide +kernel
theorem gaussian_table_checked : gaussianTableCheck = true := by decide +kernel
theorem third_table_checked : thirdTableCheck = true := by decide +kernel
theorem tail_exp_checked : gaussianCheck sb cutoffBox (lift18 tailE18) = true := by decide +kernel

theorem first_pair_checked {p : FirstPair} {j : ℕ} (hp : (p, j) ∈ firstPairs.zipIdx) :
    firstPairCheck p j = true := List.all_eq_true.mp first_table_checked (p, j) hp

theorem first_pair_aligned {p : FirstPair} {j : ℕ} (hp : (p, j) ∈ firstPairs.zipIdx) :
    p.1.1.1.index = j := of_decide_eq_true (Bool.and_eq_true_iff.mp (first_pair_checked hp)).1

theorem first_row_checked {p : FirstPair} {j : ℕ} (hp : (p, j) ∈ firstPairs.zipIdx) (hj : 0 < j) :
    firstRowCheck dt1 (lift18 p.1.2) (lift18 p.1.1.2) (lift18 p.1.1.1.H) (lift18 p.2) = true := by
  have hh := (Bool.and_eq_true_iff.mp (first_pair_checked hp)).2
  simpa only [if_neg (Nat.ne_of_gt hj)] using hh

theorem second_power_pair_checked {p : PowerPair} (hp : p ∈ secondPowerPairs) :
    powerCheck sb (lift18 p.1.G) (lift18 p.2) = true :=
  List.all_eq_true.mp second_power_table_checked p hp

theorem second_pair_checked {p : ProductPair} (hp : p ∈ secondPairs) :
    productCheck dt2 (lift18 p.1.1) (lift18 p.1.2) (lift18 p.2) = true :=
  List.all_eq_true.mp second_table_checked p hp

theorem gaussian_pair_checked {e : ℤ} {j : ℕ} (hp : (e, j) ∈ E318.zipIdx) :
    gaussianCheck sb (firstGridBox j) (lift18 e) = true :=
  List.all_eq_true.mp gaussian_table_checked (e, j) hp

theorem third_pair_checked {p : ProductPair} (hp : p ∈ thirdPairs) :
    productCheck dt1 (lift18 p.1.1) (lift18 p.1.2) (lift18 p.2) = true :=
  List.all_eq_true.mp third_table_checked p hp

theorem initial_r_zero : R18.head! = 0 := by decide +kernel
theorem head_row_matches : row118.head! = analyticHead18 := by decide +kernel
theorem row1_sum : row118.sum = 37288559317894878 := by decide +kernel
theorem row2_sum : row218.sum = 9045202206994407 := by decide +kernel
theorem row3_sum : row318.sum = 143612906406083284 := by decide +kernel

end BerryEsseen.UpperMomentNu235Checks

#print axioms BerryEsseen.UpperMomentNu235Checks.scalarPairs_indices
#print axioms BerryEsseen.UpperMomentNu235Checks.scalar_table_checked
#print axioms BerryEsseen.UpperMomentNu235Checks.recurrence_table_checked
#print axioms BerryEsseen.UpperMomentNu235Checks.first_table_checked
#print axioms BerryEsseen.UpperMomentNu235Checks.second_power_table_checked
#print axioms BerryEsseen.UpperMomentNu235Checks.second_table_checked
#print axioms BerryEsseen.UpperMomentNu235Checks.gaussian_table_checked
#print axioms BerryEsseen.UpperMomentNu235Checks.third_table_checked
#print axioms BerryEsseen.UpperMomentNu235Checks.tail_exp_checked
#print axioms BerryEsseen.UpperMomentNu235Checks.row1_sum
#print axioms BerryEsseen.UpperMomentNu235Checks.row2_sum
#print axioms BerryEsseen.UpperMomentNu235Checks.row3_sum
