module

public import BerryEsseen.FixedPointUpperMomentExp
public import BerryEsseen.FixedPointRecurrence
public import BerryEsseen.UpperMomentN47ScalarData
public import BerryEsseen.UpperMomentN47KernelWitnesses
public import BerryEsseen.UpperMomentN47IntegralWitnesses
public import Mathlib.Data.List.Enum

@[expose] public section

/-! 2026-10-30: fixed n47 numerical gates only. All traversals are linear
zips of saved witnesses. True integral/CDF clients remain separate. -/

set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace BerryEsseen.UpperMomentN47IntegralChecks

open FixedPointEnclosure FixedPointArithmetic FixedPointUpperMomentExp
open FixedFourierConstants (scale scale_positive)
open UpperMomentN47IntegralWitnesses

def lift18 (z : ℤ) : ℤ := z * factor
def sb : Box := rat scale scale_positive 752000000 54184321 (by decide)
def dt1 : Box := rat scale scale_positive 1 1280 (by decide)
def dt2 : Box := rat scale scale_positive 1 320 (by decide)
def firstGridBox (j : ℕ) : Box := rat scale scale_positive j 1280 (by decide)
def cutoffBox : Box := rat scale scale_positive 4 5 (by decide)

def recurrenceTableCheck : Bool := FixedPointRecurrence.chainCheck
  (FixedPointRecurrence.updateCheck dt1) (R18.map lift18)
  (UpperMomentN47ScalarData.firstData.map (fun r => lift18 r.H))
  (UpperMomentN47ScalarData.firstData.map (fun r => lift18 r.D))

def firstPairs := ((UpperMomentN47ScalarData.firstData.zip R18).zip
  UpperMomentN47KernelWitnesses.kernel118).zip row118

def firstTableCheck : Bool := firstPairs.zipIdx.all (fun p =>
  if p.2 = 0 then true else
    firstRowCheck dt1 (lift18 p.1.1.2) (lift18 p.1.1.1.2)
      (lift18 p.1.1.1.1.H) (lift18 p.1.2))

def secondPowerTableCheck : Bool :=
  (UpperMomentN47ScalarData.T2data.zip Q218).all
    (fun p => powerCheck sb (lift18 p.1.G) (lift18 p.2))

def secondPairs := (UpperMomentN47KernelWitnesses.kernel218.zip Q218).zip row218
def secondTableCheck : Bool := secondPairs.all (fun p =>
  productCheck dt2 (lift18 p.1.1) (lift18 p.1.2) (lift18 p.2))

def gaussianTableCheck : Bool := E318.zipIdx.all (fun p =>
  gaussianCheck sb (firstGridBox p.2) (lift18 p.1))

def thirdPairs := (UpperMomentN47KernelWitnesses.correction18.zip E318).zip row318
def thirdTableCheck : Bool := thirdPairs.all (fun p =>
  productCheck dt1 (lift18 p.1.1) (lift18 p.1.2) (lift18 p.2))

theorem recurrence_table_checked : recurrenceTableCheck = true := by decide +kernel
theorem first_table_checked : firstTableCheck = true := by decide +kernel
theorem second_power_table_checked : secondPowerTableCheck = true := by decide +kernel
theorem second_table_checked : secondTableCheck = true := by decide +kernel
theorem gaussian_table_checked : gaussianTableCheck = true := by decide +kernel
theorem third_table_checked : thirdTableCheck = true := by decide +kernel
theorem tail_exp_checked : gaussianCheck sb cutoffBox (lift18 tailE18) = true := by decide +kernel

theorem initial_r_zero : R18.head! = 0 := by decide
theorem row1_sum : row118.sum = 41180332269245895 := by decide +kernel
theorem row2_sum : row218.sum = 11559820377982515 := by decide +kernel
theorem row3_sum : row318.sum = 159389667399613223 := by decide +kernel

end BerryEsseen.UpperMomentN47IntegralChecks

#print axioms BerryEsseen.UpperMomentN47IntegralChecks.recurrence_table_checked
#print axioms BerryEsseen.UpperMomentN47IntegralChecks.first_table_checked
#print axioms BerryEsseen.UpperMomentN47IntegralChecks.second_power_table_checked
#print axioms BerryEsseen.UpperMomentN47IntegralChecks.gaussian_table_checked
#print axioms BerryEsseen.UpperMomentN47IntegralChecks.tail_exp_checked
