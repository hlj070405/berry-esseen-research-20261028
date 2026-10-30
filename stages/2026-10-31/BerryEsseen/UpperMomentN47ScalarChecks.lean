module

public import BerryEsseen.FixedPointUpperMomentCoarseW

public import BerryEsseen.UpperMomentN47ScalarData

@[expose] public section

set_option maxRecDepth 100000

set_option maxHeartbeats 0

namespace BerryEsseen.UpperMomentN47ScalarChecks

open FixedPointEnclosure FixedPointArithmetic FixedPointUpperMomentRate FixedPointUpperMomentCoarseW

open FixedFourierConstants (scale scale_positive)

open UpperMomentN47ScalarData

def ub : Box := (rat scale scale_positive (7361 : ℤ) (4000 : ℤ) (by decide))

def sb : Box := (rat scale scale_positive (752000000 : ℤ) (54184321 : ℤ) (by decide))

def lift18 (z : ℤ) : ℤ := z * 10 ^ 22

def gc : ℤ := lift18 gamma18

def firstLeft (j : Nat) : Box := rat scale scale_positive (j : ℤ) 1280 (by decide)

def firstRight (j : Nat) : Box := rat scale scale_positive ((j+1 : Nat) : ℤ) 1280 (by decide)

def T2left (j : Nat) : Box := rat scale scale_positive ((256+j : Nat) : ℤ) 320 (by decide)

def T2right (j : Nat) : Box := rat scale scale_positive ((257+j : Nat) : ℤ) 320 (by decide)

def firstCheck (r : FirstRow) : Bool :=
  coarseForcingCellCheck ub sb (firstLeft r.index) (firstRight r.index) gc
    (lift18 r.norm) (lift18 r.M4) (lift18 r.MR) (lift18 r.G)
    (lift18 r.W) (lift18 r.P) (lift18 r.H) &&
  decayCheck sb (firstLeft r.index) (firstRight r.index) (lift18 r.D)

def T2check (r : T2Row) : Bool :=
  rateCheck ub (T2left r.index) (T2right r.index) gc
    (lift18 r.norm) (lift18 r.M4) (lift18 r.MR) (lift18 r.G)

theorem gamma_checked : gammaCheck ub gc = true := by decide +kernel

theorem firstChunk0000_checked : firstChunk0000.all firstCheck = true := by decide +kernel

theorem firstChunk0008_checked : firstChunk0008.all firstCheck = true := by decide +kernel

theorem firstChunk0016_checked : firstChunk0016.all firstCheck = true := by decide +kernel

theorem firstChunk0024_checked : firstChunk0024.all firstCheck = true := by decide +kernel

theorem firstChunk0032_checked : firstChunk0032.all firstCheck = true := by decide +kernel

theorem firstChunk0040_checked : firstChunk0040.all firstCheck = true := by decide +kernel

theorem firstChunk0048_checked : firstChunk0048.all firstCheck = true := by decide +kernel

theorem firstChunk0056_checked : firstChunk0056.all firstCheck = true := by decide +kernel

theorem firstChunk0064_checked : firstChunk0064.all firstCheck = true := by decide +kernel

theorem firstChunk0072_checked : firstChunk0072.all firstCheck = true := by decide +kernel

theorem firstChunk0080_checked : firstChunk0080.all firstCheck = true := by decide +kernel

theorem firstChunk0088_checked : firstChunk0088.all firstCheck = true := by decide +kernel

theorem firstChunk0096_checked : firstChunk0096.all firstCheck = true := by decide +kernel

theorem firstChunk0104_checked : firstChunk0104.all firstCheck = true := by decide +kernel

theorem firstChunk0112_checked : firstChunk0112.all firstCheck = true := by decide +kernel

theorem firstChunk0120_checked : firstChunk0120.all firstCheck = true := by decide +kernel

theorem firstChunk0128_checked : firstChunk0128.all firstCheck = true := by decide +kernel

theorem firstChunk0136_checked : firstChunk0136.all firstCheck = true := by decide +kernel

theorem firstChunk0144_checked : firstChunk0144.all firstCheck = true := by decide +kernel

theorem firstChunk0152_checked : firstChunk0152.all firstCheck = true := by decide +kernel

theorem firstChunk0160_checked : firstChunk0160.all firstCheck = true := by decide +kernel

theorem firstChunk0168_checked : firstChunk0168.all firstCheck = true := by decide +kernel

theorem firstChunk0176_checked : firstChunk0176.all firstCheck = true := by decide +kernel

theorem firstChunk0184_checked : firstChunk0184.all firstCheck = true := by decide +kernel

theorem firstChunk0192_checked : firstChunk0192.all firstCheck = true := by decide +kernel

theorem firstChunk0200_checked : firstChunk0200.all firstCheck = true := by decide +kernel

theorem firstChunk0208_checked : firstChunk0208.all firstCheck = true := by decide +kernel

theorem firstChunk0216_checked : firstChunk0216.all firstCheck = true := by decide +kernel

theorem firstChunk0224_checked : firstChunk0224.all firstCheck = true := by decide +kernel

theorem firstChunk0232_checked : firstChunk0232.all firstCheck = true := by decide +kernel

theorem firstChunk0240_checked : firstChunk0240.all firstCheck = true := by decide +kernel

theorem firstChunk0248_checked : firstChunk0248.all firstCheck = true := by decide +kernel

theorem firstChunk0256_checked : firstChunk0256.all firstCheck = true := by decide +kernel

theorem firstChunk0264_checked : firstChunk0264.all firstCheck = true := by decide +kernel

theorem firstChunk0272_checked : firstChunk0272.all firstCheck = true := by decide +kernel

theorem firstChunk0280_checked : firstChunk0280.all firstCheck = true := by decide +kernel

theorem firstChunk0288_checked : firstChunk0288.all firstCheck = true := by decide +kernel

theorem firstChunk0296_checked : firstChunk0296.all firstCheck = true := by decide +kernel

theorem firstChunk0304_checked : firstChunk0304.all firstCheck = true := by decide +kernel

theorem firstChunk0312_checked : firstChunk0312.all firstCheck = true := by decide +kernel

theorem firstChunk0320_checked : firstChunk0320.all firstCheck = true := by decide +kernel

theorem firstChunk0328_checked : firstChunk0328.all firstCheck = true := by decide +kernel

theorem firstChunk0336_checked : firstChunk0336.all firstCheck = true := by decide +kernel

theorem firstChunk0344_checked : firstChunk0344.all firstCheck = true := by decide +kernel

theorem firstChunk0352_checked : firstChunk0352.all firstCheck = true := by decide +kernel

theorem firstChunk0360_checked : firstChunk0360.all firstCheck = true := by decide +kernel

theorem firstChunk0368_checked : firstChunk0368.all firstCheck = true := by decide +kernel

theorem firstChunk0376_checked : firstChunk0376.all firstCheck = true := by decide +kernel

theorem firstChunk0384_checked : firstChunk0384.all firstCheck = true := by decide +kernel

theorem firstChunk0392_checked : firstChunk0392.all firstCheck = true := by decide +kernel

theorem firstChunk0400_checked : firstChunk0400.all firstCheck = true := by decide +kernel

theorem firstChunk0408_checked : firstChunk0408.all firstCheck = true := by decide +kernel

theorem firstChunk0416_checked : firstChunk0416.all firstCheck = true := by decide +kernel

theorem firstChunk0424_checked : firstChunk0424.all firstCheck = true := by decide +kernel

theorem firstChunk0432_checked : firstChunk0432.all firstCheck = true := by decide +kernel

theorem firstChunk0440_checked : firstChunk0440.all firstCheck = true := by decide +kernel

theorem firstChunk0448_checked : firstChunk0448.all firstCheck = true := by decide +kernel

theorem firstChunk0456_checked : firstChunk0456.all firstCheck = true := by decide +kernel

theorem firstChunk0464_checked : firstChunk0464.all firstCheck = true := by decide +kernel

theorem firstChunk0472_checked : firstChunk0472.all firstCheck = true := by decide +kernel

theorem firstChunk0480_checked : firstChunk0480.all firstCheck = true := by decide +kernel

theorem firstChunk0488_checked : firstChunk0488.all firstCheck = true := by decide +kernel

theorem firstChunk0496_checked : firstChunk0496.all firstCheck = true := by decide +kernel

theorem firstChunk0504_checked : firstChunk0504.all firstCheck = true := by decide +kernel

theorem firstChunk0512_checked : firstChunk0512.all firstCheck = true := by decide +kernel

theorem firstChunk0520_checked : firstChunk0520.all firstCheck = true := by decide +kernel

theorem firstChunk0528_checked : firstChunk0528.all firstCheck = true := by decide +kernel

theorem firstChunk0536_checked : firstChunk0536.all firstCheck = true := by decide +kernel

theorem firstChunk0544_checked : firstChunk0544.all firstCheck = true := by decide +kernel

theorem firstChunk0552_checked : firstChunk0552.all firstCheck = true := by decide +kernel

theorem firstChunk0560_checked : firstChunk0560.all firstCheck = true := by decide +kernel

theorem firstChunk0568_checked : firstChunk0568.all firstCheck = true := by decide +kernel

theorem firstChunk0576_checked : firstChunk0576.all firstCheck = true := by decide +kernel

theorem firstChunk0584_checked : firstChunk0584.all firstCheck = true := by decide +kernel

theorem firstChunk0592_checked : firstChunk0592.all firstCheck = true := by decide +kernel

theorem firstChunk0600_checked : firstChunk0600.all firstCheck = true := by decide +kernel

theorem firstChunk0608_checked : firstChunk0608.all firstCheck = true := by decide +kernel

theorem firstChunk0616_checked : firstChunk0616.all firstCheck = true := by decide +kernel

theorem firstChunk0624_checked : firstChunk0624.all firstCheck = true := by decide +kernel

theorem firstChunk0632_checked : firstChunk0632.all firstCheck = true := by decide +kernel

theorem firstChunk0640_checked : firstChunk0640.all firstCheck = true := by decide +kernel

theorem firstChunk0648_checked : firstChunk0648.all firstCheck = true := by decide +kernel

theorem firstChunk0656_checked : firstChunk0656.all firstCheck = true := by decide +kernel

theorem firstChunk0664_checked : firstChunk0664.all firstCheck = true := by decide +kernel

theorem firstChunk0672_checked : firstChunk0672.all firstCheck = true := by decide +kernel

theorem firstChunk0680_checked : firstChunk0680.all firstCheck = true := by decide +kernel

theorem firstChunk0688_checked : firstChunk0688.all firstCheck = true := by decide +kernel

theorem firstChunk0696_checked : firstChunk0696.all firstCheck = true := by decide +kernel

theorem firstChunk0704_checked : firstChunk0704.all firstCheck = true := by decide +kernel

theorem firstChunk0712_checked : firstChunk0712.all firstCheck = true := by decide +kernel

theorem firstChunk0720_checked : firstChunk0720.all firstCheck = true := by decide +kernel

theorem firstChunk0728_checked : firstChunk0728.all firstCheck = true := by decide +kernel

theorem firstChunk0736_checked : firstChunk0736.all firstCheck = true := by decide +kernel

theorem firstChunk0744_checked : firstChunk0744.all firstCheck = true := by decide +kernel

theorem firstChunk0752_checked : firstChunk0752.all firstCheck = true := by decide +kernel

theorem firstChunk0760_checked : firstChunk0760.all firstCheck = true := by decide +kernel

theorem firstChunk0768_checked : firstChunk0768.all firstCheck = true := by decide +kernel

theorem firstChunk0776_checked : firstChunk0776.all firstCheck = true := by decide +kernel

theorem firstChunk0784_checked : firstChunk0784.all firstCheck = true := by decide +kernel

theorem firstChunk0792_checked : firstChunk0792.all firstCheck = true := by decide +kernel

theorem firstChunk0800_checked : firstChunk0800.all firstCheck = true := by decide +kernel

theorem firstChunk0808_checked : firstChunk0808.all firstCheck = true := by decide +kernel

theorem firstChunk0816_checked : firstChunk0816.all firstCheck = true := by decide +kernel

theorem firstChunk0824_checked : firstChunk0824.all firstCheck = true := by decide +kernel

theorem firstChunk0832_checked : firstChunk0832.all firstCheck = true := by decide +kernel

theorem firstChunk0840_checked : firstChunk0840.all firstCheck = true := by decide +kernel

theorem firstChunk0848_checked : firstChunk0848.all firstCheck = true := by decide +kernel

theorem firstChunk0856_checked : firstChunk0856.all firstCheck = true := by decide +kernel

theorem firstChunk0864_checked : firstChunk0864.all firstCheck = true := by decide +kernel

theorem firstChunk0872_checked : firstChunk0872.all firstCheck = true := by decide +kernel

theorem firstChunk0880_checked : firstChunk0880.all firstCheck = true := by decide +kernel

theorem firstChunk0888_checked : firstChunk0888.all firstCheck = true := by decide +kernel

theorem firstChunk0896_checked : firstChunk0896.all firstCheck = true := by decide +kernel

theorem firstChunk0904_checked : firstChunk0904.all firstCheck = true := by decide +kernel

theorem firstChunk0912_checked : firstChunk0912.all firstCheck = true := by decide +kernel

theorem firstChunk0920_checked : firstChunk0920.all firstCheck = true := by decide +kernel

theorem firstChunk0928_checked : firstChunk0928.all firstCheck = true := by decide +kernel

theorem firstChunk0936_checked : firstChunk0936.all firstCheck = true := by decide +kernel

theorem firstChunk0944_checked : firstChunk0944.all firstCheck = true := by decide +kernel

theorem firstChunk0952_checked : firstChunk0952.all firstCheck = true := by decide +kernel

theorem firstChunk0960_checked : firstChunk0960.all firstCheck = true := by decide +kernel

theorem firstChunk0968_checked : firstChunk0968.all firstCheck = true := by decide +kernel

theorem firstChunk0976_checked : firstChunk0976.all firstCheck = true := by decide +kernel

theorem firstChunk0984_checked : firstChunk0984.all firstCheck = true := by decide +kernel

theorem firstChunk0992_checked : firstChunk0992.all firstCheck = true := by decide +kernel

theorem firstChunk1000_checked : firstChunk1000.all firstCheck = true := by decide +kernel

theorem firstChunk1008_checked : firstChunk1008.all firstCheck = true := by decide +kernel

theorem firstChunk1016_checked : firstChunk1016.all firstCheck = true := by decide +kernel

theorem T2chunk0000_checked : T2chunk0000.all T2check = true := by decide +kernel

theorem T2chunk0008_checked : T2chunk0008.all T2check = true := by decide +kernel

theorem T2chunk0016_checked : T2chunk0016.all T2check = true := by decide +kernel

theorem T2chunk0024_checked : T2chunk0024.all T2check = true := by decide +kernel

theorem T2chunk0032_checked : T2chunk0032.all T2check = true := by decide +kernel

theorem T2chunk0040_checked : T2chunk0040.all T2check = true := by decide +kernel

theorem T2chunk0048_checked : T2chunk0048.all T2check = true := by decide +kernel

theorem T2chunk0056_checked : T2chunk0056.all T2check = true := by decide +kernel

theorem T2chunk0064_checked : T2chunk0064.all T2check = true := by decide +kernel

theorem T2chunk0072_checked : T2chunk0072.all T2check = true := by decide +kernel

theorem T2chunk0080_checked : T2chunk0080.all T2check = true := by decide +kernel

theorem T2chunk0088_checked : T2chunk0088.all T2check = true := by decide +kernel

theorem T2chunk0096_checked : T2chunk0096.all T2check = true := by decide +kernel

theorem T2chunk0104_checked : T2chunk0104.all T2check = true := by decide +kernel

theorem T2chunk0112_checked : T2chunk0112.all T2check = true := by decide +kernel

theorem T2chunk0120_checked : T2chunk0120.all T2check = true := by decide +kernel

theorem T2chunk0128_checked : T2chunk0128.all T2check = true := by decide +kernel

theorem T2chunk0136_checked : T2chunk0136.all T2check = true := by decide +kernel

theorem T2chunk0144_checked : T2chunk0144.all T2check = true := by decide +kernel

theorem T2chunk0152_checked : T2chunk0152.all T2check = true := by decide +kernel

theorem T2chunk0160_checked : T2chunk0160.all T2check = true := by decide +kernel

theorem T2chunk0168_checked : T2chunk0168.all T2check = true := by decide +kernel

theorem T2chunk0176_checked : T2chunk0176.all T2check = true := by decide +kernel

theorem T2chunk0184_checked : T2chunk0184.all T2check = true := by decide +kernel

theorem T2chunk0192_checked : T2chunk0192.all T2check = true := by decide +kernel

theorem T2chunk0200_checked : T2chunk0200.all T2check = true := by decide +kernel

theorem T2chunk0208_checked : T2chunk0208.all T2check = true := by decide +kernel

theorem T2chunk0216_checked : T2chunk0216.all T2check = true := by decide +kernel

theorem T2chunk0224_checked : T2chunk0224.all T2check = true := by decide +kernel

theorem T2chunk0232_checked : T2chunk0232.all T2check = true := by decide +kernel

theorem T2chunk0240_checked : T2chunk0240.all T2check = true := by decide +kernel

theorem T2chunk0248_checked : T2chunk0248.all T2check = true := by decide +kernel

theorem T2chunk0256_checked : T2chunk0256.all T2check = true := by decide +kernel

theorem T2chunk0264_checked : T2chunk0264.all T2check = true := by decide +kernel

theorem T2chunk0272_checked : T2chunk0272.all T2check = true := by decide +kernel

theorem T2chunk0280_checked : T2chunk0280.all T2check = true := by decide +kernel

theorem T2chunk0288_checked : T2chunk0288.all T2check = true := by decide +kernel

theorem T2chunk0296_checked : T2chunk0296.all T2check = true := by decide +kernel

theorem T2chunk0304_checked : T2chunk0304.all T2check = true := by decide +kernel

theorem T2chunk0312_checked : T2chunk0312.all T2check = true := by decide +kernel

theorem T2chunk0320_checked : T2chunk0320.all T2check = true := by decide +kernel

theorem T2chunk0328_checked : T2chunk0328.all T2check = true := by decide +kernel

theorem T2chunk0336_checked : T2chunk0336.all T2check = true := by decide +kernel

theorem T2chunk0344_checked : T2chunk0344.all T2check = true := by decide +kernel

theorem T2chunk0352_checked : T2chunk0352.all T2check = true := by decide +kernel

theorem T2chunk0360_checked : T2chunk0360.all T2check = true := by decide +kernel

theorem T2chunk0368_checked : T2chunk0368.all T2check = true := by decide +kernel

theorem T2chunk0376_checked : T2chunk0376.all T2check = true := by decide +kernel

theorem T2chunk0384_checked : T2chunk0384.all T2check = true := by decide +kernel

theorem T2chunk0392_checked : T2chunk0392.all T2check = true := by decide +kernel

theorem T2chunk0400_checked : T2chunk0400.all T2check = true := by decide +kernel

theorem T2chunk0408_checked : T2chunk0408.all T2check = true := by decide +kernel

theorem T2chunk0416_checked : T2chunk0416.all T2check = true := by decide +kernel

theorem T2chunk0424_checked : T2chunk0424.all T2check = true := by decide +kernel

theorem T2chunk0432_checked : T2chunk0432.all T2check = true := by decide +kernel

theorem T2chunk0440_checked : T2chunk0440.all T2check = true := by decide +kernel

theorem T2chunk0448_checked : T2chunk0448.all T2check = true := by decide +kernel

theorem T2chunk0456_checked : T2chunk0456.all T2check = true := by decide +kernel

theorem T2chunk0464_checked : T2chunk0464.all T2check = true := by decide +kernel

theorem T2chunk0472_checked : T2chunk0472.all T2check = true := by decide +kernel

theorem T2chunk0480_checked : T2chunk0480.all T2check = true := by decide +kernel

theorem T2chunk0488_checked : T2chunk0488.all T2check = true := by decide +kernel

theorem T2chunk0496_checked : T2chunk0496.all T2check = true := by decide +kernel

theorem T2chunk0504_checked : T2chunk0504.all T2check = true := by decide +kernel

theorem T2chunk0512_checked : T2chunk0512.all T2check = true := by decide +kernel

theorem T2chunk0520_checked : T2chunk0520.all T2check = true := by decide +kernel

theorem T2chunk0528_checked : T2chunk0528.all T2check = true := by decide +kernel

theorem T2chunk0536_checked : T2chunk0536.all T2check = true := by decide +kernel

theorem T2chunk0544_checked : T2chunk0544.all T2check = true := by decide +kernel

theorem T2chunk0552_checked : T2chunk0552.all T2check = true := by decide +kernel

theorem T2chunk0560_checked : T2chunk0560.all T2check = true := by decide +kernel

theorem T2chunk0568_checked : T2chunk0568.all T2check = true := by decide +kernel

theorem T2chunk0576_checked : T2chunk0576.all T2check = true := by decide +kernel

theorem T2chunk0584_checked : T2chunk0584.all T2check = true := by decide +kernel

theorem T2chunk0592_checked : T2chunk0592.all T2check = true := by decide +kernel

theorem T2chunk0600_checked : T2chunk0600.all T2check = true := by decide +kernel

theorem T2chunk0608_checked : T2chunk0608.all T2check = true := by decide +kernel

theorem T2chunk0616_checked : T2chunk0616.all T2check = true := by decide +kernel

theorem T2chunk0624_checked : T2chunk0624.all T2check = true := by decide +kernel

theorem T2chunk0632_checked : T2chunk0632.all T2check = true := by decide +kernel

theorem T2chunk0640_checked : T2chunk0640.all T2check = true := by decide +kernel

theorem T2chunk0648_checked : T2chunk0648.all T2check = true := by decide +kernel

theorem T2chunk0656_checked : T2chunk0656.all T2check = true := by decide +kernel

theorem T2chunk0664_checked : T2chunk0664.all T2check = true := by decide +kernel

theorem T2chunk0672_checked : T2chunk0672.all T2check = true := by decide +kernel

theorem T2chunk0680_checked : T2chunk0680.all T2check = true := by decide +kernel

theorem T2chunk0688_checked : T2chunk0688.all T2check = true := by decide +kernel

theorem T2chunk0696_checked : T2chunk0696.all T2check = true := by decide +kernel

theorem T2chunk0704_checked : T2chunk0704.all T2check = true := by decide +kernel

theorem T2chunk0712_checked : T2chunk0712.all T2check = true := by decide +kernel

theorem T2chunk0720_checked : T2chunk0720.all T2check = true := by decide +kernel

theorem T2chunk0728_checked : T2chunk0728.all T2check = true := by decide +kernel

theorem T2chunk0736_checked : T2chunk0736.all T2check = true := by decide +kernel

theorem T2chunk0744_checked : T2chunk0744.all T2check = true := by decide +kernel

theorem T2chunk0752_checked : T2chunk0752.all T2check = true := by decide +kernel

theorem T2chunk0760_checked : T2chunk0760.all T2check = true := by decide +kernel

theorem T2chunk0768_checked : T2chunk0768.all T2check = true := by decide +kernel

theorem T2chunk0776_checked : T2chunk0776.all T2check = true := by decide +kernel

theorem T2chunk0784_checked : T2chunk0784.all T2check = true := by decide +kernel

theorem T2chunk0792_checked : T2chunk0792.all T2check = true := by decide +kernel

theorem T2chunk0800_checked : T2chunk0800.all T2check = true := by decide +kernel

theorem T2chunk0808_checked : T2chunk0808.all T2check = true := by decide +kernel

theorem T2chunk0816_checked : T2chunk0816.all T2check = true := by decide +kernel

theorem T2chunk0824_checked : T2chunk0824.all T2check = true := by decide +kernel

theorem T2chunk0832_checked : T2chunk0832.all T2check = true := by decide +kernel

theorem T2chunk0840_checked : T2chunk0840.all T2check = true := by decide +kernel

theorem T2chunk0848_checked : T2chunk0848.all T2check = true := by decide +kernel

theorem T2chunk0856_checked : T2chunk0856.all T2check = true := by decide +kernel

theorem T2chunk0864_checked : T2chunk0864.all T2check = true := by decide +kernel

theorem T2chunk0872_checked : T2chunk0872.all T2check = true := by decide +kernel

theorem T2chunk0880_checked : T2chunk0880.all T2check = true := by decide +kernel

theorem T2chunk0888_checked : T2chunk0888.all T2check = true := by decide +kernel

theorem T2chunk0896_checked : T2chunk0896.all T2check = true := by decide +kernel

theorem T2chunk0904_checked : T2chunk0904.all T2check = true := by decide +kernel

theorem T2chunk0912_checked : T2chunk0912.all T2check = true := by decide +kernel

theorem T2chunk0920_checked : T2chunk0920.all T2check = true := by decide +kernel

theorem T2chunk0928_checked : T2chunk0928.all T2check = true := by decide +kernel

theorem T2chunk0936_checked : T2chunk0936.all T2check = true := by decide +kernel

theorem T2chunk0944_checked : T2chunk0944.all T2check = true := by decide +kernel

theorem T2chunk0952_checked : T2chunk0952.all T2check = true := by decide +kernel

theorem T2chunk0960_checked : T2chunk0960.all T2check = true := by decide +kernel

theorem T2chunk0968_checked : T2chunk0968.all T2check = true := by decide +kernel

theorem T2chunk0976_checked : T2chunk0976.all T2check = true := by decide +kernel

theorem T2chunk0984_checked : T2chunk0984.all T2check = true := by decide +kernel

theorem T2chunk0992_checked : T2chunk0992.all T2check = true := by decide +kernel

theorem T2chunk1000_checked : T2chunk1000.all T2check = true := by decide +kernel

theorem T2chunk1008_checked : T2chunk1008.all T2check = true := by decide +kernel

theorem T2chunk1016_checked : T2chunk1016.all T2check = true := by decide +kernel

theorem firstChunks_checked : firstChunks.all (fun rows => rows.all firstCheck) = true := by
  simp only [firstChunks, List.all_cons, List.all_nil, Bool.true_and,
    firstChunk0000_checked, firstChunk0008_checked, firstChunk0016_checked, firstChunk0024_checked, firstChunk0032_checked, firstChunk0040_checked, firstChunk0048_checked, firstChunk0056_checked, firstChunk0064_checked, firstChunk0072_checked, firstChunk0080_checked, firstChunk0088_checked, firstChunk0096_checked, firstChunk0104_checked, firstChunk0112_checked, firstChunk0120_checked, firstChunk0128_checked, firstChunk0136_checked, firstChunk0144_checked, firstChunk0152_checked, firstChunk0160_checked, firstChunk0168_checked, firstChunk0176_checked, firstChunk0184_checked, firstChunk0192_checked, firstChunk0200_checked, firstChunk0208_checked, firstChunk0216_checked, firstChunk0224_checked, firstChunk0232_checked, firstChunk0240_checked, firstChunk0248_checked, firstChunk0256_checked, firstChunk0264_checked, firstChunk0272_checked, firstChunk0280_checked, firstChunk0288_checked, firstChunk0296_checked, firstChunk0304_checked, firstChunk0312_checked, firstChunk0320_checked, firstChunk0328_checked, firstChunk0336_checked, firstChunk0344_checked, firstChunk0352_checked, firstChunk0360_checked, firstChunk0368_checked, firstChunk0376_checked, firstChunk0384_checked, firstChunk0392_checked, firstChunk0400_checked, firstChunk0408_checked, firstChunk0416_checked, firstChunk0424_checked, firstChunk0432_checked, firstChunk0440_checked, firstChunk0448_checked, firstChunk0456_checked, firstChunk0464_checked, firstChunk0472_checked, firstChunk0480_checked, firstChunk0488_checked, firstChunk0496_checked, firstChunk0504_checked, firstChunk0512_checked, firstChunk0520_checked, firstChunk0528_checked, firstChunk0536_checked, firstChunk0544_checked, firstChunk0552_checked, firstChunk0560_checked, firstChunk0568_checked, firstChunk0576_checked, firstChunk0584_checked, firstChunk0592_checked, firstChunk0600_checked, firstChunk0608_checked, firstChunk0616_checked, firstChunk0624_checked, firstChunk0632_checked, firstChunk0640_checked, firstChunk0648_checked, firstChunk0656_checked, firstChunk0664_checked, firstChunk0672_checked, firstChunk0680_checked, firstChunk0688_checked, firstChunk0696_checked, firstChunk0704_checked, firstChunk0712_checked, firstChunk0720_checked, firstChunk0728_checked, firstChunk0736_checked, firstChunk0744_checked, firstChunk0752_checked, firstChunk0760_checked, firstChunk0768_checked, firstChunk0776_checked, firstChunk0784_checked, firstChunk0792_checked, firstChunk0800_checked, firstChunk0808_checked, firstChunk0816_checked, firstChunk0824_checked, firstChunk0832_checked, firstChunk0840_checked, firstChunk0848_checked, firstChunk0856_checked, firstChunk0864_checked, firstChunk0872_checked, firstChunk0880_checked, firstChunk0888_checked, firstChunk0896_checked, firstChunk0904_checked, firstChunk0912_checked, firstChunk0920_checked, firstChunk0928_checked, firstChunk0936_checked, firstChunk0944_checked, firstChunk0952_checked, firstChunk0960_checked, firstChunk0968_checked, firstChunk0976_checked, firstChunk0984_checked, firstChunk0992_checked, firstChunk1000_checked, firstChunk1008_checked, firstChunk1016_checked]

theorem T2chunks_checked : T2chunks.all (fun rows => rows.all T2check) = true := by
  simp only [T2chunks, List.all_cons, List.all_nil, Bool.true_and,
    T2chunk0000_checked, T2chunk0008_checked, T2chunk0016_checked, T2chunk0024_checked, T2chunk0032_checked, T2chunk0040_checked, T2chunk0048_checked, T2chunk0056_checked, T2chunk0064_checked, T2chunk0072_checked, T2chunk0080_checked, T2chunk0088_checked, T2chunk0096_checked, T2chunk0104_checked, T2chunk0112_checked, T2chunk0120_checked, T2chunk0128_checked, T2chunk0136_checked, T2chunk0144_checked, T2chunk0152_checked, T2chunk0160_checked, T2chunk0168_checked, T2chunk0176_checked, T2chunk0184_checked, T2chunk0192_checked, T2chunk0200_checked, T2chunk0208_checked, T2chunk0216_checked, T2chunk0224_checked, T2chunk0232_checked, T2chunk0240_checked, T2chunk0248_checked, T2chunk0256_checked, T2chunk0264_checked, T2chunk0272_checked, T2chunk0280_checked, T2chunk0288_checked, T2chunk0296_checked, T2chunk0304_checked, T2chunk0312_checked, T2chunk0320_checked, T2chunk0328_checked, T2chunk0336_checked, T2chunk0344_checked, T2chunk0352_checked, T2chunk0360_checked, T2chunk0368_checked, T2chunk0376_checked, T2chunk0384_checked, T2chunk0392_checked, T2chunk0400_checked, T2chunk0408_checked, T2chunk0416_checked, T2chunk0424_checked, T2chunk0432_checked, T2chunk0440_checked, T2chunk0448_checked, T2chunk0456_checked, T2chunk0464_checked, T2chunk0472_checked, T2chunk0480_checked, T2chunk0488_checked, T2chunk0496_checked, T2chunk0504_checked, T2chunk0512_checked, T2chunk0520_checked, T2chunk0528_checked, T2chunk0536_checked, T2chunk0544_checked, T2chunk0552_checked, T2chunk0560_checked, T2chunk0568_checked, T2chunk0576_checked, T2chunk0584_checked, T2chunk0592_checked, T2chunk0600_checked, T2chunk0608_checked, T2chunk0616_checked, T2chunk0624_checked, T2chunk0632_checked, T2chunk0640_checked, T2chunk0648_checked, T2chunk0656_checked, T2chunk0664_checked, T2chunk0672_checked, T2chunk0680_checked, T2chunk0688_checked, T2chunk0696_checked, T2chunk0704_checked, T2chunk0712_checked, T2chunk0720_checked, T2chunk0728_checked, T2chunk0736_checked, T2chunk0744_checked, T2chunk0752_checked, T2chunk0760_checked, T2chunk0768_checked, T2chunk0776_checked, T2chunk0784_checked, T2chunk0792_checked, T2chunk0800_checked, T2chunk0808_checked, T2chunk0816_checked, T2chunk0824_checked, T2chunk0832_checked, T2chunk0840_checked, T2chunk0848_checked, T2chunk0856_checked, T2chunk0864_checked, T2chunk0872_checked, T2chunk0880_checked, T2chunk0888_checked, T2chunk0896_checked, T2chunk0904_checked, T2chunk0912_checked, T2chunk0920_checked, T2chunk0928_checked, T2chunk0936_checked, T2chunk0944_checked, T2chunk0952_checked, T2chunk0960_checked, T2chunk0968_checked, T2chunk0976_checked, T2chunk0984_checked, T2chunk0992_checked, T2chunk1000_checked, T2chunk1008_checked, T2chunk1016_checked]

theorem firstData_checked : firstData.all firstCheck = true := by
  simpa only [firstData, List.all_flatten] using firstChunks_checked

theorem T2data_checked : T2data.all T2check = true := by
  simpa only [T2data, List.all_flatten] using T2chunks_checked

theorem first_row_checked {r : FirstRow} (hr : r ∈ firstData) : firstCheck r = true :=
  List.all_eq_true.mp firstData_checked r hr

theorem T2_row_checked {r : T2Row} (hr : r ∈ T2data) : T2check r = true :=
  List.all_eq_true.mp T2data_checked r hr

theorem first_forcing_cell_checked {r : FirstRow} (hr : r ∈ firstData) :
    coarseForcingCellCheck ub sb (firstLeft r.index) (firstRight r.index) gc
      (lift18 r.norm) (lift18 r.M4) (lift18 r.MR) (lift18 r.G)
      (lift18 r.W) (lift18 r.P) (lift18 r.H) = true :=
  (Bool.and_eq_true_iff.mp (first_row_checked hr)).1

theorem first_decay_checked {r : FirstRow} (hr : r ∈ firstData) :
    decayCheck sb (firstLeft r.index) (firstRight r.index) (lift18 r.D) = true :=
  (Bool.and_eq_true_iff.mp (first_row_checked hr)).2

theorem first_rate_checked {r : FirstRow} (hr : r ∈ firstData) :
    rateCheck ub (firstLeft r.index) (firstRight r.index) gc
      (lift18 r.norm) (lift18 r.M4) (lift18 r.MR) (lift18 r.G) = true := by
  have h := Bool.and_eq_true_iff.mp (first_forcing_cell_checked hr)
  exact (Bool.and_eq_true_iff.mp h.1).1

theorem first_W_checked {r : FirstRow} (hr : r ∈ firstData) :
    coarseWCheck ub (firstRight r.index) (lift18 r.W) = true := by
  have h := Bool.and_eq_true_iff.mp (first_forcing_cell_checked hr)
  exact (Bool.and_eq_true_iff.mp h.1).2

theorem first_forcing_checked {r : FirstRow} (hr : r ∈ firstData) :
    forcingCheck ub sb (lift18 r.G) (lift18 r.W) (lift18 r.P) (lift18 r.H) = true :=
  (Bool.and_eq_true_iff.mp (first_forcing_cell_checked hr)).2

#print axioms firstData_checked

#print axioms T2data_checked

#print axioms first_forcing_cell_checked

#print axioms first_decay_checked

end BerryEsseen.UpperMomentN47ScalarChecks
