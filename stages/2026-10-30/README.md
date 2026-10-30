# Berry--Esseen: a Lean verification stage

Linjie Huang · Jiangsu Ocean University  
Stage snapshot: 30 October 2026

For a real probability law with mean zero, variance one, and finite third
absolute moment $\rho=\mathbb E|X|^3$, the original target is

$$
\sup_x\left|\mathbb P\!\left(\frac{X_1+\cdots+X_n}{\sqrt n}\le x\right)
-\Phi(x)\right|\le C_E\frac{\rho}{\sqrt n},\qquad
C_E=\frac{3+\sqrt{10}}{6\sqrt{2\pi}}.
$$

Here the variables are independent with the same law and $n\ge1$.
[`Target.lean`](BerryEsseen/Target.lean) defines this exact constant, the
standardized-law assumptions, and the normalized iid sum law.

This AI-assisted research stage contains all-law proofs for **n = 1 and
n = 2**, general characteristic-function and CDF comparison theorems,
spectral endpoint interpolation, Gaussian recurrence/conditional own-score
results, a fixed high-moment control endpoint, and a kernel-certified **n = 47
upper-moment CDF bound**. **The full all-n theorem remains in progress.**
The theorem map below gives the precise scope of this snapshot.

For n=47, write $\Delta_{47}(\mu,x)$ for the original closed CDF error.
The new certificate proves, for every standardized real law and every real x:

* If $\rho\le7361/4000$, then $\Delta_{47}(\mu,x)<533/5000$.
* If $173303/96000\le\rho\le7361/4000$, then
  $\Delta_{47}(\mu,x)<(81/200)\rho/\sqrt{47}$, with coefficient **0.405**.
* On the slightly wider, simpler band $9/5\le\rho\le7361/4000$,
  $\Delta_{47}(\mu,x)<(407/1000)\rho/\sqrt{47}<C_E\rho/\sqrt{47}$,
  with coefficient **0.407**.

These conclusions concern the same original law, allow arbitrary support and
atoms, and require no sharp-predecessor hypothesis. They are one-index moment
band results; they do not establish the all-n conjecture.

中文状态：本阶段保留原有八个入口，并新增 n=47 的原始闭 CDF 核证：任意标准化
实分布在 $\rho\le7361/4000$ 时误差严格小于 $533/5000$；在
$173303/96000\le\rho\le7361/4000$ 时系数为 0.405，在稍宽的
$9/5\le\rho\le7361/4000$ 时系数为 0.407，小于 Esseen 常数。
以上 n=47 结论没有支撑限制，也不依赖前驱假设。完整 all-n 猜想尚未获 Lean
核证；其他外部数值覆盖不冒充本快照的 Lean 证明。

## Sample-band, Gaussian-mask, and conditional N26 additions

For every actual integer $47\le n\le58$ and every standardized real law with
$173303/96000\le\rho\le7361/4000$, the new sample-band theorem proves
$\sqrt n\,\Delta_n(\mu,x)/\rho\le256/625=0.4096<C_E$ for every real x.
It has no support restriction or sharp-predecessor hypothesis. The previously
proved n=47 coefficients **0.405** on the original high moment cell and
**0.407** on the wider band $9/5\le\rho\le7361/4000$ remain available unchanged.

The monotone Gaussian recurrence pays the four INITIAL own-score envelopes
from actual indices **47, 63, 96, and 198**, respectively, for cells 20 through
23. Every such mask still assumes the full all-law predecessor
`fixedNSup (n-1) ≤ esseenConstant` at the actual index. These are own-score
comparisons; support, charged resources, and the rest of INITIAL remain
separate obligations.

The original-law N26 acquisition theorems require a standardized law,
`PositiveClosedMaximum μ 26 H C`, $C_E\le C$, $\rho\le11/10$, and the
**full-domain hypothesis `fixedNSup 25 ≤ esseenConstant`**. They acquire
the original law's support in $[-12/5,12/5]$ and then the actual-rho bounds

$$
M_4=\mathbb E|X|^4\le1+\frac{578}{145}(\rho-1),\qquad
M_5^{\rm abs}=\mathbb E|X|^5\le1+\frac{8511}{725}(\rho-1).
$$

Those affine moment bounds also hold directly under the displayed support
premise. The N26 low-frequency client obtains the entire original
$I_0$ contribution on $(0,1/2]$, its absolute integrability, and the signed
quotient's integrability, without incoming free moment or gamma prices:

$$
\sqrt{26}\,I_0(\mu,26,H)\le
\frac{29}{250}+\frac{127}{1000}|H|+
\frac{23}{125\sqrt{26}}.
$$

The new characteristic-function Gaussian domination assumes a finite fourth
moment $M_4\le8/5$ and the **physical-frequency restriction $|t|\le9/10$**:
$|\widehat\mu(t)|\le\exp(-t^2/2)$, with the corresponding natural-power
bound. It is a modulus bound on this finite frequency band, not an all-frequency
claim or a sub-Gaussian probability-tail theorem. The acquired N26 support and
moment bounds supply its premises in the original-maximum client.

For the actual compensated Fourier remainder
$E_{26}(H)=\texttt{FourierRemainder.value}\ \mu\ 26\ H$, the new original-law
client proves absolute integrability and the strengthened bound

$$
|E_{26}(H)|\le\frac{642}{625}+\frac{127}{1500}|H|.
$$

The imported parameterized theorem remains available: if the **genuine whole
high-frequency CF tail** has a numerical price T,

$$
\sqrt{26}\int_{9/10}^{\infty}
\frac{|\widehat\mu(t)^{26}|}{t^3}\,dt\le T,
$$

the same original client instead gives

$$
|E_{26}(H)|\le\frac{551}{1875}+\frac23T+\frac{127}{1500}|H|.
$$

Here T prices the actual law's complete tail beyond 0.9. The new
`N26QuarticHighTail` module acquires $M_4\le1014/725<7/5$ from the same law's
support and rho premises, proves $|\widehat\mu(t)|^2\le18/25$ on the whole
fixed band $[9/10,31/20]$, and pays the complete remaining infinite ray using
$|\widehat\mu(t)|\le1$. Its exact tail price is strictly below $11/10$;
the public support/original-maximum clients give $T\le11/10$, yielding the
$642/625$ Fourier constant above. No tail is omitted or replaced by a Gaussian
proxy, and `N26InitialFourierEnvelope` remains in the import closure.

**The original P39 profile and original raw-budget closure remain open.** The
new Fourier bound is not a proof of the raw budget near 1.082: the conserved
raw also contains the actual moment coefficients and an H-quadratic term.
The C25 bound above remains a hypothesis, not a proved result of this snapshot.
Further high-frequency/resource pricing is still needed for those original
obligations; these conditional acquisitions and Fourier bounds do not prove
the original all-n theorem.

中文增量：新增实际 n=47..58、原高矩带的 0.4096 严格低于 Esseen 常数结论，
无前驱假设；Gaussian own-score 的新门槛为 47/63/96/198，仍保留全域前驱假设。
N26 在原 maximum、全域 C25 假设及 $\rho\le1.1$ 下取得支撑、实际矩和低频整块。
Gaussian CF 模只在 $M_4\le8/5$、$|t|\le0.9$ 有效；新增固定高频段的四次模界
与完整无穷尾给真实尾价严格小于 $11/10$，全 Fourier 界提升为
$642/625+(127/1500)|H|$。raw 还含实际矩系数和 H 二次项，原 P39 与
raw-budget 尚未闭合；完整 all-n 尚未核证。

## Conditional N26 projected charged-resource acquisition

This addition retains the same original standardized law, actual n=26, and
threshold H. It assumes `PositiveClosedMaximum μ 26 H C`, the **full all-law
predecessor hypothesis `fixedNSup 25 ≤ esseenConstant`**, $C_E\le C$, and
$\rho\le11/10$. The predecessor first acquires the original support in
$[-12/5,12/5]$. Same-coordinate gap projection, the same-law K1 covariance
bound, classical cubic characteristic-function damping, and joint polynomial
prices then acquire

$$
\begin{aligned}
\operatorname{chargedRaw}(\mu,26,H,C)
  &=\operatorname{raw}(\mu,26,H,C)-26(C-C_E)\rho\le\frac{17}{10},\\
D(\mu)&\le\frac{12750}{12961}<1,\\
\operatorname{phase}(26,H)&\ge\frac{87}{104},\qquad
0\notin\operatorname{support}(\mu).
\end{aligned}
$$

Here D is `GapDefect.actualPhysicalDefect`. These acquisition clients have no
incoming numerical raw, defect, or phase price. The 1.7 conclusion is for the
**charged** resource. It does not conclude a general 1.7 bound for the uncharged
raw at the original actual C. The library also prices
`raw μ 26 H esseenConstant` as a literal function evaluation; it neither assumes
nor establishes a positive closed maximum at the changed score $C_E$.

The supporting cubic-CF tail theorem needs only standardization and
$\rho\le11/10$, with **no support, contact, or predecessor assumption**:

$$
\sqrt{26}\int_{9/10}^{\infty}
\frac{|\widehat\mu(t)^{26}|}{t^3}\,dt
\le\frac{4901308573}{9663676416}\approx0.5071888.
$$

It bounds the two entire frequency bands $[9/10,2]$ and $[2,9/4]$ by the
classical cubic estimate, retaining the complete inverse-cube tail above
$9/4$. With the same law's acquired support and rho bound, the complete
Fourier remainder estimate improves the preceding quartic bound to

$$
|E_{26}(H)|\le\frac{79}{125}+\frac{127}{1500}|H|.
$$

The older quartic and parameterized T results remain available in the import
closure. **This initial charged-resource bound does not prove the stronger
P39 defect target near 0.595 or its 32-round resource profile.** C25 remains a
hypothesis; neither C25 nor the global all-n theorem is established here.

中文增量：在原 n26 正最大、全域 C25 假设、$C\ge C_E$、$\rho\le1.1$ 下，
先取得原支撑，再取得 charged raw≤1.7、$D\le12750/12961<1$、phase≥87/104
和支撑不含0；没有另留数值 raw/D/phase 前提。该结论不等于原实际 C 的
uncharged raw≤1.7。无支撑条件的 cubic CF 尾价及完整 Fourier 新界已分别写明
前提；P39 的约0.595缺陷目标、32轮资源、C25及完整 all-n 仍未完成。

## Conditional uniform low-moment rebated acquisition

The uniform client keeps the **actual integer n≥26**, the same original
standardized law μ, and `PositiveClosedMaximum μ n H C`. Its remaining
premises are the **full all-law predecessor
`fixedNSup (n-1) ≤ esseenConstant`**, $C_E\le C$, and $\rho\le11/10$.
There are no additional numerical p, support, raw, defect, or phase inputs.
The original support in $[-12/5,12/5]$ is acquired first. Standardization and
the rho cap alone also place the same law's canonical sign probabilities
$p,q\in[37/100,63/100]$.

The first pass uses the varying charged-resource budget
$r(n)=11/8+\sqrt n/15$ to acquire $D<1$, phase≥5/6, and absence of zero from
the original support. This pass is established before the periodic event or
the retained curvature is used. The acquired first-pass defect and phase
license the **7/50 curvature**, without taking a second-pass defect bound as
an input.

The true opposite-sign event then pays the **complete infinite actual-CF
tail**; the Fourier bound has no remaining tail-price premise:

$$
\sqrt n\int_{9/10}^{\infty}\frac{|\widehat\mu(t)^n|}{t^3}\,dt
\le\frac9{50},\qquad
|E_n(H)|\le\frac{776}{1875}+\frac{127}{1500}|H|.
$$

Only deterministic prices use floor 26; the law, characteristic-function
power, normalization, maximum, and predecessor all retain the actual n.
The second acquisition proves

$$
\begin{aligned}
\operatorname{chargedRaw}(\mu,n,H,C)-\frac7{50}H^2&\le\frac{92}{75},\\
\kappa nD+n\sqrt n\,L&\le\frac{92}{75},\\
D&\le\frac{18400}{997n}.
\end{aligned}
$$

Here D is the original `GapDefect.actualPhysicalDefect`, L is the same
`ContactGapSum.actualL μ n H`, and κ is `ConservedTransfer.kappa`. The joint
resource theorem retains the actual gap cost L instead of dropping it. The
source also retains the stronger actual excess-score term, with a positive
coefficient bounded below by 6; no maximum at a changed score is introduced.

**92/75 is a rebated charged-resource price**, not an unrebated raw or chargedRaw
price. The predecessor hypothesis remains in every original-maximum uniform
client. These resource acquisitions do not prove $C_n\le C_E$, the global
all-n theorem, or completion of the old P39 profile.

中文增量：对每个实际整数 n≥26，在同一原 μ/正最大、完整全域前驱、$C\ge C_E$、
$\rho\le1.1$ 前提下，首遍变动预算先取得 D<1 和 phase≥5/6；p、q 的范围由
rho 自动取得，没有额外数值 p/support/raw/D/phase 输入。真实全无穷尾≤9/50，
独立首遍许可7/50曲率后，rebated charged raw≤92/75；保留 actual L 的联合资源
及 $D\le18400/(997n)$。92/75不作为未扣曲率的价格，hprev没有消除，
旧P39与完整 all-n 尚未完成。

## Original n26 count-11 local height exclusion

The new client assumes the same original standardized law and
`PositiveClosedMaximum μ 26 H C`, the **full all-law hypothesis
`fixedNSup 25 ≤ esseenConstant`**,
$C_E\le C$, $\rho\le11/10$, and the additional sign strip
$p(\mu)\in[39/100,2/5]$. For **every phase $t\in[0,1]$**, the actual
closed CDF at `canonicalThreshold μ h 26 11 t` satisfies

$$
F_{26,\mu}(x(t))-\Phi(x(t))-C_E\frac{\rho}{\sqrt{26}}
\le-\frac1{5000}.
$$

Consequently the **same original maximum** obeys
`canonicalHeight μ h 26 H ∉ [11,12]`, including the interval endpoints.
The price starts with the actual closed CDF and then subtracts the target
using that law's actual third absolute moment. The reference and actual
noise parameter stay fixed across the complete phase interval.

Two acquired quantities remain distinct: the count-11 residual variance
$15\operatorname{variance}_0+11\operatorname{variance}_1\le8/25=0.32$
licenses reference enlargement; the total noise
$\lambda=\texttt{noiseLevel}\ \mu\ h\ 26\le17/50=0.34$ prices the Gaussian
noise loss. Neither variance bound is a free hypothesis. The client takes
no old P39 profile or incoming numerical raw/defect price as a premise.

This is a local exclusion of one count/height interval in the stated sign
strip. **The whole P39 problem, the C26 bound, and the full all-n Lean theorem
are not proved by this addition; the full C25 hypothesis remains.**

中文增量：原 n26/同一正最大/完整全域 C25 假设及 $\rho\le1.1$、
$p\in[0.39,0.4]$ 下，闭 phase 区间 [0,1] 的真实正 target residual 全部
≤−1/5000，故同一最大值的 canonicalHeight 不在闭 [11,12]。count variance
0.32 与总噪声 lambda 0.34 分开取得、分开使用；不依赖旧P39 profile或free
raw/D/variance数值假设，也不声称 whole P39、C26 或完整 all-n 已完成。

## Build

Install [elan](https://github.com/leanprover/elan), then run these commands from
the directory containing this seventeen-entry snapshot:

```sh
elan toolchain install leanprover/lean4:v4.35.0
lake exe cache get
lake build BerryEsseen
```

Lean and Mathlib are pinned to **4.35.0**; `lake-manifest.json` records the exact
dependency revisions. The cache command downloads Mathlib's compiled cache;
the project proofs and integer certificate rows are built locally. The n=2
certificate and control-endpoint tables can require substantial compilation
time. No prebuilt project artifacts or personal toolchain paths are included.
For an individual entry point, use for example:

```sh
lake build BerryEsseen.UpperMomentSpectrumPrice
```

## Theorem map and premises

Unless stated otherwise, `μ : ProbabilityMeasure ℝ` satisfies
`StandardizedLaw μ`: finite third absolute moment, mean zero, and second moment
one. Conclusions use the original iid law and every real threshold, including
closed CDF events at atoms. The map lists theorem names within each linked
module namespace; the Lean signatures are the precise interfaces.

| Module | Main theorem(s) | Scope and premises |
| --- | --- | --- |
| [SingleSampleBound](BerryEsseen/SingleSampleBound.lean) | `absolute_closed_error`, `sharp_one` | n=1, every standardized law; the former proves the stronger coefficient 2/5. |
| [N2CertifiedBound](BerryEsseen/N2CertifiedBound.lean) | `sharp_two` | `Reflection.AbsoluteClosedBound 2 esseenConstant`, with no support restriction in the final theorem; joins the 65-row integer pointwise family and the analytic reductions/tails. |
| [ControlCertifiedEndpoint](BerryEsseen/ControlCertifiedEndpoint.lean) | `physical_profile_lt`, `spectral_profile_lt`, `actual_cdf_lt_at_control_beta`, `sharp_at_control_beta` | The profile is strictly below 4071/10000. The actual-law conclusions require n≥42, ρ≥7361/4000, and **ρ/√n = 13500000000000000/45949729863572161 exactly**. This is one fixed endpoint. |
| [FiniteBandRayPrice](BerryEsseen/FiniteBandRayPrice.lean) | `normalized_actual_cdf_le_profile`, `normalized_actual_cdf_le_linear_endpoints`, `normalized_actual_cdf_le_const_endpoints`, `normalized_actual_cdf_le_correlated_linear_endpoints` | A finite sample band 0<N≤n≤M, lower moment/coefficient qualifications, positive cutoffs 0<A≤V, and an admissible spectral node for s=1/(ρ/√n)². The endpoint profiles still need numerical bounds to prove a target coefficient. |
| [GenericCenterPower](BerryEsseen/GenericCenterPower.lean) | `norm_center_power_sub_real_sq`, `bernstein_identity`, `normalized_charFun_sub_gaussian_le` | Every natural power, with signed center/phase coefficients and a whole closed phase interval, including its zero-width case. Actual-law applications retain the explicit radius and Bernstein-control bounds. |
| [UpperMomentDamping](BerryEsseen/UpperMomentDamping.lean) | `charFun_norm_le_exp`, `normalized_power_le_exp`, `normalized_pred_power_le_exp` | A genuine upper moment bound ρ≤U and arbitrary fixed σ>0; normalized powers apply to every n>0, retaining the exact n and n−1 exponents. The capped variants additionally require the displayed signed-third-moment cap. |
| [UpperMomentSpectrumPrice](BerryEsseen/UpperMomentSpectrumPrice.lean) | `normalized_actual_cdf_le_scale_spectralProfile`, `normalized_actual_cdf_le_endpoints`, `normalized_actual_cdf_le_sample_endpoints`, `normalized_actual_cdf_ratio_le_endpoints` | U>0, ρ≤U, n>0, 0<A≤V. Endpoint interpolation requires 0<a<b, n/U²∈[a,b], and 1/U²≤a. The ratio theorem also requires 0<L≤ρ and pays the explicit U/L factor. No numerical endpoint value is assumed proved. |
| [GaussianInitialMask](BerryEsseen/GaussianInitialMask.lean), with [GaussianOwnScore](BerryEsseen/GaussianOwnScore.lean) | `fixedNSup_lt_gaussian_price`, `fixedNSup_lt_initialLeft_low`, `fixedNSup_lt_initialLeft20` through `fixedNSup_lt_initialLeft23`; `GaussianOwnScore.fixedNSup_lt_envelope` | **Conditional on `fixedNSup (n-1) ≤ esseenConstant`.** The Gaussian price applies from n≥26. INITIAL grid masks have the respective index cutoffs 47, 48, 66, 101, 213; the own-score envelope result applies for n≥213 and 0<r≤173303/96000. These are not unconditional sharp bounds for those indices. |
| [UpperMomentN47Certified](BerryEsseen/UpperMomentN47Certified.lean) | `profile_lt`, `actual_cdf_lt`, `actual_cdf_lt_405`, `actual_cdf_lt_407`, `sharp_on_moment_band` | n=47, every standardized real law and every real threshold. For ρ≤7361/4000, the absolute closed CDF error is <533/5000. The strict error bound uses coefficient 0.405 when 173303/96000≤ρ≤7361/4000, and 0.407<C_E on 9/5≤ρ≤7361/4000. No support restriction or sharp-predecessor premise. |
| [UpperMomentBand47To58](BerryEsseen/UpperMomentBand47To58.lean) | `ratio_le`, `sharp_on_sample_band` | Actual integer 47≤n≤58, 173303/96000≤ρ≤7361/4000: √n·CDF-error/ρ≤256/625=0.4096<C_E. Every real threshold; no support or sharp-predecessor premise. |
| [GaussianMonotoneMask](BerryEsseen/GaussianMonotoneMask.lean) | `recurrencePrice_antitoneOn`, `fixedNSup_lt_initialLeft20` through `fixedNSup_lt_initialLeft23` | INITIAL own-score masks from 47/63/96/198, respectively, each conditional on the full all-law sharp predecessor at n−1. No support or resource acquisition follows from the masks alone. |
| [N26InitialLowFrequency](BerryEsseen/N26InitialLowFrequency.lean), with [N26P39ResourceAcquisition](BerryEsseen/N26P39ResourceAcquisition.lean) | `original_low_frequency`, `original_signed_integrable`; `N26P39ResourceAcquisition.original_support`, `N26P39ResourceAcquisition.original_moment_affine` | Under the original N26 maximum, C_E≤C, full-domain C25≤C_E, and ρ≤11/10: acquires support ±12/5, the actual-rho affine M4/M5 bounds, and the entire I0 price on (0,1/2]. No incoming free moment/gamma/raw price is used for these conclusions. |
| [LowMomentGaussianBand](BerryEsseen/LowMomentGaussianBand.lean) | `norm_charFun_le_gaussian`, `norm_charFun_pow_le_gaussian`, `original_initial_segment_cost_le` | Finite M4≤8/5 and physical abs(t)≤9/10 give the Gaussian CF modulus bound. The original N26 client acquires its premises and bounds the middle CF segment by 204/1625 after √26 scaling. No all-frequency or probability-tail sub-Gaussian assertion. |
| [N26QuarticHighTail](BerryEsseen/N26QuarticHighTail.lean), with [N26InitialFourierEnvelope](BerryEsseen/N26InitialFourierEnvelope.lean) | `original_cf_tail`, `original_fourier_envelope`; `N26InitialFourierEnvelope.original_value_le_of_tail` | Under the original N26 premises: the literal Fourier remainder is absolutely integrable and abs(E26(H))≤642/625+127·abs(H)/1500. The same law's full CF tail is ≤11/10, from an exact price strictly below 11/10. The fixed quartic band is [9/10,31/20] and the entire infinite ray is paid. A genuine full CF-tail price T gives 551/1875+(2/3)T+127·abs(H)/1500 instead. The conserved raw's moment coefficients and H-quadratic term remain; original P39/raw-budget obligations are open. |
| [N26ProjectedRawAcquisition](BerryEsseen/N26ProjectedRawAcquisition.lean), with [N26CubicHighTail](BerryEsseen/N26CubicHighTail.lean) | `original_charged_raw_bound`, `original_defect_bound`, `original_phase_lower_bound`, `original_zero_absent`; `N26CubicHighTail.cf_tail_le_price`, `N26CubicHighTail.original_fourier_envelope` | Original n26 positive closed maximum, full-domain C25≤C_E, C_E≤C, ρ≤11/10: acquires support, chargedRaw≤17/10, D≤12750/12961<1, phase≥87/104 and 0 absent from support, without incoming numerical raw/D/phase prices. No general uncharged-raw≤1.7 assertion at actual C. The standalone cubic tail price needs no support; the full Fourier bound with support is 79/125+127·abs(H)/1500. Stronger P39/32-round/C25/all-n obligations remain open. |
| [UniformLowMomentRebatedAcquisition](BerryEsseen/UniformLowMomentRebatedAcquisition.lean), with [UniformLowMomentPeriodicHighTail](BerryEsseen/UniformLowMomentPeriodicHighTail.lean) | `original_rebated_charged_raw_bound`, `original_joint_resource_with_excess`, `original_joint_resource_bound`, `original_defect_bound` | Actual integer n≥26, same original positive closed maximum, full all-law predecessor at n−1, C_E≤C and ρ≤11/10. Acquires first-pass D<1 and phase≥5/6, p/q band and the complete periodic tail≤9/50; no extra numerical support/raw/D/phase premise. The 7/50 curvature licenses a rebated charged price≤92/75, with actual L and actual excess retained in the joint resource, and D≤18400/(997n). No unrebated 92/75 price, C_n≤C_E or completed P39/all-n conclusion. |
| [P39ModeTailExclusion](BerryEsseen/P39ModeTailExclusion.lean) | `original_closedCDF_le_uniform`, `original_residual_le_envelope`, `original_count11_phase_upper`, `original_not_height_interval` | Original n26 maximum, full C25≤C_E, C_E≤C, ρ≤11/10, p∈[39/100,2/5]: every t∈[0,1] has actual positive target residual≤−1/5000, so the same canonicalHeight is outside closed [11,12]. Count variance≤8/25 and total noise≤17/50 are acquired and used separately; no old P39 profile or free raw/D/variance premise. No whole P39/C26/all-n conclusion. |

`BerryEsseen.lean` imports precisely these seventeen public entry points. Its
recursive import closure includes the mathematical reductions and certificate
data actually needed by them. The explicit `literatureEnvelope` used in the
Gaussian comparison is an algebraic function; those comparisons do not silently
assume an external probabilistic bound by that name. Certificate generation
scripts, unfinished finite covers, manuscripts, build caches, and local logs are
outside this source stage.

## Mathematical and software sources

The moment-defect framework and the finite-index proof program are due to
**Kacper Rodziewicz and Bartosz Kołodziejek**, *Moment defects and sharp iid
Berry--Esseen bounds*, public working manuscript, version 3:
[version record](https://hexagonmath.org/2610.00147v3) and
[frozen supplementary sources](https://github.com/rodziewiczk/berry-esseen-045-certificate/tree/75a94708872e2bc053f42a279559b23ed91e4402).
This stage preserves that attribution rather than presenting the framework as
originating in this formalization.

The compensated Taylor/circle bounds and classical numerical constants belong
to the existing Berry--Esseen literature, including **Irina Shevtsova**:
[Taylor remainder bounds, arXiv:1301.2783v3](https://arxiv.org/abs/1301.2783v3),
[moment-type estimates (2012)](https://ami.uni-eszterhazy.hu/uploads/papers/finalpdf/AMI_39_from241to307.pdf),
and [absolute constants and structural improvements (2013)](https://www.mathnet.ru/eng/ia252).
The Lean files reconstruct the inequalities they use; these citations are
attribution, not substitute proof assumptions.

The Prawitz smoothing, symmetrized third-moment, and basic cosine/damping leaves
are adapted from **Jiyuan Tan's
[CausalSmith / Causalean](https://github.com/Jiyuan-Tan/CausalSmith/tree/a7085d88d2e4b30003db7097ca374f4718da0f01)**.
The 22-source subset and its Lean/Mathlib 4.35 compatibility changes are recorded
in [`vendor/causalean-smoothing/NOTICE`](vendor/causalean-smoothing/NOTICE).
It does not include the CausalSmith pipeline or the unrelated third-party
packages mentioned in the retained upstream notice.

The four-source interval core is adapted from
[LeanCert](https://github.com/alerad/leancert/tree/44b323a0d6af00211d5013f6e021432db032087c).
Its dated source comments and `lakefile.toml` record the module/visibility
compatibility changes. Both vendored subsets retain their **Apache-2.0**
licenses: [LeanCert license](vendor/leancert-core/LICENSE) and
[Causalean license](vendor/causalean-smoothing/LICENSE).
[Mathlib](https://github.com/leanprover-community/mathlib4/tree/56a005855ea17e0b0958f73ec801ae140b0a1679)
and its fetched dependencies retain their respective upstream licenses.
No repository-wide license is declared for the project-authored material in
this stage.
