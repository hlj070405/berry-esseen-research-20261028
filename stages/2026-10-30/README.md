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

## Build

Install [elan](https://github.com/leanprover/elan), then run these commands from
the directory containing this nine-entry snapshot:

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

`BerryEsseen.lean` imports precisely these nine public entry points. Its
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
