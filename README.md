# Berry–Esseen research snapshot

我是软件工程专业的学生。这个项目起初就是出于好奇，用 GPT 跑着玩的，也想借这个过程边做边学。

欢迎概率论、正态近似、Berry–Esseen 不等式和 Lean 形式化相关领域的朋友来交流，一起审查推导、计算和代码。有疑问或发现错误，欢迎提 Issue 或 PR！

**Lean 形式化正在进行中～** 当前材料仍是候选证明和阶段性成果，完整 Lean 验证尚未完成，也尚未经过外部同行评审。

这个是不是挺重要的一个公开问题?可以点点star吗,我都还没有过什么star🌟

I'm a software engineering student, and this project started as a just-for-fun exploration with GPT. Researchers in probability, normal approximation, and Lean are welcome to discuss the work and help review the arguments, computations, and code. Lean formalization is ongoing; complete Lean verification and external peer review are still pending.

## 当前进度（2026-10-30）

**本轮已完成的 Lean 阶段源码见 [stages/2026-10-30](stages/2026-10-30/README.md)。** 包含独立可构建的依赖闭包、精确版本和来源说明。根目录的 `lean/`、论文与旧 Release 保留 10 月 28 日快照；进一步的数值覆盖正继续接入 Lean。

本阶段已加入一份 **n=47 连续矩带的完整 Lean 证书**：任意原标准化实分布在 $9/5\le\rho\le7361/4000$ 上得到系数 $0.407<C_E$，没有支撑或前驱假设。完整数表、真实积分及原闭 CDF 已接合，并完成新的独立数学阅读；全 $n$ 形式化仍未完成。

共享谱还给出 **全部实际整数 $47\le n\le58$** 的矩带证书：在 $173303/96000\le\rho\le7361/4000$ 上，系数为 $256/625=0.4096<C_E$。

低矩初始化现已统一覆盖 **每个实际整数 $n\ge26$**：保留原最大法则、全域 $C_{n-1}\le C_E$、$C\ge C_E$ 与 $\rho\le1.1$，先直接取得 $D<1$、phase $\ge5/6$ 及支撑中的中央缺口，再支付整个无限频率尾。最终完整 Fourier 界为 $|E_n(H)|\le776/1875+(127/1500)|H|$，并取得包含物理缺陷、真实 gap 积分及分数超额的联合预算，特别有 $D\le18400/(997n)$。这条统一解析路线不输入数值 raw/D/phase 或概率分块；从小资源区域推出 $C\le C_E$ 的局部排除仍待完成。

**原分布上的连续局部排除**现已扩成右侧整族：实际 $n=26$、$\rho\le1.1$、$p=\Pr(X>0)\in[.39,.4]$ 时，在上述最大值与完整 $C_{25}\le C_E$ 条件下，同一最大元的 canonical height 必须位于 $cH+26p\in(8.5,11)$。计数 11、12、13 的整个闭相位及其后的整条右射线均已排除；对应 `P39RightCountsExclusion.original_height_window`。这些证明未输入旧 P39 profile，窗口内部及完整 $C_{26}$ 仍待闭合。

同一原分布还自动满足向内偏移总量 $\delta<1/16$、资源组合 $16v_0+14v_1<8/25$，所以计数 10 至 14 的实际方差均小于 $8/25$。实际总噪声 $\lambda<.3172$，正组残差几乎处处小于 $9/16$，由此取得更紧的共同参照。这里 $16+14$ 只是同一资源预算的比较，未把样本量换成 30。

**本轮整数区间复算包见 [stages/2026-10-30-computation](stages/2026-10-30-computation/README.md)。** 共保存 69 个不同端点价格，提供接合检查和从空目录重新计算的入口；不需要原工作区或非标准 Python 依赖。

阶段目录的构建入口：

```sh
cd stages/2026-10-30
lake exe cache get
lake build BerryEsseen
```

完整的定理范围和工具链安装命令见该阶段的 README。下面仍分别说明本地数学进展与已形式化的成果。

### 已有的候选证明

本地已有一份针对 **iid Berry–Esseen 最优常数猜想**的计算辅助候选证明稿。其完整目标是：对任意均值为 0、方差为 1、第三绝对矩有限的实分布，以及每个正整数样本量 $n$，证明

$$
\Delta_n(P)\le C_E\frac{\rho}{\sqrt n},\qquad
\rho=\mathbb E|X|^3,\qquad
C_E=\frac{3+\sqrt{10}}{6\sqrt{2\pi}}\approx0.4097321837.
$$

这里 $\Delta_n(P)$ 是标准化 iid 和与标准正态分布的最大 CDF 绝对误差。候选稿按 1–25、26–30、31–46、47 及以后四段组织全样本量证明链；26–30 的比较、Gaussian Peano 精简及实际数值接合已有正文和复算材料。路线沿用 Rodziewicz–Kołodziejek 的 moment-defect 框架，保留前作归属。

**这是覆盖原完整命题的候选稿，还不是已获外部认可或已完整 Lean 核证的最终证明。** 其中经典数值输入已独立重建，其余具体数值和全域接合仍在进入 Lean，不能把已有文稿与完整形式化混为一谈。

### Lean 已经推进到哪里

本地工程固定 Lean/mathlib 4.35.0。已核对真实构建记录的具体成果包括：

| 范围 | 当前完成内容 |
|---|---|
| $n=1$ | 任意原标准化实分布、全部实阈值的 Esseen 目标；还得到更强的 $\Delta_1\le2\rho/5$。对应 `SingleSampleBound.sharp_one`。 |
| $n=2$ | 任意原标准化实分布、全部实阈值的完整 Esseen 目标。对应 `N2CertifiedBound.sharp_two`。 |
| 一个完整 Fourier 数值控制点 | 在 $n\ge42$、$\rho\ge7361/4000$、固定 $\beta=\rho/\sqrt n\approx0.2937993333$ 时，四项真实积分已接到实际 CDF，得到严格小于 $0.4071\beta<C_E\beta$ 的界。对应 `ControlCertifiedEndpoint.sharp_at_control_beta`；目前只是一处控制点。 |
| $n=47$ 的连续矩带 | 当 $9/5\le\rho\le7361/4000$ 时，任意原标准化实分布、全部实阈值的系数严格小于 $0.407<C_E$。当 $173303/96000\le\rho\le7361/4000$ 时还有更强的 $0.405$。对应 `UpperMomentN47Certified.sharp_on_moment_band`、`actual_cdf_lt_405`；没有支撑或前驱假设。 |
| $47\le n\le58$ 的完整矩带 | 任意原标准化实分布、全部实阈值，在 $173303/96000\le\rho\le7361/4000$ 上有 $\sqrt n\Delta_n/\rho\le256/625=0.4096<C_E$。对应 `UpperMomentBand47To58.sharp_on_sample_band`；没有支撑或前驱假设。 |
| 统一低矩资源 | 每个实际 $n\ge26$，保留全域 $C_{n-1}\le C_E$、原最大法则、$C\ge C_E$、$\rho\le1.1$，取得 joint $\kappa nD+n^{3/2}L\le92/75$ 与 $D\le18400/(997n)$，还保留更强的 actual-excess 项。对应 `UniformLowMomentRebatedAcquisition`；无自由 p/raw/D/phase。 |
| 原 n26 的连续局部排除 | 在完整 $C_{25}\le C_E$、原最大值、$C\ge C_E$、$\rho\le1.1$、$p\in[.39,.4]$ 下，同一最大元的 height 被压到 $(8.5,11)$；计数11至13的闭相位及整条右射线已排除。对应 `P39RightCountsExclusion.original_height_window`；没有输入旧 P39 profile。 |
| 原 n26 的共同方差与残差帽 | 同一原条件取得 $\delta<1/16$、$16v_0+14v_1<.32$、计数10至14的真实方差 $<.32$、实际噪声 $\lambda<.3172$ 及正组残差 a.e. $<9/16$，并接入共同 Q 参照。对应 `P39RefinedResidualCaps`；没有另加源帽或方差平面。 |
| 通用解析组件 | 任意 $n$ 的复数 Taylor 中心幂与 Bernstein 整区间控制，以及有限指标段的真实 CF/CDF 谱端点桥等已构建。对应 `GenericCenterPower`、`FiniteBandRayPrice`；定理保留各自的矩条件、指标范围及系数许可条件。 |

上述已核对定理的构建公理输出只列出 Lean 的标准公理，没有用 `sorryAx` 代替证明。**完整的 `SharpIidBerryEsseen` 尚未证明；[Target.lean](lean/BerryEsseen/Target.lean) 中的该名称目前是目标命题的定义。**

### 最新数值进展与剩余工作

下表只列独立重建高矩分支时，本地已返回的覆盖结果；比分指 $\sqrt n\,\Delta_n/\rho$，$\rho_0=7361/4000$。

| 指标与矩范围 | 保存的比分上界 |
|---|---|
| $n=5,\ \rho\ge\rho_0$ | $<99/242\approx0.40909091$ |
| $6\le n\le14,\ \rho\ge\rho_0$ | $\le0.4095$ |
| $15\le n\le30,\ \rho\ge1.9$ | $<0.408$；紧域已用 31 个闭谱节点接合，最大节点上界约为 $0.407706151$。 |
| $n\ge31,\ \rho\ge\rho_0$ | $<0.4097$；其中 $n\ge42$ 的既有结果更强，为 $<0.408$。 |

这些高矩覆盖已完成分阶段独立数学阅读、有理数接合和闭域复核。其具体数值证书仍在接入 Lean；本次上传的阶段包包含通用解析定理、完整数值控制点，以及另行接通的 n=47 连续矩带证书。

本轮还把当前无限尾部证明的经典 own-score 输入，压成四个有限单元：高斯递推支付其余指标，新的上矩 CF/CDF 谱估计用 14 个闭区间和一个点补齐剩余 240 个“指标—单元”组合。在原全域尖锐前驱条件下，这一项已可独立替换；原支撑与资源前提继续保留。实际 n=31 至46、ρ∈[1.6,7361/4000] 的连续 own-score 包络也已用同一方法接通，不依赖前驱条件。两项均完成独立数学阅读，保存数据和复算入口已经包含在数值阶段中。

Gaussian 递推价格的实指标单调性把四个 INITIAL own-score cutoff 降为 47、63、96、198，仍保留实际全域前驱。低矩分支现以真实异号事件和两个固定三次 CF 频段，对所有实际 $n\ge26$ 支付完整高尾价 $9/50$；归一化 $\sqrt n$、条件方差和无穷尾均保留。下一步利用真实联合资源完成局部排除，并接通剩余矩区间与小样本证明。

**English status:** The [30 October Lean stage](stages/2026-10-30/README.md) contains the all-law cases $n=1,2$, the certified Fourier and moment-band results above, and a uniform conditional low-moment resource theorem for every actual $n\ge26$. The latter acquires the entire infinite CF tail at price $9/50$ and the joint budget $\kappa nD+n^{3/2}L\le92/75$, retaining an additional actual-excess term. It keeps the original maximum and full predecessor hypotheses, with no free p/raw/defect/phase prices. The local exclusion step and full iid Lean theorem remain in progress.

The root snapshot was captured on 28 October 2026. Dated stage directories preserve subsequent verified components separately.

This preserves a candidate proof and ongoing Lean formalization. It does not assert complete Lean verification or external peer review.

See `核心问题与证明.md`, `manuscript/main.tex`, and `lean/BerryEsseen/Target.lean`. The complete companion packet is attached to this snapshot’s Release; extract it at the repository root. Historical links outside the captured folder refer to the original research workspace.
