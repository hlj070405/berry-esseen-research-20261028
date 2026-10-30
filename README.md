# Berry–Esseen research snapshot

我是软件工程专业的学生。这个项目起初就是出于好奇，用 GPT 跑着玩的，也想借这个过程边做边学。

欢迎概率论、正态近似、Berry–Esseen 不等式和 Lean 形式化相关领域的朋友来交流，一起审查推导、计算和代码。有疑问或发现错误，欢迎提 Issue 或 PR！

**Lean 形式化正在进行中～** 当前材料仍是候选证明和阶段性成果，完整 Lean 验证尚未完成，也尚未经过外部同行评审。

这个是不是挺重要的一个公开问题?可以点点star吗,我都还没有过什么star🌟

I'm a software engineering student, and this project started as a just-for-fun exploration with GPT. Researchers in probability, normal approximation, and Lean are welcome to discuss the work and help review the arguments, computations, and code. Lean formalization is ongoing; complete Lean verification and external peer review are still pending.

## 当前进度（2026-10-30）

**本轮已完成的 Lean 阶段源码见 [stages/2026-10-30](stages/2026-10-30/README.md)。** 包含独立可构建的依赖闭包、精确版本和来源说明。根目录的 `lean/`、论文与旧 Release 保留 10 月 28 日快照；进一步的数值覆盖正继续接入 Lean。

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

**这是覆盖原完整命题的候选稿，还不是已获外部认可或已完整 Lean 核证的最终证明。** 其中引用的经典数值输入正在独立重建，不能把已有文稿与完整形式化混为一谈。

### Lean 已经推进到哪里

本地工程固定 Lean/mathlib 4.35.0。已核对真实构建记录的具体成果包括：

| 范围 | 当前完成内容 |
|---|---|
| $n=1$ | 任意原标准化实分布、全部实阈值的 Esseen 目标；还得到更强的 $\Delta_1\le2\rho/5$。对应 `SingleSampleBound.sharp_one`。 |
| $n=2$ | 任意原标准化实分布、全部实阈值的完整 Esseen 目标。对应 `N2CertifiedBound.sharp_two`。 |
| 一个完整 Fourier 数值控制点 | 在 $n\ge42$、$\rho\ge7361/4000$、固定 $\beta=\rho/\sqrt n\approx0.2937993333$ 时，四项真实积分已接到实际 CDF，得到严格小于 $0.4071\beta<C_E\beta$ 的界。对应 `ControlCertifiedEndpoint.sharp_at_control_beta`；目前只是一处控制点。 |
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

这些高矩覆盖已完成分阶段独立数学阅读、有理数接合和闭域复核。其具体数值证书仍在接入 Lean；本次上传的阶段包包含通用解析定理和上表所述的一个完整数值控制点。

本轮还把当前无限尾部证明的经典 own-score 输入，压成四个有限单元：高斯递推支付其余指标，新的上矩 CF/CDF 谱估计用 14 个闭区间和一个点补齐剩余 240 个“指标—单元”组合。在原全域尖锐前驱条件下，这一项已可独立替换；原支撑与资源前提继续保留。实际 n=31 至46、ρ∈[1.6,7361/4000] 的连续 own-score 包络也已用同一方法接通，不依赖前驱条件。两项均完成独立数学阅读，保存数据和复算入口已经包含在数值阶段中。

接下来重点把已重建的数值证书、资源取得与支撑/矩条件按原依赖接回 Lean，最终装配全分布、全样本量定理。欢迎对候选数学证明、实际计算和形式化代码分别提出具体问题。

**English status:** There is a computer-assisted candidate manuscript addressing the full iid conjecture. The [30 October Lean stage](stages/2026-10-30/README.md) contains the all-law cases $n=1,2$, one fully certified Fourier control point, and the verified analytic components described there. The full all-n theorem remains in progress. Further numerical covers are being connected to Lean.

The root snapshot was captured on 28 October 2026. Dated stage directories preserve subsequent verified components separately.

This preserves a candidate proof and ongoing Lean formalization. It does not assert complete Lean verification or external peer review.

See `核心问题与证明.md`, `manuscript/main.tex`, and `lean/BerryEsseen/Target.lean`. The complete companion packet is attached to this snapshot’s Release; extract it at the repository root. Historical links outside the captured folder refer to the original research workspace.
