# Berry--Esseen: external arithmetic stage

Linjie Huang · Jiangsu Ocean University

30 October 2026 · Python 3.11+ · standard library only

This package preserves two completed numerical calculations and provides their
fixed rerun sequence. All bounds use integer outward intervals at scale 10^40
and exact `Fraction` arithmetic. Decimal text and elapsed-time metadata are
not inputs to the mathematical decisions. **These saved numerical bounds are
not Lean numerical certificates, and the all-n conjecture is not proved here.**

The analytic Lean source stage is [../2026-10-30](../2026-10-30), in particular
`BerryEsseen.UpperMomentDamping`, `UpperMomentSpectrumPrice`, and
`GaussianInitialMask`. Its README gives the pinned Lean build commands.

## What the calculations establish

For a real standardized iid law, write ρ=E|X|³, Δ for its normalized-sum CDF
error, and C_E=(3+√10)/(6√(2π)).

* **INITIAL47 own-score replacement:** conditional on the original full-domain
  sharp predecessor `fixedNSup (n-1) ≤ C_E`, the Gaussian recurrence and four
  finite Fourier cases replace the classical INITIAL own-score input for
  every integer n≥47 and 1≤ρ≤7361/4000. Gaussian masks pay cells 0 through 19;
  cells 20 through 23 require 240 finite `(n,cell)` pairs, represented by 14
  closed spectral nodes and one integer point. The four Gaussian cutoffs are
  48, 66, 101, and 213. There are 28 distinct endpoint prices.
* **Finite n=31 through 46 affine envelope:** for every actual ρ in the closed
  interval [8/5,7361/4000], the Fourier bounds establish
  `sqrt(n)*Δ/ρ ≤ min(.469, .3322*(1+.429/ρ), .3031*(1+.646/ρ))`.
  These Fourier prices do **not** require the sharp predecessor. At each
  fixed upper moment U, the output normalization `rhoLower=1` makes the
  computed quantity B=`sqrt(nu)*absolute_Delta`; it does not assume actual
  ρ=1. Three exact affine budgets determine a lower moment L only after the
  prices are fixed. Eight coarse rounds and four fine continuation rounds
  give an exact closed union [8/5,7361/4000], using 41 distinct prices.

Neither result eliminates the original support or charged-resource premises,
completes the entire INITIAL certificate, or proves the full conjecture. The
noninteger variable `nu` labels deterministic spectral profiles, never an iid
sample size. The evaluator uses the same full two-cap sine forcing and fixed
upper-moment characteristic-function spectrum throughout each node.

中文状态：本阶段含 INITIAL47 条件 own-score 替换，以及实际 n=31..46、
ρ∈[8/5,7361/4000] 的有限 affine T 包络。前者保留原全域 sharp predecessor
假设；后者 CF 比较不需要该假设。数值仍是外部整数区间复算，尚未成为 Lean
数值核证；support、charged 及完整猜想没有因此完成。

## Verify the saved arithmetic

From this package directory:

```sh
python -I -B verify_saved.py
```

This fast check reads `saved/` and does **not** rerun the integrals. It checks
physical parameter enclosures, the four-term sums and normalization, complete
attempt records, literal price reuse, exact chord factors, Gaussian gates,
the INITIAL47 join, affine budgets/lower thresholds, and closed-interval union.
It does not independently recalculate the 69 stored integral prices. Python
assertions must remain enabled; do not use `-O`.

## Recompute into a new directory

```sh
python -I -B recompute.py --results-dir results/fresh
```

The output directory must be new or empty. The sequence is n47 pilot → original
two-node calculation (3 new prices) → case23 completion (11) → other three
INITIAL47 cases (13) → INITIAL47 join → eight coarse affine rounds (24) → four
fine affine rounds (17) → final saved-arithmetic checks. Including the pilot,
this recomputes **69 different endpoint prices**. Each process uses two CPUs;
on Linux it selects the first two allowed CPUs when the cpuset excludes 0/1.
Every downstream seed and the collector use this new directory exclusively.
The distributed saved results are never used as rerun seeds or overwritten.

For a bounded n47 rerun:

```sh
python -I -B recompute.py --results-dir results/n47-only --stop-after pilot
```

The other `--stop-after` choices are `two-node`, `case23`, `remaining`,
`initial47`, and `affine-coarse`. A partial rerun is not a completed cover.
Full recalculation can take substantial time. Checkpoints retain complete
prices and partial terms separately; producer scripts in `src/` also expose
their original new-output resume options.

## Preserved history and sources

The original right parent chord in `upper_moment_sine_nodes.json` remains
**failed**. Its four completed source prices remain literal reusable prices;
case23 completion replaces that chord with two narrower nodes. The first
affine run remains **incomplete after its fixed 8-round/24-price budget**;
the continuation retains all 24 prices, reuses the last anchor's three prices,
adds 17 prices, and closes the moment union. Neither old false status is
changed into a pass. Historical analytic-bridge flags are preserved as written
at generation time; later analytic Lean proofs are in the linked source stage.

`src/` contains the actual producers and five pure helper extractions from
their historical probe modules. Numerical formulas, cutoffs, meshes, budgets,
and mathematical decisions are unchanged. Packaging changes are limited to
removing unused historical drivers/import chains, portable CPU selection,
explicit result-directory plumbing, and normalizing path metadata to relative
file names consistently, including literal reused records.

The moment-defect framework and finite-index proof program are credited to
**Kacper Rodziewicz and Bartosz Kołodziejek**:
[working manuscript v3](https://hexagonmath.org/2610.00147v3),
[frozen sources](https://github.com/rodziewiczk/berry-esseen-045-certificate/tree/75a94708872e2bc053f42a279559b23ed91e4402).
The compensated Taylor/circle and classical constant framework is credited to
**Irina Shevtsova**, including
[Taylor bounds](https://arxiv.org/abs/1301.2783v3),
[moment estimates](https://ami.uni-eszterhazy.hu/uploads/papers/finalpdf/AMI_39_from241to307.pdf),
and [structural constants](https://www.mathnet.ru/eng/ia252).
The smoothing method is due to
[H. Prawitz (1972)](https://doi.org/10.1080/03461238.1972.10404645);
the analytic Lean smoothing and probability leaves use **Jiyuan Tan's
[CausalSmith / Causalean](https://github.com/Jiyuan-Tan/CausalSmith/tree/a7085d88d2e4b30003db7097ca374f4718da0f01)**,
whose upstream notices and licenses are preserved in the linked Lean stage.
No upstream software license is reassigned, and no new repository-wide license
is declared for project-authored material here.
