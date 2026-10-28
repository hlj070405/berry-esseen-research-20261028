"""2026-10-27: retain the actual arithmetic sources and outputs for input (I).

Python 3.10+, standard library only. Run from any directory; --list is read-only.
Copy existing frozen archives, mathematical readers and their literal local
imports, preserving workspace-relative paths below companions/low-index-support.
No calculation, download, cloud job, historical-state edit or report is run.

The underlying public certificates and comparison code are due to Rodziewicz
and Kolodziejek. The n2/n3 sources are fixed at commit
044e93ec97f377752924fe32bd08e0bc6f4334b1; the original fifth-index archive is
the cutoff5-sources-2026-10-20 release. The later frozen input and returned
archives contain this project's actual reconstruction/recomputation adapters.
All selected source contents and original archives are copied unchanged.

Frozen input ZIPs already contain the required per-panel code, coefficients,
contracts and forests: do not duplicate their expanded source trees here.
For n2/n3/n4 no returned-result ZIP exists locally; retain only the exact
mathematical shard/root objects needed by the existing readers. The n4
terminal objects and n10 two outer-process objects are retained solely because
the original joins read them; those fields establish no inequality.

See read_low_index_support.py --help and --describe for reading/extraction.
This collection is not a claim that every original numerical producer has
been ported or rerun. In particular, most original joins need python-flint;
n3 numerical replay needs a C++17 compiler and Boost.Multiprecision headers.
"""
from __future__ import annotations

import argparse
import ast
from dataclasses import dataclass
import filecmp
from fractions import Fraction as F
from pathlib import Path
import shutil

PROJECT = Path(__file__).resolve().parent
DEFAULT_WORKSPACE = PROJECT.parents[2]
DEFAULT_OUTPUT = PROJECT / "companions/low-index-support"


@dataclass(frozen=True)
class Block:
    name: str
    directory: str
    archives: tuple[str, ...] = ()
    readers: tuple[str, ...] = ()
    objects: tuple[str, ...] = ()


# These are exact existing proof-bearing artifacts, not a search over work/.
# A result ZIP may include original native calculation stdout. It is preserved
# as an indivisible original archive, rather than copying arbitrary log trees.
BLOCKS = (
    Block("n1", "berry-esseen-n1-base-20261024",
          readers=("verify_certificate_20261024.py",), objects=("rational-certificate.json",)),
    Block("n2", "berry-esseen-n2-public-check-20261024",
          ("berry_n2_public_sources_20261024.zip",),
          ("collect_replay_20261024.py", "replay_shard_20261024.py",
           "public-n2/tensor_certificate.py", "public-n2/verify_algebra.py")),
    Block("n3", "berry-esseen-n3-public-check-20261024",
          ("berry_n3_public_sources_20261024.zip",),
          ("collect_replay_20261024.py", "replay_shard_20261024.py",
           "public-n3/verify_algebra.py")),
    Block("n4", "berry-esseen-n4-public-check-20261024",
          ("n4_full206_inputs_20261025.zip",),
          ("check_full_closure_exact_20261025.py",)),
    Block("n5", "berry-esseen-c5-complete-20261025",
          ("cutoff5_20261020.zip", "c5_low_inputs_20261025.zip",
           "c5_complement_inputs_20261025.zip",
           "cloud-results-cnb-ii6-1k5p2u76k/c5_low_results_20261025.zip",
           "cloud-results-cnb-41g-1k5p0cks7/c5_complement_results_20261025.zip"),
          ("check_final_semantic_joins_20261025.py", "c5_low_fresh_20261025.py",
           "replay_gapfree_arb_20261025.py", "replay_supported_fourier_arb_20261025.py",
           "check_complement_support_arb_20261025.py", "native_proof_launch_20261025.py"),
          ("gapfree_arb_result_20261025.json",)),
    Block("n6", "berry-esseen-n6-complete-20261025",
          ("n6_fresh_inputs_20261025.zip", "n6_resume_inputs_20261025.zip",
           "cloud-results-cnb-go8-1k5pb2cff/n6_resume_results_20261025.zip"),
          ("check_n6_final_join_20261025.py",)),
    Block("n7", "berry-esseen-n7-complete-20261025",
          ("n7_fresh_inputs_20261025.zip",
           "cloud-results-cnb-8c4-1k5pfq0ca/n7_fresh_results_20261025.zip"),
          ("check_n7_final_join_20261025.py",)),
    Block("n8", "berry-esseen-n8-complete-20261025",
          ("n8_fresh_inputs_20261025.zip",
           "cloud-results-cnb-fei-1k5pn5c61/n8_fresh_results_20261025.zip"),
          ("check_n8_final_join_20261025.py",)),
    Block("n9", "berry-esseen-n9-complete-20261025",
          ("n9_fresh_inputs_20261025.zip",
           "cloud-results-cnb-km9-1k5poq2qb/n9_fresh_results_20261025.zip"),
          ("check_n9_final_join_20261025.py",), ("nine_sum_interface_20261025.tex",)),
    Block("n10", "berry-esseen-n10-complete-20261025",
          ("n10_fresh_inputs_20261025.zip",
           "cloud-results-cnb-8us-1k5pvigve/n10_fresh_results_20261025.zip"),
          ("check_n10_final_join_20261026.py",),
          ("cloud-results-cnb-8us-1k5pvigve/result.json",
           "cloud-results-cnb-8us-1k5pvigve/state.json")),
    Block("n11-14", "berry-esseen-n11-14-complete-20261026",
          ("fresh_inputs_11_14_20261026.zip",
           "cloud-results-cnb-qok-1k5q1oee3/fresh_results_11_14_20261026.zip"),
          ("check_final_join_11_14_20261026.py", "execution_adapter_11_14_20261026.py")),
    Block("n15-19", "berry-esseen-n15-19-complete-20261026",
          ("fresh_inputs_15_19_20261026.zip",
           "cloud-results-cnb-bro-1k5q4l130/fresh_results_15_19_20261026.zip"),
          ("check_final_join_15_19_20261026.py",)),
    Block("n20", "berry-esseen-n20-singlebatch-20261026",
          ("fresh_inputs_n20_20261026.zip",
           "cloud-results-cnb-sp7-1k5q6q86l/fresh_results_n20_20261026.zip"),
          ("check_final_join_n20_20261026.py",)),
    Block("n20-resume", "berry-esseen-n20-resource-resume-20261026",
          ("n20_completed_state_20261026.zip",
           "cloud-results-cnb-p0c-1k5q8s68o/fresh_results_n20_20261026.zip"),
          ("execution_adapter_n20_resource_20261026.py",)),
    Block("n21-24", "berry-esseen-n21-24-complete-20261026",
          ("fresh_inputs_21_24_20261026.zip",
           "cloud-results-cnb-ml0-1k5q9kl2s/fresh_results_21_24_20261026.zip"),
          ("check_final_join_21_24_20261026.py",)),
    Block("n25", "berry-esseen-n25-full-parent-20261026",
          ("fresh_inputs_low25_20261026.zip", "fresh_inputs_universal25_20261026.zip",
           "cloud-results-cnb-l6u-1k5qb64qh/fresh_results_low25_20261026.zip",
           "cloud-results-cnb-80t-1k5q8k45j/fresh_results_universal25_20261026.zip"),
          ("collect_low25_20261026.py", "collect_universal25_20261026.py")),
)


def local_imports(path: Path) -> set[Path]:
    """Follow only literal .py imports in the same mathematical source folder."""
    tree = ast.parse(path.read_text(encoding="utf-8-sig"), filename=str(path))
    names = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            names.update(alias.name.split(".")[0] for alias in node.names)
        elif isinstance(node, ast.ImportFrom) and node.module:
            names.add(node.module.split(".")[0])
    return {p for name in names if (p := path.parent / (name + ".py")).is_file()}


def selected_sources(workspace: Path) -> set[Path]:
    paths: set[Path] = set()
    pending: list[Path] = []
    for block in BLOCKS:
        base = workspace / "work" / block.directory
        paths.update(base / name for name in block.archives + block.objects)
        pending.extend(base / name for name in block.readers)
    while pending:
        path = pending.pop()
        if path in paths:
            continue
        if not path.is_file():
            raise FileNotFoundError(path)
        paths.add(path)
        pending.extend(local_imports(path) - paths)

    # Exact four-shard mathematical result covers; no cloud job/state trees.
    cloud = workspace / "work/berry-esseen-block-square-20261024/cloud"
    for n, run in ((2, "results-cnb-8hc-1k5muheu4"), (3, "results-cnb-cv2-1k5n1cl77")):
        paths.update(cloud / run / f"public_n{n}_shard_{i}/shard-result.json" for i in range(4))

    # The complete n4 root set follows the exact original strict-cap geometry.
    base = (workspace / "work/berry-esseen-n4-public-check-20261024/"
            "cloud-results-cnb-ac7-1k5neea2u/full206-batch-20261025")
    paths.add(base / "batch-config.json")
    roots = []
    w0, cap = F(625, 2116), F(46, 25)
    for index in range(260):
        i, j = divmod(index, 13)
        wh = w0 + (1 - w0) * F(i + 1, 20)
        tl = F(j, 20)
        if (1 + tl * tl)**2 / (wh * (1 - tl * tl)) < cap * cap:
            roots.append(index)
            paths.update(base / f"root-{index}" / name for name in ("result.json", "terminal.json"))
    if len(roots) != 206:
        raise ValueError("The exact fourth-index domain must have 206 nonempty roots")

    # Independent existing algebra/interface readers retain their original paths.
    paths.update(workspace / "work" / name for name in (
        "berry-esseen-n4-analytic-check-20261025/check_analytic_20261025.py",
        "berry-esseen-n4-high-check-20261025/check_high_interface.py",
        "berry-esseen-n4-low-check-20261025/low_cf_independent_algebra_20261025.py",
    ))
    for path in paths:
        if not path.is_file() or not path.resolve().is_relative_to(workspace):
            raise FileNotFoundError(f"Required existing arithmetic artifact unavailable: {path}")
    return paths


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--workspace", type=Path, default=DEFAULT_WORKSPACE)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--list", action="store_true", help="show selected existing artifacts; write nothing")
    args = parser.parse_args()
    workspace, output = args.workspace.resolve(), args.output.resolve()
    sources = selected_sources(workspace)
    reader = PROJECT / "read_low_index_support.py"
    if not reader.is_file():
        raise FileNotFoundError(reader)
    pairs = [(source, output / source.relative_to(workspace)) for source in sorted(sources)]
    pairs.append((reader, output / reader.name))
    if args.list:
        for source, destination in pairs:
            print(f"{source.relative_to(workspace) if source.is_relative_to(workspace) else source} -> {destination.relative_to(output)}")
        print(f"Selected bytes: {sum(p.stat().st_size for p, _ in pairs):,}")
        return
    for source, destination in pairs:
        if not destination.resolve().is_relative_to(output):
            raise ValueError(f"Destination escapes the selected collection: {destination}")
        destination.parent.mkdir(parents=True, exist_ok=True)
        if destination.exists():
            if not destination.is_file() or not filecmp.cmp(source, destination, shallow=False):
                raise FileExistsError(f"Existing companion differs: {destination}")
            continue
        shutil.copy2(source, destination)
    print(f"Retained {len(pairs)} existing arithmetic artifacts in {output}")
    print("No numerical replay or historical-state modification was performed.")


if __name__ == "__main__":
    main()
