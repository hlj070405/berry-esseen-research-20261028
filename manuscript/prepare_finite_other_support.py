"""2026-10-27: retain the other actual26..30 finite mathematical components.

Python 3.10+, standard library only. Copy selected original compressed inputs,
returned bodies, exact readers and small reader side inputs without expanding
their source trees. Run from any directory. No numerical producer, collector,
count acceptor, cloud job, report, status inventory or checksum list is run.

These are the floor25/actual-n acquisition and ordinary-count components and
the unconditional rho>=6/5 Fourier component. The later analytic profiles are
separately retained in companions/finite-steps. Partial historical executions
remain partial. The original numerical/reduction sources credit Rodziewicz
and Kolodziejek; their proof texts and source associations remain in the input
ZIPs. Project reconstruction and result readers are copied without edits.
Use read_finite_other_support.py for portable temporary source materialization.
"""
from __future__ import annotations

import argparse
import ast
import filecmp
from pathlib import Path
import shutil

PROJECT = Path(__file__).resolve().parent
WORKSPACE = PROJECT.parents[2]
DESTINATION = PROJECT / "companions/finite-other-support"
LOW = "berry-esseen-low26-30-20261026"
EXECUTION = "berry-esseen-low26-30-execution-20261026"
FOURIER = "berry-esseen-n26-30-route-20261026"

# Original archives are indivisible mathematical records. Some contain native
# stdout required by the retained joins; no unrelated standalone log is copied.
SELECTED = {
    LOW: (
        "fresh_inputs_low26_30_20261026.zip",
        "collect_low26_30_20261026.py",
        "low26_30_full_interface_reviewed_20261026.tex",
        "source/analytic/inspect_shared_frontier_20261026.py",
        "cloud-results-cnb-fvt-1k5qhmag2/fresh_results_low26_30_joined_20261026.zip",
    ),
    EXECUTION: (
        "fresh_exec_low26_30_resume_joined_20261026.zip",
        "cloud_low26_30_resume_joined_20261026.py",
        "submission_low26_30_resume_joined_20261026.json",
        "collect_low26_30_partial_b0_20261026.py",
        "partial_b0_join_20261026.json",
        "continuation_low26_30_metadata_20261026.py",
        "resume_low26_30_metadata_20261026.py",
        "join_n26_completed_subforests_20261027.py",
        "join_n27_completed_forests_20261027.py",
        "cloud-results-cnb-thh-1k5qujut6/fresh_results_low26_30_resume_joined_20261026.zip",
        "cloud-results-cnb-thh-1k5qujut6/fresh_summary_low26_30_resume_joined_20261026.json",
        "cloud-results-cnb-thh-1k5qujut6/result.json",
        "continuation-pass2-20261026/cloud-results-cnb-2d7-1k5r2m3ui/fresh_results_low26_30_cont_cd729b81671b_20261026.zip",
        "continuation-pass2-20261026/cloud-results-cnb-2d7-1k5r2m3ui/result.json",
    ),
    FOURIER: (
        "fresh_inputs_universal26_30_20261026.zip",
        "collect_universal26_30_20261026.py",
        "recover_universal26_30_completed_body_20261026.py",
        "cloud-results-cnb-803-1k5qdfgdc/fresh_results_universal26_30_20261026.zip",
        "cloud-results-cnb-803-1k5qdfgdc/result.json",
    ),
}


def selected_files(workspace: Path) -> list[Path]:
    files = [workspace / "work" / directory / name
             for directory, names in SELECTED.items() for name in names]
    # Only literal same-directory Python imports are followed. Frozen producer
    # imports are already present inside the input ZIPs, not expanded here.
    pending = [path for path in files if path.suffix == ".py"]
    included = set(files)
    while pending:
        path = pending.pop()
        tree = ast.parse(path.read_text(encoding="utf-8-sig"), filename=str(path))
        for node in ast.walk(tree):
            names = ([alias.name for alias in node.names] if isinstance(node, ast.Import)
                     else [node.module or ""] if isinstance(node, ast.ImportFrom) else [])
            for name in names:
                candidate = path.parent / (name.split(".")[0] + ".py")
                if candidate.is_file() and candidate not in included:
                    files.append(candidate)
                    included.add(candidate)
                    pending.append(candidate)
    missing = [str(path) for path in files if not path.is_file()]
    if missing:
        raise FileNotFoundError("Missing indispensable finite evidence: " + ", ".join(missing))
    return sorted(files)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--workspace", type=Path, default=WORKSPACE)
    parser.add_argument("--output", type=Path, default=DESTINATION)
    args = parser.parse_args()
    workspace, destination = args.workspace.resolve(), args.output.resolve()
    files = selected_files(workspace)
    # Validate every source before creating the collection. Existing different
    # artifacts are never silently replaced by a newer historical object.
    pairs = [(path, destination / path.relative_to(workspace)) for path in files]
    pairs.append((PROJECT / "read_finite_other_support.py", destination / "read_finite_other_support.py"))
    for source, target in pairs:
        if target.exists() and not filecmp.cmp(source, target, shallow=False):
            if target.name != "read_finite_other_support.py":
                raise FileExistsError(f"Different previously retained mathematical object: {target}")
    for source, target in pairs:
        if target.exists() and filecmp.cmp(source, target, shallow=False):
            continue
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, target)
    print("Retained original finite acquisition/count archives, Fourier bodies and mathematical readers.")
    print("The original low executions remain incomplete; later analytic steps have separate scope.")


if __name__ == "__main__":
    main()
