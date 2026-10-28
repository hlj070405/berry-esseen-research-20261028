"""2026-10-27: collect the actual finite-comparison sources for local review.

Preserve the original directory relationships so the exact-arithmetic
programs can run from the copied directory. These are the analytic
middle-moment profiles and seven lower-moment replacements, conditional
on the acquired resources and global predecessors.
No remote job, upload, hash inventory, or acquisition replay is started.
"""
from __future__ import annotations

import ast
from pathlib import Path
import shutil

PROJECT = Path(__file__).resolve().parent
WORKSPACE = PROJECT.parents[2]
SOURCE = WORKSPACE / "work/berry-esseen-low26-30-20261026"
DESTINATION = PROJECT / "companions/finite-steps"
LOWER_MOMENT_PROGRAMS = {
    "probe_b0_shared_reference_20261027.py",
    "probe_b0_p39_shared_20261027.py",
    "b0_allocation_interval_clip_20261027.py",
    "probe_b0_p41_shared_20261027.py",
    "b0_two_endpoint_budget_20261027.py",
    "b0_signed_allocation_interval_20261027.py",
    "probe_b0_n27_p41_shared_20261027.py",
    "probe_b0_n28_p41_shared_20261028.py",
    "b0_variance_endpoint_branches_20261028.py",
    "probe_b0_n29_p41_shared_20261028.py",
    "probe_b0_n30_p41_shared_20261028.py",
}


def main() -> None:
    files = [
        SOURCE / "fresh_inputs_low26_30_20261026.zip",
        SOURCE / "actual_resource_proposals_20261026.json",
        SOURCE / "low26_30_full_interface_reviewed_20261026.tex",
        SOURCE / "source/analytic/finite_gap_shared_stoploss_20261026.tex",
        SOURCE / "source/analytic/gaussian_contact_peano_20261028.tex",
        SOURCE / "source/analytic/classical_order_compression_20261028.tex",
        SOURCE / "source/analytic/improved_gaussian_entry_20261028.tex",
        SOURCE / "source/cutoff25_20261011/new_low/initial25_b0_v2/INITIAL25_B0_PROOF.json",
        SOURCE / "source/cutoff25_20261011/new_low/resource25_b0_v1/RESOURCE_B0_GLOBAL_PROOF.json",
    ]
    for subdir in ("analytic", "count_kernel", "bridge"):
        candidates = sorted((SOURCE / "source" / subdir).glob("*.py"))
        # Current research probes are written beside the established entries.
        # Only adopted B0 proofs belong to this manuscript's source collection.
        files.extend(path for path in candidates if subdir != "analytic"
                     or not path.name.startswith(("probe_b0_", "b0_"))
                     or path.name in LOWER_MOMENT_PROGRAMS)
    # Follow root-level helper imports instead of discovering them one failure
    # at a time. The analytic/kernel/bridge modules already retain their paths.
    root_modules = {path.stem: path for path in SOURCE.glob("*.py")}
    pending = [path for path in files if path.suffix == ".py"]
    included = set(files)
    while pending:
        path = pending.pop()
        tree = ast.parse(path.read_text(encoding="utf-8-sig"))
        for node in ast.walk(tree):
            names = ([alias.name for alias in node.names] if isinstance(node, ast.Import)
                     else [node.module or ""] if isinstance(node, ast.ImportFrom) else [])
            for name in names:
                dependency = root_modules.get(name.split(".")[0])
                if dependency is not None and dependency not in included:
                    files.append(dependency)
                    included.add(dependency)
                    pending.append(dependency)
    result_names = (
        "result_b0_n28_p41_complete_fresh_20261028.json",
        "result_b0_n30_p41_complete_frozen_20261028.json",
        "result_b0_n29_p41_complete_fresh_20261028.json",
        "result_b0_n27_p41_complete_fresh_20261027.json",
        "result_b0_n26_p41_complete_frozen_20261027.json",
        "result_b0_n26_p39_complete_frozen_20261027.json",
        "result_b0_n26_p40_complete_frozen_20261027.json",
        "result_n26_p35_quartic_free_fresh_20261027.json",
        "result_n26_p36_count10_simple_fresh_20261027.json",
        "result_n26_p37_count10_simple_fresh_20261027.json",
        "result_n27_central_complete_fresh_20261027.json",
        "result_n28_p37_complete_fresh_20261027.json",
        "result_n29_p35_complete_fresh_20261027.json",
        "result_n29_p37_complete_fresh_20261027.json",
        "result_n30_analytic_panels_fresh_20261027.json",
    )
    files.extend(SOURCE / "source/analytic" / name for name in result_names)
    for name in (
        "n28_p38_analytic_complete_fresh_20261027.json",
        "n28_p39_complete_fresh_20261027.json",
        "n28_p40_complete_fresh_20261027.json",
    ):
        files.append(SOURCE / name)
    if not all(path.is_file() for path in files):
        missing = [str(path.relative_to(SOURCE)) for path in files if not path.is_file()]
        raise FileNotFoundError("Missing actual source files: " + ", ".join(missing))
    for path in files:
        relative = path.relative_to(SOURCE)
        target = DESTINATION / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(path, target)
    # Original incoming physical bounds for the Peano radial replacement;
    # retain the small actual objects rather than unpacking the full tail run.
    peano_inputs = DESTINATION / 'source/analytic/support_peano_inputs'
    peano_inputs.mkdir(parents=True, exist_ok=True)
    tail_source = WORKSPACE / 'work/berry-esseen-n49-check-20261025/legacy49/legacy_phase'
    for name in ('central47_prep_proof.json', 'complement47_accepted.json',
                 'signed_resource47_table.json'):
        shutil.copy2(tail_source / name, peano_inputs / name)
    print("Prepared finite-comparison programs, acquired inputs and selected fresh outputs.")
    print("Scope: analytic profiles; global predecessor/acquisition proofs remain separate.")


if __name__ == "__main__":
    main()
