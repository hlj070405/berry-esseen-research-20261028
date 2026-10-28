#!/usr/bin/env python3
"""2026-10-27: collect and read the actual uniform n>=47 proof computation.

Python 3.10+; standard library only.  With no option, copy the original
compressed source/input archive, its returned arithmetic transcripts, and their
original mathematical join into companions/uniform-tail.  Differing original
materials are never overwritten; this helper's collected copy is updated.
No arithmetic acceptor, cloud job or timer runs.

    python prepare_uniform_tail_support.py
    python prepare_uniform_tail_support.py --list
    python prepare_uniform_tail_support.py --reader-check --join-results
    python prepare_uniform_tail_support.py --unpack NEW_DIRECTORY --show-jobs

The copied script also works after moving the collection to another directory.
--unpack preserves the archive's source/... tree and all relative imports.
--show-jobs gives the original cwd/argv of the uniform local calculation only.
Those entrypoints reconstruct the fixed numerical witnesses; unpacking or this
script's reader checks do not replace their arithmetic replay.

--reader-check temporarily unpacks a separate copy and imports the unchanged
exact local coverage reader.  It rebuilds the closed noise/phase cover, scalar
normalizations and LOW row contracts from the actual mathematical objects.
The original schedule reader is also run there through the dated launcher.
It changes exactly its two native-path dictionary key expressions to
.as_posix(); arithmetic and original source/input bytes stay unchanged.
--join-results runs the
unchanged 2026-10-25 transcript/target join against the collected two archives.
The latter deliberately retains its full historical 55-job scope, including
finite exclusions unused by the present C45,C46-to-n>=47 tail composition.

The source archive is the unmodified selected 2026-10-25 package from
rodziewiczk/berry-esseen-045-certificate, public commit
044e93ec97f377752924fe32bd08e0bc6f4334b1, acquired in
work/berry-esseen-n49-check-20261025.  Its original attribution, proof texts,
fixed source bindings and historical statuses remain inside the archive.
The original returned run used CPython 3.12.15 on Linux.  Only the relocated
readers, not the expensive acceptors, are checked by --reader-check here.

The archive contains broader historical material.  In particular its old
global composition, finite A40/P41/A45/P46/A46 scaffold, prior99 prose and
success labels are not additional premises of the new tail proof.  Mathematical
continuum arguments are in source/paper, source/paper_entry, source/paper_local
and source/audit/legacy_phase_repair.tex; the readable companion copies remain
in ../large-index/analytic-route in the manuscript collection.
"""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path, PurePosixPath
import shutil
import subprocess
import sys
import tempfile
import zipfile


HERE = Path(__file__).resolve().parent
SOURCE_ARCHIVE = "n49_sources_20261025.zip"
RESULT_ARCHIVE = "cloud-results-cnb-26f-1k5p45hdg/n49_replay_results_20261025.zip"
ORIGINAL_JOIN = "join_n49_fresh_results_20261025.py"
SCRIPT = "prepare_uniform_tail_support.py"
SCHEDULE_LAUNCHER = "run_schedule_reader_20261027.py"
OLD = "source/baseline/certificates/work/below50_20260929/"

# These are mathematical routes, not a new manifest or acceptance result.
# Paths refer to members of the unchanged source archive.
ROUTES = (
    ("All-index support, including the infinite index band", (
        OLD + "structural/accept_unrestricted_cover50.py",
        OLD + "structural/fifth_heat50.py",
        OLD + "structural/heat_support50.py",
        OLD + "structural/support50_proof.tex",
        "source/paper/sections/support.tex")),
    ("Acyclic resource acquisition to 45 central and 38 left rows", (
        "source/baseline/entry/schedule.json",
        "source/baseline/entry/validate_schedule.py",
        "source/paper_entry/resource_entry.tex",
        "source/paper_entry/entry_formula_atlas.tex",
        OLD + "entry/initial47_proof.json",
        OLD + "entry/sperner_feedback47_table.json",
        OLD + "entry/left270_input47_table.json")),
    ("Corrected preliminary/complementary phase and later signed domains", (
        "source/legacy_phase/accept_phase_corrected_v3.py",
        "source/legacy_phase/corrected_phase_callback_v2.py",
        "source/legacy_phase/check_later_phase_premises.py",
        "source/audit/portable_audit_phase_scope.py",
        "source/audit/legacy_phase_repair.tex")),
    ("Confinement, antichain feedback and noise profiles", (
        OLD + "local/confinement47_certificate.json",
        OLD + "local/sperner47_certificate.json",
        OLD + "local/left_sperner47_certificate.json",
        OLD + "local/sperner47_profile_certificate.json",
        OLD + "local/left_sperner47_profile_certificate.json")),
    ("One TINY and two MID numerical objects", (
        OLD + "local/tiny47wide_certificate.json",
        OLD + "local/mid47a_certificate.json",
        OLD + "local/left_mid47b_certificate.json")),
    ("Three LOW numerical objects", (
        OLD + "root/low47_constructed02.json",
        OLD + "root/phase_left_low47_constructed01.json",
        OLD + "root/positive_left_low47_constructed02.json")),
    ("Normalization, exact closed coverage and the uniform local derivation", (
        OLD + "entry/accept_low47_normalization.py",
        OLD + "root/low47_normalization.py",
        OLD + "local/tiny47wide_normalization.py",
        OLD + "local/mid47a_normalization.py",
        OLD + "local/left_mid47b_normalization.json",
        OLD + "local/final_review/check_local47_coverage.py",
        OLD + "local/final_review/LOCAL47_COVERAGE.json",
        "source/baseline/local/check_consolidation.py",
        "source/paper_local/local_comparison.tex",
        "source/paper/sections/global_route.tex")),
)

# The full archives retain their old 55-entrypoint scope.  This list selects
# only original entrypoints needed by the uniform local exclusion, omitting
# the finite/global scaffold.  The original schedule specifies dependency order;
# this presentation order does not launch or certify these jobs.
UNIFORM_JOBS = (
    "certificate_unrestricted_support384", "certificate_high_tail",
    "certificate_high_window", "certificate_initial47",
    "certificate_central_support47", "certificate_central_strip47",
    "corrected_legacy_acquisition", "later_phase_domains",
    "independent_phase_scope", "certificate_central_input47",
    "certificate_original_confinement47", "certificate_confined_feedback47",
    "certificate_sperner47", "certificate_sperner_feedback47",
    "certificate_left_support47", "certificate_left_input47",
    "certificate_signed_resource47", "certificate_left_radius270",
    "certificate_left270_input47", "certificate_left_strip47",
    "certificate_left_sperner47", "certificate_central_profile47",
    "certificate_left_profile47", "certificate_tiny_wide47",
    "certificate_central_mid47", "certificate_left_mid47b",
    "certificate_low_normalization47", "certificate_central_low47",
    "certificate_left_low47", "certificate_positive_left_low47",
    "coverage_local47", "entry_schedule_mapping", "local_formula_mapping",
)


def collection_default() -> Path:
    return HERE if (HERE / SOURCE_ARCHIVE).is_file() else HERE / "companions/uniform-tail"


def source_default() -> Path | None:
    for parent in (HERE, *HERE.parents):
        candidate = parent / "work/berry-esseen-n49-check-20261025"
        if (candidate / SOURCE_ARCHIVE).is_file():
            return candidate
    return None


def copy_original(source: Path, target: Path) -> None:
    if not source.is_file():
        raise FileNotFoundError(source)
    target.parent.mkdir(parents=True, exist_ok=True)
    if target.exists():
        if not target.is_file() or target.read_bytes() != source.read_bytes():
            raise ValueError(f"Refuse to replace differing collected material: {target}")
    else:
        shutil.copy2(source, target)


def prepare(origin: Path, collection: Path) -> None:
    for name in (SOURCE_ARCHIVE, RESULT_ARCHIVE, ORIGINAL_JOIN):
        copy_original(origin / name, collection / name)
    current_script = Path(__file__).resolve()
    collected_script = collection / SCRIPT
    if current_script != collected_script:
        shutil.copy2(current_script, collected_script)
    (collection / SCHEDULE_LAUNCHER).write_text(SCHEDULE_LAUNCHER_SOURCE, encoding="utf-8")
    print(f"Collected unchanged source/input archive, returned transcripts and original join: {collection}")


def check_routes(collection: Path) -> None:
    with zipfile.ZipFile(collection / SOURCE_ARCHIVE) as archive:
        names = set(archive.namelist())
        for title, paths in ROUTES:
            for path in paths:
                if path not in names:
                    raise FileNotFoundError(f"Required mathematical material absent: {path}")


def show_routes(collection: Path) -> None:
    check_routes(collection)
    for title, paths in ROUTES:
        print(title)
        for path in paths:
            print("  " + path)


def show_jobs(collection: Path) -> None:
    with zipfile.ZipFile(collection / SOURCE_ARCHIVE) as archive:
        new = json.loads(archive.read("source/new_jobs.json"))
        retained = json.loads(archive.read("source/retained_jobs.json"))
    jobs = {j["name"]: {"cwd": "source/" + j["cwd"], "argv": j["argv"]} for j in new}
    jobs.update({j["name"]: {"cwd": "source/baseline/certificates/" + j["cwd"],
                             "argv": j["argv"]} for j in retained})
    jobs.update(entry_schedule_mapping={"cwd": "source/baseline/entry", "argv": ["validate_schedule.py"]},
                local_formula_mapping={"cwd": "source/baseline/local", "argv": ["check_consolidation.py"]})
    for name in UNIFORM_JOBS:
        print(json.dumps(dict(name=name, **jobs[name]), ensure_ascii=False))
    print(json.dumps(dict(schedule_reader_launcher=str(collection / SCHEDULE_LAUNCHER),
                          argument="UNPACKED_DIRECTORY/source/baseline/entry/validate_schedule.py",
                          change="Only object-map keys on original lines 45 and 91 use .as_posix().")))
    print("Run each original argv with unoptimized Python, -B, in its stated unpacked cwd. "
          "The result archive records the original run; this command list performs no replay.")


def unpack(collection: Path, destination: Path) -> None:
    if destination.exists():
        raise FileExistsError(f"A fresh destination is required: {destination}")
    with zipfile.ZipFile(collection / SOURCE_ARCHIVE) as archive:
        entries = archive.infolist()
        if len({i.filename for i in entries}) != len(entries):
            raise ValueError("Duplicate archive member")
        for info in entries:
            path = PurePosixPath(info.filename)
            if path.is_absolute() or ".." in path.parts or "\\" in info.filename or ":" in info.filename:
                raise ValueError(f"Unsafe archive path: {info.filename}")
        destination.mkdir(parents=True)
        for info in entries:
            target = destination.joinpath(*PurePosixPath(info.filename).parts)
            target.resolve().relative_to(destination.resolve())
            if info.is_dir():
                target.mkdir(parents=True, exist_ok=True)
            else:
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(archive.read(info))


# This child imports only from a freshly relocated tree.  It uses the original
# mathematical reader rather than turning stored PASS flags into acceptance.
READER_CODE = r'''
import importlib.util, json, pathlib, sys
root = pathlib.Path(sys.argv[1]).resolve()
coverage_path = root / "source/baseline/certificates/work/below50_20260929/local/final_review/check_local47_coverage.py"
spec = importlib.util.spec_from_file_location("relocated_exact_local_coverage", coverage_path)
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)
got = module.run()
want = json.loads(coverage_path.with_name("LOCAL47_COVERAGE.json").read_text())
if got != want:
    raise ValueError("Relocated mathematical cover differs from fixed coverage object")
for name in ("low47_contract", "phase_left_low47_contract", "positive_left_low47_contract",
             "tiny47wide_normalization", "mid47a_normalization", "mid47a_kernel",
             "left_mid47b_kernel", "sperner47_contract", "left_sperner47_contract"):
    pathlib.Path(sys.modules[name].__file__).resolve().relative_to(root)
print(json.dumps(dict(operation="relocated exact mathematical coverage reader",
    probability_panels=got["probability_panels"],
    exact_partition_checks=got["exact_partition_checks"],
    low_box_coverage=got["low_box_coverage"],
    scope="Closed coverage, selected contracts and normalization interfaces reconstructed; expensive arithmetic acceptors not rerun.")))
'''


# This small standalone launcher accompanies the original archive.  The source
# replacements are narrowly specified, reviewed compatibility changes.  They
# affect object-map key spelling only, never a numerical gate or source file.
SCHEDULE_LAUNCHER_SOURCE = r'''#!/usr/bin/env python3
"""2026-10-27: run the real resource schedule reader with POSIX object keys.

Usage: python -B run_schedule_reader_20261027.py PATH/validate_schedule.py
The original 2026-10-25 source is kept unchanged.  In its line 45, key=str(...)
uses a Windows backslash string to query a POSIX-keyed mathematical object map.
Line 91 repeats that problem for an initialization source binding.  Compile a
strict two-expression overlay using .as_posix() for those keys.  No file,
mathematical condition, source binding, numerical input or result is changed.
This launches only the original small structural/mathematical schedule reader;
it does not launch any arithmetic acceptor.
"""
from pathlib import Path
import sys

REPLACEMENTS = (
    ("key=str(p.relative_to(ROOT))", "key=p.relative_to(ROOT).as_posix()"),
    ("manifest[str((OLD/p).relative_to(ROOT))]", "manifest[(OLD/p).relative_to(ROOT).as_posix()]"),
)


def main():
    if len(sys.argv) != 2 or sys.flags.optimize or not __debug__:
        raise ValueError("Use unoptimized Python and exactly one original reader path")
    original = Path(sys.argv[1]).resolve()
    if original.name != "validate_schedule.py":
        raise ValueError("Expected the original validate_schedule.py")
    source = original.read_text(encoding="utf-8-sig")
    lines = source.splitlines()
    for before, after in REPLACEMENTS:
        if source.count(before) != 1:
            raise ValueError("Expected exactly one original path-key expression: " + before)
        source = source.replace(before, after)
    changed = [j for j, (a, b) in enumerate(zip(lines, source.splitlines()), 1) if a != b]
    if changed != [45, 91]:
        raise ValueError("Expected original key expressions on lines 45 and 91: " + repr(changed))
    sys.argv = [str(original)]
    exec(compile(source, str(original), "exec"),
         {"__name__": "__main__", "__file__": str(original)})


if __name__ == "__main__":
    main()
'''


def child(command: list[str], cwd: Path) -> subprocess.CompletedProcess[str]:
    env = os.environ.copy()
    env.pop("PYTHONOPTIMIZE", None)
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    result = subprocess.run(command, cwd=cwd, env=env, text=True, encoding="utf-8",
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    if result.returncode or result.stderr.strip():
        raise RuntimeError(f"Reader failed in {cwd}\n{result.stdout}\n{result.stderr}")
    return result


def reader_check(collection: Path) -> None:
    check_routes(collection)
    with tempfile.TemporaryDirectory(prefix="uniform-tail-reader-") as temporary:
        relocated = Path(temporary) / "relocated"
        unpack(collection, relocated)
        result = child([sys.executable, "-I", "-B", "-c", READER_CODE, str(relocated)], Path(temporary))
        print(result.stdout.strip())
        schedule_dir = relocated / "source/baseline/entry"
        result = child([sys.executable, "-I", "-B", str(collection / SCHEDULE_LAUNCHER),
                        str(schedule_dir / "validate_schedule.py")], schedule_dir)
        schedule = json.loads(result.stdout)
        print(json.dumps(dict(operation="relocated original resource schedule reader",
                              final_central_panels=schedule["final_central_panels"],
                              final_left_panels=schedule["final_left_panels"],
                              scope=schedule["scope"],
                              path_adapter="Only original lines 45 and 91 use .as_posix() for object-map keys",
                              limitation="Structural schedule and numerical inputs read; entry inequalities not replayed.")))


def join_results(collection: Path) -> None:
    result = child([sys.executable, "-I", "-B", str(collection / ORIGINAL_JOIN),
                    "--sources", str(collection / SOURCE_ARCHIVE),
                    "--results", str(collection / RESULT_ARCHIVE)], collection)
    joined = json.loads(result.stdout)
    # The full historical output is available by running ORIGINAL_JOIN directly.
    # Only substantive quantities are displayed here; its status label is not
    # promoted into a new theorem or fresh arithmetic acceptance.
    print(json.dumps(dict(operation="original transcript-to-mathematical-target join",
                          historical_entrypoints=joined["entrypoints"],
                          acquisition_panels=joined["acquisition_panels"],
                          low_closed_boxes=joined["low_closed_boxes"],
                          exact_partition_checks=joined["exact_partition_checks"],
                          scope=joined["scope"])))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--origin", type=Path, default=source_default(),
                        help="Original work/berry-esseen-n49-check-20261025 directory")
    parser.add_argument("--collection", type=Path, default=collection_default())
    parser.add_argument("--prepare", action="store_true", help="Copy original materials; default if no action supplied")
    parser.add_argument("--list", action="store_true", help="Locate the actual mathematical objects inside the archive")
    parser.add_argument("--show-jobs", action="store_true", help="Print original uniform-local cwd/argv; execute none")
    parser.add_argument("--unpack", type=Path, metavar="NEW_DIRECTORY")
    parser.add_argument("--reader-check", action="store_true", help="Rebuild exact local cover after temporary relocation")
    parser.add_argument("--join-results", action="store_true", help="Run original archive transcript/target join")
    args = parser.parse_args()
    collection = args.collection.resolve()
    if args.prepare or not any((args.list, args.show_jobs, args.unpack, args.reader_check, args.join_results)):
        if args.origin is None:
            raise ValueError("Original workspace not present; use --origin, or read the already collected archives")
        prepare(args.origin.resolve(), collection)
    if args.list:
        show_routes(collection)
    if args.show_jobs:
        show_jobs(collection)
    if args.unpack:
        unpack(collection, args.unpack.resolve())
        print(f"Unpacked unchanged source/input files with original relative paths: {args.unpack.resolve()}")
    if args.reader_check:
        reader_check(collection)
    if args.join_results:
        join_results(collection)


if __name__ == "__main__":
    main()
