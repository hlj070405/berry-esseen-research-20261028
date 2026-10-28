"""2026-10-27: read the relocated low-index arithmetic without a long replay.

This reader uses only the Python standard library. The retained original
join/producer programs may need python-flint (import name flint), sympy, or
C++17/Boost, as described by --describe. Never run Python with -O for the
original mathematical readers, which use assertions for exact comparisons.

Examples, from this collection directory:
  python -B read_low_index_support.py --describe
  python -B read_low_index_support.py --smoke
  python -B read_low_index_support.py --check-n4
  python -B read_low_index_support.py --check-n25-high
  python -B read_low_index_support.py --members n25-high
  python -B read_low_index_support.py --read n25-high universal25_plan_20261026.json
  python -B read_low_index_support.py --extract-input n25-high --into C:/scratch/n25

Extraction is explicit and preserves every member byte and relative path.
No old result/status is promoted to an inequality. --smoke performs the n1
all-real rational certificate check, reads the complete n2/n3 shard covers,
parses all n2/n3 coefficient objects and n3 analytic constants, and checks the entire n25-high closed
parameter cover and its actual rational infinite-tail inequality. It does
not repeat n2/n3 positivity subdivision, frequency meshes, resources or counts.
--check-n4 calls the retained original exact scalar reader on all 260 root
domains. That reader does not recompute HIGH Fourier tables; its scope is
printed by the original code. Neither command is an all-index proof replay.
--check-n25-high needs python-flint and reads all 85 actual returned Fourier
cell bounds with the original collector; no frequency mesh is rerun.

Public mathematical source attribution: Rodziewicz--Kolodziejek; the n2/n3
source commit is 044e93ec97f377752924fe32bd08e0bc6f4334b1. Existing producer,
collector, coefficient and archive contents have not been rewritten.
"""
from __future__ import annotations

import argparse
import importlib.util
import json
from pathlib import Path, PurePosixPath
import shutil
import sys
import tempfile
import zipfile

ROOT = Path(__file__).resolve().parent
if not (ROOT / "work").is_dir():
    ROOT = ROOT / "companions/low-index-support"
sys.dont_write_bytecode = True


def work(directory: str) -> Path:
    return ROOT / "work" / ("berry-esseen-" + directory)


# Role names deliberately distinguish the fifth-index original source graph,
# the sixth-index overlay/prefix, and the two separate actual25 moment domains.
INPUTS = {
    "n2": ("n2-public-check-20261024", "berry_n2_public_sources_20261024.zip"),
    "n3": ("n3-public-check-20261024", "berry_n3_public_sources_20261024.zip"),
    "n4": ("n4-public-check-20261024", "n4_full206_inputs_20261025.zip"),
    "n5-original": ("c5-complete-20261025", "cutoff5_20261020.zip"),
    "n5-low": ("c5-complete-20261025", "c5_low_inputs_20261025.zip"),
    "n5-high": ("c5-complete-20261025", "c5_complement_inputs_20261025.zip"),
    "n6": ("n6-complete-20261025", "n6_fresh_inputs_20261025.zip"),
    "n6-overlay": ("n6-complete-20261025", "n6_resume_inputs_20261025.zip"),
    "n7": ("n7-complete-20261025", "n7_fresh_inputs_20261025.zip"),
    "n8": ("n8-complete-20261025", "n8_fresh_inputs_20261025.zip"),
    "n9": ("n9-complete-20261025", "n9_fresh_inputs_20261025.zip"),
    "n10": ("n10-complete-20261025", "n10_fresh_inputs_20261025.zip"),
    "n11-14": ("n11-14-complete-20261026", "fresh_inputs_11_14_20261026.zip"),
    "n15-19": ("n15-19-complete-20261026", "fresh_inputs_15_19_20261026.zip"),
    "n20": ("n20-singlebatch-20261026", "fresh_inputs_n20_20261026.zip"),
    "n21-24": ("n21-24-complete-20261026", "fresh_inputs_21_24_20261026.zip"),
    "n25-low": ("n25-full-parent-20261026", "fresh_inputs_low25_20261026.zip"),
    "n25-high": ("n25-full-parent-20261026", "fresh_inputs_universal25_20261026.zip"),
}

DESCRIPTIONS = """Actual arithmetic joins and prerequisites

n1: work/berry-esseen-n1-base-20261024/verify_certificate_20261024.py
    reads rational-certificate.json beside it; standard library only.
n2,n3: the two public-check collect_replay_20261024.py readers take their
    respective retained four-shard result directory under
    work/berry-esseen-block-square-20261024/cloud/. The source ZIPs contain
    all 70/111 original coefficient cells and exact replay kernels. n2 replay
    uses the standard library; n3 replay compiles C++17 with Boost headers.
n4: public-check/check_full_closure_exact_20261025.py reads the retained
    full206-batch-20261025 directory. All 206 numeric root results, original
    terminal objects and the exact schedule config are present. No controller
    logs are needed. Its HIGH, LOW and analytic independent interface readers
    are retained in their original sibling directories; HIGH/LOW need sympy.
n5: c5-complete/check_final_semantic_joins_20261025.py needs python-flint.
    Its original source graph is compressed in cutoff5_20261020.zip; use the
    retained c5_low_fresh_20261025.extract(archive, source_directory) only for
    source materialization (not main(), which computes). The exact expected
    directory is fresh-low-work-20261025/source. The corner forest additionally
    belongs at original/work/cutoff5_20261020/root/gapfree5_exact_v1/FOREST.json.
    The low result JSON is inside c5_low_results_20261025.zip and must be read
    beside that ZIP; the two high JSONs are inside c5_complement_results_20261025.zip
    and must be read beside that ZIP. The separate actual corner result JSON
    and its unchanged corner arithmetic code are retained.
n6: n6-complete/check_n6_final_join_20261025.py takes --results <resume ZIP>,
    --original <fresh input ZIP>, --overlay <resume input ZIP>. Extract the
    two input ZIPs together beside this reader first. The overlay embeds the
    actual earlier returned prefix; a second standalone copy is unnecessary.
    Needs python-flint.
n7,n8,n9: the corresponding check_nN_final_join_20261025.py takes --original
    <input ZIP> and --results <fresh returned ZIP>. Extract that frozen input
    beside its reader first; its exact mathematical source reads are unchanged.
    Needs python-flint.
n10: n10-complete/check_n10_final_join_20261026.py reads --original <input ZIP>
    directly, --results <returned ZIP>, and --c9-proof <retained n9 TeX>.
    Its two original outer-process JSONs are beside the result ZIP. Needs
    python-flint; its numerical reader imports selected modules from the ZIP.
n11-14: check_final_join_11_14_20261026.py needs --input <input ZIP>,
    --frozen-root <extracted input directory>, --results <returned ZIP>.
    The original single-assert execution adapter is retained beside the reader.
    Needs python-flint.
n15-19: check_final_join_15_19_20261026.py needs --input <input ZIP>,
    --frozen-root <extracted input directory>, --results <returned ZIP>.
n20: singlebatch/check_final_join_n20_20261026.py needs --input <input ZIP>,
    --frozen-root <extracted input directory>, --results <resource-resume ZIP>,
    --resume-state <resource-resume/n20_completed_state_20261026.zip>,
    --prior-results <singlebatch first returned ZIP>, and --execution-adapter
    <resource-resume/execution_adapter_n20_resource_20261026.py>. All are
    retained. Do not substitute the incomplete first returned ZIP for the
    final resource-resume ZIP. The reader imports the original scalar kernels.
n21-24: check_final_join_21_24_20261026.py needs --input <input ZIP>,
    --frozen-root <extracted input directory>, --results <returned ZIP>.
n25-low: collect_low25_20261026.py needs --input <low input ZIP>,
    --frozen-root <extracted input directory>, --results <low returned ZIP>.
    The distinct --selftest checks source/predecessor interfaces only.
n25-high: collect_universal25_20261026.py needs --result-zip <high returned ZIP>;
    first extract the high input beside that reader. Its native interval
    implementation, scalar kappa calculation and full 85-cell schedule are
    already inside that small input ZIP.

The continuous attainment/contact/comparison theorems and external predecessor
bounds are mathematical premises in the separate companions/low-index and
companions/common/finite-analytic proof texts. The archive readers do not
replace those arguments. No all-index numerical replay is asserted here.
"""


def load(path: Path, name: str):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise ImportError(path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def packet(key: str) -> Path:
    directory, name = INPUTS[key]
    return work(directory) / name


def safe_member(name: str) -> PurePosixPath:
    pure = PurePosixPath(name)
    if pure.is_absolute() or ".." in pure.parts or "\\" in name or pure.as_posix() != name.rstrip("/"):
        raise ValueError(f"Unsafe archive member: {name}")
    return pure


def extract(source: Path, destination: Path) -> None:
    """Explicit source expansion; never overwrite a different existing file."""
    destination = destination.resolve()
    with zipfile.ZipFile(source) as archive:
        for info in archive.infolist():
            pure = safe_member(info.filename)
            target = destination.joinpath(*pure.parts)
            if not target.resolve().is_relative_to(destination):
                raise ValueError(target)
            if info.is_dir():
                continue
            if target.exists():
                with archive.open(info) as a, target.open("rb") as b:
                    while True:
                        x, y = a.read(1024 * 1024), b.read(1024 * 1024)
                        if x != y:
                            raise FileExistsError(f"Refusing to overwrite differing file: {target}")
                        if not x:
                            break
                continue
            target.parent.mkdir(parents=True, exist_ok=True)
            with archive.open(info) as incoming, target.open("xb") as outgoing:
                shutil.copyfileobj(incoming, outgoing)


def smoke() -> None:
    if not __debug__:
        raise ValueError("Mathematical readers require Python assertions; omit -O")
    n1 = work("n1-base-20261024")
    verifier = load(n1 / "verify_certificate_20261024.py", "relocated_n1_exact_reader")
    result = verifier.verify(n1 / "rational-certificate.json", 100, False)
    if result["status"] != "ALL_REAL_CERTIFICATE_VERIFIED":
        raise ValueError("Incomplete first-index rational certificate")
    print(f"n1: all-real rational certificate, {result['cells']} cells; margin > 1/50")

    cloud = work("block-square-20261024") / "cloud"
    for n, run, total in ((2, "results-cnb-8hc-1k5muheu4", 70),
                          (3, "results-cnb-cv2-1k5n1cl77", 111)):
        collector = load(work(f"n{n}-public-check-20261024") / "collect_replay_20261024.py",
                         f"relocated_n{n}_whole_cover_reader")
        result = collector.collect(cloud / run)
        if result["cells"] != total:
            raise ValueError(f"Incomplete n{n} shard cover")
        print(f"n{n}: exact four-shard returned cover, {total} closed threshold cells")

    # Read every actual n2 coefficient cell and its exact expected interval.
    with tempfile.TemporaryDirectory(prefix="be-low-reader-") as temporary:
        temporary = Path(temporary)
        with zipfile.ZipFile(packet("n2")) as archive:
            prefix = "berry-esseen-n2-public-check-20261024/public-n2/"
            names = [prefix + "independent_integer_check.py"]
            names += [prefix + f"certificate/{i:03d}.json" for i in range(70)]
            for name in names:
                target = temporary / safe_member(name)
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(archive.read(name))
        source = temporary / prefix
        checker = load(source / "independent_integer_check.py", "relocated_n2_coefficient_reader")
        for i in range(70):
            checker.parse(source / f"certificate/{i:03d}.json", i)
        print("n2: all 70 original rational coefficient objects parsed with exact schema/endpoints")

        with zipfile.ZipFile(packet("n3")) as archive:
            prefix = "berry-esseen-n3-public-check-20261024/public-n3/"
            names = [prefix + "verify.py"]
            names += [name for name in archive.namelist()
                      if name.startswith(prefix + "certificate/") and name.endswith(".json")]
            if len(names) != 112:
                raise ValueError("The original n3 source must have exactly 111 coefficient cells")
            for name in names:
                target = temporary / safe_member(name)
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(archive.read(name))
        source = temporary / prefix
        checker = load(source / "verify.py", "relocated_n3_coefficient_reader")
        checker.analytic_constants()
        if len(checker.load_records(source / "certificate")) != 111:
            raise ValueError("Incomplete n3 rational coefficient cover")
        print("n3: all 111 original 59-coefficient objects and exact analytic/tail constants checked")

        # This import/closed-cover test uses no flint and performs no integration.
        with zipfile.ZipFile(packet("n25-high")) as archive:
            name = "replay_universal25_20261026.py"
            path = temporary / name
            path.write_bytes(archive.read(name))
            plan = json.loads(archive.read("universal25_plan_20261026.json"))
        reader = load(path, "relocated_actual25_cover_reader")
        cells, coverage = reader.cover(plan)
        if len(cells) != 85 or coverage["strips"] != 43:
            raise ValueError("Incomplete actual25 closed rho/H cover")
        print("n25 high: 43 complete closed rho strips, 85 common-H cells; rational infinite-tail inequality")
    print("Smoke scope: exact small readers/imports only; no frequency/resource/count replay.")


def check_n25_high() -> None:
    """Temporary 83-file native-reader closure, not a mesh computation."""
    if not __debug__:
        raise ValueError("Original mathematical readers require assertions; omit -O")
    base = work("n25-full-parent-20261026")
    with tempfile.TemporaryDirectory(prefix="be-n25-high-reader-") as directory:
        directory = Path(directory)
        source = packet("n25-high")
        extract(source, directory)
        shutil.copy2(source, directory / source.name)
        name = "collect_universal25_20261026.py"
        shutil.copy2(base / name, directory / name)
        load(directory / "replay_universal25_20261026.py", "replay_universal25_20261026")
        collector = load(directory / name, "relocated_n25_high_full_collector")
        result = collector.collect(base / "cloud-results-cnb-80t-1k5q8k45j/fresh_results_universal25_20261026.zip")
        print(json.dumps({key: result[key] for key in (
            "n", "rho_interval", "fresh_complete_cells", "four_terms_checked",
            "maximum_exact_upper", "maximum_upper_float", "published_tail_upper",
            "mesh_reruns", "predecessor_used", "support_used", "sufficient_complement_statement",
        )}, indent=2))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--describe", action="store_true")
    group.add_argument("--smoke", action="store_true")
    group.add_argument("--check-n4", action="store_true")
    group.add_argument("--check-n25-high", action="store_true")
    group.add_argument("--members", choices=INPUTS)
    group.add_argument("--read", nargs=2, metavar=("INPUT", "MEMBER"))
    group.add_argument("--extract-input", choices=INPUTS)
    parser.add_argument("--into", type=Path, help="explicit extraction directory; only with --extract-input")
    args = parser.parse_args()
    if args.into is not None and not args.extract_input:
        parser.error("--into is only valid with --extract-input")
    if args.describe:
        print(DESCRIPTIONS)
    elif args.smoke:
        smoke()
    elif args.check_n4:
        if not __debug__:
            raise ValueError("Original mathematical readers require assertions; omit -O")
        base = work("n4-public-check-20261024")
        reader = load(base / "check_full_closure_exact_20261025.py", "relocated_n4_scalar_reader")
        reader.check(base / "cloud-results-cnb-ac7-1k5neea2u/full206-batch-20261025")
    elif args.check_n25_high:
        check_n25_high()
    elif args.members:
        with zipfile.ZipFile(packet(args.members)) as archive:
            print("\n".join(archive.namelist()))
    elif args.read:
        key, member = args.read
        if key not in INPUTS:
            parser.error(f"Unknown input role: {key}")
        safe_member(member)
        with zipfile.ZipFile(packet(key)) as archive:
            sys.stdout.write(archive.read(member).decode("utf-8-sig"))
    elif args.extract_input:
        if args.into is None:
            parser.error("Explicit --into is required; large source trees are never expanded by default")
        extract(packet(args.extract_input), args.into)
        print(f"Extracted existing source bytes into {args.into.resolve()}")


if __name__ == "__main__":
    main()
