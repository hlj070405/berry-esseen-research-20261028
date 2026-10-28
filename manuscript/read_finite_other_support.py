"""2026-10-27: portable readers for the other actual26..30 finite components.

Python 3.10+, standard library only; use -B and omit -O. Sources are extracted
to a temporary sibling layout, then removed. Original archives and historical
failed/timeout objects are never changed. No mode runs a frequency mesh or
ordinary count acceptor. Full B0 reading is explicit, and can take minutes.

  python -B read_finite_other_support.py --describe
  python -B read_finite_other_support.py --smoke
  python -B read_finite_other_support.py --check-acquisition
  python -B read_finite_other_support.py --check-ordinary 26
  python -B read_finite_other_support.py --check-n26-p40
  python -B read_finite_other_support.py --check-fourier
  python -B read_finite_other_support.py --check-b0

The original mathematical code and reduction arguments are attributed to
Rodziewicz--Kolodziejek in the frozen source proof texts. Later project
collectors retain their exact source/receipt bindings. These readers compose
conditional pieces; global predecessors and the later analytic remainders
are separate mathematical inputs.
"""
from __future__ import annotations

import argparse
import ast
from contextlib import contextmanager
from fractions import Fraction as F
import importlib.util
import json
from pathlib import Path, PurePosixPath, PureWindowsPath
import shutil
import sys
import tempfile
from types import SimpleNamespace
import zipfile

ROOT = Path(__file__).resolve().parent
if not (ROOT / "work").is_dir():
    ROOT = ROOT / "companions/finite-other-support"
LOW = "berry-esseen-low26-30-20261026"
EXECUTION = "berry-esseen-low26-30-execution-20261026"
FOURIER = "berry-esseen-n26-30-route-20261026"
ORIGIN = ROOT / "work" / LOW / "cloud-results-cnb-fvt-1k5qhmag2/fresh_results_low26_30_joined_20261026.zip"
RESUME = ROOT / "work" / EXECUTION / "cloud-results-cnb-thh-1k5qujut6/fresh_results_low26_30_resume_joined_20261026.zip"
PASS2 = ROOT / "work" / EXECUTION / "continuation-pass2-20261026/cloud-results-cnb-2d7-1k5r2m3ui/fresh_results_low26_30_cont_cd729b81671b_20261026.zip"
HIGH = ROOT / "work" / FOURIER / "cloud-results-cnb-803-1k5qdfgdc/fresh_results_universal26_30_20261026.zip"
sys.dont_write_bytecode = True

DESCRIPTION = """The low input ZIP contains all 345 frozen mathematical inputs, including the
floor25 signed INITIAL/resource histories, actual-n contracts, count kernel,
support kernel, physical acquisition adapter and complete actual-n plan.
The 98 MB original and 159 MB resume archives preserve the full original
floor/support/acquisition ancestry and completed B0 rho=[1,11/10] forests.
partial_b0_join_20261026.json is the existing exact read-only B0 receipt;
--check-b0 repeats its expensive reader, preserving the failed execution.

The 211 MB pass2 archive contains the ordinary accepted outer B1 forests at
P32/P33/P41/P42 for every n=26..30 and both N26 P40 halves. --check-ordinary
requires each requested whole original p panel, all actual-n interfaces,
strict native scores, receipt/forest identity and original count parents.
The original own-n join already has generic mathematical checks; its narrow
adapter only extends the literal index guard from 27..30 to 26..30. Selecting
P40 uses the same original join with its panel list set to (40,).
Other pending native forests remain pending even when a later analytic
profile proves their required remainder by a separate argument.

--check-acquisition repeats the physical implications for all 1000 original
probability panels from the frozen floor histories, checks 455 actual-n
support payload bindings, and validates all 134 complete count interfaces.
The full floor25 signed-block/resource validation remains the separate B0
reader prerequisite; this narrower check does not replace it.

The Fourier input and returned ZIP contain all 85 closed rho/H cells and
425 actual-n rows, together with exact heads, tail and normalization. The
original recovery reader checks the complete body and the one observed
stdlib shutdown trace. Its original wrapper remains timeout with native
returncode -15. The resulting rho>=6/5 inequality uses no predecessor,
support or sample-size monotonicity; the published tail starts at 19/10.

--smoke checks the complete closed Fourier parameter cover, literal imports,
one N26 P40 physical acquisition/interface and one whole accepted P40 half
forest. It neither repeats the full B0 reader nor accepts pending trees.
"""


def load(path: Path, name: str):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise ImportError(path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def extract(source: Path, destination: Path) -> None:
    """Expand one named frozen source archive; refuse noncanonical paths."""
    with zipfile.ZipFile(source) as archive:
        names = archive.namelist()
        assert len(names) == len(set(names))
        for info in archive.infolist():
            pure = PurePosixPath(info.filename)
            assert not pure.is_absolute() and ".." not in pure.parts and "\\" not in info.filename
            assert pure.as_posix() == info.filename and not info.is_dir()
            target = destination.joinpath(*pure.parts)
            if not target.resolve().is_relative_to(destination.resolve()):
                raise ValueError(f"Archive member escapes the temporary source directory: {info.filename}")
            target.parent.mkdir(parents=True, exist_ok=True)
            with archive.open(info) as incoming, target.open("xb") as outgoing:
                shutil.copyfileobj(incoming, outgoing)


@contextmanager
def low_sources():
    with tempfile.TemporaryDirectory(prefix="finite-other-low-") as temporary:
        math = Path(temporary) / "work" / LOW
        packet = ROOT / "work" / LOW / "fresh_inputs_low26_30_20261026.zip"
        extract(packet, math)
        # The original readers also read this ZIP beside the expanded sources.
        shutil.copy2(packet, math / packet.name)
        shutil.copy2(ROOT / "work" / LOW / "collect_low26_30_20261026.py", math / "collect_low26_30_20261026.py")
        execution = ROOT / "work" / EXECUTION
        sys.path[:0] = [str(math), str(execution)]
        r = load(math / "replay_low26_30_20261026.py", "replay_low26_30_20261026")
        collector = load(math / "collect_low26_30_20261026.py", "collect_low26_30_20261026")
        c = load(execution / "continuation_low26_30_metadata_20261026.py", "continuation_low26_30_metadata_20261026")
        partial = load(execution / "collect_low26_30_partial_b0_20261026.py", "collect_low26_30_partial_b0_20261026")
        assert r.source_guard() == c.EPOCH
        calls = partial.install_forbidden_evaluators(r)
        yield math, r, collector, c, partial, calls
        assert not calls, "A proof reader attempted a prohibited evaluator"


def acquisition(r, collector, c, z):
    """Rejoin own-n support/acquisition formulas, without repeating floor gates."""
    plan = r.p.read(r.ROOT / "low26_30_plan_20261026.json")
    floor = c.obj(z.read("current/fresh_floor_parents.json"))
    objects, occurrences = r.inventory()
    assert occurrences == dict(B0=49, B1=41)
    distinct = {r.f.digest(row["request"]): row["request"] for row in objects}
    additional = {row["band"]: row["request"] for row in plan["additional_actual_q0_support_requests"]}
    for request in additional.values():
        distinct[r.f.digest(request)] = request

    def saved(phase, i, packet, parent):
        checkpoint = c.obj(z.read(f"current/checkpoints/{phase}/{i}.json"))
        assert checkpoint["epoch"] == c.EPOCH and checkpoint["parent"] == parent
        assert checkpoint["key"] == r.f.digest(dict(epoch=c.EPOCH, parent=parent, phase=phase, index=i, packet=packet))
        value = checkpoint["result"]
        assert checkpoint["result_digest"] == r.f.digest(value)
        return value

    supports = []
    for i, (n, request) in enumerate((n, distinct[key]) for n in plan["indices"] for key in sorted(distinct)):
        value = saved("ACTUAL_SUPPORT", i, (n, request), floor["parent"])
        assert value["n"] == n and value["request"] == request
        sp = value["support"]
        assert type(sp["n"]) is int and sp["n"] == n and sp["K"] == sp["q_contact"] == "0"
        assert all(sp[k] == request[k] for k in ("radius", "support_sign", "rho_upper", "beta_interval"))
        assert sp["gaussian"]["n"] == n and sp["gaussian"]["mesh"] == request["mesh"]
        assert sp["gaussian"]["radius"] == request["radius"]
        assert [row["sign"] for row in sp["ray_rows"]] == ([-1, 1] if request["support_sign"] == 0 else [request["support_sign"]])
        assert all(F(row[k]) < 0 for row in sp["ray_rows"] for k in
                   ("coefficient_at_R", "contact_derivative_at_R", "contact_derivative_slope_at_R", "contact_upper"))
        supports.append(value)
    assert len(supports) == 455
    lookup = {(row["n"], r.f.digest(row["request"])): row for row in supports}
    parent = r.f.digest(dict(previous=floor["parent"], supports=supports, inventory=objects))
    physical = r.q.module(r.SOURCE / "bridge/lower_actual_acquisition_v1.py", "portable_finite_physical")
    interface = r.q.module(r.SOURCE / "bridge/actual_m_resource_interface_v1.py", "portable_finite_interface")
    acquisitions, count_interfaces = [], 0
    for i, (n, band) in enumerate((n, band) for n in plan["indices"] for band in r.p.EPOCHS):
        bindings = [lookup[n, r.f.digest(row["request"])] for row in objects if row["band"] == band]
        extra = None if band not in additional else lookup[n, r.f.digest(additional[band])]
        value = saved("ACTUAL_ACQUISITION", i, (n, band, bindings, extra), parent)
        e = r.p.EPOCHS[band]
        initial = r.p.read(r.SOURCE / e["initial"] / f"INITIAL25_{band}_PROOF.json")
        resources = r.p.read(r.SOURCE / e["resource"] / f"RESOURCE_{band}_GLOBAL_PROOF.json")
        outcomes = [physical.acquire_panel(initial["export"]["panels"][j], row, F(e["rho"][0]), F(e["rho"][1]), n)
                    for j, row in enumerate(resources["rows"])]
        if band == "B1":
            outcomes = [collector.strengthen(row, F(5, 2)) for row in outcomes]
        assert value["n"] == n and value["band"] == band and value["rho"] == e["rho"] and value["outcomes"] == outcomes
        assert [row["index"] for row in outcomes] == list(range(100)) and value["complete_probability_panels"] == 100
        assert value["support_occurrences"] == occurrences[band] and value["support_binding_digest"] == r.f.digest(bindings)
        assert value["extra_full_support"] == extra and value["conditional_global_predecessor"] == f"C{n-1} <= CE"
        assert value["support_used_before_dependent_radius"] is True
        tasks = [task for task in plan["tasks"] if task["n"] == n and task["band"] == band]
        assert [task["index"] for task in tasks] == [row["index"] for row in outcomes if not row["excluded"]]
        checked = []
        for task in tasks:
            document = r.p.read(r.ROOT / task["contract"])
            joined = interface.validate(outcomes[task["index"]], document["rows"][0])
            assert joined == document["actual_interface"]
            checked.append(dict(id=task["id"], n=n, index=task["index"], interface=joined, contract_sha256=r.p.sha(r.ROOT / task["contract"])))
        assert value["count_interfaces"] == checked
        count_interfaces += len(checked)
        acquisitions.append(value)
    runtime = c.obj(z.read("current/continuation_runtime.json"))
    assert runtime["counts_parent"] == r.f.digest(dict(previous=parent, acquisitions=acquisitions))
    assert count_interfaces == 134
    return dict(status="PASS_ACTUAL26_30_PHYSICAL_ACQUISITION_JOIN", actual_support_payloads=455,
                actual_acquisitions=10, complete_probability_panels=1000, whole_count_interfaces=134,
                floor25_gate_validation="separate retained original B0 reader prerequisite",
                global_predecessors_discharged_here=False, native_execution_still_incomplete=True)


def ordinary(math: Path, n: int, panels=(32, 33, 41, 42)):
    path = ROOT / "work" / EXECUTION / "join_n27_completed_forests_20261027.py"
    tree = ast.parse(path.read_text(encoding="utf-8-sig"), filename=str(path))
    # 2026-10-27 portability/general-index adapter: every original own-n
    # acquisition, partition and strict forest check remains byte-for-AST.
    guards = [node for node in ast.walk(tree) if isinstance(node, ast.Compare)
              and ast.dump(node, include_attributes=False) == ast.dump(ast.parse("27 <= n <= 30", mode="eval").body, include_attributes=False)]
    assert len(guards) == 1
    guards[0].left.value = 26
    namespace = dict(__file__=str(path), __name__="portable_finite_ordinary_join")
    exec(compile(tree, str(path), "exec"), namespace)
    namespace["MATH"] = math
    namespace["PANELS"] = panels
    return namespace["join"](PASS2, n=n)


def smoke(math, r, collector, c, partial):
    plan = r.p.read(r.ROOT / "low26_30_plan_20261026.json")
    task, root = c.task_for(plan, "N26_B1_P40L")
    with zipfile.ZipFile(PASS2) as z:
        names = c.canonical_names(z)
        summary = c.origin_summary(z)
        assert summary["status"] == "timeout" and summary["numeric_components_complete"] is False
        acquired = c.obj(z.read("current/checkpoints/ACTUAL_ACQUISITION/1.json"))["result"]
        e = r.p.EPOCHS["B1"]
        initial = r.p.read(r.SOURCE / e["initial"] / "INITIAL25_B1_PROOF.json")
        resources = r.p.read(r.SOURCE / e["resource"] / "RESOURCE_B1_GLOBAL_PROOF.json")
        physical = r.q.module(r.SOURCE / "bridge/lower_actual_acquisition_v1.py", "portable_smoke_physical")
        outcome = collector.strengthen(physical.acquire_panel(initial["export"]["panels"][40], resources["rows"][40], F(11, 10), F(6, 5), 26), F(5, 2))
        assert outcome == acquired["outcomes"][40]
        _, document = c.derived_document(math, plan, task["id"])
        interface = r.q.module(r.SOURCE / "bridge/actual_m_resource_interface_v1.py", "portable_smoke_interface")
        assert interface.validate(outcome, document["rows"][0]) == document["actual_interface"]
        source = z.read(task["contract"])
        c.representation((json.dumps(document, indent=2) + "\n").encode(), source)
        view = SimpleNamespace(ROOT=c.OverlayRoot(math, z, names, {task["contract"]: source}), SOURCE=r.SOURCE,
                               WORK=c.ArchivePath(z, "current", names), p=r.p, f=r.f)
        folder = "current/native-counts/" + task["id"] + "/"
        receipt = c.obj(z.read(folder + "COUNT40_ACCEPTED.json"))
        c.base.representation = c.representation
        assert c.base.strict_contract_binding(view, task, receipt)
        raw = z.read(folder + "contract.json")
        header = c.base.expected_header(view, task, c.digest(raw))
        assert F(header["target"]) == collector.exact_target()
        stats = collector.inspect_forest(c.obj(z.read(folder + "COUNT40_FOREST.json")), document["rows"][0], header)
        assert stats == receipt["statistics"] and F(stats["maximum_score"]) < F(header["target"])
        assert partial.panel_partition(root, [task]) is False
    return dict(status="PASS_BOUNDED_FINITE_ARCHIVE_BODY_READ", actual_acquisition_panel="N26_B1_P40",
                accepted_half_forest="N26_B1_P40L", actual_roots=27, leaves=stats["leaves"],
                strict_maximum_score=stats["maximum_score"], whole_P40_not_inferred_from_half=True,
                full_B0_reader_run=False, native_acceptors_run=0)


def fourier(check: bool):
    directory = ROOT / "work" / FOURIER
    with tempfile.TemporaryDirectory(prefix="finite-other-fourier-") as temporary:
        staged = Path(temporary)
        packet = directory / "fresh_inputs_universal26_30_20261026.zip"
        extract(packet, staged)
        shutil.copy2(packet, staged / packet.name)
        for name in ("collect_universal26_30_20261026.py", "recover_universal26_30_completed_body_20261026.py"):
            shutil.copy2(directory / name, staged / name)
        sys.path.insert(0, str(staged))
        r = load(staged / "replay_universal26_30_20261026.py", "replay_universal26_30_20261026")
        r.source_guard()
        cells, coverage = r.cover(r.read(r.PLAN))
        assert len(cells) == 85 and coverage["per_n_rows"] == 425 and coverage["common_H_complete"] is True
        if check:
            recovery = load(staged / "recover_universal26_30_completed_body_20261026.py", "portable_finite_fourier_recovery")
            recovery.unchanged_mathematical_body()
            return recovery.collect(HIGH)
        return dict(status="PASS_CLOSED_LITERAL26_30_FOURIER_PARAMETER_COVER", **coverage)


def b0(math, partial):
    execution = ROOT / "work" / EXECUTION
    source = execution / "submission_low26_30_resume_joined_20261026.json"
    original = partial.c.obj(source.read_bytes())
    # Only the historical local pathname is projected into this collection.
    # Preserve and check the original run-directory name and every other field;
    # no mathematical result, process code or historical file is rewritten.
    assert PureWindowsPath(original["result_directory"]).name == RESUME.parent.name
    projected = dict(original, result_directory=str(RESUME.parent.resolve()))
    with tempfile.TemporaryDirectory(prefix="finite-other-path-") as temporary:
        submission = Path(temporary) / source.name
        submission.write_text(json.dumps(projected, indent=2) + "\n", encoding="utf-8")
        return partial.collect(RESUME, math.resolve(), ORIGIN,
                               execution / "cloud_low26_30_resume_joined_20261026.py", submission)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--describe", action="store_true")
    group.add_argument("--smoke", action="store_true")
    group.add_argument("--check-acquisition", action="store_true")
    group.add_argument("--check-ordinary", type=int, choices=range(26, 31), metavar="N")
    group.add_argument("--check-n26-p40", action="store_true")
    group.add_argument("--check-fourier", action="store_true")
    group.add_argument("--check-b0", action="store_true")
    args = parser.parse_args()
    if args.describe:
        print(DESCRIPTION)
        return
    if not __debug__ or sys.flags.optimize:
        raise RuntimeError("Exact readers require Python assertions; omit -O")
    if args.check_fourier:
        result = fourier(True)
    else:
        with low_sources() as (math, r, collector, c, partial, _):
            if args.smoke:
                result = dict(low=smoke(math, r, collector, c, partial), fourier=fourier(False))
            elif args.check_acquisition:
                with zipfile.ZipFile(PASS2) as archive:
                    result = acquisition(r, collector, c, archive)
            elif args.check_ordinary is not None:
                result = ordinary(math, args.check_ordinary)
            elif args.check_n26_p40:
                result = ordinary(math, 26, panels=(40,))
            else:
                result = b0(math, partial)
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
