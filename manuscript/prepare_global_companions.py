"""2026-10-27: copy the existing mathematical companions for this working draft.

This standard-library script copies proof text, preserving its contents and
attribution. It resolves literal local TeX input/include dependencies, including
the multifile n>=49 proof, without executing TeX or any numerical calculation.
Run from any directory with Python 3.10+; --list identifies the real statements.

The output is a readable proof-source collection, NOT a portable executable
computer-assisted proof. Frozen code, coefficient tables, forests, exact runtime
dependencies, fresh output archives and their mathematical joins remain separate.
Existing companions/profile-parameters.json and all unlisted files are untouched.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
from pathlib import Path
import re
import shutil

PROJECT = Path(__file__).resolve().parent
DEFAULT_WORKSPACE = PROJECT.parents[2]


@dataclass(frozen=True)
class Source:
    source: str
    destination: str
    reference: str
    anchor: str = ""
    required: tuple[str, ...] = ()


# Paths are relative to the original workspace. The destination is a directory;
# source filenames and the relative structure below a declared anchor survive.
# References describe actual labels/captions, including explicitly unlabelled
# statements. No new theorem label or archival identity is invented here.
SOURCES = [
    Source("work/berry-esseen-n1-base-20261024/n1_base.tex", "low-index/n1",
           "Theorem 1, label thm:base: C1<=2/5", required=(r"\label{thm:base}",)),
    Source("work/berry-esseen-n20-complete-20261025/source/work/cutoff20_20261016/"
           "01_consolidated/BE_Manuscript/manuscript.tex", "low-index/n2-n3",
           "labels n2:thm:main and n3:thm:main; their support and tensor proofs",
           required=(r"\label{n2:thm:main}", r"\label{n3:thm:main}")),
    Source("work/berry-esseen-sources-20261024/moment-defects-v3.pdf",
           "references/rk-v3",
           "Existing public v3 PDF, Section 26, Theorem 26.1 and its proof: C4<=.4097; "
           "no local TeX for this complete fourth-index proof was found"),
    Source("work/berry-esseen-c5-complete-20261025/five_sum_completion_20261025.tex",
           "low-index/n5", "Theorem 1, label composition: C5<=CE",
           required=(r"\label{composition}",)),
    Source("work/berry-esseen-c5-complete-20261025/high_moment_complement_20261025.tex",
           "low-index/n5-high-moment", "Fifth-index supported Fourier complement"),
    Source("work/berry-esseen-n6-complete-20261025/six_sum_interface_20261025.tex",
           "low-index/n6", "Proposition 1 and completed composition: C6<=CE"),
    Source("work/berry-esseen-n7-complete-20261025/seven_sum_interface_20261025.tex",
           "low-index/n7", "Proposition 1 and completed composition: C7<=CE"),
    Source("work/berry-esseen-n8-complete-20261025/eight_sum_interface_20261025.tex",
           "low-index/n8", "Proposition 1 and completed composition: C8<=CE"),
    Source("work/berry-esseen-n9-complete-20261025/nine_sum_interface_20261025.tex",
           "low-index/n9", "Proposition 1 and completed composition: C9<=CE"),
    Source("work/berry-esseen-n10-complete-20261025/n10-interface/main.tex",
           "low-index/n10", "Theorem 2, Unrestricted tenth-index conclusion"),
    Source("work/berry-esseen-n11-14-complete-20261026/conditional_11_14_interface_20261026.tex",
           "low-index/n11-14",
           "Unnumbered actual-index implication and final ordered C10->...->C14 display"),
    Source("work/berry-esseen-n15-19-complete-20261026/n15-19-interface/main.tex",
           "low-index/n15-19", "Theorem 1: C15,...,C19<=CE, from global C14<=CE"),
    Source("work/berry-esseen-n20-complete-20261025/twenty_sum_interface_20261025.tex",
           "low-index/n20", "Proposition 1 and completed global C20 composition"),
    Source("work/berry-esseen-n20-singlebatch-20261026/actual20_singlebatch_interface_20261026.tex",
           "low-index/n20-current-execution",
           "Unnumbered actual20 domain and one-batch execution interface; not a new theorem"),
    Source("work/berry-esseen-n21-24-complete-20261026/n21-24-interface/main.tex",
           "low-index/n21-24", "Theorem 1: C21,...,C24<=CE and auxiliary C24<.419"),
    Source("work/berry-esseen-n25-full-parent-20261026/n25-interface/main.tex",
           "low-index/n25", "Theorem 1: unrestricted C25<=CE"),
    Source("work/berry-esseen-n25-full-parent-20261026/literal25-fourier-proof/main.tex",
           "low-index/n25-fourier",
           "Displayed universal rho>=6/5 implication, at actual indices 25,...,30"),
    Source("work/berry-esseen-c5-complete-20261025/fresh-low-work-20261025/source/work/"
           "short35_20261007/root/BE_cutoff35_streamlined.tex", "common/finite-analytic",
           "Continuous derivations: global:attainment, global:contact, "
           "complete44ent:smooth-fourier, complete44ent:fourier-early-low, "
           "complete44ent:re-enclosure, res:contract, complete44loc:theorem; "
           "also the section One finite-count comparison for all the new indices",
           required=(r"\label{global:contact}", r"\label{res:contract}",
                     r"\label{complete44loc:theorem}")),
    Source("work/berry-esseen-n31-primary-check-20261025/"
           "sharp31_bridge_composition_20261025/main.tex", "actual-index/n31-34",
           "Propositions prop:31 and prop:bridges; coarse a30<1/100 entry and "
           "weighted actual-index bridges", required=(r"\label{prop:31}",
                                                     r"\label{prop:bridges}")),
    Source("work/berry-esseen-n31-primary-check-20261025/sharp31_B7_D_domain_20261025.tex",
           "actual-index/n31-domain", "Gaussian-weight and band-7 defect-domain extension"),
    Source("work/berry-esseen-n31-primary-check-20261025/source/threshold31_20261008/"
           "audit/paired_general31/general_paired_extension.tex", "actual-index/n31-paired",
           "Continuous general paired Fourier extension used by actual31"),
    Source("work/berry-esseen-n35-complete-20261025/actual35_conditional_composition_20261025.tex",
           "actual-index/n35", "Theorem 3, Unrestricted index--35 conclusion; "
           "preceding exceptional-D continuous derivation"),
    Source("work/berry-esseen-n36-38-complete-20261026/"
           "actual36_38_conditional_composition_20261026.tex", "actual-index/n36-38",
           "Proposition 3, Unrestricted conclusions at 36, 37 and 38"),
    Source("work/berry-esseen-n39-complete-20261026/actual39_two_step_composition_20261026/main.tex",
           "actual-index/n39", "Propositions 1 and 2: positive and sharp budgets at index 39"),
    Source("work/berry-esseen-n39-complete-20261026/actual39_continuous_lemmas_20261026.tex",
           "actual-index/n39-continuous",
           "Actual39 antichain, deleted-error, confinement and normalization derivations"),
    Source("work/berry-esseen-n40-route-20261026/n40-48-interface/main.tex",
           "actual-index/n40-48", "Theorem thm:main; Propositions prop:forty and prop:two",
           required=(r"\label{thm:main}", r"\label{prop:forty}", r"\label{prop:two}")),
    Source("work/berry-esseen-n40-route-20261026/actual40_continuous_lemmas_20261026.tex",
           "actual-index/n40-continuous", "Actual40 finite-domain analytic justification"),
    Source("work/berry-esseen-n40-route-20261026/source/BE_cutoff35_release_20261007/"
           "work/cutoff40_release_20261007/documents/BE_cutoff40_20261007.tex",
           "actual-index/n40-original",
           "Original floor-40 analytic compilation, including thm:bin and idx40:scope"),
    Source("work/berry-esseen-n41-48-route-20261026/uniform42_continuous_interface_20261026.tex",
           "actual-index/n42-continuous", "Finite-band 42--48 weighted local interpretation"),
    Source("work/berry-esseen-n49-check-20261025/n49_completion_20261025.tex",
           "large-index/completion",
           "Proposition 1, Scalar completion; Theorem 1, The reconstructed public tail bound"),
    Source("work/berry-esseen-n49-check-20261025/legacy49/paper/main.tex",
           "large-index/analytic-route", "global:main; global:local; global:smoothing; "
           "re:enclosure; shortloc:theorem and their continuous proofs",
           anchor="work/berry-esseen-n49-check-20261025/legacy49"),
]

N42 = "work/berry-esseen-n41-48-route-20261026/source/local42"
for path in ("joint_resource.tex", "signed_cubic_repair.tex",
             "local/local42_signed_gaussian_v2.tex",
             "local/paired_extension/paired_extension_with_signed_k.tex"):
    SOURCES.append(Source(f"{N42}/{path}", "actual-index/n42-local",
                          "Original finite-band joint-resource and signed local-comparison proof",
                          anchor=N42))

C5 = ("work/berry-esseen-c5-complete-20261025/fresh-low-work-20261025/source")

# These are original mathematical proof texts, not new reports or receipts.
# Preserve the original work/... structure so references in the proof map remain
# intelligible; numerical CHECKED.json/status files are deliberately not copied.
C5_PROOFS = (
    "work/cutoff10_20261018/analytic/fixed_n_attainment_review_v1/PROOF.txt",
    "work/cutoff10_20261018/analytic/fixed_n_contact_review_v1/PROOF.txt",
    "work/cutoff10_20261018/analytic/direct_support_from_contact_v1/PROOF.txt",
    "work/cutoff10_20261018/audit/signed_low_review_v1/REVIEW.txt",
    "work/cutoff10_20261018/root/high10_centered_v1/PROOF.txt",
    "work/cutoff10_20261018/root/high10_moment_v1/PROOF.txt",
    "work/cutoff10_20261018/fourier/corner10_14_v3/PROOF.txt",
    "work/cutoff6_20261018/audit/finite_window_low_v1/PROOF.txt",
    "work/cutoff15_20261017/root/cancellation_high_v1/PROOF.txt",
    "work/cutoff25_rethink_20261015/root/FOURIER_REDUCTION_V2.txt",
    "work/cutoff25_rethink_20261015/scale_analytic/kappa_62_625_v1/PROOF.txt",
    "work/cutoff20_20261016/fourier/PROOF.txt",
    "work/cutoff25_continue_20261015/phase_rectangle_v1/PROOF.txt",
    "work/cutoff5_20261020/audit/ANALYTIC_DEPENDENCIES_V2.txt",
    "work/cutoff5_20261020/audit/conserved_identity_review_v1/PROOF.txt",
    "work/cutoff5_20261020/audit/low_phase_port_review_v1/REVIEW.txt",
    "work/cutoff5_20261020/audit/resource_semantics_review_v1/PROOF.txt",
    "work/cutoff5_20261020/audit/count_kernel_analytic_review_v1/PROOF.txt",
    "work/cutoff5_20261020/root/COUNT_ANALYTIC_REDERIVATION.txt",
    "work/cutoff5_20261020/root/fourier_scalar_review_v1/REVIEW.txt",
    "work/cutoff5_20261020/high/CONTINUOUS_DEPENDENCIES.txt",
    "work/cutoff5_20261020/high/extended_kernel_v1/PROOF.txt",
    "work/cutoff5_20261020/audit/resource_ports_review_v1/REVIEW.txt",
    "work/cutoff5_20261020/audit/extensions_review_v2/REVIEW.txt",
)
for path in C5_PROOFS:
    SOURCES.append(Source(f"{C5}/{path}", "low-index/continuous-sources",
                          "Original fixed-index continuous derivation or its source map",
                          anchor=C5))

N25_FOURIER = "work/berry-esseen-n25-full-parent-20261026/fourier_source"
for path in (
    "work/cutoff20_20261016/fourier/PROOF.txt",
    "work/cutoff20_20261016/fourier/coupled_v1/PROOF.txt",
    "work/cutoff25_rethink_20261015/scale_analytic/fourier_absmean_v1/PROOF.txt",
    "work/cutoff25_rethink_20261015/scale_analytic/fourier_interval/PROOF.txt",
):
    SOURCES.append(Source(f"{N25_FOURIER}/{path}", "low-index/n25-fourier-sources",
                          "Actual25 universal Fourier moment reduction and integral enclosures",
                          anchor=N25_FOURIER))

FINITE = "work/berry-esseen-low26-30-20261026/source"
for path in (
    "analytic/UNIFORM25_CANTELLI_PRODUCTGAP_REVIEW.txt",
    "analytic/UNIFORM25_BETA0_SOURCE_AND_COMPOSITION_REVIEW.txt",
    "original/new_audit/SCALED_INWARD_PHYSICAL_DERIVATION_V1.txt",
):
    SOURCES.append(Source(f"{FINITE}/{path}", "localization",
                          "Fixed-floor weighted transfer and actual-index inward-plane derivation",
                          anchor=FINITE))

INPUT = re.compile(r"\\(?:input|include)\b\s*(?:\{([^{}]+)\}|([^\s{}%]+))")


def without_comments(text: str) -> str:
    result = []
    for line in text.splitlines():
        end = len(line)
        for i, char in enumerate(line):
            if char != "%":
                continue
            j = i - 1
            while j >= 0 and line[j] == "\\":
                j -= 1
            if (i - 1 - j) % 2 == 0:
                end = i
                break
        result.append(line[:end])
    return "\n".join(result)


def literal_inputs(path: Path) -> list[str]:
    if path.suffix.lower() != ".tex":
        return []
    text = without_comments(path.read_text(encoding="utf-8-sig"))
    names = [a or b for a, b in INPUT.findall(text)]
    if any(any(char in name for char in "\\#$") for name in names):
        raise ValueError(f"Nonliteral TeX input requires a source-specific resolution: {path}")
    return names


def plan(workspace: Path) -> tuple[dict[Path, Path], list[tuple[Source, Path]]]:
    """Resolve the selected source trees before creating or overwriting a file."""
    output = (PROJECT / "companions").resolve()
    files: dict[Path, Path] = {}
    roots = []

    for item in SOURCES:
        source = (workspace / item.source).resolve()
        anchor = (workspace / item.anchor).resolve() if item.anchor else source.parent
        if not source.is_file() or not source.is_relative_to(workspace):
            raise FileNotFoundError(f"Required existing proof source is unavailable: {source}")
        if not source.is_relative_to(anchor) or not anchor.is_relative_to(workspace):
            raise ValueError(f"Invalid source anchor: {source}")
        if item.required:
            text = source.read_text(encoding="utf-8-sig")
            for token in item.required:
                if token not in text:
                    raise ValueError(f"Expected actual theorem anchor {token!r} absent in {source}")
        prefix = (output / item.destination).resolve()
        compile_dir = source.parent
        visited: set[Path] = set()
        active: set[Path] = set()

        def visit(path: Path) -> None:
            if path in active:
                raise ValueError(f"Cyclic TeX input in {source}: {path}")
            if path in visited:
                return
            if not path.is_relative_to(anchor):
                raise ValueError(f"TeX input escapes its retained tree: {path}")
            destination = (prefix / path.relative_to(anchor)).resolve()
            if not destination.is_relative_to(output):
                raise ValueError(f"Copy would escape companions: {destination}")
            previous = files.get(destination)
            if previous is not None and previous != path:
                raise ValueError(f"Two different sources target {destination}")
            files[destination] = path
            active.add(path)
            for name in literal_inputs(path):
                relative = Path(name)
                if not relative.suffix:
                    relative = relative.with_suffix(".tex")
                # Ordinary TeX resolves these historical trees from the main
                # document's working directory. Current-file-relative lookup is
                # a fallback only for separately reusable proof fragments.
                candidates = [(compile_dir / relative).resolve(),
                              (path.parent / relative).resolve()]
                child = next((p for p in candidates if p.is_file()), None)
                if child is None:
                    raise FileNotFoundError(f"Unresolved TeX input {name!r} from {path}")
                visit(child)
            active.remove(path)
            visited.add(path)

        visit(source)
        roots.append((item, prefix / source.relative_to(anchor)))
    return files, roots


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--workspace", type=Path, default=DEFAULT_WORKSPACE)
    parser.add_argument("--list", action="store_true",
                        help="Print source/statement locations without copying.")
    parser.add_argument("--check-only", action="store_true",
                        help="Resolve all sources and TeX dependencies without copying.")
    parser.add_argument("--replace", action="store_true",
                        help="Replace an existing listed copy whose contents were edited.")
    args = parser.parse_args()
    files, roots = plan(args.workspace.resolve())
    if args.list:
        for item, destination in roots:
            if destination.suffix.lower() in {".tex", ".pdf"}:
                print(f"{destination.relative_to(PROJECT).as_posix()}: {item.reference}")
        return
    if args.check_only:
        print(f"Resolved {len(files)} existing proof files, including every local TeX input/include.")
        return
    changed = 0
    # Preserve edited copies unless an explicit replacement was requested.
    for destination, source in files.items():
        if destination.exists() and destination.read_bytes() != source.read_bytes() and not args.replace:
            raise FileExistsError(f"Edited companion is preserved; use --replace deliberately: {destination}")
    for destination, source in files.items():
        if destination.exists() and destination.read_bytes() == source.read_bytes():
            continue
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, destination)
        changed += 1
    print(f"Prepared {len(files)} existing proof files; copied {changed}; all TeX inputs resolved.")
    print("Contents and original attribution are unchanged. Unlisted companion files are untouched.")
    print("Readable proof sources only: frozen code, tables/forests, exact runtime and fresh "
          "output archives with their joins must still be supplied as executable support.")
    print("Use --list for actual theorem labels/captions and --check-only for a read-only closure check.")


if __name__ == "__main__":
    main()
