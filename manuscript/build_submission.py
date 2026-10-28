"""2026-10-27: flatten the editable manuscript for the IMS single-TeX format.

Run with Python 3; only the standard library is used. This prepares a local
source file and does not upload, submit, contact a journal, or alter styles.
"""
from __future__ import annotations

import argparse
from collections import Counter
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parent
INPUT = re.compile(r"^\s*\\input\{([^}]+)\}\s*(?:%.*)?$")


def expand(path: Path, ancestors: tuple[Path, ...] = ()) -> str:
    path = path.resolve()
    if not path.is_relative_to(ROOT):
        raise ValueError(f"Input lies outside the manuscript project: {path}")
    if path in ancestors:
        raise ValueError(f"Cyclic input: {path.name}")
    lines = []
    for line in path.read_text(encoding="utf-8").splitlines():
        match = INPUT.fullmatch(line)
        if match:
            child = ROOT / match.group(1)
            if child.suffix != ".tex":
                child = child.with_suffix(".tex")
            lines.append(expand(child, ancestors + (path,)))
        elif not line.lstrip().startswith("%"):
            lines.append(line)
    return "\n".join(lines) + "\n"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", default="submission.tex")
    args = parser.parse_args()
    output = (ROOT / args.output).resolve()
    if output.parent != ROOT or output.name == "main.tex":
        parser.error("Choose a generated TeX filename in the project directory.")
    text = expand(ROOT / "main.tex")
    if re.search(r"\\(?:input|include)\s*\{", text):
        raise ValueError("An unexpanded TeX input remains.")
    labels = re.findall(r"\\label\s*\{([^{}]+)\}", text)
    duplicates = [label for label, count in Counter(labels).items() if count > 1]
    references = set(re.findall(r"\\(?:eqref|ref|pageref)\s*\{([^{}]+)\}", text))
    missing = references - set(labels)
    bibitems = set(re.findall(r"\\bibitem(?:\[[^\]]*\])?\s*\{([^{}]+)\}", text))
    citations = re.findall(r"\\cite[a-zA-Z]*(?:\[[^\]]*\])*\s*\{([^{}]+)\}", text)
    absent_citations = {key.strip() for group in citations for key in group.split(",")} - bibitems
    if duplicates or missing or absent_citations:
        raise ValueError(f"Unresolved manuscript references: duplicates={duplicates}, "
                         f"missing={sorted(missing)}, citations={sorted(absent_citations)}")
    output.write_text(text, encoding="utf-8", newline="\n")
    print(f"Prepared {output.name}: {len(text.splitlines())} lines; no upload.")


if __name__ == "__main__":
    main()
