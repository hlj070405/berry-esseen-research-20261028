"""2026-10-28: compile the editable manuscript to a local review PDF.

Use a pre-existing Tectonic executable, supplied with --engine or found in
the workspace's portable tools directory. TeX support files may be downloaded
by Tectonic; manuscript sources are processed locally. No upload is performed.
Intermediate files and compiler diagnostics stay under tmp/pdfs/.
"""
from __future__ import annotations

import argparse
from pathlib import Path
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent
WORKSPACE = ROOT.parents[2]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--engine", type=Path, default=(
        WORKSPACE / "tmp/typesetting/tectonic-0.17.0/tectonic.exe"))
    args = parser.parse_args()
    engine = args.engine.resolve()
    if not engine.is_file():
        parser.error("Supply an existing Tectonic executable with --engine.")
    build = WORKSPACE / "tmp/pdfs/berry-esseen"
    build.mkdir(parents=True, exist_ok=True)
    process = subprocess.run(
        [str(engine), "--untrusted", "--keep-logs", "--color", "never",
         "--outdir", str(build), str(ROOT / "main.tex")],
        cwd=ROOT, check=False)
    if process.returncode:
        raise SystemExit(process.returncode)
    pdf = build / "main.pdf"
    if not pdf.is_file() or pdf.read_bytes()[:5] != b"%PDF-":
        raise RuntimeError("The compiler did not return a PDF.")
    destination = ROOT / "main.pdf"
    shutil.copyfile(pdf, destination)
    print(f"Prepared local review PDF: {destination}")


if __name__ == "__main__":
    main()
