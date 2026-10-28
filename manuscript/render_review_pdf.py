"""2026-10-28: render the local review PDF and make temporary page sheets.

Run with the bundled document Python (Pillow and pypdf) and Poppler. Images
stay under tmp/pdfs/berry-esseen/review; no report or external job is created.
The sheets help inspect every page; individual PNGs retain readable detail.
"""
from __future__ import annotations

import argparse
from pathlib import Path
import subprocess

from PIL import Image, ImageDraw
from pypdf import PdfReader

ROOT = Path(__file__).resolve().parent
WORKSPACE = ROOT.parents[2]
RUNTIME = Path.home() / ".cache/codex-runtimes/codex-primary-runtime/dependencies"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--poppler", type=Path, default=(
        RUNTIME / "native/poppler/Library/bin/pdftoppm.exe"))
    args = parser.parse_args()
    pdf = ROOT / "main.pdf"
    output = WORKSPACE / "tmp/pdfs/berry-esseen/review"
    output.mkdir(parents=True, exist_ok=True)
    if not output.resolve().is_relative_to((WORKSPACE / "tmp/pdfs").resolve()):
        raise RuntimeError("Review images must stay in the temporary PDF directory.")
    for pattern in ("page-*.png", "sheet-*.png"):
        for previous in output.glob(pattern):
            previous.unlink()
    subprocess.run([str(args.poppler), "-png", "-scale-to", "1500",
                    str(pdf), str(output / "page")], check=True)
    reader = PdfReader(pdf)
    pages = sorted(output.glob("page-*.png"))
    if len(pages) != len(reader.pages):
        raise RuntimeError("Rendered pages do not match this PDF; use a fresh review directory.")
    for start in range(0, len(pages), 6):
        sheet = Image.new("RGB", (1230, 1100), "#dedede")
        draw = ImageDraw.Draw(sheet)
        for offset, page in enumerate(pages[start:start+6]):
            image = Image.open(page).convert("RGB")
            image.thumbnail((396, 518))
            x, y = (offset % 3) * 410 + 7, (offset // 3) * 550 + 24
            sheet.paste(image, (x, y))
            draw.text((x, y-18), f"Page {start+offset+1}", fill="black")
        sheet.save(output / f"sheet-{start//6+1:02d}.png")
    print(f"Rendered {len(pages)} pages to {output}")
    print("PDF subject:", reader.metadata.subject)
    for index, page in enumerate(reader.pages, 1):
        text = page.extract_text()
        for title in ("A fixed-floor Fourier", "The complete high-frequency", "The five finite-index steps",
                      "Actual support and the interpretation", "Locations of the companion"):
            if title in text:
                print(f"Page {index}: {title}")


if __name__ == "__main__":
    main()
