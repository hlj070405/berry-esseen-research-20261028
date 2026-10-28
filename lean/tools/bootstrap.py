"""2026-10-28: install a local pinned Lean and fetch selected mathlib caches.

No global PATH/settings changes and no cloud execution. Child processes use
two CPUs on Windows. Downloads are official Lean/mathlib resources; local
mathematical sources are never uploaded. Run with Python 3 and zstandard.
"""
from __future__ import annotations

import ctypes
import os
from pathlib import Path
import subprocess
import sys
import tarfile

import zstandard

PROJECT = Path(__file__).resolve().parents[1]
VERSION = "4.35.0"
CACHE = Path.home() / ".cache/berry-esseen-tools"
SDK = CACHE / f"lean-{VERSION}-windows"


def run(arguments: list[str], *, env: dict | None = None) -> None:
    subprocess.run(arguments, cwd=PROJECT, env=env, check=True)


def main() -> None:
    if os.name == "nt":
        kernel = ctypes.windll.kernel32
        kernel.GetCurrentProcess.restype = ctypes.c_void_p
        kernel.SetProcessAffinityMask.argtypes = [ctypes.c_void_p, ctypes.c_size_t]
        if not kernel.SetProcessAffinityMask(kernel.GetCurrentProcess(), 3):
            raise OSError("Could not restrict this bootstrap process to two CPUs.")
    CACHE.mkdir(parents=True, exist_ok=True)
    archive = CACHE / f"lean-{VERSION}-windows.tar.zst"
    if not (SDK / "bin/lean.exe").is_file():
        print("Downloading the pinned official Lean SDK (resumable).", flush=True)
        run(["curl.exe", "--silent", "--show-error", "--location", "--fail",
             "--retry", "2", "--continue-at", "-", "--output", str(archive),
             f"https://github.com/leanprover/lean4/releases/download/v{VERSION}/{archive.name}"])
        print("Extracting the SDK into the local tool cache.", flush=True)
        with archive.open("rb") as raw:
            with zstandard.ZstdDecompressor().stream_reader(raw) as stream:
                with tarfile.open(fileobj=stream, mode="r|") as source:
                    for member in source:
                        if member.name.split("/")[0] != SDK.name:
                            raise ValueError("Unexpected SDK archive root.")
                        source.extract(member, CACHE, filter="data")
    environment = os.environ.copy()
    environment["PATH"] = str(SDK / "bin") + os.pathsep + environment["PATH"]
    environment["MATHLIB_NO_CACHE_ON_UPDATE"] = "1"
    run([str(SDK / "bin/lean.exe"), "--version"], env=environment)
    lake = str(SDK / "bin/lake.exe")
    if not (PROJECT / "lake-manifest.json").is_file():
        run([lake, "update"], env=environment)
    print("Fetching only the requested compiled mathlib modules.", flush=True)
    modules = sys.argv[1:] or [
        "Mathlib.Data.Real.Basic",
        "Mathlib.Algebra.Order.BigOperators.Group.Finset",
        "Mathlib.Tactic.Linarith",
        "Mathlib.Tactic.NormNum",
        "Mathlib.Tactic.Positivity",
        "Mathlib.Tactic.Ring",
        "Mathlib.Tactic.FieldSimp",
        "Mathlib.MeasureTheory.Integral.Bochner.Set",
        "Mathlib.MeasureTheory.Measure.ProbabilityMeasure",
        "Mathlib.MeasureTheory.Constructions.Pi",
        "Mathlib.Probability.Distributions.Gaussian.Real",
    ]
    run([lake, "exe", "cache", "get", *modules], env=environment)
    print(f"Local Lean environment ready: {SDK / 'bin'}", flush=True)


if __name__ == "__main__":
    main()
