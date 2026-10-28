"""2026-10-27: export exact profile parameters for the mathematical companion.

This light calculation reads the already acquired actual-index resources,
runs the finite signed-budget projection, and exports the 34 analytic
profiles used in the paper. It does not rerun or establish the preceding
Fourier/support acquisition and does not treat a file label as its proof.
"""
from __future__ import annotations

from fractions import Fraction
import json
from pathlib import Path
import sys

PROJECT = Path(__file__).resolve().parent
WORKSPACE = PROJECT.parents[2]
ANALYTIC = WORKSPACE / "work/berry-esseen-low26-30-20261026/source/analytic"
sys.path.insert(0, str(ANALYTIC))
from probe_p37_contact_price_geometry_20261027 import load_profile, contact_geometry
from finite_gap_transfer_exact_20261026 import CE_LO


def decimal(value: Fraction) -> str:
    """Write terminating rational input caps exactly, without float rounding."""
    den = value.denominator
    exponents = []
    for prime in (2, 5):
        exponent = 0
        while den % prime == 0:
            den //= prime
            exponent += 1
        exponents.append(exponent)
    if den != 1:
        raise ValueError(f"Nonterminating decimal cap: {value}")
    places = max(exponents)
    if not places:
        return str(value.numerator)
    sign = "-" if value < 0 else ""
    integer = abs(value.numerator) * 10**places // value.denominator
    digits = str(integer).zfill(places + 1)
    return (sign + digits[:-places] + "." + digits[-places:]).rstrip("0").rstrip(".")


def encode(value):
    if isinstance(value, Fraction):
        return str(value)
    if isinstance(value, dict):
        return {key: encode(item) for key, item in value.items()}
    if isinstance(value, (tuple, list)):
        return [encode(item) for item in value]
    return value


def main() -> None:
    profiles = []
    table = [
        r"\section{The analytic profile parameters}\label{app:parameters}",
        r"The table gives the original joint inward intercept $\Delta$ and",
        r"noise intercept $\Lambda$, together with the improved necessary",
        r"actual-noise cap $L_*$, for the $34$ middle-moment profiles.",
        r"All entries are exact terminating decimals. The simultaneous",
        r"signed coefficients, outward support caps and contact domains",
        r"are supplied as exact rational numbers in the accompanying",
        r"\texttt{profile-parameters.json}; they are acquired conditions",
        r"on an extremizer, not independent free parameters.",
        r"\begingroup\small",
        r"\begin{longtable}{ccrrr}\toprule",
        r"$n$ & interval & $\Delta$ & $\Lambda$ & $L_*$\\\midrule\endhead",
    ]
    for n in range(26, 31):
        for index in range(34, 40 if n == 26 else 41):
            z = load_profile(index, n=n)
            assert z["budget"]["binding"]["required_global_predecessor"] == f"C{n-1} <= CE"
            scalar_keys = ("pl", "pu", "Delta", "Lambda", "L", "R", "g", "hm", "hp", "O0", "O1")
            profile = dict(n=n, index=index, **{key: z[key] for key in scalar_keys})
            profile.update(
                Hminus=z["cfg"]["Hminus"], Hplus=z["cfg"]["Hplus"],
                noise=[0, z["Lambda"]/8, z["Lambda"]/4, 5*z["Lambda"]/16,
                       3*z["Lambda"]/8, 7*z["Lambda"]/16, z["Lambda"]/2, z["L"]],
                allocation=[Fraction(j, 4) for j in range(5)],
                contact=contact_geometry(z),
            )
            assert all(a < b for a, b in zip(profile["noise"], profile["noise"][1:]))
            profiles.append(profile)
            values = " & ".join(decimal(z[key]) for key in ("Delta", "Lambda", "L"))
            table.append(f"${n}$ & $I_{{{index}}}$ & {values}" + r"\\")
        if n != 30:
            table.append(r"\addlinespace")
    assert len(profiles) == 34
    table.extend([
        r"\bottomrule\end{longtable}\endgroup",
        r"The analytic programs use the Python 3 standard library and retain",
        r"exact rational arithmetic. In the companion directory",
        r"\path{finite-steps/source/analytic}, the seven actual-$30$",
        r"profiles can be recomputed with",
        r"\par\noindent\texttt{python -B}\ \path{replay_n30_analytic_panels_20261027.py}",
        r"\ \texttt{--output fresh.json}\par",
        r"An explicit \texttt{--output} argument selects a fresh filename;",
        r"the program refuses to overwrite an existing result.",
        r"The option \texttt{--indices 37} recomputes just that complete",
        r"profile, including its contact domain and the CDF bridge.",
        r"The finite-index mathematical companion states the count and phase",
        r"composition for every profile; the executable calculation supplies",
        r"the enclosed faces, derivatives and strict margins used there.",
        "",
    ])
    output = PROJECT / "companions"
    output.mkdir(exist_ok=True)
    document = dict(
        description="Exact acquired parameters for the 34 analytic middle-band profiles; acquisition proofs are separate.",
        actual_moment_band=["11/10", "6/5"],
        target="CE/sqrt(n) in the manuscript; outward calculations use a lower rational coefficient",
        directed_constant_lower=CE_LO,
        profiles=profiles,
    )
    (output / "profile-parameters.json").write_text(json.dumps(encode(document), indent=2) + "\n", encoding="utf-8")
    (PROJECT / "sections/profile-parameters.tex").write_text("\n".join(table), encoding="utf-8", newline="\n")
    print("Prepared 34 exact profile rows and the TeX parameter table.")


if __name__ == "__main__":
    main()
