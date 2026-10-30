"""2026-10-30: pure INITIAL47 helper extraction from rational_kernel_endpoint_probe.py.
Mathematical definitions are copied unchanged; unrelated probe drivers are omitted.
"""
from __future__ import annotations

import n4_band_interval_certificate as base
I, S, ONE, PI = base.I, base.S, base.ONE, base.PI

def regular_tail(z: I) -> I:
    """Terms 2,3,4 plus the exact telescoping upper bound on terms >=5."""
    z2 = z.sqr()
    return ONE/(4-z2)+ONE/(9-z2)+ONE/(16-z2)+I.rat(9, 40)

def rational_kernel_upper(z: I, *, final_cell: bool = False) -> I:
    assert 0 < z.lo <= z.hi < S
    w = ONE-z
    imag = w.sqr()/(PI*(ONE-w.sqr()))+w.sqr()*regular_tail(w)/PI
    return ((w/2).sqr()+imag.sqr()).sqrt().upper()

def rational_correction_upper(z: I, first_cell: bool = False) -> I:
    # At zero this is the continuous extension used in the integral, not
    # a claim about the source's totalized singular expression at that point.
    assert 0 <= z.lo <= z.hi < S
    imag = z/(PI*(ONE+z))+z*(ONE-z)*regular_tail(z)/PI
    price = (((ONE-z)/2).sqr()+imag.sqr()).sqrt()
    return base.min_upper(price, ONE/2)
