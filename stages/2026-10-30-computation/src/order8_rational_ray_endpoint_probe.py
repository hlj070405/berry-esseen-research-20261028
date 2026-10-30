"""2026-10-30: pure INITIAL47 helper extraction from order8_rational_ray_endpoint_probe.py.
Mathematical definitions are copied unchanged; unrelated probe drivers are omitted.
"""
from __future__ import annotations

import n4_band_interval_certificate as base
import rational_kernel_endpoint_probe as kernel_probe
I, S, ONE = base.I, base.S, base.ONE

def exp_neg_order8(x: I) -> I:
    assert 0 <= x.lo <= x.hi <= 32*S
    y = x/32
    term, partial = ONE, ONE
    for k in range(1, 9):
        term = term*y/k
        partial = partial+term
    next_term = term*y/9
    tail = next_term/(ONE-y/10)
    small = I(partial.lo, (partial+tail).hi)
    return ONE/(small**32)
