"""2026-10-30: pure INITIAL47 helper extraction from n15_reference_circle_boundary_probe.py.
Mathematical definitions are copied unchanged; unrelated probe drivers are omitted.
"""
from __future__ import annotations

from fractions import Fraction as F
import order8_rational_ray_endpoint_probe as scalar
base, kernel = scalar.base, scalar.kernel_probe
I, S, ONE, PI = scalar.I, scalar.S, scalar.ONE, base.PI
ZERO = I.rat(0)

def rat(x: F | int) -> I:
    x = F(x)
    return I.rat(x.numerator, x.denominator)

SQRT3 = I.rat(3).sqrt()

OLD_THETA_A = I.rat(27)/(50*PI.sqr())+3*SQRT3/(10*PI)

OLD_THETA_B = I.rat(27)/(125*(PI**3))+9*SQRT3/(50*PI.sqr())

NEW_THETA_A = I.rat(4)/(3*PI.sqr())+I.rat(2)/(3*PI)

NEW_THETA_B = I.rat(16)/(27*(PI**3))+I.rat(4)/(9*PI.sqr())

def exp_minus_upper(x: I) -> I:
    assert x.lo >= 0
    return scalar.exp_neg_order8(I(min(x.lo, 32*S), min(x.hi, 32*S))).upper()
