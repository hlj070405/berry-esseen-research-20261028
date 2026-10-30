"""2026-10-30: pure INITIAL47 helper extraction from finite_n_closed_rho_box_pilots.py.
Mathematical definitions are copied unchanged; unrelated probe drivers are omitted.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as F
from n4_band_interval_certificate import I, S, PI, sincos

def rat(x: F | int) -> I:
    x = F(x)
    return I.rat(x.numerator, x.denominator)

def min_interval(x: I, y: I) -> I:
    return I(min(x.lo, y.lo), min(x.hi, y.hi))

@dataclass(frozen=True)
class RhoBox:
    n: int

    rho_lower: F

    rho_upper: F

    target: F

    full_high_rho_upper_text: str

    @property
    def root(self) -> I:
        return I.rat(self.n).sqrt()

    @property
    def gamma(self) -> I:
        rho = rat(self.rho_upper)
        inner = (rho.sqr()-4+rho*(rho.sqr()+8).sqrt())/2
        assert inner.lo > 0
        return inner.sqrt()

    def h_complete(self, s: I) -> I:
        rho = rat(self.rho_upper)
        assert s.lo >= 0
        z = min_interval(s, PI/rho)
        w = min_interval(s, PI/2)
        sh, _ = sincos(rho*z/4)
        sw, cw = sincos(w)
        first = 8*sh.sqr()/rho+2*(s-z).nonneg()
        second = (sw-w*cw).nonneg()+(s.sqr()-w.sqr()).nonneg()/2
        return (first+second).upper()
