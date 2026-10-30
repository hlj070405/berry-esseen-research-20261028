"""2026-10-30: pure INITIAL47 helper extraction from n4_band_interval_certificate.py.
Mathematical definitions are copied unchanged; unrelated probe drivers are omitted.
"""
from __future__ import annotations

import ctypes
from dataclasses import dataclass
from math import factorial, isqrt
import os

S = 10**40

def ceildiv(n: int, d: int) -> int:
    assert d > 0
    return -((-n) // d)

@dataclass(frozen=True, slots=True)
class I:
    lo: int
    hi: int

    def __post_init__(self):
        assert self.lo <= self.hi

    @staticmethod
    def rat(n: int, d: int = 1) -> I:
        assert d > 0
        return I(n*S//d, ceildiv(n*S, d))

    @staticmethod
    def box(lo: I, hi: I) -> I:
        return I(lo.lo, hi.hi)

    def __add__(self, other: I | int) -> I:
        if isinstance(other, int):
            other = I.rat(other)
        return I(self.lo+other.lo, self.hi+other.hi)

    __radd__ = __add__

    def __neg__(self) -> I:
        return I(-self.hi, -self.lo)

    def __sub__(self, other: I | int) -> I:
        return self + (-other if isinstance(other, I) else -other)

    def __rsub__(self, other: int) -> I:
        return I.rat(other) - self

    def __mul__(self, other: I | int) -> I:
        if isinstance(other, int):
            other = I.rat(other)
        vals = (self.lo*other.lo, self.lo*other.hi,
                self.hi*other.lo, self.hi*other.hi)
        return I(min(vals)//S, ceildiv(max(vals), S))

    __rmul__ = __mul__

    def __truediv__(self, other: I | int) -> I:
        if isinstance(other, int):
            assert other > 0
            return I(self.lo//other, ceildiv(self.hi, other))
        assert other.lo > 0
        inv = I(S*S//other.hi, ceildiv(S*S, other.lo))
        return self*inv

    def sqr(self) -> I:
        hi = max(self.lo*self.lo, self.hi*self.hi)
        lo = 0 if self.lo <= 0 <= self.hi else min(self.lo*self.lo, self.hi*self.hi)
        return I(lo//S, ceildiv(hi, S))

    def __pow__(self, n: int) -> I:
        assert n >= 0
        ans, x = I.rat(1), self
        while n:
            if n & 1:
                ans = ans*x
            n >>= 1
            if n:
                x = x.sqr()
        return ans

    def sqrt(self) -> I:
        assert self.lo >= 0
        lo = isqrt(self.lo*S)
        hi = isqrt(self.hi*S)
        if hi*hi < self.hi*S:
            hi += 1
        return I(lo, hi)

    def upper(self) -> I:
        return I(self.hi, self.hi)

    def nonneg(self) -> I:
        assert self.hi >= 0
        return I(max(0, self.lo), self.hi)

    def decimal_upper(self, places: int = 15) -> str:
        scale = 10**places
        num = ceildiv(self.hi*scale, S)
        return f'{num//scale}.{num%scale:0{places}d}'

ONE = I.rat(1)

ZERO = I.rat(0)

def atan_reciprocal(d: int, terms: int = 64) -> I:
    # Alternating series; after 64 terms the next term is positive.
    ans = ZERO
    for k in range(terms):
        term = I.rat(1, (2*k+1)*d**(2*k+1))
        ans = ans + (term if k % 2 == 0 else -term)
    next_term = I.rat(1, (2*terms+1)*d**(2*terms+1))
    if terms % 2 == 0:
        return I(ans.lo, (ans+next_term).hi)
    return I((ans-next_term).lo, ans.hi)

PI = 16*atan_reciprocal(5)-4*atan_reciprocal(239)

def sincos(x: I) -> tuple[I, I]:
    """Taylor at the fixed-point midpoint, then the 1-Lipschitz bound."""
    assert max(abs(x.lo), abs(x.hi)) <= 4*S
    mid = (x.lo+x.hi)//2
    c = I(mid, mid)
    radius = max(mid-x.lo, x.hi-mid)
    x2 = c.sqr()
    ts, tc = c, ONE
    ss, cc = ts, tc
    for k in range(1, 25):
        ts = -(ts*x2/((2*k)*(2*k+1)))
        tc = -(tc*x2/((2*k-1)*(2*k)))
        ss, cc = ss+ts, cc+tc
    # sin polynomial degree 49 and cos polynomial degree 48.
    ac = I(max(abs(c.lo), abs(c.hi)), max(abs(c.lo), abs(c.hi)))
    rs = (ac**50)/factorial(50)
    rc = (ac**49)/factorial(49)
    sin_i = I(max(-S, ss.lo-rs.hi-radius), min(S, ss.hi+rs.hi+radius))
    cos_i = I(max(-S, cc.lo-rc.hi-radius), min(S, cc.hi+rc.hi+radius))
    return sin_i, cos_i

def min_upper(*xs: I) -> I:
    hi = min(x.hi for x in xs)
    assert hi >= 0
    return I(hi, hi)

def rational_text(x: I) -> dict[str, str]:
    return {'upper_numerator': str(x.hi), 'denominator': str(S),
            'decimal_upper': x.decimal_upper()}

def pin_two_cpus():
    if os.name == 'nt':
        kernel32 = ctypes.WinDLL('kernel32', use_last_error=True)
        kernel32.GetCurrentProcess.restype = ctypes.c_void_p
        kernel32.SetProcessAffinityMask.argtypes = [ctypes.c_void_p, ctypes.c_size_t]
        assert kernel32.SetProcessAffinityMask(kernel32.GetCurrentProcess(), 3)
    else:
        # 2026-10-30: portability only; use two CPUs within the allowed cpuset.
        allowed = sorted(os.sched_getaffinity(0))
        assert len(allowed) >= 2, "Two allowed CPUs are required."
        os.sched_setaffinity(0, set(allowed[:2]))
