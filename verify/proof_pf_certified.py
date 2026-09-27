#!/usr/bin/env python3
"""Certified (interval-arithmetic) recomputation of the explicit constants of the M1 proof.

    python3 audit/proof_pf_certified.py          # Python standard library only

This file recomputes, with rigorous interval arithmetic, every numerical value and
every numerical inequality on which the explicit constants of the M1 proof rest
(proof manuscript v2, manuscript/proof/*.md, and the English paper papers/m1/m1.tex:
Sections "The height condition (HGT)", "Assembly and constants", "Transfer to the
stopping time" and Appendix A).  It is the certified counterpart of the
double-precision script audit/proof_pf.py; it does not import that script.

Arithmetic.  An interval is a pair [lo, hi] of exact dyadic rationals k / 2^PREC
(a subset of fractions.Fraction; the integer numerators are stored for speed).
Every operation rounds lo down and hi up, so the true real value always lies in
the interval.  Transcendental functions are evaluated from explicit series with
explicit remainder bounds:
  ln x  : x = 2^k m with m in [2^-1/2, 2^1/2], ln m = 2 atanh((m-1)/(m+1));
          tail of the atanh series bounded by the last included power of t.
  exp x : x = k ln 2 + r, e^r = (e^(r/2^S))^(2^S), Taylor series of e^(r/2^S)
          with the Lagrange-type tail bound 2 |y|^N / N!  (|y| <= 1/2).
  sqrt  : integer isqrt with outward rounding.
Decimal constants of the manuscript (e.g. 9e-4, 1.23, 53.6) enter as exact
rationals; binary floating point is never used in a certified quantity (floats
are rejected by the interval constructor).

Output.  One line per claim: identifier, certified enclosure, claim, status and a
note.  Identifiers "pf-*" are the tags of audit/proof_pf.py (and of the manuscript);
"x-*" are further numbers quoted in the manuscript or the paper.  A suffix names
the source of the stated decimal: "/A.1" (Appendix A.1), "/ms" (manuscript text),
"/pf" (a reference value of proof_pf.py, checked with that script's tolerance).
Equality claims are checked against the rounding interval of the stated decimal
(to nearest, or down/up where the text says so); inequality claims directly.
Displayed values that the text labels as gains (losses) are checked to be rounded
down (up), as Appendix A states.  Thresholds obtained by bisection are certified
at the stated value together with the monotonicity argument (printed).  The last
line is a one-line summary.  Exit code 1 if any claim fails.

This is a certificate for the arithmetic only.  It does not check the proofs in
which the numbers are used.
"""
from __future__ import annotations

import math
import random
import sys
import time
from decimal import Decimal, localcontext, ROUND_CEILING, ROUND_FLOOR
from fractions import Fraction

sys.dont_write_bytecode = True

# =====================================================================================
# 1. Interval arithmetic on dyadic rationals
# =====================================================================================

PREC = 256                      # endpoints are integers n meaning n / 2^PREC
_ONE = 1 << PREC


def _floor_scaled(x: Fraction) -> int:
    """floor(x * 2^PREC) for an exact rational x."""
    return (x.numerator << PREC) // x.denominator


def _ceil_scaled(x: Fraction) -> int:
    """ceil(x * 2^PREC) for an exact rational x."""
    return -((-(x.numerator << PREC)) // x.denominator)


def _to_fraction(x) -> Fraction:
    if isinstance(x, float):
        raise TypeError("binary floats are not allowed in certified quantities; use a str or Fraction")
    return Fraction(x)


class Iv:
    """Closed interval [lo, hi] / 2^PREC with outward rounding."""

    __slots__ = ("lo", "hi")

    def __init__(self, lo: int, hi: int):
        if lo > hi:
            raise ValueError("empty interval")
        self.lo = lo
        self.hi = hi

    # ---- construction -------------------------------------------------------------
    @staticmethod
    def of(x) -> "Iv":
        """Smallest grid interval containing the exact rational x (int, str, Fraction)."""
        if isinstance(x, Iv):
            return x
        fr = _to_fraction(x)
        return Iv(_floor_scaled(fr), _ceil_scaled(fr))

    @staticmethod
    def hull(a, b) -> "Iv":
        a, b = Iv.of(a), Iv.of(b)
        return Iv(min(a.lo, b.lo), max(a.hi, b.hi))

    # ---- inspection -------------------------------------------------------------
    def lo_f(self) -> Fraction:
        return Fraction(self.lo, _ONE)

    def hi_f(self) -> Fraction:
        return Fraction(self.hi, _ONE)

    def width(self) -> Fraction:
        return Fraction(self.hi - self.lo, _ONE)

    def contains(self, x) -> bool:
        fr = _to_fraction(x)
        return self.lo_f() <= fr <= self.hi_f()

    def mag(self) -> int:
        """Upper bound of |x| (scaled integer)."""
        return max(abs(self.lo), abs(self.hi))

    # certain comparisons: True only if the relation holds for every pair of points
    def lt(self, o) -> bool:
        return self.hi < Iv.of(o).lo

    def le(self, o) -> bool:
        return self.hi <= Iv.of(o).lo

    def gt(self, o) -> bool:
        return Iv.of(o).lt(self)

    def ge(self, o) -> bool:
        return Iv.of(o).le(self)

    # ---- arithmetic -------------------------------------------------------------
    def __add__(self, o):
        o = Iv.of(o)
        return Iv(self.lo + o.lo, self.hi + o.hi)

    __radd__ = __add__

    def __neg__(self):
        return Iv(-self.hi, -self.lo)

    def __sub__(self, o):
        o = Iv.of(o)
        return Iv(self.lo - o.hi, self.hi - o.lo)

    def __rsub__(self, o):
        return Iv.of(o) - self

    def __mul__(self, o):
        o = Iv.of(o)
        if self.lo >= 0 and o.lo >= 0:
            lo, hi = self.lo * o.lo, self.hi * o.hi
        else:
            c = (self.lo * o.lo, self.lo * o.hi, self.hi * o.lo, self.hi * o.hi)
            lo, hi = min(c), max(c)
        return Iv(lo >> PREC, -((-hi) >> PREC))

    __rmul__ = __mul__

    def __truediv__(self, o):
        o = Iv.of(o)
        if o.lo <= 0 <= o.hi:
            raise ZeroDivisionError("division by an interval containing 0")
        fl, cl = [], []
        for n in (self.lo, self.hi):
            ns = n << PREC
            for d in (o.lo, o.hi):
                fl.append(ns // d)
                cl.append(-((-ns) // d))
        return Iv(min(fl), max(cl))

    def __rtruediv__(self, o):
        return Iv.of(o) / self

    def __pow__(self, n: int):
        if not isinstance(n, int):
            raise TypeError("use pw(x, y) for real exponents")
        if n < 0:
            return Iv.of(1) / (self ** (-n))
        if self.lo < 0:
            raise ValueError("integer powers are implemented for nonnegative bases only")
        result, base = Iv.of(1), self
        while n:
            if n & 1:
                result = result * base
            n >>= 1
            if n:
                base = base * base
        return result

    def shift(self, k: int) -> "Iv":
        """Multiply by 2^k (exact for k >= 0, outward rounding for k < 0)."""
        if k >= 0:
            return Iv(self.lo << k, self.hi << k)
        return Iv(self.lo >> (-k), -((-self.hi) >> (-k)))

    # ---- output -------------------------------------------------------------
    def fmt(self, digits: int = 12) -> str:
        return f"[{_dec(self.lo, ROUND_FLOOR, digits)}, {_dec(self.hi, ROUND_CEILING, digits)}]"

    def __repr__(self):
        return "Iv" + self.fmt()


def _dec(n: int, rounding, digits: int) -> str:
    with localcontext() as ctx:
        ctx.prec = digits
        ctx.rounding = rounding
        v = Decimal(n) / Decimal(_ONE)
    return f"{v:.{digits - 1}E}" if v != 0 else "0"


def imin(a, b) -> Iv:
    a, b = Iv.of(a), Iv.of(b)
    return Iv(min(a.lo, b.lo), min(a.hi, b.hi))


def imax(a, b) -> Iv:
    a, b = Iv.of(a), Iv.of(b)
    return Iv(max(a.lo, b.lo), max(a.hi, b.hi))


def ifloor(x: Iv):
    """floor of every point of x if it is the same integer, else None (ambiguous)."""
    a, b = x.lo >> PREC, x.hi >> PREC
    return a if a == b else None


def iceil(x: Iv):
    a, b = -((-x.lo) >> PREC), -((-x.hi) >> PREC)
    return a if a == b else None


def isqrt_iv(x) -> Iv:
    x = Iv.of(x)
    if x.lo < 0:
        raise ValueError("sqrt of a negative number")
    lo = math.isqrt(x.lo << PREC)
    n = x.hi << PREC
    hi = math.isqrt(n)
    if hi * hi < n:
        hi += 1
    return Iv(lo, hi)


# ---- logarithm ------------------------------------------------------------------
_THIN = PREC // 2               # intervals narrower than 2^-(PREC/2) are evaluated directly


def _atanh_series(t: Iv) -> Iv:
    """atanh(t) for |t| <= 0.34, with the tail bounded by the last included power of t.

    atanh t = sum_{i>=0} t^(2i+1)/(2i+1).  After the term with t^(2n+1) the tail is at
    most |t|^(2n+3) / ((2n+3)(1-t^2)) <= |t|^(2n+1) * t^2/(1-t^2) <= |t|^(2n+1) for t^2 <= 1/2.
    """
    if t.mag() * 100 > 34 * _ONE:
        raise ValueError("atanh series used outside |t| <= 0.34")
    t2 = t * t
    power = t
    s = t
    i = 1
    stop = 1 << 8                                  # stop once |t|^(2i+1) <= 2^(8 - PREC)
    while power.mag() > stop:
        power = power * t2
        s = s + power / (2 * i + 1)
        i += 1
    r = power.mag() + 1                            # tail bound (scaled), +1 for safety
    return Iv(s.lo - r, s.hi + r)


LN2 = _atanh_series(Iv.of(Fraction(1, 3))) * 2      # ln 2 = 2 atanh(1/3)
_SQRT2 = isqrt_iv(2)


def _ln_direct(x: Iv) -> Iv:
    # range reduction by the position of the leading bit of x.lo: m = x / 2^k in [1, 2)
    k = x.lo.bit_length() - 1 - PREC
    m = x.shift(-k)
    if m.lo > _SQRT2.hi:                           # m in (sqrt2, 2): use m/2 in (1/sqrt2, 1)
        k += 1
        m = x.shift(-k)
    t = (m - 1) / (m + 1)
    return _atanh_series(t) * 2 + LN2 * k


def ln(x) -> Iv:
    x = Iv.of(x)
    if x.lo <= 0:
        raise ValueError("ln of an interval not contained in (0, inf)")
    if x.hi - x.lo < (1 << _THIN) and (x.hi.bit_length() == x.lo.bit_length()):
        return _ln_direct(x)
    # wide interval: ln is increasing, evaluate the endpoints
    return Iv(_ln_direct(Iv(x.lo, x.lo)).lo, _ln_direct(Iv(x.hi, x.hi)).hi)


def log2(x) -> Iv:
    return ln(x) / LN2


# ---- exponential ------------------------------------------------------------------
_EXP_S = 8                                          # e^r = (e^(r/2^S))^(2^S)


def _exp_direct(x: Iv) -> Iv:
    k = round(x.lo_f() / LN2.lo_f())
    r = x - LN2 * k                                 # |r| <= ln2/2 + tiny
    y = r.shift(-_EXP_S)                            # |y| <= 0.0014
    term = Iv.of(1)
    s = Iv.of(1)
    n = 1
    stop = 1 << 4
    while True:
        term = term * y / n
        s = s + term
        n += 1
        if term.mag() <= stop:
            break
    # tail: sum_{j>=n} |y|^j/j! <= 2 |y|^n / n!  (|y| <= 1/2); |term| = |y|^(n-1)/(n-1)! bounds it
    r_tail = term.mag() + 1
    s = Iv(s.lo - r_tail, s.hi + r_tail)
    for _ in range(_EXP_S):
        s = s * s
    return s.shift(k)


def exp(x) -> Iv:
    x = Iv.of(x)
    if x.hi - x.lo < (1 << _THIN):
        return _exp_direct(x)
    return Iv(_exp_direct(Iv(x.lo, x.lo)).lo, _exp_direct(Iv(x.hi, x.hi)).hi)


def pw(a, b) -> Iv:
    """a^b = exp(b ln a) for a > 0 (b real)."""
    return exp(Iv.of(b) * ln(a))


def pw2(b) -> Iv:
    """2^b."""
    return exp(Iv.of(b) * LN2)


LN3 = ln(3)
LN8 = LN2 * 3
LN9 = LN3 * 2

# =====================================================================================
# 2. Self-tests of the interval library
# =====================================================================================

# Decimal expansions (40 digits after the point), cross-checked in the self-test against
# the correctly rounded ln of Python's decimal module at 90 digits.
LN2_DEC = "0.6931471805599453094172321214581765680755"
LN3_DEC = "1.0986122886681096913952452369225257046474"
LOG2_3_DEC = "1.5849625007211561814537389439478165087598"


def _dec_iv(s: str, digits_after_point: int) -> Iv:
    """Interval [s, s + 10^-d] for a truncated decimal expansion s."""
    v = Fraction(s)
    return Iv.hull(v, v + Fraction(1, 10 ** digits_after_point))


def _decimal_of(fr: Fraction) -> Decimal:
    return Decimal(fr.numerator) / Decimal(fr.denominator)


def _check_against_decimal(iv: Iv, dval: Decimal, tol_rel: Fraction) -> bool:
    """True if iv meets the ball dval +- tol_rel*|dval| (dval is correctly rounded at 90 digits)."""
    d = Fraction(dval)
    tol = abs(d) * tol_rel + Fraction(1, 10 ** 85)
    return iv.lo_f() <= d + tol and d - tol <= iv.hi_f()


def selftest() -> list[str]:
    fails: list[str] = []
    rng = random.Random(20260926)

    def chk(cond: bool, what: str) -> None:
        if not cond:
            fails.append(what)

    with localcontext() as ctx:
        ctx.prec = 90
        # --- known constants
        chk(LN2.width() < Fraction(1, 10 ** 70), "ln2 width")
        chk(LN3.width() < Fraction(1, 10 ** 70), "ln3 width")
        lam = LN3 / LN2
        for name, iv, s in (("ln 2", LN2, LN2_DEC), ("ln 3", LN3, LN3_DEC), ("log2 3", lam, LOG2_3_DEC)):
            ref = _dec_iv(s, 40)
            chk(iv.hi >= ref.lo and ref.hi >= iv.lo, f"{name} vs hard-coded 40 digits")
        chk(_check_against_decimal(LN2, Decimal(2).ln(), Fraction(1, 10 ** 70)), "ln2 vs decimal")
        chk(_check_against_decimal(LN3, Decimal(3).ln(), Fraction(1, 10 ** 70)), "ln3 vs decimal")
        chk(_check_against_decimal(lam, Decimal(3).ln() / Decimal(2).ln(), Fraction(1, 10 ** 70)), "log2 3 vs decimal")
        # independent series: ln 3 = ln 2 + 2 atanh(1/5)
        ln3b = LN2 + _atanh_series(Iv.of(Fraction(1, 5))) * 2
        chk(ln3b.hi >= LN3.lo and LN3.hi >= ln3b.lo, "ln 3 two series")
        # identities
        chk(exp(LN3).contains(3), "exp(ln 3) contains 3")
        chk(exp(LN2 * 10).contains(1024), "exp(10 ln 2) contains 1024")
        chk(log2(Iv.of(8)).contains(3), "log2 8 contains 3")
        r2a, r2b = pw(Iv.of(2), Iv.of(Fraction(1, 2))), isqrt_iv(2)
        chk(r2a.hi >= r2b.lo and r2b.hi >= r2a.lo, "2^(1/2) vs sqrt 2")
        chk(pw2(Iv.of(-1)).contains(Fraction(1, 2)), "2^-1 contains 1/2")
        # --- random arguments: ln, exp, sqrt against decimal (strong) and math (float agreement)
        for _ in range(300):
            num = rng.randrange(1, 10 ** 12)
            den = rng.randrange(1, 10 ** 12)
            x = Fraction(num, den) * Fraction(10) ** rng.randrange(-8, 9)
            xi = Iv.of(x)
            dx = _decimal_of(x)
            l = ln(xi)
            chk(_check_against_decimal(l, dx.ln(), Fraction(1, 10 ** 70)), f"ln({x}) vs decimal")
            chk(abs(float(l.lo_f()) - math.log(float(x))) <= 4e-15 * max(1.0, abs(math.log(float(x)))), f"ln({x}) vs math.log")
            chk(l.width() < Fraction(1, 10 ** 50), f"ln({x}) width")
            y = Fraction(rng.randrange(-30 * 10 ** 6, 30 * 10 ** 6), 10 ** 6)
            e = exp(Iv.of(y))
            chk(_check_against_decimal(e, _decimal_of(y).exp(), Fraction(1, 10 ** 55)), f"exp({y}) vs decimal")
            chk(e.width() <= e.hi_f() * Fraction(1, 10 ** 55), f"exp({y}) width")
            chk(abs(float(e.lo_f()) / math.exp(float(y)) - 1) <= 4e-15, f"exp({y}) vs math.exp")
            s = isqrt_iv(xi)
            chk(s.lo_f() ** 2 <= x <= s.hi_f() ** 2, f"sqrt({x}) exact containment")
            chk(abs(float(s.lo_f()) / math.sqrt(float(x)) - 1) <= 4e-16, f"sqrt({x}) vs math.sqrt")
        # --- field operations: exact containment
        for _ in range(300):
            a = Fraction(rng.randrange(-10 ** 9, 10 ** 9), rng.randrange(1, 10 ** 9))
            b = Fraction(rng.randrange(1, 10 ** 9), rng.randrange(1, 10 ** 9)) * rng.choice((1, -1))
            A, B = Iv.of(a), Iv.of(b)
            chk((A + B).contains(a + b), "add")
            chk((A - B).contains(a - b), "sub")
            chk((A * B).contains(a * b), "mul")
            chk((A / B).contains(a / b), "div")
            chk((Iv.of(abs(a)) ** 5).contains(abs(a) ** 5), "pow")
        # --- floor/ceil and ambiguity
        chk(ifloor(LN3) == 1 and iceil(LN3) == 2, "floor/ceil of ln 3")
        chk(ifloor(Iv.hull(Fraction("2.999"), Fraction("3.001"))) is None, "floor ambiguity detected")
        chk(ifloor(Iv.of(3)) == 3, "floor of exact integer")
        try:
            Iv.of(0.5)
            chk(False, "floats must be rejected")
        except TypeError:
            pass
    return fails


# =====================================================================================
# 3. The constants (manuscript Section 1.4, 4, 13, 14; proof_pf.py sections [1]-[5])
# =====================================================================================

def D(s: str) -> Fraction:
    """An exact decimal constant of the manuscript, e.g. D('9e-4')."""
    return Fraction(s)


def H(x: Iv) -> Iv:
    return -(x * log2(x)) - (1 - x) * log2(1 - x)


LAM = LN3 / LN2                                   # lambda = log2 3
A = LAM - 1                                       # a = lambda - 1
RHO = 1 / LAM                                     # rho_c
C = 1 - H(RHO)                                    # c = 1 - H(rho_c)
TSTAR = log2(1 / A) / LAM                         # t*
F = (pw2(TSTAR * A) + pw2(-TSTAR)) / 2            # f = m(t*)
RC = isqrt_iv(RHO * (1 - RHO)) * 2                # r_c
M2 = (pw2(TSTAR * A * 2) + pw2(-TSTAR * 2)) / 2   # M_2
PINS = RHO * RHO * 2 / LN2                        # Pinsker coefficient (2/ln2) rho_c^2
RHO_SHARP = RHO + D("1e-4")                       # rho^sharp
C2_4 = D("53.6")                                  # Bugeaud (2002) Theorem 2, c_2(4)
BUG_CONST = 3 * C2_4 / LN8 ** 4                   # 3 * 53.6 / (ln 8)^4
BUG_BITS = BUG_CONST * LN9 * LN2
Y_FLOOR = LN8 * 4                                 # 4 ln 8


def theta(gamma, rho) -> Iv:
    """Theta_gamma(rho) = 1 - 2 (1 - gamma) rho (1 - rho)."""
    return 1 - (1 - Iv.of(gamma)) * rho * (1 - rho) * 2


def phi(p: int) -> Iv:
    """phi_p = (2^-p' + 2^(1-2p'))^(1/p'), p' = p/(p-1); with y = 2^-p' this is (y + 2y^2)^(1/p')."""
    pp = Fraction(p, p - 1)
    y = pw2(-pp)
    return exp(ln(y + y * y * 2) / pp)


LTH = -log2(theta(D("0.5"), RHO_SHARP))           # log2(1/Theta^sharp_{1/2})
SHALLOW = log2(2 / (1 + RC))                      # log2(2/(1 + r_c))

# tables indexed by p: T[p] = log2(1 + r_c^p), LT[p] = log2(1/Theta^sharp_{phi_p}), PHI[p]
_RCP: dict[int, Iv] = {}
_T: dict[int, Iv] = {}
_LT: dict[int, Iv] = {}
_PHI: dict[int, Iv] = {}


def rcp(p: int) -> Iv:
    if p not in _RCP:
        _RCP[p] = RC ** p
    return _RCP[p]


def T(p: int) -> Iv:
    if p not in _T:
        _T[p] = log2(1 + rcp(p))
    return _T[p]


def PHI(p: int) -> Iv:
    if p not in _PHI:
        _PHI[p] = phi(p)
    return _PHI[p]


def LT(p: int) -> Iv:
    if p not in _LT:
        _LT[p] = -log2(theta(PHI(p), RHO_SHARP))
    return _LT[p]


def cD_of(beta) -> Iv:
    return imin(D("9e-4"), (Iv.of(beta) - 1) / 2)


def p_candidates(cD: Iv) -> tuple[int, int]:
    """All values of the rule p(c_D) = min{p >= 80 : log2(1 + r_c^p) <= 0.025 c_D} for c_D in cD
    lie in [pmin, pmax] (T is decreasing in p since r_c < 1).  pmin == pmax means p is determined."""
    target = cD * D("0.025")
    p = 80
    while not T(p).lo <= target.hi:                # p is impossible for every c_D in cD
        p += 1
    pmin = p
    while not T(p).hi <= target.lo:                # p is certain for every c_D in cD
        p += 1
    return pmin, p


def budget(cD, p: int) -> Iv:
    return Iv.of(cD) / 2 * LT(p) - T(p) / p


class Ambiguous(Exception):
    pass


def constants(beta):
    """(delta, c_D, p, B, which) for an exact beta; raises Ambiguous if a discrete choice is undetermined."""
    beta = Iv.of(beta)
    cD = cD_of(beta)
    pmin, pmax = p_candidates(cD)
    if pmin != pmax:
        raise Ambiguous(f"p not determined: candidates {pmin}..{pmax}")
    p = pmin
    B = budget(cD, p)
    lin = (beta - 1) * D("1e-4")
    b3 = B * D("0.3")
    if b3.lt(lin):
        which = "0.3B"
    elif lin.lt(b3):
        which = "1e-4(beta-1)"
    else:
        raise Ambiguous("min{0.3B, 1e-4(beta-1)} not determined")
    return imin(b3, lin), cD, p, B, which


def keff_of(beta) -> Iv:
    d, cD, p, B, _ = constants(beta)
    return B - TSTAR * d * d * D("3.5") - d * D("2.5")


def eps_of(alpha: Fraction):
    """epsilon(alpha) = min{1.70 delta^2 (1-alpha), (1/2)(1-c)(2 alpha - 1)}; returns (eps, which)."""
    beta = alpha / (1 - alpha)
    d = constants(beta)[0]
    e1 = d * d * D("1.70") * (1 - alpha)
    e2 = (1 - C) * (2 * alpha - 1) / 2
    if e1.lt(e2):
        return e1, "1.70 delta^2 (1-alpha)"
    if e2.lt(e1):
        return e2, "(1/2)(1-c)(2alpha-1)"
    raise Ambiguous("min in epsilon(alpha) not determined")


def bug_Y(x, beta) -> Iv:
    """Y = max{ln b' + ln ln 8 + 0.64, 4 ln 8} with b' = beta/(2 lambda ln2 x) + 1/ln 9 (proof_pf.bug_Y)."""
    bprime = Iv.of(beta) / (LAM * LN2 * Iv.of(x) * 2) + 1 / LN9
    return imax(ln(bprime) + ln(LN8) + D("0.64"), Y_FLOOR)


def bug_Z(x, beta) -> Iv:
    bprime = Iv.of(beta) / (LAM * LN2 * Iv.of(x) * 2) + 1 / LN9
    return ln(bprime) + ln(LN8) + D("0.64")


def bug_coef(x, beta) -> Iv:
    Y = bug_Y(x, beta)
    return BUG_BITS * Y * Y * Iv.of(x)


# =====================================================================================
# 4. The certify helper
# =====================================================================================

RESULTS: list[tuple[str, bool]] = []


def _ulp(stated: str) -> Fraction:
    return Fraction(10) ** Decimal(stated).as_tuple().exponent


def _enc(x) -> str:
    if isinstance(x, str):
        return x
    if isinstance(x, Iv):
        return x.fmt(11)
    if isinstance(x, tuple):                       # (lo, hi) exact bracket
        return f"[{_decimal_of(Fraction(x[0])):.10E}, {_decimal_of(Fraction(x[1])):.10E}]"
    fr = Fraction(x)
    return f"{_decimal_of(fr):.11E} (exact)" if fr.denominator != 1 or abs(fr) > 10 ** 12 else f"{fr} (exact)"


def certify(name: str, ok: bool, enclosure, claim: str, note: str = "") -> bool:
    RESULTS.append((name, ok))
    status = "PASS" if ok else "FAIL"
    tail = f"   [{note}]" if note else ""
    print(f"  {status}  {name:<26} {_enc(enclosure):<50} {claim}{tail}")
    return ok


def cert_value(name: str, x, stated: str, mode: str = "nearest", note: str = "") -> bool:
    """Equality claim with a stated decimal.

    nearest : |x - v| <= ulp/2       (the stated value is x rounded to nearest)
    down    : v <= x < v + ulp       (the stated value is x rounded down / truncated)
    up      : v - ulp < x <= v       (the stated value is x rounded up)
    """
    v, u = Fraction(stated), _ulp(stated)
    lo, hi = (x.lo_f(), x.hi_f()) if isinstance(x, Iv) else (Fraction(x), Fraction(x))
    if mode == "nearest":
        ok = v - u / 2 <= lo and hi <= v + u / 2
        claim = f"= {stated} (rounded to nearest)"
    elif mode == "down":
        ok = v <= lo and hi < v + u
        claim = f"= {stated} (rounded down)"
    elif mode == "up":
        ok = v - u < lo and hi <= v
        claim = f"= {stated} (rounded up)"
    else:
        raise ValueError(mode)
    return certify(name, ok, x, claim, note)


def cert_tol(name: str, x, stated: str, tol: str, note: str = "") -> bool:
    """A reference value of proof_pf.py checked with that script's own tolerance: |x - v| <= tol."""
    X = x if isinstance(x, Iv) else Iv.of(x)
    v, t = Fraction(stated), Fraction(tol)
    ok = v - t <= X.lo_f() and X.hi_f() <= v + t
    return certify(name, ok, x, f"= {stated} +- {tol} (proof_pf.py tolerance)", note)


def cert_cmp(name: str, x, rel: str, bound, note: str = "") -> bool:
    """Inequality claim x rel bound (rel in <, <=, >, >=); x, bound intervals or exact rationals."""
    X = Iv.of(x) if not isinstance(x, Iv) else x
    Bd = Iv.of(bound) if not isinstance(bound, Iv) else bound
    ok = {"<": X.lt(Bd), "<=": X.le(Bd), ">": X.gt(Bd), ">=": X.ge(Bd)}[rel]
    if not isinstance(x, Iv):                     # exact rationals: decide exactly
        xb = Fraction(x)
        if not isinstance(bound, Iv):
            b = Fraction(bound)
            ok = {"<": xb < b, "<=": xb <= b, ">": xb > b, ">=": xb >= b}[rel]
    bstr = bound if isinstance(bound, str) else (_enc(bound) if isinstance(bound, Iv) else str(_decimal_of(Fraction(bound))))
    return certify(name, ok, x, f"{rel} {bstr}", note)


def cert_true(name: str, ok: bool, what: str, note: str = "") -> bool:
    return certify(name, ok, "exact / finite check", what, note)


def crossing(fun, lo: int, hi: int) -> tuple[int, int]:
    """For fun(q) (an interval) negative at lo and positive at hi, return integers a < b, b = a + 1,
    with fun(a) certainly < 0 and fun(b) certainly >= 0 (bisection on integers)."""
    if not (fun(lo).hi < 0 and fun(hi).lo >= 0):
        raise Ambiguous("crossing not bracketed")
    while hi - lo > 1:
        mid = (lo + hi) // 2
        v = fun(mid)
        if v.hi < 0:
            lo = mid
        elif v.lo >= 0:
            hi = mid
        else:
            raise Ambiguous(f"sign of the threshold function undetermined at q = {mid}")
    return lo, hi


def crossing_frac(fun, lo: Fraction, hi: Fraction, rel_width: Fraction) -> tuple[Fraction, Fraction]:
    """Bisection on rationals for fun increasing: fun(lo) < 0 <= fun(hi) certainly."""
    if not (fun(lo).hi < 0 and fun(hi).lo >= 0):
        raise Ambiguous("crossing not bracketed")
    while hi - lo > rel_width * hi:
        mid = (lo + hi) / 2
        mid = Fraction(math.floor(mid * 2 ** 90), 2 ** 90) if mid.denominator > 2 ** 90 else mid
        v = fun(mid)
        if v.hi < 0:
            lo = mid
        elif v.lo >= 0:
            hi = mid
        else:
            raise Ambiguous("sign undetermined")
    return lo, hi


# =====================================================================================
# 5. The claims
# =====================================================================================

def group1_basic() -> None:
    print("[1] Basic constants (manuscript 1.4, Appendix A.1; paper Notation, Section 1.4, Appendix A.1)")
    cert_value("pf-c", C, "0.05004")
    cert_value("pf-c/A.1", C, "0.0500445")
    cert_value("pf-c/abstract", C, "0.05004", "down", "paper writes 0.05004...")
    cert_value("pf-tstar", TSTAR, "0.48808")
    cert_value("pf-tstar/A.1", TSTAR, "0.4880771")
    diff = F - pw2(-C)
    certify("pf-f-eq", diff.gt(D("-1e-14")) and diff.lt(D("1e-14")), diff,
            "|f - 2^-c| < 1e-14", "identity of Lemma 1.7 (i), numerical check")
    cert_value("pf-rc", RC, "0.96511")
    cert_value("pf-rc/A.1", RC, "0.9651060")
    cert_value("pf-m2", M2, "0.99695")
    cert_value("pf-m2/A.1", M2, "0.9969500")
    cert_cmp("pf-m2-le1", M2, "<=", 1, "only M_2 <= 1 is used")
    cert_value("x-lambda/A.1", LAM, "1.5849625")
    cert_value("x-lambda/notation", LAM, "1.58496")
    cert_value("x-a/notation", A, "0.58496")
    cert_value("x-rho/A.1", RHO, "0.6309298")
    cert_value("x-rho/notation", RHO, "0.63093")
    cert_value("x-f/notation", F, "0.96591")


def group2_thmA() -> None:
    print("[2] Theorem A and Corollary A (manuscript 4, Appendix A.1, A.6)")
    slope = -log2(1 - 1 / (LAM - D("0.1")))
    cert_value("pf-slope", slope, "1.6145")
    cert_value("pf-slope/A.1", slope, "1.61448")
    cert_cmp("pf-slope-le-1.62", slope, "<=", D("1.62"), "loss side, rounded up to 1.62")
    cert_value("pf-pins", PINS, "1.148594")
    cert_true("pf-A-s1", 1 - D("0.81") * D("1.23") == D("0.0037"), "1 - 0.81 x 1.23 = 0.0037 (exact)")
    s2 = TSTAR * D("3.5")
    cert_value("pf-A-s2", s2, "1.70827")
    cert_cmp("pf-A-s2-ge", s2, ">=", D("1.708"), "gain side, rounded down")
    cert_true("x-A-s3-base", D("1.23") - D("3.5e-3") == D("1.2265"), "1.23 - 3.5e-3 = 1.2265 (exact)")
    s3 = PINS * (D("1.23") - D("3.5e-3")) ** 2
    cert_value("pf-A-s3", s3, "1.72783")
    cert_cmp("pf-A-s3-ge", s3, ">=", D("1.727"), "gain side, rounded down")
    dom = D("0.0037") / D("1.70")
    cert_value("pf-A-s1-dom/pf", dom, "0.0021765")
    cert_value("pf-A-s1-dom", dom, "0.00218", "nearest", "manuscript 4: 0.0037/1.70 = 0.00218")
    cert_cmp("pf-A-s1-dom-1e-3", D("1e-3"), "<=", dom, "0.0037 delta >= 1.70 delta^2 for delta <= 1e-3")
    cert_cmp("pf-A-s1-dom-0.00217", D("0.00217"), "<=", dom, "A.1: (delta <= 0.00217)")
    cert_cmp("pf-A-min", min(D("1.708"), D("1.727")), ">=", D("1.70"))
    cert_true("x-l33-sum", D("1.94") + D("0.00123") == D("1.94123"), "s + h_p <= 1.94 q + 0.00123 q = 1.94123 q")
    cert_cmp("pf-l33", (2 - D("1.94123")) * 67, ">", LAM * 2, "Lemma 3.3 (iii): 1.94123 q < 2q - 2 lambda for q >= 67")
    cert_cmp("x-Lp10", 1 / (LAM * 10), ">", D("0.0630"), "L_p/10 >= q/(10 lambda) - 0.1 > 0.0630 q - 0.1")
    cert_cmp("x-Hprime", log2(1 / A), "<", D("0.78"), "|H'(rho_c)| = log2(1/a) < 0.78 (|H'| increasing on [1/2,1])")
    opt = PINS / D("0.81") ** 2
    cert_value("pf-A-opt", opt, "1.7506")
    cert_value("x-A-opt-97pct", D("1.70") / opt * 100, "97", "nearest", "1.70 is 97% of 1.7506")
    sl = -log2(1 - 1 / (LAM - D("0.002")))
    cert_value("pf-slope-narrow", sl, "1.4412")
    optn = PINS / (sl / 2) ** 2
    cert_value("pf-A-opt-narrow", optn, "2.21", "nearest", "manuscript: about 2.21; proof_pf.py: 2.2119 +- 5e-4")
    cert_tol("pf-A-opt-narrow/pf", optn, "2.2119", "5e-4", "correctly rounded: 2.2121")
    cert_value("x-A-opt-77pct", D("1.70") / optn * 100, "77", "nearest", "1.70 is 77% of it")
    cert_value("x-A-opt-1.26", optn / opt, "1.26", "nearest", "a further factor of about 1.26")
    cert_value("x-A6-1.78", (D("0.4") / D("0.3")) ** 2, "1.78", "nearest", "(0.4/0.3)^2 = 1.78")


def group3_bugeaud() -> None:
    print("[3] Proposition 13.2 / Bugeaud (2002) Theorem 2, m = 8, mu = 4, c_2(4) = 53.6 (manuscript 13, A.3)")
    cert_value("pf-bug-const/val", BUG_CONST, "8.6000145")
    cert_cmp("pf-bug-const", BUG_CONST, "<=", D("8.60002"), "loss side, rounded up")
    bits = LN9 * LN2 * D("8.60002")
    cert_value("pf-bug-bits/val", bits, "13.0978306")
    cert_cmp("pf-bug-bits", bits, "<=", D("13.09784"), "loss side, rounded up")
    cert_value("pf-bug-floor", Y_FLOOR, "8.31777")
    cert_cmp("pf-bug-floor-le", Y_FLOOR, "<=", D("8.31777"), "8.31777 enters squared on the loss side")
    x0, b0 = D("9e-4") + D("1e-8"), D("1.94") + D("1e-8")
    Z = bug_Z(x0, b0)
    cert_value("pf-bug-Zval", Z, "8.2612", "nearest", "Z at s/q = 1.94 + 1e-8, c_D + 1e-8 = 9.0001e-4")
    cert_cmp("pf-bug-Zval-floor", Z, "<", Y_FLOOR, "the floor 4 ln 8 is active")
    coef = D("13.09784") * imax(Z, D("8.31777")) ** 2 * x0
    cert_value("pf-bug-coef", coef, "0.81557")
    cert_cmp("pf-bug-coef-lt", coef, "<", D("0.82"))
    cert_cmp("pf-bug-coef-exact-le", bug_coef(x0, b0), "<=", coef, "unrounded constants give a smaller value")
    zthr = exp(2 - ln(LN8) - D("0.64"))
    cert_value("pf-bug-Zthr", zthr, "1.8737")
    cert_cmp("x-bug-Zthr-1.9", zthr, "<", D("1.9"), "b_1/(x + ln 3) >= 1.9 gives Z >= 2")
    cert_cmp("x-Phi-mono", Z, ">=", 2,
             "Phi nondecreasing on x <= 9.0001e-4: needs Z >= 2 there; Z is decreasing in x, so Z(9.0001e-4) >= 2 suffices")
    # paper, comment after Prop. 13.2: with s/q = 1.94 the floor is active for c_D >= 8.51e-4 (Z decreasing in x)
    z851 = bug_Z(D("8.51e-4"), b0)
    cert_cmp("x-floor-8.51e-4", z851, "<=", Y_FLOOR, "Z(c_D = 8.51e-4, s/q = 1.94 + 1e-8) <= 4 ln 8; Z decreasing in c_D")
    lo, hi = crossing_frac(lambda x: Y_FLOOR - bug_Z(x, b0), D("8e-4"), D("9e-4"), Fraction(1, 10 ** 9))
    certify("x-floor-crossing", True, (lo, hi), "c_D where Z = 4 ln 8 (s/q = 1.94 + 1e-8)", "information")
    # (H2) fails -> v_2(3^L b0 - a0) = 1 ; exact integer check as in proof_pf.py
    viol = 0
    for L in range(1, 40):
        e = L % 2
        for b0_ in range(1, 60, 2):
            for a0 in range(-59, 60, 2):
                if (a0 - 3 ** e * b0_) % 4 != 0:
                    x = 3 ** L * b0_ - a0
                    viol += (x & -x).bit_length() - 1 != 1
    cert_true("pf-h2-viol", viol == 0, "v_2 = 1 when (H2) fails: L < 40, b0 < 60, |a0| < 60 (exact integers)")
    viol = 0
    for m in range(0, 4001):
        a1 = 3 ** m - 1
        if m >= 1:
            v = (a1 & -a1).bit_length() - 1
            want = (((m & -m).bit_length() - 1) + 2) if m % 2 == 0 else 1
            viol += v != want
        b1 = 3 ** m + 1
        viol += (b1 & -b1).bit_length() - 1 > 2
    cert_true("pf-lte-viol", viol == 0, "lifting-the-exponent forms for m <= 4000 (exact integers)")
    # best pair (m = 2^u, mu): the upper limit of c_D with coefficient < 0.9 (proof_pf.gen_coef)
    C2 = {4: D("53.6"), 6: D("35.5"), 8: D("27.4"), 10: D("22.9"), 15: D("18.0")}

    def gen_coef(x, u: int, mu: int) -> Iv:
        e = 1 if u == 2 else 2 ** (u - 2)
        logA1 = imax(LN2 * 2, LN3) if u == 2 else imax(LN3 * e, LN2 * u)
        Y = imax(ln(D("1.94") / (LAM * LN2 * Iv.of(x)) / e + 1 / logA1) + ln(LN2 * u) + D("0.64"), LN2 * (mu * u))
        return u * C2[mu] / (LN2 * u) ** 4 * logA1 * LN2 * Y * Y * Iv.of(x)

    brackets = {}
    for u in (2, 3, 4, 5):
        for mu in C2:
            brackets[(u, mu)] = crossing_frac(lambda x: gen_coef(x, u, mu) - D("0.9"), D("1e-7"), D("0.5"),
                                              Fraction(1, 10 ** 7))
    best = brackets[(3, 4)]
    others = max(b[1] for k, b in brackets.items() if k != (3, 4))
    runner = max((b[1], k) for k, b in brackets.items() if k != (3, 4))[1]
    certify("pf-bug-best", others < best[0], (others, best[0]),
            "(m, mu) = (8, 4) has the largest limit (runner-up limit < limit of (8,4))",
            f"runner-up m = {2 ** runner[0]}, mu = {runner[1]}; x*Y^2 nondecreasing since mu*u*ln2 >= 2")
    cert_value("pf-bug-best-cD", Iv.hull(best[0], best[1]), "9.93e-4")


def group4_rules() -> dict:
    print("[4] Section 14.1 rules and Lemma 14.0 (manuscript 14.1, A.2; paper Section 14.1, Appendix A.2)")
    cert_true("pf-cD-flat", 1 + 2 * D("9e-4") == D("1.0018"), "c_D = 9e-4 iff beta >= 1 + 2*9e-4 = 1.0018 (exact)")
    cD = D("9e-4")
    target = cD * D("0.025")
    cert_true("x-target", target == D("2.25e-5"), "0.025 c_D = 2.25e-5 (exact)")
    cert_cmp("x-rc-lt-1", RC, "<", 1, "r_c < 1, so log2(1 + r_c^p) is decreasing in p")
    cert_cmp("pf-p311-fails", T(311), ">", target, "log2(1 + r_c^311) > 2.25e-5")
    cert_cmp("pf-p", T(312), "<=", target, "log2(1 + r_c^312) <= 2.25e-5, hence p = 312 (p = 80..311 fail by monotonicity)")
    allfail = all(T(p).gt(target) for p in range(80, 312))
    cert_true("x-p-80-311", allfail, "log2(1 + r_c^p) > 2.25e-5 for every p = 80..311 (direct interval evaluation)")
    cert_value("pf-phi", PHI(312), "0.9966737")
    cert_value("pf-logth-phi", LT(312), "0.00223635", "down", "A.2 item 3: gain side, rounded down")
    l1 = T(312) / 312
    cert_value("pf-l1rp-p", l1, "7.1191e-8", "up", "A.2 item 4: loss side, rounded up")
    b_disp = D("4.5e-4") * D("0.00223635") - D("7.1191e-8")
    cert_value("x-A2-4-B-display", b_disp, "9.3517e-7", "nearest", "A.2 item 4: 4.5e-4 x 0.00223635 - 7.1191e-8 (exact)")
    d6, cD6, p6, B6, which6 = constants(Fraction(3, 2))
    certify("x-constants-0.6", p6 == 312 and which6 == "0.3B", d6, "alpha = 0.6: c_D = 9e-4, p = 312, delta = 0.3B")
    cert_value("pf-B", B6, "9.3517e-7")
    cert_cmp("pf-B-ge", B6, ">=", D("9.351e-7"))
    cert_cmp("x-A2-4-B-lower", b_disp, "<=", B6, "the displayed computation (gain down, loss up) is a lower bound for B")
    cert_value("pf-delta", d6, "2.8055e-7")
    cert_cmp("pf-delta-ge", d6, ">=", D("2.805e-7"))
    k6 = B6 - TSTAR * d6 * d6 * D("3.5") - d6 * D("2.5")
    cert_value("pf-keff", k6, "2.3379e-7")
    cert_cmp("x-keff-pos", k6, ">", 0)
    bstar = 1 + B6 * 3000                          # 1e-4 (beta - 1) = 0.3 B
    cert_value("pf-beta1", bstar, "1.002806", "nearest", "beta* = 1 + 0.3B/1e-4 (proof_pf.py writes 1.0028056 +- 5e-7)")
    cert_tol("pf-beta1/pf", bstar, "1.0028056", "5e-7", "correctly rounded: 1.0028055")
    cert_cmp("pf-beta1-safe", bstar, "<=", D("1.002806"), "for beta >= 1.002806 the term 0.3B is active")
    alpha_star = bstar / (1 + bstar)
    cert_cmp("x-alpha-0.500701", Fraction("0.500701") / (1 - Fraction("0.500701")), ">=", bstar,
             "alpha >= 0.500701 gives beta >= beta*: the constants do not depend on alpha (14.1, A.2 items 5 and heading)")
    cert_value("x-alpha-star", alpha_star, "0.5007", "nearest", "alpha* = beta*/(1 + beta*)")
    # Lemma 14.0 (a): 1 - phi_p >= 1/p for p >= 80 (analytic proof); certified constants
    l15 = LN2 * D("1.5")
    l125 = LN2 * LN2 * D("1.25")
    cert_value("pf-phi-x2", l15, "1.0397")
    cert_cmp("pf-phi-x2-dir", l15, ">=", D("1.0397"), "used as 1 - 1.5 ln2 x <= 1 - 1.0397 x")
    cert_value("pf-phi-x2b", l125, "0.6006")
    cert_cmp("pf-phi-x2b-dir", l125, "<=", D("0.6006"), "used as (5/4) ln2^2 x^2 <= 0.6006 x^2")
    xmax = (l15 - 1) / (l125 + 1)
    cert_tol("pf-phi-xmax", xmax, "0.02484", "5e-5", "correctly rounded: 0.02482")
    cert_value("pf-phi-xmax/ms", xmax, "0.0248", "down", "manuscript/paper: x <= 0.0248")
    cert_cmp("pf-phi-xmax/ms-ineq", D("0.0248"), "<=", D("0.0397") / D("1.6006"),
             "1 - 1.0397x + 0.6006x^2 <= 1 - x - x^2 for 0 <= x <= 0.0248 (exact)")
    cert_cmp("x-1/79", Fraction(1, 79), "<=", D("0.0248"), "x = 1/(p-1) <= 1/79 <= 0.0248")
    rs = RHO_SHARP * (1 - RHO_SHARP)
    rsl = rs * 2 / LN2
    cert_tol("pf-rs", rsl, "0.67180", "5e-5", "correctly rounded: 0.67181")
    cert_cmp("pf-rs-ge", rsl, ">=", D("0.6718"), "manuscript/paper: log2(1/Theta) >= 0.6718/p")
    cert_value("pf-B-lb", rsl / 2 - D("0.025"), "0.3109")
    cert_cmp("pf-B-lb/ms", D("0.6718") / 2 - D("0.025"), ">=", D("0.3108"), "B >= (c_D/p)(0.6718/2 - 0.025) >= 0.3108 c_D/p")
    cert_cmp("x-B-lb-0.6", B6, ">=", D("0.3108") * cD / 312, "Lemma 14.0 (a) at alpha = 0.6")
    # Lemma 14.0 (c)
    cert_value("pf-15ln2", l15, "1.039721")
    cert_cmp("pf-15ln2-le", l15, "<=", D("1.03973"))
    gap = D("1.03973") / 79
    cert_cmp("pf-phi-lb", gap, "<=", D("0.0131612"), "phi_p >= 1 - 1.03973/79 >= 1 - 0.0131612 (exact)")
    cert_cmp("x-phi-gap-0.01317", D("0.0131612"), "<=", D("0.01317"), "1 - phi_p <= 0.01317")
    u_disp = rs * D("0.0131612") * 2
    cert_cmp("pf-u-le", u_disp, "<=", D("0.0061287"), "u <= 2 x 0.0131612 rho#(1-rho#) <= 0.0061287")
    ltub = D("0.0061287") / ((1 - D("0.0061287")) * LN2)   # u/((1-u) ln 2) is increasing in u
    cert_cmp("pf-logth-ub", ltub, "<=", D("0.0088964"), "u <= 0.0061287 gives u/((1-u) ln 2) <= 0.0088964")
    cert_cmp("pf-logth-ub-le", ltub, "<=", D("0.00890"), "u <= 0.0061287 gives u/((1-u) ln 2) <= 0.00890")
    dmax = D("0.3") * D("9e-4") / 2 * D("0.00890")
    cert_true("pf-delta-max", dmax == D("1.2015e-6"), "0.3 (9e-4/2) 0.00890 = 1.2015e-6 (exact)")
    cert_cmp("x-delta-max-1.21", dmax, "<=", D("1.21e-6"))
    cert_cmp("x-3.5delta2", D("3.5") * D("1.21e-6") ** 2, "<=", D("1e-8"), "3.5 delta^2 <= 1e-8")
    # Lemma 14.0 (b)
    cert_cmp("x-b-1.71", TSTAR * D("3.5"), "<=", D("1.71"), "3.5 t* <= 1.71")
    cert_cmp("x-b-2.1e-6", D("1.71") * D("1.21e-6"), "<=", D("2.1e-6"), "then 3.5 t* delta^2 <= 0.3 * 2.1e-6 B << 0.25 B")
    # Lemma 14.0 (d), (e), (f), (g)
    cert_value("pf-logth-half", LTH, "0.38238")
    cert_cmp("pf-first-margin", LTH, ">", D("7.5") * D("0.00890"), "Lemma 14.0 (d)")
    cert_cmp("x-e-0.19", LTH / 2, ">=", D("0.19"), "Lemma 14.0 (e): 2.5e-4 (beta-1) < 0.19 (beta-1) <= (1/2) log2(1/Theta#_1/2) (beta-1)")
    epl = D("1.23e-4") / LAM
    cert_value("pf-epsrho-lim", epl, "7.7604e-5")
    cert_cmp("x-f-7.77e-5", epl, "<=", D("7.77e-5"), "Lemma 14.0 (f)")
    cert_cmp("x-g-0.025392", SHALLOW, ">=", D("0.025392"), "Lemma 14.0 (g): log2(2/(1+r_c)) >= 0.025392 (gain side)")
    cert_true("pf-shallow-80", 40 * D("0.025392") == D("1.01568"), "40 x 0.025392 = 1.01568 (exact)")
    cert_cmp("x-shallow-80-gt1", D("1.01568"), ">", 1, "Lemma 14.0 (g): (p/2) log2(2/(1+r_c)) >= 1.01568 > 1 for p >= 80")
    cert_value("pf-shallow-val", SHALLOW * 156, "3.9613")
    cert_value("pf-first-val", LTH * D("4.5e-4"), "1.7207e-4")
    cert_cmp("x-A2-7", d6 * 25, "<=", D("7.02e-6"), "A.2 item 7: 10 delta' = 25 delta <= 7.02e-6")
    epsr6 = d6 * D("1.23") / (LAM * D("0.5"))
    cert_value("x-A2-9", epsr6, "4.35e-7", "nearest", "A.2 item 9: eps_rho at alpha = 0.6")
    cert_cmp("x-A2-9-le", epsr6, "<=", D("1e-4"), "only eps_rho <= 1e-4 is used")
    return {"d6": d6, "B6": B6, "k6": k6, "bstar": bstar, "alpha_star": alpha_star}


def group4_grids() -> None:
    print("[4b] Direct checks over p (manuscript 14.0 (a)(c): double checks of the analytic bounds)")
    ps = list(range(80, 20001))
    big = [10 ** k for k in range(5, 10)]
    bad_ineq = [p for p in ps if not (1 - PHI(p)).ge(Fraction(1, p))]
    cert_true("pf-phi-ineq", not bad_ineq, "1 - phi_p >= 1/p for every p = 80..20000 (interval evaluation)",
              f"violations/undecided: {bad_ineq[:5]}" if bad_ineq else "the analytic proof covers all p >= 80")
    bad_lb = [p for p in ps + big if not (1 - PHI(p)).le(D("1.03973") / (p - 1))]
    cert_true("pf-phi-lb-check", not bad_lb, "1 - phi_p <= 1.03973/(p-1) for p = 80..20000 and p = 10^5..10^9",
              f"violations/undecided: {bad_lb[:5]}" if bad_lb else "")
    bad_gap = [p for p in ps if not (1 - PHI(p)).le(D("0.0131612"))]
    cert_true("x-phi-gap-grid", not bad_gap, "1 - phi_p <= 0.0131612 for p = 80..20000 (direct evaluation)",
              f"max at p = 80: 1 - phi_80 in {(1 - PHI(80)).fmt(8)}" if not bad_gap else f"violations: {bad_gap[:5]}")
    bad_lt = [p for p in ps if not LT(p).le(D("0.00890"))]
    cert_true("pf-logth-ub-check", not bad_lt, "log2(1/Theta#_{phi_p}) <= 0.00890 for p = 80..20000",
              f"violations/undecided: {bad_lt[:5]}" if bad_lt else "")


def conditions_box(bm1: Iv, cD: Iv, p: int) -> dict[str, bool]:
    """The conditions of proof_pf.conditions(beta), certified for every beta - 1 in bm1 and c_D in cD."""
    beta = bm1 + 1
    B = budget(cD, p)
    d = imin(B * D("0.3"), bm1 * D("1e-4"))
    return {
        "bugeaud": bug_coef(cD + d * d * D("3.5") + D("1e-9"), beta).lt(D("0.9")),
        "window": cD.lt(bm1),
        "keff": (B - TSTAR * d * d * D("3.5") - d * D("2.5")).gt(0),
        "first": (cD / 2 * LTH).gt(d * 25),
        "outer": (d * D("2.5")).lt(bm1 * LTH / 2),
        "epsrho": (d * D("1.23") / (LAM * bm1)).lt(D("1e-4")),
        "shallow": (SHALLOW * p / 2).gt(1),
        "thmA": d.le(D("1e-3")),
        "hL": (d * d * D("3.5")).le(D("1e-8")),
        "delta>0": d.gt(0),
    }


def group4_cover() -> None:
    print("[4c] Lemma 14.0 and the coefficient condition of Prop. 13.2 on a covering of beta in [1 + 1e-14, 1.94]")
    edges = [D("1e-14")]
    top = D("0.94")
    while edges[-1] < top:
        nx = edges[-1] * Fraction(101, 100)
        nx = Fraction(math.ceil(nx * 2 ** 80), 2 ** 80)
        edges.append(min(nx, top))
    fails, pmax_all, pairs = [], 0, 0
    for i in range(len(edges) - 1):
        bm1 = Iv.hull(edges[i], edges[i + 1])
        cD = imin(D("9e-4"), bm1 / 2)
        pmin, pmax = p_candidates(cD)
        pmax_all = max(pmax_all, pmax)
        for p in range(pmin, pmax + 1):
            pairs += 1
            for k, ok in conditions_box(bm1, cD, p).items():
                if not ok:
                    fails.append((i, p, k))
    cert_true("pf-range-viol", not fails,
              f"all 9 conditions and delta > 0 hold for every beta - 1 in [1e-14, 0.94] ({len(edges) - 1} boxes,"
              f" {pairs} (box, p) pairs)",
              f"failures: {fails[:5]}" if fails else
              f"contains the 20,004 grid points of proof_pf.py (smallest beta - 1 = 1.2e-13); p ranges up to {pmax_all};"
              " beta - 1 < 1e-14 only by the analytic Lemma 14.0")


def group4_A4() -> None:
    print("[4d] Which term of delta is active near alpha = 1/2 (manuscript A.4; paper A.4 and 14.3)")
    a = D("0.5001")
    d, cD, p, B, which = constants(a / (1 - a))
    certify("x-active-0.5001", which == "1e-4(beta-1)", d, "alpha = 0.5001: delta = 1e-4(beta-1) is active",
            f"c_D = (beta-1)/2, p = {p}")
    a = D("0.5007")
    d, cD, p, B, which = constants(a / (1 - a))
    certify("x-active-0.5007", which == "1e-4(beta-1)", d, "alpha = 0.5007: delta = 1e-4(beta-1) is active")
    bm1 = D("3e-6")
    d, cD, p, B, which = constants(1 + bm1)
    certify("x-active-exception-3e-6", which == "0.3B", B * D("0.3"),
            "A.4: at beta - 1 = 3e-6 the term 0.3B is smaller than 1e-4(beta-1) = 3e-10", f"p = {p}")
    # the linear term is active on beta - 1 in [5e-6, beta* - 1): boxes on [5e-6, 0.0018]; on [0.0018, beta* - 1)
    # c_D = 9e-4, p = 312 and B are constant, so 1e-4 (beta - 1) < 1e-4 (beta* - 1) = 0.3B there
    edges = [D("5e-6")]
    while edges[-1] < D("0.0018"):
        nx = Fraction(math.ceil(edges[-1] * Fraction(1001, 1000) * 2 ** 80), 2 ** 80)
        edges.append(min(nx, D("0.0018")))
    bad = 0
    for i in range(len(edges) - 1):
        bm1 = Iv.hull(edges[i], edges[i + 1])
        cD = imin(D("9e-4"), bm1 / 2)
        pmin, pmax = p_candidates(cD)
        bad += sum(1 for p in range(pmin, pmax + 1) if not (bm1 * D("1e-4")).lt(budget(cD, p) * D("0.3")))
    cert_true("x-active-range", bad == 0,
              f"delta = 1e-4(beta-1) is active for every beta - 1 in [5e-6, beta* - 1) ({len(edges) - 1} boxes)",
              "so the exceptions lie in alpha - 1/2 < 1.25e-6 ('narrow ranges very close to 1/2')")


def group4_thresholds(d6: Iv, k6: Iv) -> None:
    print("[4e] Thresholds for 'K sufficiently large' at alpha = 0.6 (manuscript 14.4, A.5)")
    print("     Each threshold function f(q) = (linear gain) q - log2(polynomial in q) has f'(q) = const - (sum of")
    print("     positive terms decreasing in q), so f' is nondecreasing; f(Q) >= 0 and f'(Q) >= 0 give f(q) >= 0")
    print("     for all q >= Q.  (This monotonicity is not stated in the manuscript, which only reports bisection.)")
    two11 = pw2(D("1.1"))
    k151 = D("1.51")

    def fB(q) -> Iv:                               # Theorem B: (delta' - 2 delta) q - log2(Gamma_L (2L+1) q (q+1) 2^1.1)
        L = k151 * q / LAM + 1
        return (d6 * D("2.5") - d6 * 2) * q - log2((3 + L * LN3) * (L * 2 + 1) * q * (q + 1) * two11)

    def dfB(q) -> Iv:
        L = k151 * q / LAM + 1
        s = (k151 * LN3 / LAM) / (3 + L * LN3) + (k151 * 2 / LAM) / (L * 2 + 1) + Fraction(1, q) + Fraction(1, q + 1)
        return d6 / 2 - s / LN2

    c312 = pw(Iv.of(25), Fraction(1, 312)) * 8 * two11
    lt312 = LT(312)

    def g0(q) -> Iv:                               # Prop. 14.1, step 4, third term
        poly = c312 * (q + 2) ** 2 * q * (q + 1) * q ** 2
        return k6 * q - log2(poly) - lt312 * D("1.5") - 3

    def dg0(q) -> Iv:
        return k6 - (Fraction(2, q + 2) + Fraction(3, q) + Fraction(1, q + 1)) / LN2

    def hA(q) -> Iv:                               # reference value: 1.70 delta^2 q >= log2(2 s), s <= 1.51 q
        return d6 * d6 * D("1.70") * q - log2(k151 * 2 * q)

    def dhA(q) -> Iv:
        return d6 * d6 * D("1.70") - 1 / (LN2 * q)

    brackets = {}
    for name, f, df, stated, lo, hi in (("pf-q0", g0, dg0, "7.89e8", 10 ** 8, 10 ** 10),
                                        ("pf-qB", fB, dfB, "8.62e8", 10 ** 8, 10 ** 10),
                                        ("pf-qA", hA, dhA, "3.74e14", 10 ** 13, 10 ** 16)):
        a, b = crossing(f, lo, hi)
        brackets[name] = (a, b)
        cert_value(name, Iv.hull(a, b), stated, "up", "the stated threshold is the crossing rounded up")
        Q = int(Fraction(stated))
        fq, dq = f(Q), df(Q)
        certify(name + "-safe", fq.ge(0) and dq.ge(0), fq,
                f"condition holds for all q >= {stated}: f({stated}) >= 0 and f'({stated}) >= 0",
                f"crossing in [{a}, {b}]")
    qB, q0 = brackets["pf-qB"], brackets["pf-q0"]
    cert_value("x-qB-crossing", Iv.hull(*qB), "8.6133e8", "down", "A.5: the crossing point is 8.6133e8 (in [8.6133e8, 8.6134e8))")
    cert_value("x-qB-crossing-nearest", Iv.hull(*qB), "8.6133e8", "nearest")
    cert_value("x-qA-3.7e14", Iv.hull(*brackets["pf-qA"]), "3.7e14", "nearest", "14.4: from q ~ 3.7e14 on")
    certify("pf-qB-dominates", q0[1] < qB[0], (q0[1], qB[0]), "q_0 < q_B (upper end of q_0 bracket < lower end of q_B bracket)")
    QB = 862 * 10 ** 6
    cert_value("x-K-2.2e9", Iv.hull(Fraction(5, 2) * qB[0], Fraction(5, 2) * QB), "2.2e9", "nearest",
               "K = s + q, q/K -> 0.4: K ~ 2.5 q (q from the crossing to the stated q_B)")
    cert_value("x-gain-bits-at-qB", d6 * d6 * D("1.70") * QB, "1.2e-4", "nearest", "1.70 delta^2 q bits at q = q_B = 8.62e8")


TABLE = (("0.5001", "1.360e-15", "1.36e-15"), ("0.501", "6.677e-14", "6.67e-14"), ("0.51", "6.556e-14", "6.55e-14"),
         ("0.55", "6.021e-14", "6.02e-14"), ("0.6", "5.352e-14", "5.35e-14"), ("0.65", "4.683e-14", "4.68e-14"),
         ("0.659", "4.563e-14", "4.56e-14"))


def group5_eps(B6: Iv, bstar: Iv, alpha_star: Iv) -> None:
    print("[5] The gain epsilon(alpha) and the divergent-orbit corollary (manuscript 14.3, 14.5, A.4)")
    eps = {}
    for a, v4, v3 in TABLE:
        al = D(a)
        e, which = eps_of(al)
        eps[a] = e
        _, cD, p, _, dwhich = constants(al / (1 - al))
        certify(f"x-eps-min-{a}", which == "1.70 delta^2 (1-alpha)", e,
                "min in epsilon(alpha) is the first term", f"delta = {dwhich}, p = {p}")
        cert_value(f"pf-eps-{a}", e, v4, "nearest", "proof_pf.py value")
        cert_value(f"x-eps-table-{a}", e, v3, "down", "manuscript/paper table (rounded down)")
    e6 = eps["0.6"]
    cert_value("pf-eps-06", e6, "5.3522e-14", "nearest", "Section 14.3 text")
    cert_cmp("pf-gain-ge", e6, ">=", D("5.35e-14"), "epsilon(0.6) >= 5.35e-14 (main theorem)")
    other6 = (1 - C) * D("0.2") / 2
    cert_value("x-other-term-0.6", other6, "0.095", "nearest", "(1/2)(1-c) 0.2")
    cert_value("x-other-term-0.6/A.4", other6, "0.0950", "nearest")
    cert_value("pf-gain-v1-ratio", e6 / D("1.0672e-18"), "5.0e4", "nearest",
               "manuscript: about 5.0e4 times v1; the v1 value 1.0672e-18 is an input, not recomputed")
    cert_tol("pf-gain-v1-ratio/pf", e6 / D("1.0672e-18"), "5.015e4", "10")
    r = eps["0.501"] / D("0.501")
    cert_value("pf-div", r, "1.3327e-13")
    cert_cmp("pf-div-ge", r, ">=", D("1.33e-13"), "Corollary 14.5: exponent 1 - c - 1.33e-13")
    # sup_alpha epsilon(alpha)/alpha in closed form (see the argument printed below)
    sup = (B6 * D("0.3")) ** 2 * D("1.70") / bstar
    print("     sup_alpha eps(alpha)/alpha: (i) alpha >= alpha*: beta >= beta* >= 1.0018, so c_D = 9e-4, p = 312, delta = 0.3B,")
    print("     and eps/alpha <= 1.70 (0.3B)^2 (1-alpha)/alpha, decreasing; (ii) alpha <= alpha*: delta <= 1e-4 (beta-1), so")
    print("     eps/alpha <= 1.70e-8 (beta-1)^2/beta, increasing in beta.  Both bounds equal 1.70 (0.3B)^2/beta* at alpha*,")
    print("     where the bound is attained (delta = 0.3B = 1e-4(beta*-1) and the min is the first term).")
    cert_cmp("x-sup-premise-1", bstar, ">=", D("1.0018"), "beta* >= 1.0018")
    e_star1 = (B6 * D("0.3")) ** 2 * D("1.70") * (1 - alpha_star)
    e_star2 = (1 - C) * (alpha_star * 2 - 1) / 2
    cert_cmp("x-sup-premise-2", e_star1, "<", e_star2, "at alpha* the min is 1.70 delta^2 (1 - alpha)")
    cert_value("pf-div-sup", sup, "1.3343e-13", "nearest", "max over alpha, attained at alpha* = beta*/(1+beta*)")
    cert_value("x-div-sup-alpha", alpha_star, "0.5007", "nearest", "alpha ~ 0.5007")
    cert_value("x-alpha(1-c)-0.6", (1 - C) * D("0.6"), "0.570", "nearest", "introduction, remark on the size (1)")
    cert_cmp("x-alpha(1-c)>0.47", (1 - C) / 2, ">", D("0.47"), "alpha (1-c) > 0.47 for alpha > 1/2 (proof of Thm 14.4)")
    cert_cmp("x-eps-le-0.1", D("1.70") * D("1.21e-6") ** 2 / 2, "<=", D("0.1"), "epsilon(alpha) <= 0.1")


def group6_misc() -> None:
    print("[6] Other numerical steps quoted in the paper (Sections 7, 9, 14.5)")
    cert_cmp("x-l25-1.1", log2((RHO + D("0.05")) / (1 - RHO - D("0.05"))), "<=", D("1.1"),
             "Lemma 2.5 (ii): |H'| <= 1.1 on (rho_c, rho_c + 0.05], hence |E_L| >= 2^((1-c)q - 1.1)/(q(q+1))")
    cert_cmp("x-l75-1.71e-6", TSTAR * D("3.5e-6"), "<=", D("1.71e-6"), "Lemma 7.5: t* h_L <= 1.71e-6 q")
    cert_cmp("x-l75-q23", (C - D("1.71e-6")) * 23, ">=", 1, "Lemma 7.5: 1.71e-6 q <= c q - 1 for q >= 23")
    th = theta(D("0.5"), RHO)
    cert_value("x-s9-0.767", th, "0.767", "nearest", "Theta_1/2(rho_c)")
    cert_value("x-s9-0.19", -log2(th) / 2, "0.19", "nearest", "delta'_H ~ 0.19 (s/q - 1)")
    cert_value("x-s9-0.096", -log2(th) / 4, "0.096", "nearest", "s/q = 1.5")
    cert_cmp("x-lmn-0.911", 1 / LN3, "<=", D("0.911"), "Lemma 14.3: k/ln 3 <= 0.911 k")
    cert_cmp("x-lmn-0.631", LN2 / LN3, "<=", D("0.631"), "o < k log_3 2 <= 0.631 k")
    cert_cmp("x-lmn-sum", D("0.911") + D("0.631"), "<=", 2, "b' <= 2k")
    cert_value("x-lmn-33.95", LN3 * D("30.9"), "33.95")
    cert_cmp("x-lmn-34", LN3 * D("30.9"), "<", 34)
    cert_cmp("x-lmn-27", LN3 * D("24.34"), "<", 27, "Corollaire 2 variant")
    cert_cmp("x-lmn-Gamma", LN2, "<=", 1, "Gamma <= ln 2 <= 1")


def main() -> int:
    t0 = time.time()
    print(f"Certified recomputation of the M1 constants (interval arithmetic, {PREC}-bit dyadic endpoints)")
    fails = selftest()
    if fails:
        print("SELF-TEST FAILED:", fails[:10])
        return 1
    print(f"  self-test of the interval library: passed ({time.time() - t0:.1f} s)")
    print("  ln 2   =", LN2.fmt(36))
    print("  ln 3   =", LN3.fmt(36))
    print("  log2 3 =", LAM.fmt(36))
    group1_basic()
    group2_thmA()
    group3_bugeaud()
    info = group4_rules()
    group4_grids()
    group4_cover()
    group4_A4()
    group4_thresholds(info["d6"], info["k6"])
    group5_eps(info["B6"], info["bstar"], info["alpha_star"])
    group6_misc()
    n_fail = sum(1 for _, ok in RESULTS if not ok)
    n_pass = len(RESULTS) - n_fail
    if n_fail:
        print("\nFAIL:", ", ".join(n for n, ok in RESULTS if not ok))
    verdict = "all PASS" if not n_fail else f"{n_pass} PASS, {n_fail} FAIL"
    print(f"\nSUMMARY: {len(RESULTS)} numerical claims of the M1 proof checked with rigorous interval arithmetic"
          f" ({PREC}-bit dyadic endpoints, Python standard library): {verdict} ({time.time() - t0:.0f} s).")
    return 1 if n_fail else 0


if __name__ == "__main__":
    sys.exit(main())
