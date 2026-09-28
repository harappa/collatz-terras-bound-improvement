#!/usr/bin/env python3
"""Certified (interval-arithmetic) recomputation of the explicit constants of the M1 proof, version v3.

    python3 audit/proof_pf_certified_v3.py       # Python standard library only; about 15 s

It imports proof_pf_certified.py from its own directory, so both files must be shipped together.

This file certifies, with rigorous interval arithmetic, the numerical values and numerical
inequalities of the v3 constants of the M1 proof, as they appear in revision r7 of the English
paper papers/m1/m1.tex (Definition of R_delta, Lemma "Gtilde" (iii), Section "Theorem A",
the lemmas "rhobar" and "j0", Section "Theorem 1 of Bugeaud and a wider window", Section
"Assembly and constants", Section "Transfer to the stopping time" and Appendix A) and in the
Japanese proof manuscript v3 (manuscript/proof/v3-05-thmA.md, v3-13-thm1.md, v3-14-constants.md).

The v3 constants differ from those of revision r6 (certified by proof_pf_certified.py) in three
places: (A) the window width c_D may go up to 9e-3 (Theorem 1 of Bugeaud (2002) instead of
Theorem 2); (B) Theorem A has the coefficient 2.18 (R_delta: h_L <= 4.48 delta^2 q,
0 < h_p <= 1.38 delta q, delta <= 1e-4, slope bound 1.4412); (C) delta = min{0.45 B, 1e-4 (beta-1)}
and delta' = 19 delta / 9.

Arithmetic.  The interval library (256-bit dyadic endpoints, outward rounding; ln, exp and sqrt
from explicit series with explicit remainder bounds), the basic constants and the helpers that
do not depend on the rules (p_candidates, budget, certify, cert_value, cert_cmp, crossing, ...)
are imported from proof_pf_certified.py and are not duplicated here.  The functions that depend
on the rules (c_D, the constants, epsilon(alpha), the threshold functions, the covering of the
range of beta) are defined below for the v3 rules; proof_pf_certified.py is not modified and its
v2 functions are not patched.  Decimal constants of the text enter as exact rationals; binary
floating point is never used in a certified quantity.

Output.  One line per claim: identifier, certified enclosure, claim, status and a note, as in
proof_pf_certified.py.  Identifiers "v3-*" are new in v3; "pf-*" and "x-*" are the identifiers of
proof_pf_certified.py (claims unchanged since revision r6: some groups of that program are called
unchanged, and a few of its claims are repeated here because they are quoted in the v3 text).
A suffix names the place of the stated decimal ("/A.2": Appendix A.2, "/13.4": Section 13.4,
"/14.1": Section 14.1, and so on).  Equality claims are checked against the rounding interval of
the stated decimal: "down" for gains (larger is better), "up" for losses, "nearest" where the text
does not fix a direction or writes "about"; inequality claims directly.  The thresholds are
certified by f(Q) >= 0 and f'(Q) >= 0 at the stated value Q with f' nondecreasing (the argument is
printed).  The supremum of epsilon(alpha)/alpha is certified in closed form.  The remark that
condition (1) of Bugeaud's Theorem 1 holds from about q = 4.1e4 on is certified for all q: block
by block (exact log of prod k!) up to a point K_1, and by an explicit lower bound
M_inf K - A ln K - B beyond it (the derivation is printed).  The last line is a one-line summary;
the exit code is 1 if any claim fails.

This is a certificate for the arithmetic only.  It does not check the proofs in which the numbers
are used.
"""
from __future__ import annotations

import math
import os
import sys
import time
from fractions import Fraction

sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import proof_pf_certified as cf  # noqa: E402
from proof_pf_certified import (  # noqa: E402  (imported by name, so that Iv is a class to type checkers)
    Iv, D, ln, log2,
    imin, ifloor, Ambiguous,
    LN2, LN3, LN8, LN9, LAM,
    A as A_, RHO, C, TSTAR, RC, PINS,
    RHO_SHARP, LTH, SHALLOW,
    T, PHI, LT, budget, p_candidates,
    certify, cert_value, cert_cmp, cert_true,
)

# =====================================================================================
# 1. The v3 rules (paper Section 14.1; manuscript v3 Section 14.6.1)
# =====================================================================================

CD_MAX = D("9e-3")                 # upper limit of c_D (Proposition "HGT-B", Theorem 1 of Bugeaud)
DELTA_B = D("0.45")                # delta <= 0.45 B
DELTA_LIN = D("1e-4")              # delta <= 1e-4 (beta - 1)
DPR = Fraction(19, 9)              # delta' = 19 delta / 9
ETA_A = D("4.48")                  # h_L <= 4.48 delta^2 q
X_A = D("1.38")                    # h_p <= 1.38 delta q
COEF_A = D("2.18")                 # coefficient of Corollary A
SLOPE = D("1.4412")                # slope bound of step 1 of Theorem A (h_p <= L_p/500)
ONE8 = 1 - D("1e-8")               # 1 - 1e-8
CD8 = CD_MAX + D("1e-8")           # c_D + 1e-8 at c_D = 9e-3
BETA1 = (D("1.94") + D("1e-8")) / (LAM * 2)     # (1.94 + 1e-8)/(2 lambda)


def cD_v3(beta) -> Iv:
    """c_D = min{9e-3, (beta - 1)/2}."""
    return imin(CD_MAX, (Iv.of(beta) - 1) / 2)


def constants_v3(beta):
    """(delta, c_D, p, B, which) for an exact beta under the v3 rules; raises Ambiguous if a discrete
    choice is undetermined.  delta = min{0.45 B, 1e-4 (beta - 1)}."""
    beta = Iv.of(beta)
    cD = cD_v3(beta)
    pmin, pmax = p_candidates(cD)
    if pmin != pmax:
        raise Ambiguous(f"p not determined: candidates {pmin}..{pmax}")
    B = budget(cD, pmin)
    lin = (beta - 1) * DELTA_LIN
    b45 = B * DELTA_B
    if b45.lt(lin):
        which = "0.45B"
    elif lin.lt(b45):
        which = "1e-4(beta-1)"
    else:
        raise Ambiguous("min{0.45B, 1e-4(beta-1)} not determined")
    return imin(b45, lin), cD, pmin, B, which


def keff_v3(B: Iv, d: Iv) -> Iv:
    """kappa_eff = B - 4.48 t* delta^2 - 19 delta / 9."""
    return B - TSTAR * d * d * ETA_A - d * DPR


def eps_v3(alpha: Fraction):
    """epsilon(alpha) = min{2.18 delta^2 (1 - alpha), (1/2)(1 - c)(2 alpha - 1)}; returns (eps, which)."""
    d = constants_v3(alpha / (1 - alpha))[0]
    e1 = d * d * COEF_A * (1 - alpha)
    e2 = (1 - C) * (2 * alpha - 1) / 2
    if e1.lt(e2):
        return e1, "2.18 delta^2 (1-alpha)"
    if e2.lt(e1):
        return e2, "(1/2)(1-c)(2alpha-1)"
    raise Ambiguous("min in epsilon(alpha) not determined")


def minf_of(cD, Lb: int = 7, S2: int = 9) -> Iv:
    """The limit M_inf (paper Section 13.4) for Theorem 1 with L^B = Lb, R_1^B = Lb, S_1^B = 1, S_2^B = S2:
    (Lb - 1) ln 8 - Lb^2 ln 9/(3 S2) - Lb^2 S2 ln 2 (c_D + 1e-8)/(1 - 1e-8)
      - ln((Lb/S2 + 3 Lb (S2 - 1) beta_1/(1 - 1e-8))/2) - 3/2.
    For (Lb, S2) = (7, 9) this is the displayed formula with 49/27, 441 and 168."""
    return (LN8 * (Lb - 1) - LN9 * Fraction(Lb * Lb, 3 * S2) - LN2 * (Lb * Lb * S2) * (Iv.of(cD) + D("1e-8")) / ONE8
            - ln((Fraction(Lb, S2) + BETA1 * (3 * Lb * (S2 - 1)) / ONE8) / 2) - Fraction(3, 2))


def minf_zero(Lb: int, S2: int) -> Iv:
    """The c_D at which M_inf(Lb, S2) vanishes (M_inf is affine and decreasing in c_D)."""
    m0 = minf_of(0, Lb, S2) + LN2 * (Lb * Lb * S2) * D("1e-8") / ONE8        # the part without c_D
    return m0 * ONE8 / (LN2 * (Lb * Lb * S2)) - D("1e-8")


# =====================================================================================
# 2. The claims
# =====================================================================================

def group2_thmA() -> None:
    print("[2] Definition of R_delta, Lemma Gtilde (iii), Theorem A and Corollary A (v3), Lemmas rhobar and j0"
          " (paper Sections 1.5, 3.3, 4, 6.3, 7; Appendix A.1; manuscript v3 4.2)")
    cert_true("v3-Rdelta-hL/1.5", ETA_A * D("1e-4") ** 2 == D("4.48e-8"), "4.48 (1e-4)^2 = 4.48e-8 (exact)",
              "Definition R_delta: h_L <= 4.48e-8 q for delta <= 1e-4")
    cert_true("v3-Rdelta-hp/1.5", X_A * D("1e-4") == D("1.38e-4"), "1.38 x 1e-4 = 1.38e-4 (exact)",
              "Definition R_delta: h_p <= 1.38e-4 q for delta <= 1e-4")
    cert_true("v3-Gt-hp", X_A * D("1e-3") == D("0.00138") and D("1.94") + D("0.00138") == D("1.94138"),
              "1.38 delta q <= 0.00138 q (delta <= 1e-3) and 1.94 + 0.00138 = 1.94138 (exact)", "Lemma Gtilde (iii)")
    cert_cmp("v3-Gt-q67", (2 - D("1.94138")) * 67, ">", LAM * 2,
             "Lemma Gtilde (iii): 1.94138 q < 2q - 2 lambda at q = 67, hence for all q >= 67 (linear in q)")
    cert_cmp("v3-A-beta-range", D("0.659") / (1 - D("0.659")), "<=", D("1.933"),
             "Corollary A, Section 14.1: alpha/(1-alpha) <= 1.933 for alpha <= 0.659 (exact)")
    slope = -log2(1 - 1 / (LAM - D("0.002")))
    cert_value("v3-A-slope/A.1", slope, "1.44115", "nearest", "step 1: -log2(1 - 1/(lambda - 0.002))")
    cert_cmp("v3-A-slope-le", slope, "<=", SLOPE, "loss side, rounded up to 1.4412")
    cert_cmp("v3-A-Lp500", 1 / (LAM * 500), ">", D("0.00126"),
             "L_p/500 > (q/lambda - 1)/500 > 0.00126 q - 0.002 (L_p > q/lambda - 1)")
    cert_cmp("v3-A-x0-Lp500", (D("0.00126") - D("1.38e-4")) * 2, ">=", D("0.002"),
             "1.38e-4 q <= 0.00126 q - 0.002 for q >= 2 (exact), so x_0 = 1.38 delta q <= L_p/500")
    cert_true("v3-A-half-slope", SLOPE / 2 == D("0.7206"), "1.4412/2 = 0.7206 (exact)")
    s1 = 1 - D("0.7206") * X_A
    cert_value("v3-A-s1/A.1", s1, "0.005572", "nearest", "1 - 0.7206 x 1.38 (exact)")
    cert_value("v3-A-s1/4", s1, "0.00557", "nearest", "Section 4, step 2")
    cert_cmp("v3-A-s1-ge", s1, ">=", D("0.0055"), "gain of S_1: coefficient of delta q rounded down to 0.0055")
    s2 = TSTAR * ETA_A
    cert_value("v3-A-s2/A.1", s2, "2.18658", "down", "gain of S_2: 4.48 t*")
    cert_cmp("v3-A-s2-ge", s2, ">=", D("2.186"), "gain side, rounded down to 2.186")
    base = X_A - ETA_A * D("1e-4")
    cert_true("v3-A-s3-base", base == D("1.379552"), "1.38 - 4.48e-4 = 1.379552 (exact)",
              "(1.38 - 4.48 delta)^2 >= 1.379552^2 for 0 < delta <= 1e-4")
    s3 = PINS * base ** 2
    cert_value("v3-A-s3/A.1", s3, "2.18596", "down", "gain of S_3: (2/ln2) rho_c^2 (1.38 - 4.48e-4)^2")
    cert_cmp("v3-A-s3-ge", s3, ">=", D("2.185"), "gain side, rounded down to 2.185")
    cert_cmp("v3-A-x0-eta", base, ">", 0, "1.38 delta - 4.48 delta^2 > 0 for delta <= 1e-4 (step 4)")
    cert_value("pf-pins", PINS, "1.148594")
    cert_cmp("x-Hprime", log2(1 / A_), "<", D("0.78"), "|H'(rho_c)| = log2(1/a) < 0.78 (step 4)")
    dom = D("0.0055") / COEF_A
    cert_value("v3-A-dom", dom, "0.00252", "down", "Corollary A: 0.0055/2.18 = 0.00252; Appendix A.1: delta <= 0.00252")
    cert_cmp("v3-A-dom-1e-4", D("1e-4"), "<=", dom, "0.0055 delta >= 2.18 delta^2 for delta <= 1e-4")
    cert_cmp("v3-A-min", min(D("2.186"), D("2.185")), ">=", COEF_A, "min(2.186, 2.185) >= 2.18 (Corollary A)")
    opt = PINS / D("0.7206") ** 2
    cert_value("v3-A-opt/A.1", opt, "2.2120", "nearest", "upper limit of the coefficient (2/ln2) rho_c^2/0.7206^2")
    cert_value("v3-A-opt/4", opt, "2.212", "nearest", "Section 4, remarks; Appendix A.6")
    opt_disp = D("1.1486") / D("0.7206") ** 2
    cert_value("v3-A-opt-display/4", opt_disp, "2.212", "nearest", "Section 4: 1.1486/0.7206^2 = 2.212 (exact)")
    cert_value("v3-A-98.6pct", COEF_A / opt * 100, "98.6", "nearest", "2.18 is 98.6% of 2.2120 (Section 4, A.6)")
    cert_value("v3-A-98.6pct-display", COEF_A / opt_disp * 100, "98.6", "nearest", "2.18 is 98.6% of 1.1486/0.7206^2")
    cert_value("v3-A-1.3877", 1 / D("0.7206"), "1.3877", "nearest", "Section 4, remarks: delta q/0.7206 = 1.3877 delta q")
    cert_cmp("v3-A-1.38-lt", X_A, "<", 1 / D("0.7206"), "the cut 1.38 delta q lies below 1.3877 delta q")
    cert_value("v3-A-2.173", PINS * (X_A - ETA_A * D("1e-3")) ** 2, "2.173", "nearest",
               "Section 4, remarks: at delta = 1e-3 the coefficient of step 4 would be 2.173")
    cert_true("v3-rhobar", ETA_A * D("1e-3") <= X_A, "4.48 delta^2 <= 1.38 delta for delta <= 1e-3 (exact)", "Lemma rhobar")
    cert_true("v3-j0-hL", ETA_A * D("1e-3") ** 2 == D("4.48e-6") and 2 * ETA_A == D("8.96"),
              "4.48 (1e-3)^2 = 4.48e-6 and 2 x 4.48 = 8.96 (exact)", "Lemma j0: h_L <= 4.48e-6 q, 2 t* h_L <= 8.96 t* delta^2 q")
    cert_cmp("v3-j0-tstar", TSTAR * D("4.48e-6"), "<=", D("2.19e-6"), "Lemma j0: t* h_L <= 2.19e-6 q")
    cert_cmp("v3-j0-q23", (C - D("2.19e-6")) * 23, ">=", 1, "Lemma j0: 2.19e-6 q <= c q - 1 for q >= 23 (linear in q)")


def group4_thm1() -> None:
    print("[4] Proposition HGT-B / Theorem 1 of Bugeaud (2002), L^B = 7, R_1^B = 7, S_1^B = 1, S_2^B = 9"
          " (paper Section 13.4, Appendix A.3b; manuscript v3 13.5)")
    t1 = LN8 * 6
    t2 = LN9 * Fraction(49, 27)
    t3 = LN2 * 441 * CD8 / ONE8
    t4 = ln((Fraction(7, 9) + BETA1 * 168 / ONE8) / 2) + Fraction(3, 2)
    cert_true("v3-B1-coef", Fraction(1, 3) * 7 * Fraction(7, 9) == Fraction(49, 27)
              and Fraction(1, 3) * 7 * 9 * 21 == 441 and 8 * 21 == 168,
              "gamma -> 1/3, R/K -> 7/9, q/K -> 21/(1-1e-8): (1/3) 7 (7/9) = 49/27, (1/3) 7 9 21 = 441, 8 x 21 = 168 (exact)")
    cert_value("v3-B1-6ln8/A.3b", t1, "12.476649", "down", "K(L-1) ln 8 / K = 6 ln 8 (gain)")
    cert_value("v3-B1-49/27/A.3b", t2, "3.987556", "up", "(49/27) ln 9 (loss)")
    cert_value("v3-B1-441/A.3b", t3, "2.751105", "up", "441 ln 2 (c_D + 1e-8)/(1 - 1e-8) at c_D = 9e-3 (loss)")
    cert_value("v3-B1-beta1/A.3b", BETA1, "0.6120019", "up", "(1.94 + 1e-8)/(2 lambda) (loss)")
    cert_value("v3-B1-lnb/A.3b", t4, "5.447334", "up", "ln((7/9 + 168 beta_1/(1 - 1e-8))/2) + 3/2 (loss)")
    minf = t1 - t2 - t3 - t4
    m79 = minf_of(CD_MAX)
    certify("v3-B1-Minf-formula", m79.hi >= minf.lo and minf.hi >= m79.lo, m79,
            "the general formula M_inf(c_D; L^B, S_2^B) at (9e-3; 7, 9) meets the displayed M_inf",
            "consistency of the two evaluations")
    cert_value("v3-B1-Minf/A.3b", minf, "0.290656", "down", "M_inf at c_D = 9e-3 (gain)")
    cert_value("v3-B1-Minf/13.4", minf, "0.29065", "down", "Section 13.4: M_inf = 0.29065")
    cert_cmp("v3-B1-Minf-pos", minf, ">", 0, "M_inf > 0; it is affine and decreasing in c_D (coefficient -441 ln2/(1-1e-8))")
    disp = D("12.476649") - D("3.987556") - D("2.751105") - D("5.447334")
    cert_true("v3-B1-Minf-display", disp == D("0.290654") and disp > 0,
              "12.476649 - 3.987556 - 2.751105 - 5.447334 = 0.290654 > 0 (exact; the rounded table gives a lower bound)")
    # exact algebra of the parameter choice, checked for every K up to 20000
    bad = 0
    for K in range(3, 20001):
        R2 = (7 * (K - 1)) // 9 + 1
        RS = (R2 + 6) * 9
        gam = Fraction(1, 2) - Fraction(7 * K, 6 * RS)
        bad += not (7 * K + 47 < RS <= 7 * K + 56 and Fraction(1, 3) < gam <= Fraction(1, 2) - Fraction(7 * K, 6 * (7 * K + 56))
                    and 9 * R2 > 7 * (K - 1) and R2 <= Fraction(7 * K, 9) + 1)
    cert_true("v3-B1-RS", bad == 0, "7K + 47 < R S <= 7K + 56, 1/3 < gamma <= 1/2 - 7K/(6(7K+56)), 9 R_2 > 7(K-1),"
              " R_2 <= 7K/9 + 1 for K = 3..20000 (exact)", "the displayed algebra proves it for all K")
    cert_true("v3-B1-R2-q27", Fraction(7, 9) / 21 == Fraction(1, 27), "7K/9 <= q/27 when 21 K <= q (exact)")
    cert_cmp("v3-B1-card-q8", (1 / (LAM * 2) - Fraction(1, 27)) * 8, ">=", 2,
             "R_2 <= q/27 + 1 <= q/(2 lambda) - 1 <= b_1 for q >= 8 (cardinality condition)")
    cz = minf_zero(7, 9)
    cert_value("v3-B1-zero/A.3b", cz, "9.95e-3", "nearest", "M_inf vanishes at c_D = 9.95e-3")
    cert_cmp("v3-B1-zero-gt-9e-3", cz, ">", CD_MAX, "so M_inf > 0 on the whole range c_D <= 9e-3")
    # the best (L^B, S_2^B) for this shape
    best_other, arg_other = None, None
    for Lb in range(2, 21):
        for S2 in range(1, 101):
            if (Lb, S2) == (7, 9):
                continue
            z = minf_zero(Lb, S2)
            if best_other is None or z.hi > best_other.hi:
                best_other, arg_other = z, (Lb, S2)
    # tails: M_inf(Lb, S2, c) < 0 at c = 9.9e-3 for Lb >= 21 (any S2) and for Lb <= 20, S2 >= 101.
    # AM-GM: Lb^2 (ln9/(3 S2) + S2 ln2 c') >= Lb^2 * 2 sqrt(ln9 ln2 c'/3) =: Lb^2 Am with c' = (c + 1e-8)/(1 - 1e-8);
    # the log term is >= 0 for Lb >= 2 (its argument is >= Lb/2 >= 1 if S2 = 1 and >= 3 Lb beta_1/2 > 1 if S2 >= 2).
    ct = D("9.9e-3")
    cpr = (ct + D("1e-8")) / ONE8
    Am = cf.isqrt_iv(LN9 * LN2 * cpr / 3) * 2
    quad = lambda x: Am * (x * x) - LN8 * x + LN8 + Fraction(3, 2)
    tail_L = quad(21).gt(0) and (LN8 / (Am * 2)).lt(21) and (BETA1 * 3).ge(1)   # increasing beyond its vertex
    tail_S = all((LN2 * (Lb * Lb * 101) * cpr).gt(LN8 * (Lb - 1) - Fraction(3, 2)) for Lb in range(2, 21))
    cert_true("v3-B1-opt", best_other.hi < cz.lo and best_other.lt(ct) and tail_L and tail_S,
              "among L^B >= 2, S_2^B >= 1 (S_1^B = 1, R_1^B = L^B) the largest c_D with M_inf > 0 is at (7, 9)",
              f"runner-up {arg_other} with limit {best_other.fmt(6)}; tails Lb >= 21 and S2 >= 101 negative at c_D = 9.9e-3")
    cert_value("v3-B1-opt/13.4", cz, "9.95e-3", "nearest", "Section 13.4: the largest c_D for this shape is 9.95e-3")
    # Theorem 2 in the form of Proposition 13.2: 13.0978306 (4 ln 8)^2 (c_D + 1e-8) < 1 - 1e-8 (the floor 4 ln 8 is
    # active for c_D >= 8.51e-4, claim x-floor-8.51e-4)
    c2 = ONE8 / (cf.BUG_BITS * cf.Y_FLOOR ** 2) - D("1e-8")
    cert_value("v3-B1-thm2-limit/13.4", c2, "1.10e-3", "nearest",
               "Theorem 2 form: limit of c_D with 3*53.6/(ln8)^4 ln9 ln2 (4 ln8)^2 (c_D + 1e-8) < 1 - 1e-8")
    cert_cmp("v3-B1-thm2-floor", c2, ">=", D("8.51e-4"), "the floor 4 ln 8 is active there (Z decreasing in c_D)")
    cert_true("v3-B1-ten", CD_MAX / D("9e-4") == 10, "window 9e-3 versus 9e-4: ten times wider (exact)")
    cert_value("v3-B1-limits-ratio", (cz + D("1e-8")) / (c2 + D("1e-8")), "9.0", "nearest",
               "ratio of the two limits (9.95e-3 versus 1.10e-3)")
    lnb = t4
    ceff = ONE8 * LN8 ** 4 / (lnb * lnb * LN9 * LN2 * (cz + D("1e-8")) * 3)
    cert_value("v3-B1-Ceff/13.4", ceff, "13.9", "nearest",
               "effective constant: c with 3 c (ln8)^-4 (ln b)^2 ln9 ln2 (c_D + 1e-8) = 1 - 1e-8 at the limit c_D")
    cert_value("v3-B1-lnb-ratio/13.4", lnb / LN8, "2.62", "nearest", "ln b^B / ln 8 (the role of Y/log m)")
    cert_value("v3-B1-3.9/13.4", D("53.6") / D("13.9"), "3.9", "nearest", "53.6/13.9 (exact)")
    cert_value("v3-B1-3.9-exact", D("53.6") / ceff, "3.9", "nearest", "53.6 over the unrounded effective constant")
    cert_value("v3-B1-2.3/13.4", (Fraction(4) / D("2.62")) ** 2, "2.3", "nearest", "(4/2.62)^2 (exact)")
    cert_value("v3-B1-2.3-exact", (LN8 * 4 / lnb) ** 2, "2.3", "nearest", "(4 ln 8/ln b^B)^2")
    thm1_threshold(minf)


# ---- the remark "(1) and the cardinality conditions hold from about q >= 4.1e4 on" ----------------------------

def _thm1_K(q: int) -> int:
    """K^B = floor(((1 - 1e-8) q - 2 log2 q - 2)/21) (certified floor)."""
    k = ifloor((ONE8 * q - log2(q) * 2 - 2) / 21)
    if k is None:
        raise Ambiguous(f"K^B undetermined at q = {q}")
    return k


def _thm1_lhs(q: int, K: int, lnprod: Iv) -> Iv:
    """Left-hand side of (1) at c_D = 9e-3 with the worst-case bounds h(x2/y2) <= ln2((c_D + 1e-8) q + 2 log2 q + 1)
    + ln 3 and b_1 <= (1.94 + 1e-8) q/(2 lambda); lnprod = ln prod_{k=1}^{K-1} k! (an enclosure)."""
    R2 = (7 * (K - 1)) // 9 + 1
    R, S, N = R2 + 6, 9, 7 * K
    gam = Fraction(1, 2) - Fraction(N, 6 * R * S)
    b1 = BETA1 * q
    h2 = LN2 * (CD8 * q + log2(q) * 2 + 1) + LN3
    logb = ln(((R - 1) + b1 * (S - 1)) / 2) - lnprod * Fraction(2, K * K - K)
    return LN8 * (6 * K) - ln(N) * 3 - logb * (K - 1) - LN9 * (gam * 7 * R) - h2 * (gam * 7 * S)


def _thm1_tail(K1: int, minf: Iv):
    """Constants (A, B) with LHS(q) >= M_inf K - A ln K - B for every q whose K^B = K >= K1 (derivation printed)."""
    l0 = log2(D("21.22") * (1 + Fraction(1, K1)))
    aH = LN2 * 21 * CD8 / ONE8
    bH = (1 + CD8 / ONE8) * 2
    cH = bH * LN2 * l0 + LN2 * (CD8 * 23 / ONE8 + 1) + LN3
    mu = (Fraction(7, 9) + BETA1 * 168 / ONE8) / 2
    nu0 = (Fraction(47, 9) + BETA1 * 8 * 23 / ONE8) / 2 + BETA1 * 8 * l0 / ONE8
    nuK = BETA1 * 8 / (ONE8 * LN2)
    g = 21 + Fraction(84, K1 + 8)
    A = 4 + nuK / mu + bH * g
    B = ln(7) * 3 - ln(mu) - 4 + Fraction(4, K1) + nu0 / mu + LN9 * Fraction(196, 9) + aH * 84 + cH * g
    return A, B


def thm1_threshold(minf: Iv) -> None:
    print("     Remark of Section 13.4: (1) and the cardinality conditions hold from about q >= 4.1e4 on.  Certified for")
    print("     all q (c_D = 9e-3, s/q <= 1.94, worst-case h(x2/y2) and b_1).  Within a block of constant K^B the left-hand")
    print("     side of (1) decreases in q, so it is evaluated at the last q of the block, with the exact log of prod k!.")
    print("     For K^B >= K_1 an explicit bound is used: with q <= Q(K) := (21K + 23 + 2 l(K))/(1-1e-8), l(K) :=")
    print("     log2(21.22 (K+1)) (from 0.99 q <= (1-1e-8) q - 2 log2 q - 2 < 21(K+1) for q >= 3000), ln b^B <=")
    print("     ln(mu K + nu(K)) - 2 I(K)/(K^2-K), I(K) = int_1^{K-1} (x ln x - x + 1) dx <= ln prod k!, ln(mu K + nu) <=")
    print("     ln K + ln mu + nu/(mu K), 2 I(K)/K >= (K-2) ln K - 1.5 K + 4 - 4/K, gamma 7 R <= 49K/27 + 196/9, 63 gamma <=")
    print("     21 + 84/(K+8), the left-hand side of (1) is >= M_inf K - A ln K - B (A, B below), increasing for K >= A/M_inf.")
    lnprod = {1: Iv.of(0)}                                     # lnprod[K] = sum_{k=1}^{K-1} ln k!
    state = {"K": 1, "fact": Iv.of(0)}                         # fact = ln(K!) for the current K

    def lnprod_upto(K: int) -> Iv:
        while state["K"] < K:
            k = state["K"]
            lnprod[k + 1] = lnprod[k] + state["fact"]
            state["K"] = k + 1
            state["fact"] = state["fact"] + ln(k + 1)
        return lnprod[K]
    q_fail = 41087
    K_fail = _thm1_K(q_fail)
    lhs_fail = _thm1_lhs(q_fail, K_fail, lnprod_upto(K_fail))
    # the explicit bound: the smallest K1 = K_fail + 1 + 5j with f(K1) > 0 and K1 >= A/M_inf
    for K1 in range(K_fail + 1, K_fail + 2000, 5):
        A1, B1 = _thm1_tail(K1, minf)
        f1 = minf * K1 - A1 * ln(K1) - B1
        if f1.gt(0) and (A1 / minf).lt(K1):
            break
    else:
        raise Ambiguous("no K_1 found for the explicit bound")
    # blocks K^B = K_fail + 1 .. K1 - 1: evaluate at the last q of each block
    q = q_fail + 1
    Kq = _thm1_K(q)
    starts_block = Kq == K_fail + 1                            # q_fail + 1 is the first q of the next block
    ok, nblocks = True, 0
    while Kq < K1:
        Kn = _thm1_K(q + 1)                                   # K^B increases by at most 1 when q increases by 1
        if Kn != Kq:                                           # q is the last q of block Kq
            ok &= _thm1_lhs(q, Kq, lnprod_upto(Kq)).gt(0)
            nblocks += 1
            Kq = Kn
        q += 1
    q1 = q                                                     # the first q with K^B = K1
    cert_true("v3-B1-q-fail", lhs_fail.lt(0) and starts_block,
              f"at q = {q_fail} (K^B = {K_fail}) the worst-case left-hand side of (1) is negative;"
              f" q = {q_fail + 1} starts the block K^B = {K_fail + 1}", f"LHS in {lhs_fail.fmt(6)}")
    cert_true("v3-B1-q-blocks", ok and nblocks == K1 - K_fail - 1,
              f"(1) holds on the {nblocks} blocks K^B = {K_fail + 1}..{K1 - 1} (q = {q_fail + 1}..{q1 - 1}), exact ln prod k!",
              "cardinality condition: claim v3-B1-card-q8 (q >= 8)")
    certify("v3-B1-q-tail", f1.gt(0) and (A1 / minf).lt(K1), f1,
            f"for K^B >= K_1 = {K1} (q >= {q1}): M_inf K_1 - A ln K_1 - B > 0 and K_1 >= A/M_inf",
            f"A <= {float(A1.hi_f()):.3f}, B <= {float(B1.hi_f()):.2f}; 21 K_1 >= 3000")
    cert_true("v3-B1-q-tail-pre", 21 * K1 >= 3000 and ((ONE8 - D("0.99")) * 3000 - log2(3000) * 2 - 2).gt(0)
              and (ONE8 - D("0.99")) * 3000 * LN2.lo_f() >= 2,
              "0.99 q <= (1-1e-8) q - 2 log2 q - 2 for q >= 3000 (value at 3000 and derivative)")
    cert_value("v3-B1-q-from/13.4", q_fail + 1, "4.1e4", "nearest",
               f"(1) and the cardinality conditions hold for every q >= {q_fail + 1} and fail (worst case) at q = {q_fail}")


def group5_rules() -> dict:
    print("[5] Section 14.1 rules and Lemma rules (a)-(g) (paper Section 14.1, Appendix A.2; manuscript v3 14.6)")
    cert_true("v3-cD-flat", 1 + 2 * CD_MAX == D("1.018"), "c_D = 9e-3 iff beta >= 1 + 2 x 9e-3 = 1.018 (exact)")
    target = CD_MAX * D("0.025")
    cert_true("v3-target/A.2", target == D("2.25e-4"), "0.025 c_D = 2.25e-4 (exact)")
    cert_cmp("x-rc-lt-1", RC, "<", 1, "r_c < 1, so log2(1 + r_c^p) is decreasing in p")
    cert_cmp("v3-p246-fails/A.2", T(246), ">", target, "log2(1 + r_c^246) > 2.25e-4")
    cert_cmp("v3-p/A.2", T(247), "<=", target, "log2(1 + r_c^247) <= 2.25e-4, hence p = 247")
    cert_true("v3-p-80-246", all(T(p).gt(target) for p in range(80, 247)),
              "log2(1 + r_c^p) > 2.25e-4 for every p = 80..246 (direct interval evaluation)")
    cert_value("v3-phi/A.2", PHI(247), "0.9958004", "nearest", "phi_247")
    cert_value("v3-logth-phi/A.2", LT(247), "0.00282406", "down", "log2(1/Theta#_{phi_247}) (gain)")
    cert_value("pf-logth-half", LTH, "0.38238", "nearest", "log2(1/Theta#_{1/2}); Lemma rules (d), Appendix A.2")
    l1 = T(247) / 247
    cert_value("v3-l1rp/A.2", l1, "9.0464e-7", "up", "log2(1 + r_c^247)/247 (loss)")
    b_disp = D("4.5e-3") * D("0.00282406") - D("9.0464e-7")
    cert_value("v3-B-display/A.2", b_disp, "1.18036e-5", "nearest", "4.5e-3 x 0.00282406 - 9.0464e-7 (exact)")
    d6, cD6, p6, B6, which6 = constants_v3(Fraction(3, 2))
    certify("v3-constants-0.6", p6 == 247 and which6 == "0.45B" and cD6.contains(CD_MAX)
            and cD6.width() <= Fraction(1, 2 ** 250), d6,
            "alpha = 0.6: c_D = 9e-3, p = 247, delta = 0.45 B")
    cert_value("v3-B/A.2", B6, "1.18036e-5", "down", "B (gain); Section 14.1: B = 1.18036e-5")
    cert_cmp("v3-B-display-lower", b_disp, "<=", B6, "the displayed computation (gain down, loss up) is a lower bound for B")
    cert_value("v3-delta/A.2", d6, "5.3116e-6", "down", "delta = 0.45 B (rounded down); Sections 14.1, 14.3")
    dp6 = d6 * DPR
    cert_value("v3-dprime/A.2", dp6, "1.12135e-5", "nearest", "delta' = 19 delta/9")
    bstar = 1 + B6 * (DELTA_B / DELTA_LIN)                  # 1e-4 (beta - 1) = 0.45 B
    alpha_star = bstar / (1 + bstar)
    cert_value("v3-beta*/A.2", bstar, "1.0531165", "nearest", "1e-4(beta-1) >= 0.45 B iff beta >= beta* = 1 + 4500 B")
    cert_cmp("v3-beta*-le/A.2", bstar, "<=", D("1.0531165"), "beta >= 1.0531165 gives delta = 0.45 B")
    cert_cmp("v3-beta*-le/14.1", bstar, "<=", D("1.053117"), "Section 14.1: for beta >= 1.053117, delta = 0.45 B")
    cert_value("v3-alpha*/A.2", alpha_star, "0.5129356", "nearest", "alpha* = beta*/(1 + beta*); Appendix A.2, A.4")
    cert_cmp("v3-alpha*-le/A.2", alpha_star, "<=", D("0.5129356"), "alpha >= 0.5129356 gives delta = 0.45 B")
    cert_cmp("v3-alpha*-le/14.1", alpha_star, "<=", D("0.512936"), "Section 14.1: for alpha >= 0.512936 the constants"
             " do not depend on alpha (alpha/(1-alpha) increasing)")
    cert_cmp("v3-beta*-ge-1.018", bstar, ">=", D("1.018"), "beta* >= 1.018: for beta >= beta*, c_D = 9e-3, p = 247, B fixed")
    k6 = keff_v3(B6, d6)
    cert_value("v3-keff/A.2", k6, "5.9012e-7", "down", "kappa_eff = B - 4.48 t* delta^2 - 19 delta/9 (gain)")
    cert_cmp("v3-keff-pos", k6, ">", 0)
    cert_value("v3-keff-0.05B/A.2", k6 / B6, "0.05", "nearest", "kappa_eff is about 0.05 B")
    first = CD_MAX / 2 * LTH
    cert_value("v3-first/A.2", first, "1.7207e-3", "down", "(c_D/2) log2(1/Theta#_{1/2}) (gain)")
    cert_value("v3-10dprime/A.2", dp6 * 10, "1.1214e-4", "up", "10 delta' (loss)")
    cert_cmp("v3-first-gt", first, ">", dp6 * 10, "step 4 of Proposition allshells, Lemma rules (d) at alpha = 0.6")
    sh = SHALLOW * Fraction(247, 2)
    cert_value("v3-shallow/A.2", sh, "3.1360", "down", "(p/2) log2(2/(1 + r_c)) at p = 247 (gain)")
    cert_cmp("v3-shallow-gt1", sh, ">", 1)
    er6 = d6 * X_A / (LAM * D("0.5"))
    cert_value("v3-epsrho-0.6/A.2", er6, "9.250e-6", "up", "1.38 delta/(lambda (beta - 1)) at beta = 1.5 (loss)")
    epl = X_A * DELTA_LIN / LAM
    cert_value("v3-epsrho-lim/A.2", epl, "8.7069e-5", "up", "1.38e-4/lambda: Lemma rules (f), Appendix A.2 item 9")
    cert_cmp("v3-epsrho-lim-8.71e-5", epl, "<=", D("8.71e-5"), "Lemma rules (f): <= 8.71e-5 < 1e-4")
    # Lemma rules (a): 1 - phi_p >= 1/p (analytic proof, as in r6) and B >= 0.3108 c_D/p
    l15 = LN2 * D("1.5")
    l125 = LN2 * LN2 * D("1.25")
    cert_value("pf-phi-x2", l15, "1.0397")
    cert_cmp("pf-phi-x2-dir", l15, ">=", D("1.0397"), "used as 1 - 1.5 ln2 x <= 1 - 1.0397 x")
    cert_value("pf-phi-x2b", l125, "0.6006")
    cert_cmp("pf-phi-x2b-dir", l125, "<=", D("0.6006"), "used as (5/4) ln2^2 x^2 <= 0.6006 x^2")
    cert_value("pf-phi-xmax/ms", (l15 - 1) / (l125 + 1), "0.0248", "down", "x <= 0.0248")
    cert_cmp("pf-phi-xmax/ms-ineq", D("0.0248"), "<=", D("0.0397") / D("1.6006"),
             "1 - 1.0397x + 0.6006x^2 <= 1 - x - x^2 for 0 <= x <= 0.0248 (exact)")
    cert_cmp("x-1/79", Fraction(1, 79), "<=", D("0.0248"), "x = 1/(p-1) <= 1/79 <= 0.0248")
    rs = RHO_SHARP * (1 - RHO_SHARP)
    rsl = rs * 2 / LN2
    cert_cmp("pf-rs-ge", rsl, ">=", D("0.6718"), "log2(1/Theta#_{phi_p}) >= 0.6718/p")
    cert_cmp("pf-B-lb/ms", D("0.6718") / 2 - D("0.025"), ">=", D("0.3108"), "B >= (c_D/p)(0.6718/2 - 0.025) >= 0.3108 c_D/p")
    cert_cmp("v3-B-lb-0.6", B6, ">=", D("0.3108") * CD_MAX / 247, "Lemma rules (a) at alpha = 0.6")
    # Lemma rules (b)
    cert_true("v3-b-0.95", DPR * DELTA_B == D("0.95") and 1 - D("0.95") == D("0.05"),
              "delta <= 0.45 B gives delta' = 19 delta/9 <= 0.95 B, so kappa_eff >= 0.05 B - 4.48 t* delta^2 (exact)")
    cert_cmp("v3-b-2.19", TSTAR * ETA_A, "<=", D("2.19"), "4.48 t* <= 2.19")
    cert_cmp("v3-b-4e-5", D("2.19") * D("1.81e-5"), "<=", D("4e-5"), "4.48 t* delta^2 <= 2.19 (1.81e-5) delta <= 4e-5 delta")
    cert_cmp("v3-b-small", DELTA_B * D("4e-5"), "<", D("0.05"), "<= 0.45 x 4e-5 B, much smaller than 0.05 B (exact)")
    kb = B6 * D("0.05") - TSTAR * d6 * d6 * ETA_A
    certify("v3-keff-b-0.6", (k6 - kb).mag() <= 1 << 16 and kb.gt(0), kb,
            "Lemma rules (b) at alpha = 0.6: kappa_eff = 0.05 B - 4.48 t* delta^2 > 0 (equality, since delta = 0.45 B)")
    # Lemma rules (c)
    cert_value("pf-15ln2", l15, "1.039721")
    cert_cmp("pf-15ln2-le", l15, "<=", D("1.03973"))
    cert_cmp("pf-phi-lb", D("1.03973") / 79, "<=", D("0.0131612"), "phi_p >= 1 - 1.03973/79 >= 1 - 0.0131612 (exact)")
    cert_cmp("x-phi-gap-0.01317", D("0.0131612"), "<=", D("0.01317"), "1 - phi_p <= 0.01317")
    cert_cmp("pf-u-le", rs * D("0.0131612") * 2, "<=", D("0.0061287"), "u <= 2 x 0.0131612 rho#(1-rho#) <= 0.0061287")
    ltub = D("0.0061287") / ((1 - D("0.0061287")) * LN2)
    cert_cmp("pf-logth-ub", ltub, "<=", D("0.0088964"), "u/((1-u) ln 2) <= 0.0088964 (increasing in u)")
    cert_cmp("pf-logth-ub-le", ltub, "<=", D("0.00890"))
    dmax = DELTA_B * CD_MAX / 2 * D("0.00890")
    cert_value("v3-delta-max", dmax, "1.8023e-5", "up", "0.45 (9e-3/2) 0.00890 = 1.80225e-5 (exact), Lemma rules (c)")
    cert_cmp("v3-delta-max-1.81", dmax, "<=", D("1.81e-5"), "delta <= 1.81e-5 (hence delta <= 1e-4)")
    h46 = ETA_A * D("1.8023e-5") ** 2
    cert_cmp("v3-4.48delta2", h46, "<=", D("1.46e-9"), "4.48 delta^2 <= 1.46e-9 (exact)")
    cert_cmp("v3-4.48delta2-1e-8", D("1.46e-9"), "<=", D("1e-8"), "4.48 delta^2 <= 1e-8")
    # Lemma rules (d), (e), (g)
    cert_true("v3-d-9.5", Fraction(190, 9) * DELTA_B == D("9.5"), "10 delta' = 190 delta/9 <= (190/9) 0.45 B = 9.5 B (exact)")
    cert_cmp("v3-d", LTH, ">", D("9.5") * D("0.00890"), "Lemma rules (d): 0.38238 > 9.5 x 0.00890")
    cert_cmp("v3-e", DPR * DELTA_LIN, "<", D("0.19"), "Lemma rules (e): (19/9) 1e-4 < 0.19 (exact)")
    cert_cmp("x-e-0.19", LTH / 2, ">=", D("0.19"), "0.19 (beta - 1) <= (1/2) log2(1/Theta#_{1/2}) (beta - 1)")
    cert_cmp("x-g-0.025392", SHALLOW, ">=", D("0.025392"), "Lemma rules (g): log2(2/(1+r_c)) >= 0.025392")
    cert_true("pf-shallow-80", 40 * D("0.025392") == D("1.01568"), "40 x 0.025392 = 1.01568 > 1 (exact)")
    cert_true("v3-thmB-margin", DPR - 2 == Fraction(1, 9), "delta' - 2 delta = delta/9 (exact)")
    cert_cmp("v3-j0-nonempty", DPR * D("1.81e-5"), "<", C, "delta' <= (19/9) 1.81e-5 < c: the set defining j_0 is"
             " nonempty for large q (Proposition allshells, step 1)")
    return {"d6": d6, "B6": B6, "k6": k6, "bstar": bstar, "alpha_star": alpha_star}


def conditions_box_v3(bm1: Iv, cD: Iv, p: int) -> dict[str, bool]:
    """Lemma rules (a)-(g), delta <= 1e-4, 4.48 delta^2 <= 1e-8 and c_D <= 9e-3, certified for every beta - 1 in bm1
    and c_D in cD (p one candidate of the rule)."""
    B = budget(cD, p)
    d = imin(B * DELTA_B, bm1 * DELTA_LIN)
    return {
        "(a)": B.ge(cD * D("0.3108") / p),
        "(b)": (B * D("0.05") - TSTAR * d * d * ETA_A).gt(0),      # kappa_eff >= 0.05 B - 4.48 t* delta^2 (pointwise)
        "(c)": d.le(D("1.81e-5")) and (d * d * ETA_A).le(D("1e-8")),
        "(d)": (cD / 2 * LTH).gt(d * Fraction(190, 9)),
        "(e)": (d * DPR).lt(bm1 * LTH / 2),
        "(f)": (d * X_A / (LAM * bm1)).lt(D("1e-4")),
        "(g)": cD.lt(bm1) and (SHALLOW * p / 2).gt(1),
        "HGT-B": cD.hi <= Iv.of(CD_MAX).hi,                       # c_D <= 9e-3 (up to the enclosure of 9e-3)
        "delta>0": d.gt(0),
    }


def group6_cover() -> None:
    print("[6c] Lemma rules (a)-(g) on a covering of beta in [1 + 1e-14, 1.94] (v3 rules)")
    edges = [D("1e-14")]
    top = D("0.94")
    while edges[-1] < top:
        nx = Fraction(math.ceil(edges[-1] * Fraction(101, 100) * 2 ** 80), 2 ** 80)
        edges.append(min(nx, top))
    fails, pmax_all, pairs = [], 0, 0
    for i in range(len(edges) - 1):
        bm1 = Iv.hull(edges[i], edges[i + 1])
        cD = imin(CD_MAX, bm1 / 2)
        pmin, pmax = p_candidates(cD)
        pmax_all = max(pmax_all, pmax)
        for p in range(pmin, pmax + 1):
            pairs += 1
            for k, ok in conditions_box_v3(bm1, cD, p).items():
                if not ok:
                    fails.append((i, p, k))
    cert_true("v3-range-viol", not fails,
              f"Lemma rules (a)-(g), c_D <= 9e-3 and delta > 0 hold for every beta - 1 in [1e-14, 0.94]"
              f" ({len(edges) - 1} boxes, {pairs} (box, p) pairs)",
              f"failures: {fails[:5]}" if fails else
              f"p ranges up to {pmax_all}; (f) is checked as < 1e-4 here, <= 8.71e-5 by claim v3-epsrho-lim;"
              " beta - 1 < 1e-14 only by the analytic Lemma rules")


def group6_active() -> None:
    print("[6d] Which term of delta is active near alpha = 1/2 (paper Appendix A.4 and the table of Section 14.3)")
    for a in ("0.5001", "0.501", "0.51"):
        al = D(a)
        d, cD, p, B, which = constants_v3(al / (1 - al))
        certify(f"v3-active-{a}", which == "1e-4(beta-1)", d, f"alpha = {a}: delta = 1e-4(beta-1) is active",
                f"p = {p}")
    for a in ("0.55", "0.6", "0.65", "0.659"):
        al = D(a)
        d, cD, p, B, which = constants_v3(al / (1 - al))
        certify(f"v3-active-{a}", which == "0.45B", d, f"alpha = {a}: delta = 0.45 B is active", f"p = {p}")
    bm1 = D("1e-10")
    d, cD, p, B, which = constants_v3(1 + bm1)
    certify("v3-active-exception-1e-10", which == "0.45B", B * DELTA_B,
            "A.4: at beta - 1 = 1e-10 the term 0.45 B is smaller than 1e-4 (beta - 1) = 1e-14", f"p = {p}")
    # the linear term is active on beta - 1 in [1e-9, beta* - 1): boxes on [1e-9, 0.018]; on [0.018, beta* - 1)
    # c_D = 9e-3, p = 247 and B are constant, so 1e-4 (beta - 1) < 1e-4 (beta* - 1) = 0.45 B there
    lo, top = D("1e-9"), D("0.018")
    edges = [lo]
    while edges[-1] < top:
        nx = Fraction(math.ceil(edges[-1] * Fraction(1004, 1000) * 2 ** 80), 2 ** 80)
        edges.append(min(nx, top))
    bad = 0
    for i in range(len(edges) - 1):
        bm1 = Iv.hull(edges[i], edges[i + 1])
        cD = imin(CD_MAX, bm1 / 2)
        pmin, pmax = p_candidates(cD)
        bad += sum(1 for p in range(pmin, pmax + 1) if not (bm1 * DELTA_LIN).lt(budget(cD, p) * DELTA_B))
    cert_true("v3-active-range", bad == 0,
              f"delta = 1e-4(beta-1) is active for every beta - 1 in [1e-9, beta* - 1) ({len(edges) - 1} boxes)",
              "so the exceptions lie in alpha - 1/2 < 2.5e-10 ('narrow ranges very close to 1/2')")


def group7_thresholds(d6: Iv, k6: Iv) -> None:
    print("[7] Thresholds for 'K sufficiently large' at alpha = 0.6 (paper Section 14.4, Appendix A.5; v3 constants)")
    print("     Each threshold function f(q) = (linear gain) q - log2(polynomial in q) has f'(q) = const - (sum of")
    print("     positive terms decreasing in q), so f' is nondecreasing; f(Q) >= 0 and f'(Q) >= 0 give f(q) >= 0")
    print("     for all q >= Q.")
    two11 = cf.pw2(D("1.1"))
    k151 = D("1.51")

    def fB(q) -> Iv:                               # Theorem B: (delta' - 2 delta) q = (delta/9) q
        L = k151 * q / LAM + 1
        return d6 / 9 * q - log2((3 + L * LN3) * (L * 2 + 1) * q * (q + 1) * two11)

    def dfB(q) -> Iv:
        L = k151 * q / LAM + 1
        s = (k151 * LN3 / LAM) / (3 + L * LN3) + (k151 * 2 / LAM) / (L * 2 + 1) + Fraction(1, q) + Fraction(1, q + 1)
        return d6 / 9 - s / LN2

    c247 = cf.pw(Iv.of(25), Fraction(1, 247)) * 8 * two11
    lt247 = LT(247)

    def g0(q) -> Iv:                               # Proposition allshells, step 4, third term
        return k6 * q - log2(c247 * (q + 2) ** 2 * q * (q + 1) * q ** 2) - lt247 * D("1.5") - 3

    def dg0(q) -> Iv:
        return k6 - (Fraction(2, q + 2) + Fraction(3, q) + Fraction(1, q + 1)) / LN2

    def hA(q) -> Iv:                               # reference value: 2.18 delta^2 q >= log2(2 s), s <= 1.51 q
        return d6 * d6 * COEF_A * q - log2(k151 * 2 * q)

    def dhA(q) -> Iv:
        return d6 * d6 * COEF_A - 1 / (LN2 * q)

    br = {}
    for name, f, df, stated, lo, hi in (("v3-q0", g0, dg0, "2.99e8", 10 ** 7, 10 ** 10),
                                        ("v3-qB", fB, dfB, "1.90e8", 10 ** 7, 10 ** 10),
                                        ("v3-qA", hA, dhA, "6.65e11", 10 ** 10, 10 ** 13)):
        a, b = cf.crossing(f, lo, hi)
        br[name] = (a, b)
        cert_value(name, Iv.hull(a, b), stated, "up", "the stated threshold is the crossing rounded up")
        Q = int(Fraction(stated))
        fq, dq = f(Q), df(Q)
        certify(name + "-safe", fq.ge(0) and dq.ge(0), fq,
                f"condition holds for all q >= {stated}: f({stated}) >= 0 and f'({stated}) >= 0", f"crossing in [{a}, {b}]")
    qB, q0, qA = br["v3-qB"], br["v3-q0"], br["v3-qA"]
    cert_value("v3-qB-crossing/A.5", Iv.hull(*qB), "1.899e8", "nearest", "A.5: the crossing point is 1.899e8")
    certify("v3-q0-dominates", qB[1] < q0[0], (qB[1], q0[0]), "q_B < q_0: at the stage of (WF) q_0 is the dominant threshold")
    cert_cmp("v3-intro-3e8", D("3e8"), ">=", D("2.99e8"), "introduction, remark (3): (WF) holds from q >= 3e8 on"
             " (3e8 >= q_0 > q_B, claims v3-q0-safe and v3-qB-safe)")
    Q0 = 299 * 10 ** 6
    cert_value("v3-K-7.5e8", Iv.hull(Fraction(5, 2) * q0[0], Fraction(5, 2) * Q0), "7.5e8", "nearest",
               "K = s + q, q/K -> 0.4: K ~ 2.5 q (q from the crossing to the stated q_0)")
    cert_value("v3-gain-bits-at-q0", d6 * d6 * COEF_A * Q0, "1.8e-2", "nearest", "2.18 delta^2 q bits at q = q_0 = 2.99e8")
    cert_value("v3-qA-6.6e11", Iv.hull(*qA), "6.6e11", "nearest", "Section 14.4: from q ~ 6.6e11 on (the crossing,"
               " two digits; rounded up it is q_A = 6.65e11)")


TABLE_V3 = (("0.5001", "1.74e-15", "1e-4(beta-1)"), ("0.501", "1.74e-13", "1e-4(beta-1)"),
            ("0.51", "1.77e-11", "1e-4(beta-1)"), ("0.55", "2.76e-11", "0.45B"), ("0.6", "2.46e-11", "0.45B"),
            ("0.65", "2.15e-11", "0.45B"), ("0.659", "2.09e-11", "0.45B"))


def group8_eps(B6: Iv, d6: Iv, bstar: Iv, alpha_star: Iv) -> None:
    print("[8] The gain epsilon(alpha) and the divergent-orbit corollary (paper Sections 14.3, 14.5, Appendix A.4)")
    eps = {}
    for a, v3, dwhich in TABLE_V3:
        al = D(a)
        e, which = eps_v3(al)
        eps[a] = e
        _, _, p, _, dw = constants_v3(al / (1 - al))
        certify(f"v3-eps-min-{a}", which == "2.18 delta^2 (1-alpha)" and dw == dwhich, e,
                "min in epsilon(alpha) is the first term", f"delta = {dw}, p = {p}")
        cert_value(f"v3-eps-table-{a}", e, v3, "down", "table of Section 14.3 (rounded down)")
    e6 = eps["0.6"]
    cert_value("v3-eps-06/14.3", e6, "2.4602e-11", "down", "Section 14.3, Appendix A.4")
    cert_cmp("v3-gain-ge", e6, ">=", D("2.46e-11"), "epsilon(0.6) >= 2.46e-11 (main theorem, Definition M1, introduction)")
    cert_value("v3-eps-06-display", COEF_A * D("5.3116e-6") ** 2 * D("0.4"), "2.4602e-11", "nearest",
               "2.18 x (5.3116e-6)^2 x 0.4 (exact), as displayed")
    other6 = (1 - C) * D("0.2") / 2
    cert_value("x-other-term-0.6", other6, "0.095", "nearest", "(1/2)(1-c) 0.2 (Section 14.3)")
    cert_value("x-other-term-0.6/A.4", other6, "0.0950", "nearest")
    a = D("0.51294")
    ba = a / (1 - a)
    _, _, pa, _, wa = constants_v3(ba)
    ea, _ = eps_v3(a)
    cert_true("v3-div-alpha", wa == "0.45B" and pa == 247, "alpha = 0.51294: beta >= beta*, c_D = 9e-3, p = 247, delta = 0.45 B")
    r = ea / a
    cert_value("v3-div/14.5", r, "5.8402e-11", "down", "epsilon(0.51294)/0.51294 (Section 14.5, Appendix A.4)")
    cert_cmp("v3-div-ge", r, ">=", D("5.84e-11"), "Corollary divergent-explicit: exponent 1 - c - 5.84e-11")
    print("     sup_alpha eps(alpha)/alpha: (i) alpha >= alpha*: beta >= beta* >= 1.018, so c_D = 9e-3, p = 247, delta = 0.45B,")
    print("     and eps/alpha <= 2.18 (0.45B)^2 (1-alpha)/alpha, decreasing; (ii) alpha <= alpha*: delta <= 1e-4 (beta-1), so")
    print("     eps/alpha <= 2.18e-8 (beta-1)^2/beta, increasing in beta.  Both bounds equal 2.18 (0.45B)^2/beta* at alpha*,")
    print("     where the bound is attained (delta = 0.45B = 1e-4(beta*-1) and the min is the first term).")
    e_star1 = (B6 * DELTA_B) ** 2 * COEF_A * (1 - alpha_star)
    e_star2 = (1 - C) * (alpha_star * 2 - 1) / 2
    cert_cmp("v3-sup-premise", e_star1, "<", e_star2, "at alpha* the min is 2.18 delta^2 (1 - alpha)")
    sup = (B6 * DELTA_B) ** 2 * COEF_A / bstar
    cert_value("v3-div-sup", sup, "5.8403e-11", "down", "max over alpha, attained at alpha*; gain side, rounded down"
               " (Section 14.5, A.4)")
    cert_value("v3-div-sup-alpha/A.4", alpha_star, "0.5129356", "nearest", "attained at alpha = 0.5129356 (A.4)")
    cert_value("v3-div-sup-alpha/14.5", alpha_star, "0.5129356", "nearest", "Section 14.5: attained at alpha = 0.5129356")
    cert_value("x-alpha(1-c)-0.6", (1 - C) * D("0.6"), "0.570", "nearest", "introduction, remark on the size (1)")
    cert_cmp("x-alpha(1-c)>0.47", (1 - C) / 2, ">", D("0.47"), "alpha (1-c) > 0.47 for alpha > 1/2 (proof of the stopping-time theorem)")
    cert_cmp("v3-eps-le-0.1", COEF_A * D("1.81e-5") ** 2 / 2, "<=", D("0.1"), "epsilon(alpha) <= 0.1")
    # the r6 value quoted in Section 14.1 and in the remark on Theorem 2: v2 rules of proof_pf_certified.py
    e_r6, w_r6 = cf.eps_of(Fraction(3, 5))
    cert_value("v3-r6-eps06", e_r6, "5.35e-14", "down", "revision r6 (v2 rules, proof_pf_certified.eps_of): epsilon(0.6)"
               " = 5.35e-14 (introduction, Section 14.1, remark thm2route)")
    a6 = D("0.501")
    cert_value("v3-r6-div", cf.eps_of(a6)[0] / a6, "1.33e-13", "down", "revision r6: epsilon(0.501)/0.501 = 1.33e-13"
               " (introduction, remark (1))")


def group8b_room(B6: Iv) -> None:
    print("[8b] Remaining room for improvement (paper Appendix A.6)")
    cert_value("v3-A6-1.24", (D("0.5") / DELTA_B) ** 2, "1.24", "up", "(0.5/0.45)^2 = 1.2346, rounded up (an upper bound)")
    # p maximizing B at c_D = 9e-3: direct for 80 <= p <= 400; for p > 400, B < (c_D/2) U(p) with
    # U(p) := u/((1-u) ln 2), u := 2 rho#(1-rho#) 1.03973/(p-1) (Lemma rules (c): 1 - phi_p <= 1.03973/(p-1)), decreasing in p
    Bs = {p: budget(CD_MAX, p) for p in range(80, 401)}
    top = max(Bs, key=lambda p: Bs[p].lo)
    others = all(Bs[p].lt(Bs[top]) for p in Bs if p != top)
    u401 = RHO_SHARP * (1 - RHO_SHARP) * 2 * D("1.03973") / 400
    tail = (CD_MAX / 2 * u401 / ((1 - u401) * LN2)).lt(Bs[top])
    cert_true("v3-A6-p236", top == 236 and others and tail, "at c_D = 9e-3 the p >= 80 maximizing B is p = 236",
              "p <= 400 directly; p > 400 by B < (c_D/2) log2(1/Theta#_{phi_p}) <= (c_D/2) U(401)")
    cert_cmp("v3-A6-1pct", Bs[236] / B6, "<", D("1.01"), "B(236)/B(247) < 1.01 (raises B by less than 1%)")


def group9_misc() -> None:
    print("[9] Other numerical steps quoted in the paper (Sections 2.3, 9, 14.2, 14.5; unchanged since r6 except 14.2)")
    cert_cmp("x-l25-1.1", log2((RHO + D("0.05")) / (1 - RHO - D("0.05"))), "<=", D("1.1"),
             "Lemma lower (ii): |H'| <= 1.1 on (rho_c, rho_c + 0.05]")
    th = cf.theta(D("0.5"), RHO)
    cert_value("x-s9-0.767", th, "0.767", "nearest", "Theta_1/2(rho_c)")
    cert_value("x-s9-0.19", -log2(th) / 2, "0.19", "nearest", "delta'_H ~ 0.19 (s/q - 1)")
    cert_value("x-s9-0.096", -log2(th) / 4, "0.096", "nearest", "s/q = 1.5")
    cert_true("v3-allshells-sum", Fraction(1, 2) + 3 * Fraction(1, 8) < 1,
              "2^(-delta'q-1) + 3 2^(-delta'q-3) < 2^(-delta'q) (exact)", "Proposition allshells, step 4")
    cert_cmp("x-lmn-0.911", 1 / LN3, "<=", D("0.911"), "Lemma Bk: k/ln 3 <= 0.911 k")
    cert_cmp("x-lmn-0.631", LN2 / LN3, "<=", D("0.631"), "o < k log_3 2 <= 0.631 k")
    cert_cmp("x-lmn-sum", D("0.911") + D("0.631"), "<=", 2, "b' <= 2k")
    cert_value("x-lmn-33.95", LN3 * D("30.9"), "33.95")
    cert_cmp("x-lmn-34", LN3 * D("30.9"), "<", 34)
    cert_cmp("x-lmn-27", LN3 * D("24.34"), "<", 27, "Corollaire 2 variant")
    cert_cmp("x-lmn-Gamma", LN2, "<=", 1, "Gamma <= ln 2 <= 1")


def main() -> int:
    t0 = time.time()
    print(f"Certified recomputation of the M1 constants, v3 (interval arithmetic, {cf.PREC}-bit dyadic endpoints)")
    fails = cf.selftest()
    if fails:
        print("SELF-TEST FAILED:", fails[:10])
        return 1
    print(f"  self-test of the interval library (proof_pf_certified.py): passed ({time.time() - t0:.1f} s)")
    print("  ln 2   =", LN2.fmt(36))
    print("  ln 3   =", LN3.fmt(36))
    print("  log2 3 =", LAM.fmt(36))
    print("[1] (reused from proof_pf_certified.py, unchanged since revision r6)")
    cf.group1_basic()
    group2_thmA()
    print("[3] Theorem 2 of Bugeaud (Sections 13.1-13.3, Appendix A.3; the route of the remark thm2route)"
          " (reused from proof_pf_certified.py, unchanged since revision r6)")
    cf.group3_bugeaud()
    group4_thm1()
    info = group5_rules()
    print("[6] (reused from proof_pf_certified.py) Lemma rules (a) and (c) hold for every p >= 80, independently of c_D")
    cf.group4_grids()
    group6_cover()
    group6_active()
    group7_thresholds(info["d6"], info["k6"])
    group8_eps(info["B6"], info["d6"], info["bstar"], info["alpha_star"])
    group8b_room(info["B6"])
    group9_misc()
    results = cf.RESULTS
    n_fail = sum(1 for _, ok in results if not ok)
    n_pass = len(results) - n_fail
    names = [n for n, _ in results]
    dup = sorted({n for n in names if names.count(n) > 1})
    if dup:
        print("\nWARNING: duplicate claim identifiers:", ", ".join(dup))
    if n_fail:
        print("\nFAIL:", ", ".join(n for n, ok in results if not ok))
    verdict = "all PASS" if not n_fail else f"{n_pass} PASS, {n_fail} FAIL"
    print(f"\nSUMMARY: {len(results)} numerical claims of the M1 proof (v3 constants, paper revision r7) checked with"
          f" rigorous interval arithmetic ({cf.PREC}-bit dyadic endpoints, Python standard library): {verdict}"
          f" ({time.time() - t0:.0f} s).")
    return 1 if n_fail or dup else 0


if __name__ == "__main__":
    sys.exit(main())
