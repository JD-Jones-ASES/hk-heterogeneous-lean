#!/usr/bin/env python3
"""check_hk.py -- exact replay of the heterogeneous Hegselmann-Krause systems of this repository
under the SBC / SBI models of Mirtabatabaei-Bullo (arXiv:1103.2829v2, eq. (2.1)): the six systems
of Hegarty-Ognissanti-Wedin (arXiv:2610.03229v1, sections 2-5) and the two smaller
constant-digraph systems stated in Challenge.lean (five SBC agents, six SBI agents).

Standard library only (python >= 3.9), one process, exact arithmetic throughout: rationals are
fractions.Fraction and numbers of Q(sqrt d) (d = 2, 5, 249 here) are pairs (a, b) meaning
a + b*sqrt d, compared by exact sign tests. Floats appear only in display strings, never in a
check. No assert statements: every check appends to an explicit failure list.

What it checks (agents 0-indexed: the paper's agent i is index i-1):
  1. replay x(t+1) = A(x(t)) x(t) for t < T (default 60) from each system's initial data, and at
     every step: the closed form, the full neighbourhood table against the expected (pinned)
     table for the parity of t, and that no pair sits on a boundary (|x_i - x_j| != R exactly for
     every i != j and R in {r_i, r_j});
  2. the inductive step for all t: positions are affine in the atoms (u = lambda^t, and
     w = 5^-t or 4^-t for the spectator systems); every membership inequality is shown to have a
     constant strict sign on the stated atom boxes (exact corner test), the update identities
     (mean of x_inf over each row equals x_inf_i; mean of each offset vector equals rate * entry)
     hold exactly, and u -> lambda*u carries each parity box into the other;
  3. the equi-topology distances (MB Def 4.1) at the limits;
  4. the per-step convergence factors (MB Def 6.1) of the four constant-digraph systems for
     t = 0..5, with fvct(x(t)) certified by A(x(t)) x_inf = x_inf and A(x(t)) v = lambda v;
  5. forged controls that must FAIL.
The last line printed is VERDICT: PASS or VERDICT: FAIL (exit code 0 / 1).

Options: --T=N replays N steps; --explore adds report-only widest-interval tables. Setting the
environment variable HK_KILL to a file path makes every loop stop (and the verdict FAIL) as soon
as that file exists; unset, no stop file is consulted.
"""
import os
import sys
import time
from fractions import Fraction as Fr
from itertools import product
from math import isqrt

KILL = os.environ.get("HK_KILL", "")


def killed():
    return bool(KILL) and os.path.exists(KILL)


# ---------------------------------------------------------------- Q(sqrt d), exact
class QD:
    """a + b*sqrt(d) with a, b rational and d a positive non-square integer; d is None for a
    rational (b == 0), which combines with any field."""
    __slots__ = ("a", "b", "d")

    def __init__(self, a, b=0, d=None):
        self.a = a if type(a) is Fr else Fr(a)
        self.b = b if type(b) is Fr else Fr(b)
        if self.b == 0:
            d = None
        elif d is None or d < 2 or isqrt(d) ** 2 == d:
            raise ValueError("QD needs a positive non-square d when b != 0")
        self.d = d

    def _field(s, o):
        if s.d is None:
            return o.d
        if o.d is None or o.d == s.d:
            return s.d
        raise ValueError("QD: mixing Q(sqrt %d) and Q(sqrt %d)" % (s.d, o.d))

    def __add__(s, o):
        o = q(o)
        return QD(s.a + o.a, s.b + o.b, s._field(o))

    __radd__ = __add__

    def __sub__(s, o):
        o = q(o)
        return QD(s.a - o.a, s.b - o.b, s._field(o))

    def __rsub__(s, o):
        return q(o) - s

    def __neg__(s):
        return QD(-s.a, -s.b, s.d)

    def __mul__(s, o):
        o = q(o)
        d = s._field(o)
        dd = d if d is not None else 0
        return QD(s.a * o.a + dd * s.b * o.b, s.a * o.b + s.b * o.a, d)

    __rmul__ = __mul__

    def inv(s):
        dd = s.d if s.d is not None else 0
        nrm = s.a * s.a - dd * s.b * s.b  # nonzero for s != 0 since sqrt d is irrational
        if nrm == 0:
            raise ZeroDivisionError("QD inverse of zero")
        return QD(s.a / nrm, -s.b / nrm, s.d)

    def __truediv__(s, o):
        return s * q(o).inv()

    def __rtruediv__(s, o):
        return q(o) * s.inv()

    def sign(s):
        a, b = s.a, s.b
        if b == 0:
            return (a > 0) - (a < 0)
        if a == 0:
            return (b > 0) - (b < 0)
        if a > 0 and b > 0:
            return 1
        if a < 0 and b < 0:
            return -1
        n = a * a - s.d * b * b  # sign of |a| - |b| sqrt d
        if a > 0:  # b < 0
            return (n > 0) - (n < 0)
        return (n < 0) - (n > 0)  # a < 0 < b

    def __eq__(s, o):
        o = q(o)
        return s.a == o.a and s.b == o.b and (s.b == 0 or s.d == o.d)

    def __ne__(s, o):
        return not s.__eq__(o)

    def __hash__(s):
        return hash((s.a, s.b, s.d))

    def __lt__(s, o):
        return (s - o).sign() < 0

    def __le__(s, o):
        return (s - o).sign() <= 0

    def __gt__(s, o):
        return (s - o).sign() > 0

    def __ge__(s, o):
        return (s - o).sign() >= 0

    def __abs__(s):
        return -s if s.sign() < 0 else s

    def approx(s):  # display only
        return float(s.a) + (float(s.b) * s.d ** 0.5 if s.d else 0.0)

    def __repr__(s):
        if s.b == 0:
            return str(s.a)
        if s.a == 0:
            return "%s*sqrt%d" % (s.b, s.d)
        return "(%s %s %s*sqrt%d)" % (s.a, "+" if s.b > 0 else "-", abs(s.b), s.d)


def q(x):
    return x if isinstance(x, QD) else QD(x)


def vec(*xs):
    return [q(x) for x in xs]


SQRT2 = QD(0, 1, 2)
SQRT5 = QD(0, 1, 5)
SQRT249 = QD(0, 1, 249)
PHI = (1 + SQRT5) / 2                 # golden ratio
LAM = (1 - SQRT5) / 8                 # (1 - sqrt5)/8, the rate of the SBI systems of HOW
XI = q(Fr(-1, 6))                     # -1/6, the rate of the SBC systems of HOW
PHI_INV = PHI - 1                     # 1/phi
RATE5 = (1 - SQRT2) / 3               # the five-agent SBC system
RATE6 = (13 - SQRT249) / 40           # the six-agent SBI system


# ---------------------------------------------------------------- the systems
def S(name, model, r, x0, lim, terms, even, odd, odd_lo):
    return dict(name=name, model=model, r=r, x0=x0, lim=lim, terms=terms,
                tables={0: [frozenset(s) for s in even], 1: [frozenset(s) for s in odd]},
                odd_lo=odd_lo)


def systems():
    half = Fr(1, 2)
    v_sbi = vec(0, 1, -PHI, 0, PHI, -1, 0)
    a_even = [{0}, {0, 1, 2}, {1, 2, 3, 4}, {3}, {2, 3, 4, 5}, {4, 5, 6}, {6}]
    a_odd = [{0}, {0, 1, 2}, {1, 2, 3, 4}, {2, 3, 4}, {2, 3, 4, 5}, {4, 5, 6}, {6}]
    b_even = [{0}, {0, 1, 2, 3}, {1, 2, 3, 4}, {1, 2, 3, 4, 5}, {2, 3, 4, 5}, {3, 4, 5, 6}, {6}]
    b_odd = [{0}, {0, 1, 2, 3}, {1, 2, 3, 4}, {2, 3, 4}, {2, 3, 4, 5}, {3, 4, 5, 6}, {6}]
    c_tab = [{0}, {0, 1, 2}, {0, 1, 2, 3}, {2, 3, 4, 5}, {3, 4, 5}, {5}]
    d_tab = [{0}, {0, 1, 2, 3}, {1, 2, 3, 4}, {2, 3, 4}, {2, 3, 4, 5}, {3, 4, 5, 6}, {6}]
    e_tab = c_tab + [{4, 5, 6, 7, 8}, {7}, {8}]
    f_tab = [{0}, {0, 1, 2, 4}, {0, 2, 3, 4}, {2, 3, 4, 5}, {3, 4, 5}, {3, 4, 5, 6},
             {4, 5, 6, 7}, {7}]
    s5_tab = [{0}, {0, 1, 2}, {1, 2, 3}, {2, 3, 4}, {4}]
    s6_tab = [{0}, {0, 1, 2, 3}, {0, 1, 2, 3, 4}, {0, 2, 3, 4, 5}, {2, 3, 4, 5}, {5}]
    return [
        S("sbc7", "sbc", vec(18, 42, 48, 12, 48, 42, 18), vec(0, 38, 69, 84, 99, 130, 168),
          vec(0, 36, 72, 84, 96, 132, 168), [(XI, vec(0, 2, -3, 0, 3, -2, 0))],
          a_even, a_odd, XI),
        S("sbi7", "sbi", vec(8, 4, 4, 8, 4, 4, 8),
          vec(0, Fr(15, 2), 10 - PHI * half, 11, 12 + PHI * half, Fr(29, 2), 22),
          vec(0, 7, 10, 11, 12, 15, 22), [(LAM, [x * half for x in v_sbi])],
          b_even, b_odd, LAM),
        S("sbc6", "sbc", vec(10, 70, 70, 70, 70, 10), vec(0, 22, 37, 103, 118, 140),
          vec(0, 20, 40, 100, 120, 140), [(XI, vec(0, 2, -3, 3, -2, 0))], c_tab, c_tab, XI),
        S("sbi7b", "sbi", vec(85, 35, 35, 75, 35, 35, 85),
          vec(0, 71, 100 - PHI, 110, 120 + PHI, 149, 220),
          vec(0, 70, 100, 110, 120, 150, 220), [(LAM, v_sbi)], d_tab, d_tab, LAM),
        S("sbc9", "sbc", vec(10, 70, 70, 70, 70, 10, 100, 10, 10),
          vec(0, 22, 37, 103, 118, 140, 210, 280, 300),
          vec(0, 20, 40, 100, 120, 140, 210, 280, 300),
          [(XI, vec(0, 2, -3, 3, -2, 0, Fr(12, 11), 0, 0)),
           (q(Fr(1, 5)), vec(0, 0, 0, 0, 0, 0, Fr(-12, 11), 0, 0))], e_tab, e_tab, XI),
        S("sbi8", "sbi", vec(85, 1, 35, 35, 75, 35, 35, 85),
          vec(0, 60, 71, 100 - PHI, 110, 120 + PHI, 149, 220),
          vec(0, 60, 70, 100, 110, 120, 150, 220),
          [(LAM, vec(0, -PHI_INV, 1, -PHI, 0, PHI, -1, 0)),
           (q(Fr(1, 4)), vec(0, PHI_INV, 0, 0, 0, 0, 0, 0))], f_tab, f_tab, LAM),
        S("sbc5", "sbc", vec(3, 9, 9, 9, 3), vec(0, 7, 12 - SQRT2, 19, 24),
          vec(0, 6, 12, 18, 24), [(RATE5, vec(0, 1, -SQRT2, 1, 0))], s5_tab, s5_tab, RATE5),
        S("sbi6", "sbi", vec(45, 18, 27, Fr(45, 2), 27, 54),
          vec(0, 25 + Fr(10, 16), 31 + (-5 - SQRT249) / 16, 44 + Fr(8, 16), 55 + Fr(10, 16), 90),
          vec(0, 25, 31, 44, 55, 90),
          [(RATE6, vec(0, Fr(10, 16), (-5 - SQRT249) / 16, Fr(8, 16), Fr(10, 16), 0))],
          s6_tab, s6_tab, RATE6),
    ]


def by_name(syss):
    return {sd["name"]: sd for sd in syss}


def table_from_arcs(n, arcs1):
    """HOW's arc lists are 1-indexed, self-loops implicit; (i, j) = i listens to j."""
    t = [{i} for i in range(n)]
    for (i, j) in arcs1:
        t[i - 1].add(j - 1)
    return [frozenset(s) for s in t]


HOW_ARCS_C = [(2, 1), (3, 1), (3, 2), (2, 3), (4, 3), (3, 4), (5, 4), (4, 5), (4, 6), (5, 6)]
HOW_ARCS_D = [(2, 1), (3, 2), (2, 3), (4, 3), (5, 3), (2, 4), (3, 4), (5, 4), (6, 4), (3, 5),
              (4, 5), (6, 5), (5, 6), (6, 7)]


# ---------------------------------------------------------------- the model, MB (2.1)
def bound(model, r, i, j):
    return r[i] if model == "sbc" else r[j]


def neighbours(model, r, x):
    n = len(x)
    tab, ties = [], []
    for i in range(n):
        s = set()
        for j in range(n):
            d = abs(x[i] - x[j])
            if (d - bound(model, r, i, j)).sign() <= 0:
                s.add(j)
            if j != i:
                for R in (r[i], r[j]):
                    if (d - R).sign() == 0:
                        ties.append((i, j, R))
        tab.append(frozenset(s))
    return tab, ties


def step(x, tab):
    return [sum((x[j] for j in sorted(tab[i])), q(0)) / len(tab[i]) for i in range(len(x))]


def fmt_tab(tab):
    return "[" + ", ".join("{" + ",".join(str(j) for j in sorted(s)) + "}" for s in tab) + "]"


# ---------------------------------------------------------------- 1. replay
def replay(sysd, T):
    fails = []
    x = list(sysd["x0"])
    powers = [q(1) for _ in sysd["terms"]]
    seen = {0: set(), 1: set()}
    for t in range(T):
        if killed():
            fails.append("stop file present: stopped at t=%d" % t)
            return fails, seen
        cf = [sysd["lim"][i] + sum((powers[k] * sysd["terms"][k][1][i]
                                    for k in range(len(powers))), q(0)) for i in range(len(x))]
        if any(x[i] != cf[i] for i in range(len(x))):
            fails.append("%s t=%d: closed form differs from replay" % (sysd["name"], t))
            return fails, seen
        tab, ties = neighbours(sysd["model"], sysd["r"], x)
        seen[t % 2].add(tuple(tab))
        if ties:
            fails.append("%s t=%d: boundary ties %s" % (sysd["name"], t, ties[:3]))
        exp = sysd["tables"][t % 2]
        if tab != exp:
            fails.append("%s t=%d: table %s != expected %s" % (sysd["name"], t, fmt_tab(tab),
                                                              fmt_tab(exp)))
            return fails, seen
        x = step(x, tab)
        powers = [powers[k] * sysd["terms"][k][0] for k in range(len(powers))]
    return fails, seen


# ---------------------------------------------------------------- 2. inductive step on atom boxes
def affine_forms(sysd, i, j):
    """p_i - p_j - R <= 0 and -(p_i - p_j) - R <= 0, each as (const, [coef per atom])."""
    R = bound(sysd["model"], sysd["r"], i, j)
    dL = sysd["lim"][i] - sysd["lim"][j]
    dV = [V[i] - V[j] for (_, V) in sysd["terms"]]
    return (dL - R, dV), (-dL - R, [-c for c in dV])


def strict_on_box(f, box, s):
    """Sufficient exact test that s*f > 0 on the box. box: per atom (lo, lo_closed, hi, hi_closed),
    each atom interval with at least one closed end. s*f >= 0 at every corner of the closure and
    s*f > 0 at every corner that lies in the box imply s*f > 0 on the box (f affine)."""
    c0, cs = f
    for corner in product(*[((lo, lc), (hi, hc)) for (lo, lc, hi, hc) in box]):
        val = c0 + sum((cs[k] * corner[k][0] for k in range(len(cs))), q(0))
        sg = s * val.sign()
        if sg < 0:
            return False
        if sg == 0 and all(c[1] for c in corner):
            return False
    return True


def table_on_box(sysd, tab, box):
    bad = []
    n = len(sysd["x0"])
    for i in range(n):
        for j in range(n):
            f1, f2 = affine_forms(sysd, i, j)
            if j in tab[i]:
                ok = strict_on_box(f1, box, -1) and strict_on_box(f2, box, -1)
            else:
                ok = strict_on_box(f1, box, 1) or strict_on_box(f2, box, 1)
            if not ok:
                bad.append((i, j))
    return bad


def update_identities(sysd, tab):
    bad = []
    for i, row in enumerate(tab):
        m = len(row)
        if sum((sysd["lim"][j] for j in row), q(0)) / m != sysd["lim"][i]:
            bad.append((i, "limit"))
        for (rate, V) in sysd["terms"]:
            if sum((V[j] for j in row), q(0)) / m != rate * V[i]:
                bad.append((i, "offset rate %r" % (rate,)))
    return bad


def table_at_atoms(sysd, atoms):
    x = [sysd["lim"][i] + sum((atoms[k] * sysd["terms"][k][1][i] for k in range(len(atoms))),
                              q(0)) for i in range(len(sysd["x0"]))]
    return neighbours(sysd["model"], sysd["r"], x)[0]


def widest(sysd, side):
    """Single atom u: the widest interval from 0 towards sign `side` on which the table is
    constant. Returns (table near 0, endpoint or None, 'open'/'closed'/'unbounded')."""
    n = len(sysd["x0"])
    roots = set()
    for i in range(n):
        for j in range(n):
            for (c0, cs) in affine_forms(sysd, i, j):
                if cs[0].sign() != 0:
                    u = -c0 / cs[0]
                    if u.sign() == side:
                        roots.add(u)
    roots = sorted(roots, key=lambda u: side * u)
    first = roots[0] if roots else q(side)
    t0 = table_at_atoms(sysd, [first * Fr(1, 2)])
    for k, b in enumerate(roots):
        if table_at_atoms(sysd, [b]) != t0:
            return t0, b, "open"
        nxt = roots[k + 1] if k + 1 < len(roots) else b * 2
        if table_at_atoms(sysd, [(b + nxt) * Fr(1, 2)]) != t0:
            return t0, b, "closed"
    return t0, None, "unbounded"


# ---------------------------------------------------------------- 3, 4. epsilon and factors
def eps_vector(r, z):
    n = len(z)
    out = []
    for i in range(n):
        vals = [abs(abs(z[i] - z[j]) - R) for j in range(n) if j != i for R in (r[i], r[j])]
        m = vals[0]
        for v in vals[1:]:
            if v < m:
                m = v
        out.append(m * Fr(1, 2))
    return out


def per_step_factors(sysd, tmax):
    """MB Def 6.1 with fvct(x(t)) certified as x_inf: A(x(t)) x_inf = x_inf and
    A(x(t)) v = lambda v with |lambda| < 1 give A(x(t))^s x(t) = x_inf + lambda^(t+s) v -> x_inf."""
    fails, rows = [], []
    rate, V = sysd["terms"][0]
    if not (abs(rate) < 1):
        fails.append("%s: rate not below 1 in absolute value" % sysd["name"])
    x = list(sysd["x0"])
    L = sysd["lim"]
    for t in range(tmax + 1):
        if killed():
            fails.append("stop file present")
            return fails, rows
        tab, _ = neighbours(sysd["model"], sysd["r"], x)
        if step(L, tab) != L:
            fails.append("%s t=%d: A(x(t)) x_inf != x_inf" % (sysd["name"], t))
        if step(V, tab) != [rate * c for c in V]:
            fails.append("%s t=%d: A(x(t)) v != lambda v" % (sysd["name"], t))
        xn = step(x, tab)
        ks = []
        for i in range(len(x)):
            num, den = xn[i] - L[i], x[i] - L[i]
            if den.sign() == 0:
                ks.append("0/0" if num.sign() == 0 else "x/0")
            else:
                ks.append(num / den)
        rows.append(ks)
        x = xn
    return fails, rows


# ---------------------------------------------------------------- the boxes
def boxes_of(sd):
    one, zero = q(1), q(0)
    lo = sd["odd_lo"]
    if len(sd["terms"]) == 1:
        return ({0: [(zero, False, one, True)], 1: [(lo, True, zero, False)]},
                {0: "u in (0,1]", 1: "u in [%r,0)" % (lo,)})
    return ({0: [(zero, False, one, True), (zero, False, one, True)],
             1: [(lo, True, zero, False), (zero, False, one, True)]},
            {0: "u in (0,1], w in (0,1]", 1: "u in [%r,0), w in (0,1]" % (lo,)})


def box_failures(sd):
    """The inductive step: both parity tables constant on their boxes, the update identities, and
    the boxes carried into each other by the rates (u -> rate*u maps (0,1] onto [rate,0) and
    [rate,0) onto (0,rate^2] inside (0,1]; w -> w*rate2 keeps (0,1]; u = w = 1 at t = 0)."""
    fails, lines = [], []
    boxes, desc = boxes_of(sd)
    for p in (0, 1):
        bad = table_on_box(sd, sd["tables"][p], boxes[p])
        ids = update_identities(sd, sd["tables"][p])
        if bad:
            fails.append("%s parity %d: table not constant on %s at pairs %s" % (
                sd["name"], p, desc[p], bad[:5]))
        if ids:
            fails.append("%s parity %d: update identities fail %s" % (sd["name"], p, ids))
        lines.append("box %-6s %s: %s; identities %s" % (
            sd["name"], desc[p], "table constant" if not bad else "FAIL %s" % bad[:4],
            "exact" if not ids else "FAIL"))
    rate = sd["terms"][0][0]
    if not (rate.sign() < 0 and rate == sd["odd_lo"] and rate * rate <= 1):
        fails.append("%s: the u-boxes are not carried into each other" % sd["name"])
    for (rate2, _) in sd["terms"][1:]:
        if not (rate2.sign() > 0 and rate2 <= 1):
            fails.append("%s: the w-box is not invariant" % sd["name"])
    return fails, lines


# ---------------------------------------------------------------- driver
ALTERNATING = ("sbc7", "sbi7")
CONSTANT_DIGRAPH = ("sbc6", "sbi7b", "sbc5", "sbi6")
# MB Def 4.1 at the limits: the pinned zero sets of the alternating systems, and positivity at the
# limits of the constant-digraph systems.
PINNED_EPS_ZERO = {"sbc7": {2, 3, 4}, "sbi7": {1, 3, 5}, "sbc6": set(), "sbi7b": set(),
                   "sbc5": set(), "sbi6": set()}
# The agents whose per-step factor is the rate (every other agent sits at its limit).
PINNED_FACTOR = {"sbc6": {1, 2, 3, 4}, "sbi7b": {1, 2, 4, 5}, "sbc5": {1, 2, 3},
                 "sbi6": {1, 2, 3, 4}}


def run_genuine(T, out):
    fails = []
    syss = systems()
    B = by_name(syss)
    t0 = time.time()
    for sd in syss:
        f, seen = replay(sd, T)
        fails += f
        out.append("replay %-6s t<%d: %s; even tables seen %d, odd tables seen %d" % (
            sd["name"], T, "ok" if not f else "FAIL", len(seen[0]), len(seen[1])))
        for p in (0, 1):
            out.append("   %s table: %s" % ("even" if p == 0 else "odd ", fmt_tab(sd["tables"][p])))
    out.append("time replay: %.2fs" % (time.time() - t0))

    # alternation and constancy as data
    for sd in syss:
        alt = sd["tables"][0] != sd["tables"][1]
        if alt != (sd["name"] in ALTERNATING):
            fails.append("%s: alternation expected %s" % (sd["name"], sd["name"] in ALTERNATING))
        if alt:
            diff = [i for i in range(len(sd["x0"])) if sd["tables"][0][i] != sd["tables"][1][i]]
            out.append("%s: tables differ exactly at rows %s" % (sd["name"], diff))

    # HOW's arc lists (sections 4 and 5) and the spectator claims
    if table_from_arcs(6, HOW_ARCS_C) != B["sbc6"]["tables"][0]:
        fails.append("sbc6: HOW section 4 arc list != table")
    if table_from_arcs(7, HOW_ARCS_D) != B["sbi7b"]["tables"][0]:
        fails.append("sbi7b: HOW section 5 arc list != table")
    e_t = B["sbc9"]["tables"][0]
    if not (all(e_t[i] <= frozenset(range(6)) for i in range(6)) and e_t[7] == {7} and
            e_t[8] == {8} and e_t[6] == {4, 5, 6, 7, 8} and e_t[:6] == B["sbc6"]["tables"][0]):
        fails.append("sbc9: HOW section 4 Claim 1 fails")
    f_t = B["sbi8"]["tables"][0]
    if not (f_t[1] == {0, 1, 2, 4} and all(1 not in f_t[i] for i in range(8) if i != 1)):
        fails.append("sbi8: HOW section 5 Claim 1 fails")
    shift = lambda s: frozenset(0 if j == 0 else j + 1 for j in s)
    d_t = B["sbi7b"]["tables"][0]
    if [f_t[0]] + f_t[2:] != [shift(d_t[0])] + [shift(d_t[k]) for k in range(1, 7)]:
        fails.append("sbi8: rows other than the spectator are not section 5's shifted")
    out.append("HOW arc lists (s4, s5) and Claim 1 of both spectator systems: compared")

    # spectator sides (HOW Claim 3 consequences), exact over the replay horizon
    t1 = time.time()
    for t in range(1, T):
        if killed():
            fails.append("stop file present")
            break
        e7 = Fr(12, 11) * ((Fr(-1, 6)) ** t - Fr(1, 5) ** t)
        if not e7 < 0:
            fails.append("sbc9 t=%d: spectator not left of 210" % t)
        lt = q(1)
        for _ in range(t):
            lt = lt * LAM
        f2 = PHI_INV * (q(Fr(1, 4) ** t) - lt)
        if not f2.sign() > 0:
            fails.append("sbi8 t=%d: spectator not right of 60" % t)
    out.append("spectators: sbc9 strictly left of 210, sbi8 strictly right of 60, 1 <= t < %d" % T)

    # 2. boxes, identities, closure
    for sd in syss:
        f, lines = box_failures(sd)
        fails += f
        out += lines
    out.append("induction closure: rate*(0,1] = [rate,0), rate*[rate,0) in (0,1], w-rate in (0,1]: "
               "checked for all %d systems" % len(syss))
    out.append("time boxes+identities: %.2fs" % (time.time() - t1))
    return fails, syss


def explore(syss, out):
    """Report-only: widest u-intervals and looser boxes (no verdict depends on these)."""
    one, zero = q(1), q(0)
    for sd in syss:
        if len(sd["terms"]) == 1:
            for side in (1, -1):
                t0, b, kind = widest(sd, side)
                which = [p for p in (0, 1) if sd["tables"][p] == t0]
                if b is None:
                    rng = "u %s 0, unbounded" % (">" if side > 0 else "<")
                elif side > 0:
                    rng = "u in (0, %r%s  (~%.6f)" % (b, "]" if kind == "closed" else ")", b.approx())
                else:
                    rng = "u in %s%r, 0)  (~%.6f)" % ("[" if kind == "closed" else "(", b, b.approx())
                out.append("widest %-6s side %+d: table of parity %s holds for %s" % (
                    sd["name"], side, which, rng))
            out.append("   table at u = 0 (the limit itself): %s" %
                       fmt_tab(table_at_atoms(sd, [zero])))
        boxes = {"u in [-1,1], w in (0,1]": [(-one, True, one, True), (zero, False, one, True)],
                 "u in [-1,1], w in [0,1]": [(-one, True, one, True), (zero, True, one, True)]}
        for nm, bx in boxes.items():
            bx = bx[:len(sd["terms"])]
            if len(sd["terms"]) == 1 and nm.endswith("[0,1]"):
                continue
            bad = table_on_box(sd, sd["tables"][0], bx)
            out.append("loose box %-6s %s (even table): %s" % (
                sd["name"], nm.split(",")[0] if len(sd["terms"]) == 1 else nm,
                "constant" if not bad else "not certified, pairs %s" % bad[:6]))


def factor_failures(sd, out):
    fails, rows = per_step_factors(sd, 5)
    rate = sd["terms"][0][0]
    for t, ks in enumerate(rows):
        out.append("k(t=%d) %-6s = %s" % (t, sd["name"], ks))
        got = {i for i, k in enumerate(ks) if isinstance(k, QD) and k == rate}
        fixed = {i for i, k in enumerate(ks) if isinstance(k, str) and k == "0/0"}
        if got != PINNED_FACTOR[sd["name"]] or len(got) + len(fixed) != len(ks):
            fails.append("%s t=%d: factor set %s, fixed %s" % (sd["name"], t, got, fixed))
    if not fails:
        out.append("fvct(x(t)) = x_inf certified for %s, t=0..5 (eigen-identities exact)" %
                   sd["name"])
    return fails


def run_eps_factors(syss, out):
    fails = []
    for sd in syss:
        if sd["name"] not in PINNED_EPS_ZERO:
            continue
        e = eps_vector(sd["r"], sd["lim"])
        zeros = {i for i, v in enumerate(e) if v.sign() == 0}
        out.append("eps(x_inf) %-6s = %s ; zero at %s" % (sd["name"], e, sorted(zeros)))
        if zeros != PINNED_EPS_ZERO[sd["name"]]:
            fails.append("%s: eps zero set %s, pinned %s" % (sd["name"], sorted(zeros),
                                                            sorted(PINNED_EPS_ZERO[sd["name"]])))
    for sd in syss:
        if sd["name"] in CONSTANT_DIGRAPH:
            fails += factor_failures(sd, out)
    return fails


def forged(T):
    """Controls that must FAIL; each names the one check that has to reject it."""
    res = []
    one, zero = q(1), q(0)
    B = by_name(systems())
    sd = B["sbc7"]
    sd["x0"] = list(sd["x0"])
    sd["x0"][1] = sd["x0"][1] + 1  # 38 -> 39
    res.append(("replay: x0 of sbc7 with 38 -> 39", replay(sd, T)[0]))
    sd = by_name(systems())["sbc7"]
    ev, od = list(sd["tables"][0]), list(sd["tables"][1])
    ev[3], od[3] = od[3], ev[3]
    sd["tables"] = {0: ev, 1: od}
    res.append(("replay: sbc7 row 3 with the parities swapped", replay(sd, T)[0]))
    res.append(("even box: the swapped even table on u in (0,1]",
                table_on_box(sd, ev, [(zero, False, one, True)])))
    res.append(("odd box: the swapped odd table on u in [-1/6,0)",
                table_on_box(sd, od, [(XI, True, zero, False)])))
    sd = by_name(systems())["sbc7"]
    sd["r"] = list(sd["r"])
    sd["r"][3] = q(13)  # the middle agent's radius 12 -> 13
    res.append(("replay: sbc7 with r_3 = 13", replay(sd, T)[0]))
    sd = by_name(systems())["sbc6"]
    sd["r"] = list(sd["r"])
    sd["r"][0] = q(22)  # agent 0 at 0, agent 1 at 22: a boundary tie at t = 0
    res.append(("tie detector: sbc6 with r_0 = 22", [x for x in replay(sd, 1)[0] if "ties" in x]))
    sd = by_name(systems())["sbc6"]
    sd["terms"] = [(q(Fr(-1, 5)), sd["terms"][0][1])]
    res.append(("update identities: sbc6 with rate -1/5", update_identities(sd, sd["tables"][0])))
    # the five-agent SBC system: the conjugate initial opinion 12 + sqrt2 for agent 2
    sd = by_name(systems())["sbc5"]
    sd["x0"] = list(sd["x0"])
    sd["x0"][2] = 12 + SQRT2
    res.append(("replay: sbc5 with x0_2 = 12 + sqrt2", replay(sd, T)[0]))
    # the six-agent SBI system: the conjugate rate (13 + sqrt249)/40 on the genuine offsets
    sd = by_name(systems())["sbi6"]
    sd["terms"] = [((13 + SQRT249) / 40, sd["terms"][0][1])]
    sd["odd_lo"] = sd["terms"][0][0]
    res.append(("update identities and box closure: sbi6 with rate (13 + sqrt249)/40",
                box_failures(sd)[0]))
    return res


def main():
    T = 60
    explore_on = False
    for a in sys.argv[1:]:
        if a.startswith("--T="):
            T = int(a[4:])
        if a == "--explore":
            explore_on = True
    start = time.time()
    out = []
    fails, syss = run_genuine(T, out)
    fails += run_eps_factors(syss, out)
    if explore_on:
        t2 = time.time()
        explore(syss, out)
        out.append("time explore: %.2fs" % (time.time() - t2))
    for line in out:
        print(line)
    t3 = time.time()
    ctrl_ok = True
    for name, f in forged(T):
        rejected = len(f) > 0
        ctrl_ok = ctrl_ok and rejected
        print("forged control [%s]: %s%s" % (name, "rejected (FAIL as required)" if rejected
                                             else "ACCEPTED -- checker is blind",
                                             ("; first: " + str(f[0])) if f else ""))
    print("time forged controls: %.2fs" % (time.time() - t3))
    for f in fails:
        print("FAILURE:", f)
    print("genuine failures: %d; total time %.2fs" % (len(fails), time.time() - start))
    ok = (not fails) and ctrl_ok
    print("VERDICT: PASS" if ok else "VERDICT: FAIL")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
