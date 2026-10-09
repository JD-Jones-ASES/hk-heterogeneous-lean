#!/usr/bin/env python3
"""Certificate 0007: replays of the near-homogeneous families of
note/near-homogeneity-and-paths.md.

  (A) section 4, the SBC5 family r(d) = (6-3d, 6+3d, 6+3d, 6+3d, 6-3d), x(0) = L + d v,
      exact in Q(sqrt 2): table, closed form, alternation for t < 200; the near-homogeneity
      witnesses d = min(1/2, eps/4); the exact threshold d* = 6/(3 + sqrt 2).
  (B) section 5, the SBI6 family, exact in Q(sqrt 17), with every distance bullet of the
      section at every step; the note's S2 (not a member) under the same table; the exact
      threshold delta* = 16/(19 + sqrt 17) at t = 0.
  (C) sections 1-3, the SBC path family for n = 5..12 and every admissible k, decimal
      arithmetic at 260 digits under the error budget documented in path_run().
  (D) the near-homogeneity choices of sections 3 and 4, an exact rational scan.

Agents are indexed from 0.  SBC: i hears j iff |x_i - x_j| <= r_i.  SBI: iff |x_i - x_j| <= r_j.
x_i(t+1) is the mean of x_j(t) over N_i(t).  Every neighbourhood is computed from the current
state by these inequalities at every step; the claimed tables and closed forms are compared with
the replay, never used to drive it.

Standard library only.  No assert statements: failures are collected and printed as FAIL lines,
and the exit code is 1.  Every forged control must be rejected.  The last line is the VERDICT.
"""
import math
import sys
import time
from decimal import Decimal as Dec, localcontext
from fractions import Fraction as F

START = time.perf_counter()
FAILS = []


def need(ok, msg):
    if not ok:
        FAILS.append(msg)
    return ok


# --------------------------------------------------------------------------- exact Q(sqrt D)
class QF:
    """a + b sqrt(D) with Fractions a, b and a fixed non-square integer D > 1."""
    __slots__ = ('a', 'b', 'D')

    def __init__(self, a, b=0, D=2):
        self.a = F(a)
        self.b = F(b)
        self.D = D

    def _c(self, o):
        if isinstance(o, QF):
            if o.D != self.D:
                raise ArithmeticError('mixed quadratic fields')
            return o
        return QF(o, 0, self.D)

    def __add__(self, o):
        o = self._c(o)
        return QF(self.a + o.a, self.b + o.b, self.D)
    __radd__ = __add__

    def __neg__(self):
        return QF(-self.a, -self.b, self.D)

    def __sub__(self, o):
        o = self._c(o)
        return QF(self.a - o.a, self.b - o.b, self.D)

    def __rsub__(self, o):
        return self._c(o) - self

    def __mul__(self, o):
        o = self._c(o)
        return QF(self.a * o.a + self.D * self.b * o.b, self.a * o.b + self.b * o.a, self.D)
    __rmul__ = __mul__

    def __truediv__(self, o):
        o = self._c(o)
        n = o.a * o.a - self.D * o.b * o.b
        if n == 0:
            raise ZeroDivisionError('division by zero in Q(sqrt D)')
        return self * QF(o.a / n, -o.b / n, self.D)

    def sign(self):
        """Exact sign: equal-sign parts decide; otherwise compare a^2 with D b^2 in Q."""
        sa = (self.a > 0) - (self.a < 0)
        sb = (self.b > 0) - (self.b < 0)
        if sb == 0:
            return sa
        if sa == 0:
            return sb
        if sa == sb:
            return sa
        c = self.a * self.a - self.D * self.b * self.b
        if c == 0:
            raise ArithmeticError('a^2 = D b^2 with b != 0: D would be a square')
        return sa if c > 0 else sb

    def __eq__(self, o):
        o = self._c(o)
        return self.a == o.a and self.b == o.b

    __hash__ = None

    def abs(self):
        return self if self.sign() >= 0 else -self

    def approx(self):
        """display only; no decision uses it"""
        return float(self.a) + float(self.b) * math.sqrt(self.D)

    def __repr__(self):
        return '(%s) + (%s)*sqrt%d' % (self.a, self.b, self.D)


def fmt(N):
    return [list(row) for row in N]


def nbhd_exact(model, r, x):
    """Neighbourhoods of the state x by the model's inequality, the boundary ties (ordered pairs
    i != j with |x_i - x_j| equal to the bound) and the least |bound - distance| over i != j."""
    n = len(x)
    N, ties, low = [], [], None
    for i in range(n):
        row = []
        for j in range(n):
            bound = r[i] if model == 'SBC' else r[j]
            gap = bound - (x[i] - x[j]).abs()
            s = gap.sign()
            if s >= 0:
                row.append(j)
            if i != j:
                if s == 0:
                    ties.append((i, j))
                g = gap if s >= 0 else -gap
                if low is None or (g - low).sign() < 0:
                    low = g
        N.append(tuple(row))
    return tuple(N), ties, low


def step_exact(N, x):
    zero = QF(0, 0, x[0].D)
    return [sum((x[j] for j in row), zero) * F(1, len(row)) for row in N]


def replay_exact(model, r, L, v, amp, lam, table, T, movers, bullets=None):
    """Replay x(0) = L + amp v by the update rule for t < T.  At every t: no boundary tie, the
    computed neighbourhoods equal the claimed table, the state equals L + amp lam^t v exactly,
    each agent in movers is strictly on the side sign(v_i) (-1)^t of its limit, and the optional
    distance bullets hold.  Returns (failures, least |bound - distance|, steps completed)."""
    fails = []
    n = len(L)
    x = [L[i] + amp * v[i] for i in range(n)]
    u = amp * QF(1, 0, L[0].D)
    low = None
    steps = 0
    for t in range(T):
        N, ties, ms = nbhd_exact(model, r, x)
        if ties:
            fails.append('t=%d: boundary tie(s) %s' % (t, ties))
            break
        if N != table:
            fails.append('t=%d: neighbourhoods %s are not the claimed table' % (t, fmt(N)))
            break
        if low is None or (ms - low).sign() < 0:
            low = ms
        if any(not (x[i] == L[i] + u * v[i]) for i in range(n)):
            fails.append('t=%d: the replayed state is not the closed form' % t)
            break
        par = 1 if t % 2 == 0 else -1
        off = [i for i in movers if v[i].sign() == 0 or (x[i] - L[i]).sign() != par * v[i].sign()]
        if off:
            fails.append('t=%d: agents %s not strictly on the alternating side' % (t, off))
            break
        if bullets is not None:
            bad = bullets(x, u)
            if bad:
                fails.append('t=%d: distance bullets fail: %s' % (t, bad[:4]))
                break
        x = step_exact(N, x)
        u = u * lam
        steps = t + 1
    return fails, low, steps


def row_means(table, L, v, lam):
    out = []
    zero = QF(0, 0, L[0].D)
    for i, row in enumerate(table):
        if not (sum((L[j] for j in row), zero) * F(1, len(row)) == L[i]):
            out.append('row %d: the mean of L is not L_%d' % (i, i))
        if not (sum((v[j] for j in row), zero) * F(1, len(row)) == lam * v[i]):
            out.append('row %d: the mean of v is not lam v_%d' % (i, i))
    return out


# --------------------------------------------------------------------------- (A) SBC5 family
R2 = QF(0, 1, 2)
A_LAM = (1 - R2) * F(1, 3)
A_L = [QF(6 * i) for i in range(5)]
A_V = [QF(0), QF(1), -R2, QF(1), QF(0)]
A_TABLE = ((0,), (0, 1, 2), (1, 2, 3), (2, 3, 4), (4,))
A_BROKEN = ((0,), (0, 1, 2), (0, 1, 2, 3), (2, 3, 4), (4,))   # agent 2 also hears agent 0


def a_radii(d, r1_sign=1):
    d = d if isinstance(d, QF) else QF(d)
    return [6 - 3 * d, 6 + r1_sign * 3 * d, 6 + 3 * d, 6 + 3 * d, 6 - 3 * d]


def family_a(d, T=200, r1_sign=1):
    d = d if isinstance(d, QF) else QF(d)
    return replay_exact('SBC', a_radii(d, r1_sign), A_L, A_V, d, A_LAM, A_TABLE, T, (1, 2, 3))


def section_a():
    print('(A) SBC5 family (section 4), exact in Q(sqrt 2); lam = (1 - sqrt 2)/3, '
          'L = (0,6,12,18,24), v = (0,1,-sqrt2,1,0)')
    need(A_LAM * A_LAM - F(2, 3) * A_LAM - F(1, 9) == 0, 'A: lam is not a root of x^2 - (2/3)x - 1/9')
    need(A_LAM.sign() < 0 and (A_LAM + F(1, 3)).sign() > 0, 'A: lam is not in (-1/3, 0)')
    for msg in row_means(A_TABLE, A_L, A_V, A_LAM):
        need(False, 'A: ' + msg)
    for d in (F(1), F(1, 2), F(1, 10), F(1, 100), F(1, 1000)):
        f, low, steps = family_a(d)
        for msg in f:
            need(False, 'A d=%s: %s' % (d, msg))
        print('  d=%-6s t<200: table, no tie, closed form, agents 1,2,3 alternate: %s'
              '  (least |r - dist| %.4g)' % (d, 'yes' if not f else 'NO', low.approx() if low else -1))
    for eps in (F(1), F(1, 10), F(1, 1000)):
        d = min(F(1, 2), eps / 4)
        r = [6 - 3 * d, 6 + 3 * d, 6 + 3 * d, 6 + 3 * d, 6 - 3 * d]
        ok = (all(q > 0 for q in r) and r[0] < r[1]
              and all(r[i] < (1 + eps) * r[j] for i in range(5) for j in range(5)))
        ratio = max(r) / min(r)
        ok = ok and ratio == (2 + d) / (2 - d) and ratio - 1 == 2 * d / (2 - d) and ratio - 1 <= 2 * d
        need(ok, 'A eps=%s: a radius inequality fails at d=%s' % (eps, d))
        f, low, steps = family_a(d)
        for msg in f:
            need(False, 'A eps=%s, d=%s: %s' % (eps, d, msg))
        print('  eps=%-6s d=%-6s r_i < (1+eps) r_j for all i,j, r > 0, r_0 < r_1: %s; max r/min r = %s;'
              ' replay t<200: %s' % (eps, d, 'yes' if ok else 'NO', ratio, 'yes' if not f else 'NO'))
    dstar = QF(6) / QF(3, 1)
    below, above = F(1699, 1250), F(34, 25)
    need(dstar == QF(F(18, 7), F(-6, 7)), 'A: 6/(3+sqrt2) is not 18/7 - (6/7) sqrt2')
    need((dstar - below).sign() > 0 and (QF(above) - dstar).sign() > 0, 'A: not 1699/1250 < d* < 34/25')
    res = []
    for d, want_N, want_ties in ((QF(below), A_TABLE, []), (dstar, A_BROKEN, [(2, 0)]),
                                 (QF(above), A_BROKEN, [])):
        x0 = [A_L[i] + d * A_V[i] for i in range(5)]
        N, ties, low = nbhd_exact('SBC', a_radii(d), x0)
        need(N == want_N and ties == want_ties,
             'A threshold d=%r, t=0: neighbourhoods %s, ties %s' % (d, fmt(N), ties))
        res.append((fmt(N)[2], ties))
    f, low, steps = family_a(below)
    for msg in f:
        need(False, 'A d=1699/1250: %s' % msg)
    print('  threshold d* = 6/(3+sqrt2) = 18/7 - (6/7)sqrt2 ~ %.10f, 1699/1250 < d* < 34/25' % dstar.approx())
    print('    t=0  d=1699/1250: N_2=%s ties %s (table; full replay t<200: %s)'
          % (res[0][0], res[0][1], 'yes' if not f else 'NO'))
    print('    t=0  d=d*       : N_2=%s ties %s (tie (2,0): agent 2 at distance r_2 from 0)' % res[1])
    print('    t=0  d=34/25    : N_2=%s ties %s (table fails)' % res[2])


# --------------------------------------------------------------------------- (B) SBI6 family
R17 = QF(0, 1, 17)
B_LAM = (3 - R17) * F(1, 8)
B_L = [QF(q, 0, 17) for q in (0, 2, 3, 3, 4, 6)]
B_V = [QF(0, 0, 17), QF(4, 0, 17), 1 - R17, 1 - R17, QF(4, 0, 17), QF(0, 0, 17)]
B_TABLE = ((0,), (0, 1, 2, 3), (1, 2, 3, 4), (1, 2, 3, 4), (2, 3, 4, 5), (5,))


def b_radii(dl):
    dl = QF(dl, 0, 17)
    return [2 + dl, 2 - dl, 2 - dl, 2 - dl, 2 - dl, 2 + dl]


def b_bullets(dl):
    """The distance bullets of section 5 at state x with z = eps lam^t."""
    dl = QF(dl, 0, 17)
    s = R17

    def check(x, z):
        bad = []

        def req(name, ok):
            if not ok:
                bad.append(name)

        def dd(i, j):
            return x[j] - x[i]

        def lt(p, q):
            return (p - q).sign() < 0
        req('|z| <= delta/16', not lt(dl * F(1, 16), z.abs()))
        req('d01 = 2+4z', dd(0, 1) == 2 + 4 * z)
        req('d45 = 2-4z', dd(4, 5) == 2 - 4 * z)
        for nm, p in (('d01', dd(0, 1)), ('d45', dd(4, 5))):
            req(nm + ' in (2-delta, 2+delta)', lt(2 - dl, p) and lt(p, 2 + dl))
        req('d02 = 3-(s-1)z', dd(0, 2) == 3 - (s - 1) * z)
        req('d35 = 3+(s-1)z', dd(3, 5) == 3 + (s - 1) * z)
        for nm, p in (('d02', dd(0, 2)), ('d03', dd(0, 3)), ('d25', dd(2, 5)), ('d35', dd(3, 5))):
            req(nm + ' > 3-delta/4', lt(3 - dl * F(1, 4), p))
        req('3-delta/4 > 2+delta', lt(2 + dl, 3 - dl * F(1, 4)))
        req('d14 = 2', dd(1, 4) == 2)
        req('2 > 2-delta', lt(2 - dl, QF(2, 0, 17)))
        req('d12 = 1-(s+3)z', dd(1, 2) == 1 - (s + 3) * z)
        req('d34 = 1+(s+3)z', dd(3, 4) == 1 + (s + 3) * z)
        for nm, p in (('d12', dd(1, 2)), ('d13', dd(1, 3)), ('d24', dd(2, 4)), ('d34', dd(3, 4))):
            req(nm + ' in (0, 1+delta/2)', p.sign() > 0 and lt(p, 1 + dl * F(1, 2)))
        req('1+delta/2 < 2-delta', lt(1 + dl * F(1, 2), 2 - dl))
        req('d23 = 0', dd(2, 3) == 0)
        for nm, p in (('d04', dd(0, 4)), ('d15', dd(1, 5))):
            req(nm + ' >= 4-delta/4', not lt(p, 4 - dl * F(1, 4)))
        req('4-delta/4 > 2+delta', lt(2 + dl, 4 - dl * F(1, 4)))
        req('d05 = 6', dd(0, 5) == 6)
        return bad
    return check


def family_b(dl, T=200, amp=None, bullets=True):
    amp = dl / 16 if amp is None else amp
    return replay_exact('SBI', b_radii(dl), B_L, B_V, QF(amp, 0, 17), B_LAM, B_TABLE, T, (1, 2, 3, 4),
                        b_bullets(dl) if bullets else None)


def section_b():
    print('(B) SBI6 family (section 5), exact in Q(sqrt 17); s = sqrt17, lam = (3 - s)/8, '
          'L = (0,2,3,3,4,6), v = (0,4,1-s,1-s,4,0)')
    s = R17
    need(B_LAM * B_LAM - F(3, 4) * B_LAM - F(1, 8) == 0, 'B: lam is not a root of x^2 - (3/4)x - 1/8')
    need(B_LAM.sign() < 0 and (B_LAM + 1).sign() > 0, 'B: lam is not in (-1, 0)')
    for msg in row_means(B_TABLE, B_L, B_V, B_LAM):
        need(False, 'B: ' + msg)
    need((4 + 2 * (1 - s)) * F(1, 4) == (3 - s) * F(1, 2) and (3 - s) * F(1, 2) == 4 * B_LAM,
         'B: outer row mean (4+2(1-s))/4 = (3-s)/2 = 4 lam fails')
    need((8 + 2 * (1 - s)) * F(1, 4) == (5 - s) * F(1, 2) and (5 - s) * F(1, 2) == B_LAM * (1 - s),
         'B: clone row mean (4+2(1-s)+4)/4 = (5-s)/2 = lam(1-s) fails')
    need((s + 3) * (-B_LAM) == 1, 'B: (s+3)|lam| = 1 fails')
    print('  lam root of x^2 - (3/4)x - 1/8, in (-1,0); row means of L and v; the two row-mean identities: checked')
    for dl in (F(1, 4), F(1, 10), F(1, 100)):
        f, low, steps = family_b(dl)
        for msg in f:
            need(False, 'B delta=%s: %s' % (dl, msg))
        r = [2 + dl, 2 - dl, 2 - dl, 2 - dl, 2 - dl, 2 + dl]
        ratio = max(r) / min(r)
        need(ratio == (2 + dl) / (2 - dl) and min(r) > 0, 'B delta=%s: radius ratio' % dl)
        print('  delta=%-5s eps=delta/16 t<200: table, no tie, closed form, agents 1-4 alternate, every'
              ' section-5 bullet: %s; ratio (2+d)/(2-d) = %s (least |r - dist| %.4g)'
              % (dl, 'yes' if not f else 'NO', ratio, low.approx() if low else -1))
    f, low, steps = family_b(F(1, 2), amp=F(1, 16), bullets=False)
    for msg in f:
        need(False, 'B S2: %s' % msg)
    need(b_radii(F(1, 2)) == [QF(q, 0, 17) for q in (F(5, 2), F(3, 2), F(3, 2), F(3, 2), F(3, 2), F(5, 2))],
         'B: S2 radii are not r(1/2)')
    print('  S2 (r = (5/2,3/2,3/2,3/2,3/2,5/2), amplitude 1/16) t<200: same table, no tie, closed form,'
          ' agents 1-4 alternate: %s' % ('yes' if not f else 'NO'))
    print('    S2 is not a member: the family needs delta < 1/2 and its amplitude at delta = 1/2 would be 1/32')
    # the note's exact threshold delta* = 16/(19 + s): agent 4 at distance r_2 = r_3 from agents 2, 3
    dstar = QF(16, 0, 17) / (19 + s)
    below, above = F(6919, 10000), F(173, 250)
    need(dstar == QF(F(38, 43), F(-2, 43), 17), 'B: 16/(19+s) is not 38/43 - (2/43) s')
    need((dstar - below).sign() > 0 and (QF(above, 0, 17) - dstar).sign() > 0, 'B: not 6919/10000 < d* < 173/250')
    broken = ((0,), (0, 1, 2, 3), (1, 2, 3), (1, 2, 3), (4, 5), (5,))
    res = []
    for dl, want_N, want_ties in ((QF(below, 0, 17), B_TABLE, []),
                                  (dstar, B_TABLE, [(2, 4), (3, 4), (4, 2), (4, 3)]),
                                  (QF(above, 0, 17), broken, [])):
        x0 = [B_L[i] + dl * F(1, 16) * B_V[i] for i in range(6)]
        rr = [2 + dl, 2 - dl, 2 - dl, 2 - dl, 2 - dl, 2 + dl]
        N, ties, low = nbhd_exact('SBI', rr, x0)
        need(N == want_N and ties == want_ties, 'B threshold delta=%r, t=0: neighbourhoods %s, ties %s'
             % (dl, fmt(N), ties))
        res.append((fmt(N), ties))
    f, low, steps = family_b(below, bullets=False)
    for msg in f:
        need(False, 'B delta=6919/10000: %s' % msg)
    print('  threshold delta* = 16/(19+s) = 38/43 - (2/43)s ~ %.10f, 6919/10000 < delta* < 173/250' % dstar.approx())
    print('    t=0  delta=6919/10000: table, ties %s (full replay t<200: %s)' % (res[0][1], 'yes' if not f else 'NO'))
    print('    t=0  delta=delta*    : table, ties %s (the table, with ties: non-strict inequality)' % (res[1][1],))
    print('    t=0  delta=173/250   : %s, ties %s (table fails)' % (res[2][0], res[2][1]))


# --------------------------------------------------------------------------- (C) path family
PREC, XPREC = 260, 320
E_BOUND = Dec('1e-250')
HALF_ULP = Dec('5e-259')     # half an ulp at 260 digits for any |value| < 100


def pi_dec():
    """pi at the current precision (the decimal-module recipe, two guard digits)."""
    with localcontext() as ctx:
        ctx.prec += 2
        three = Dec(3)
        lasts, t, s, n, na, d, da = 0, three, 3, 1, 0, 0, 24
        while s != lasts:
            lasts = s
            n, na = n + na, na + 8
            d, da = d + da, da + 32
            t = (t * n) / d
            s += t
    return +s


def sin_dec(x):
    with localcontext() as ctx:
        ctx.prec += 2
        i, lasts, s, fact, num, sign = 1, 0, x, 1, x, 1
        while s != lasts:
            lasts = s
            i += 2
            fact *= i * (i - 1)
            num *= x * x
            sign *= -1
            s += num / fact * sign
    return +s


def cos_dec(x):
    with localcontext() as ctx:
        ctx.prec += 2
        i, lasts, s, fact, num, sign = 0, 0, 1, 1, 1, 1
        while s != lasts:
            lasts = s
            i += 2
            fact *= i * (i - 1)
            num *= x * x
            sign *= -1
            s += num / fact * sign
    return +s


def path_data(n, k, prec):
    """lam_k = (1 + 2 cos(k pi/m))/3 and v_i = sin(i k pi/m), evaluated with prec + 20 working
    digits and rounded to prec; v_i = 0 exactly when m divides i k (the integer criterion)."""
    m = n - 1
    with localcontext() as ctx:
        ctx.prec = prec + 20
        pi = pi_dec()
        lam = (1 + 2 * cos_dec(pi * k / m)) / 3
        v = []
        for i in range(m + 1):
            if (i * k) % m == 0:
                v.append(Dec(0))
            else:
                a = (i * k) % (2 * m)
                if a > m:
                    a -= 2 * m            # the angle i k pi/m reduced into (-pi, pi)
                v.append(sin_dec(pi * a / m))
    with localcontext() as ctx:
        ctx.prec = prec
        return +lam, [+q for q in v]


def path_run(n, k, dl, T, lam, v, xdiff, interior_minus=False):
    """Replay x_i(0) = i + eps v_i (eps = delta/4) by the SBC update rule at 260 digits.

    Error budget.  Every |value| stays below 100 (checked), so each Decimal operation rounds by at
    most HALF_ULP = 5e-259.  The initial state is within eps*xdiff + 2 HALF_ULP of the exact one
    (xdiff: the 260-digit lam and v against a 320-digit evaluation).  While the computed and the
    exact tables agree, an update is a row-stochastic average (non-expansive in the max norm) plus at
    most three roundings, so the deviation grows by at most 3 HALF_ULP per step: below
    budget = eps*xdiff + 2 HALF_ULP + 3 T HALF_ULP < 1e-250 = E_BOUND for t < T.  Every table
    decision has computed slack above delta/2 (checked), far beyond 2 E_BOUND + 2 HALF_ULP, so the
    exact table equals the computed one at every step and the induction closes.  Signs of offsets
    are accepted only when |offset| > 2 E_BOUND.  xdiff is a cross-check of the transcendental inputs,
    not an enclosure of their error, so (C) is labelled COMPUTED."""
    m = n - 1
    fails, info = [], {}
    with localcontext() as ctx:
        ctx.prec = PREC
        dlD = Dec(dl.numerator) / Dec(dl.denominator)
        eps = dlD / 4
        if F(dlD) != dl or F(eps) != dl / 4:
            return ['delta or eps is not exact in decimal'], info
        half = dlD / 2
        budget = eps * xdiff + 2 * HALF_ULP + 3 * T * HALF_ULP
        info['budget'] = budget
        if not (budget < E_BOUND and half > 2 * E_BOUND + 2 * HALF_ULP):
            return ['error budget %.3e exceeds 1e-250' % budget], info
        r_in = 1 - dlD if interior_minus else 1 + dlD
        r = [1 - dlD] + [r_in] * (m - 1) + [1 - dlD]
        table = tuple([(0,)] + [(i - 1, i, i + 1) for i in range(1, m)] + [(m,)])
        movers = [i for i in range(1, m) if (i * k) % m != 0]
        still = [i for i in range(1, m) if (i * k) % m == 0]
        tiny = 2 * E_BOUND
        x = [Dec(i) + eps * v[i] for i in range(m + 1)]
        p = Dec(1)
        low = sig = None
        cfmax = Dec(0)
        for t in range(T):
            N, ms = [], None
            for i in range(m + 1):
                row = []
                for j in range(m + 1):
                    gap = r[i] - abs(x[i] - x[j])
                    if gap >= 0:
                        row.append(j)
                    if i != j and (ms is None or abs(gap) < ms):
                        ms = abs(gap)
                N.append(tuple(row))
            N = tuple(N)
            if N != table:
                fails.append('t=%d: neighbourhoods %s are not the claimed table' % (t, fmt(N)[:4]))
                break
            if not ms > half:
                fails.append('t=%d: a table decision has slack %.4g <= delta/2' % (t, ms))
                break
            low = ms if low is None else min(low, ms)
            if not (x[0] == 0 and x[m] == m and max(abs(q) for q in x) < 100):
                fails.append('t=%d: endpoints moved or a value left (-100, 100)' % t)
                break
            dev = max(abs(x[i] - (i + eps * p * v[i])) for i in range(m + 1))
            cfmax = max(cfmax, dev)
            if not dev <= E_BOUND:
                fails.append('t=%d: replay and closed form differ by %.3e > 1e-250' % (t, dev))
                break
            par = 1 if t % 2 == 0 else -1
            for i in movers:
                y = x[i] - i
                sig = abs(y) if sig is None else min(sig, abs(y))
                if not (abs(y) > tiny and (1 if y > 0 else -1) == par * (1 if v[i] > 0 else -1)):
                    fails.append('t=%d: agent %d not strictly on the alternating side' % (t, i))
            for i in still:
                if not abs(x[i] - i) <= E_BOUND:
                    fails.append('t=%d: zero-mode agent %d moved' % (t, i))
            if fails:
                break
            x = [sum((x[j] for j in row), Dec(0)) / len(row) for row in N]
            p = p * lam
        info.update(low=low, sig=sig, cfmax=cfmax, movers=movers, still=still)
    return fails, info


def section_c():
    T = 100
    print('(C) SBC path family (sections 1-3): n = 5..12, every k with 2m/3 < k <= m-1, delta in {1/4, 1/10},'
          ' eps = delta/4, t < %d, %d digits' % (T, PREC))
    pairs = 0
    for n in range(5, 13):
        m = n - 1
        for k in range(1, m):
            if not 3 * k > 2 * m:
                continue
            pairs += 1
            lam, v = path_data(n, k, PREC)
            lamx, vx = path_data(n, k, XPREC)
            with localcontext() as ctx:
                ctx.prec = XPREC
                xdiff = max([abs(lam - lamx)] + [abs(a - b) for a, b in zip(v, vx)])
            tag = 'C n=%d k=%d' % (n, k)
            need(xdiff < Dec('1e-255'), '%s: 260- and 320-digit evaluations differ by %s' % (tag, xdiff))
            with localcontext() as ctx:
                ctx.prec = PREC
                tiny = 2 * E_BOUND
                need(lam < -tiny and 3 * lam + 1 > tiny, '%s: lam_k not in (-1/3, 0)' % tag)
                eig = max(abs(v[i - 1] + v[i] + v[i + 1] - 3 * lam * v[i]) for i in range(1, m))
                need(eig < E_BOUND, '%s: eigen-identity residual %s' % (tag, eig))
                need(v[0] == 0 and v[m] == 0 and abs(v[1]) > tiny, '%s: v_0, v_m not 0 or v_1 = 0' % tag)
                if k == m - 1:
                    need(all((i * k) % m != 0 for i in range(1, m)), '%s: k = m-1 with a zero interior mode' % tag)
                if (n, k) == (5, 3):
                    s2 = Dec(2).sqrt()
                    pat = [Dec(0), Dec(1), -s2, Dec(1), Dec(0)]
                    e1 = abs(lam - (1 - s2) / 3)
                    e2 = max(abs(v[i] / v[1] - pat[i]) for i in range(5))
                    need(e1 < Dec('1e-200') and e2 < Dec('1e-200'),
                         '%s: lam or v is not (1-sqrt2)/3, (0,1,-sqrt2,1,0)' % tag)
                    s1line = ('    (5,3): |lam - (1-sqrt2)/3| = %.1e, max |v/v_1 - (0,1,-sqrt2,1,0)| = %.1e'
                              % (e1, e2))
            parts = []
            for dl in (F(1, 4), F(1, 10)):
                f, info = path_run(n, k, dl, T, lam, v, xdiff)
                for msg in f:
                    need(False, '%s delta=%s: %s' % (tag, dl, msg))
                parts.append('d=%s %s slack %.4f' % (dl, 'ok' if not f else 'NO', info.get('low') or -1))
                if dl == F(1, 10):
                    parts.append('|offset| >= %.1e, |x - cf| <= %.1e, budget %.1e'
                                 % (info.get('sig') or -1, info.get('cfmax') or -1, info.get('budget') or -1))
            print('  n=%-2d k=%-2d lam=%+.6f eig %.0e xdiff %.0e alternating %s zero %s | %s'
                  % (n, k, lam, eig, xdiff, info.get('movers'), info.get('still'), '; '.join(parts)))
    print(s1line)
    need(pairs == 15, 'C: expected 15 admissible (n, k), found %d' % pairs)


# --------------------------------------------------------------------------- (D) choices
def section_d():
    tol = sorted(set([F(1, 10 ** k) for k in range(13)] + [F(k) for k in range(1, 200)]
                     + [F(10 ** k) for k in range(3, 13)] + [F(p, q) for p in range(1, 60) for q in range(1, 60)]))
    bad = []
    for eta in tol:
        d = min(F(1, 2), eta / 4)
        if not (0 < d <= 1 and 6 + 3 * d < (1 + eta) * (6 - 3 * d) and (2 + d) / (2 - d) < 1 + eta
                and (2 + d) / (2 - d) - 1 <= 2 * d):
            bad.append(('SBC5 d = min(1/2, eta/4)', eta))
        dl = min(F(1, 2), eta / (2 + eta)) * F(999, 1000)
        if not (0 < dl < F(1, 2) and (1 + dl) / (1 - dl) < 1 + eta and (2 + dl) / (2 - dl) < 1 + eta):
            bad.append(('path/SBI6 delta < min(1/2, eta/(2+eta))', eta))
    for eta in (F(1), F(1, 10), F(3)):
        dl = eta / (2 + eta)
        if not (1 + dl) / (1 - dl) == 1 + eta:
            bad.append(('boundary delta = eta/(2+eta)', eta))
    for b in bad[:5]:
        need(False, 'D: %s fails at eta = %s' % b)
    print('(D) near-homogeneity choices, exact scan over %d tolerances eta in [1e-12, 1e12]: sections 3-4 choices'
          ' give ratio < 1 + eta: %s; delta = eta/(2+eta) gives exactly 1 + eta' % (len(tol), 'yes' if not bad else 'NO'))


# --------------------------------------------------------------------------- forged controls
def controls():
    print('forged controls (each must be rejected):')
    cases = [
        ('SBC5 family at d = 34/25', lambda: family_a(F(34, 25))[0]),
        ('SBC5 family with r_1 = 6 - 3d (wrong sign), d = 1/2', lambda: family_a(F(1, 2), r1_sign=-1)[0]),
        ('SBI6 family at delta = 3/4', lambda: family_b(F(3, 4))[0]),
        ('path family n=5 k=3 delta=1/4 with interior radius 1 - delta', lambda: forged_path()),
        # the remaining four show that the tie, closed-form and bullet detectors are live
        ('tie detector: SBC5 family at d = 6/(3+sqrt2)', lambda: family_a(QF(6) / QF(3, 1))[0]),
        ('closed-form detector: SBC5 d = 1/2 with lam replaced by 1/3',
         lambda: replay_exact('SBC', a_radii(F(1, 2)), A_L, A_V, QF(F(1, 2)), QF(F(1, 3)), A_TABLE, 200,
                              (1, 2, 3))[0]),
        ('bullet detector: S2 checked against the family bullets at delta = 1/2',
         lambda: family_b(F(1, 2), amp=F(1, 16), bullets=True)[0]),
        ('closed-form detector: path n=5 k=3 delta=1/4 with lam_k + 1e-200', lambda: forged_path(Dec('1e-200'))),
    ]
    for label, run in cases:
        try:
            f = run()
        except Exception as e:      # a control must be rejected by a check, not by a crash
            need(False, 'forged control [%s] raised %s: %s' % (label, type(e).__name__, e))
            continue
        if f:
            print('  forged control [%s]: rejected (%s)' % (label, f[0]))
        else:
            need(False, 'forged control [%s] ACCEPTED' % label)
            print('  forged control [%s]: ACCEPTED -- control failure' % label)


def forged_path(lam_shift=None):
    """interior radius 1 - delta, or (with lam_shift) the true radii and a shifted rate"""
    lam, v = path_data(5, 3, PREC)
    lamx, vx = path_data(5, 3, XPREC)
    with localcontext() as ctx:
        ctx.prec = XPREC
        xdiff = max([abs(lam - lamx)] + [abs(a - b) for a, b in zip(v, vx)])
    if lam_shift is None:
        return path_run(5, 3, F(1, 4), 100, lam, v, xdiff, interior_minus=True)[0]
    with localcontext() as ctx:
        ctx.prec = PREC
        lam = lam + lam_shift
    return path_run(5, 3, F(1, 4), 100, lam, v, xdiff)[0]


def main():
    for D in (2, 17):
        need(math.isqrt(D) ** 2 != D, 'field Q(sqrt %d): %d is a square' % (D, D))
    try:
        section_a()
        section_b()
        section_c()
        section_d()
        controls()
    except Exception as e:          # an unexpected error is a failure, never a pass
        need(False, 'unexpected %s: %s' % (type(e).__name__, e))
    print('genuine failures: %d; total time %.1f s' % (len(FAILS), time.perf_counter() - START))
    if FAILS:
        for msg in FAILS[:40]:
            print('FAIL:', msg)
        print('VERDICT: FAIL')
        sys.exit(1)
    print('VERDICT: PASS')


if __name__ == '__main__':
    main()
