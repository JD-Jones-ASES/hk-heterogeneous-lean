"""Witness extraction + exact replay for systems found by stage 2 / pairs.

Given model, n, patterns P+ (u in (0,1]) and P- (u in [lam,0)), the field Q(lam), a limit x (rational,
a choice of the c-parameter if any) and an eigenvector w over Q(lam): scan s = sg * 2^-k and pick a
rational r inside the exact per-bound interval; then replay the REAL update rule from
x(0) = x_inf + s w for T steps in Q(lam) (neighbourhoods by exact sign tests) and compare with the
closed form x_inf + lam^t s w and with the patterns.
"""
import os
import sys
from fractions import Fraction as Fr
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from exactlib import K, killed


def nbhd(model, n, r, y):
    N = []
    for i in range(n):
        m = 0
        for j in range(n):
            R = r[i] if model == 'SBC' else r[j]
            d = y[i] - y[j]
            ad = d if d.sign() >= 0 else -d
            if (R - ad).sign() >= 0:
                m |= 1 << j
        N.append(m)
    return N


def step(n, N, y):
    out = []
    for i in range(n):
        idx = [j for j in range(n) if N[i] >> j & 1]
        s = y[idx[0]]
        for j in idx[1:]:
            s = s + y[j]
        out.append(s / len(idx))
    return out


def r_interval(model, n, Pp, Pm, F, X, v):
    """for each bound index R: (lower, lower_strict, upper, upper_strict) over the endpoints."""
    lam = F.gen()
    lows = {R: [] for R in range(n)}
    ups = {R: [] for R in range(n)}
    for P, us in ((Pp, (F.rat(0), F.rat(1))), (Pm, (F.rat(0), lam))):
        for i in range(n):
            for j in range(n):
                if i == j:
                    continue
                R = i if model == 'SBC' else j
                sig = -1 if i < j else 1
                for u in us:
                    d = F.rat(X[i] - X[j]) + u * (v[i] - v[j])
                    if P[i] >> j & 1:
                        ad = d if d.sign() >= 0 else -d
                        lows[R].append((ad, False))
                    else:
                        ups[R].append((d * sig, not u.iszero()))
    return lows, ups


def choose_r(lows, ups, n, F):
    """rational r_R with every lower <= r (strict as flagged) and r < / <= every upper; None if empty."""
    r = []
    for R in range(n):
        lo = max((a for a, _ in lows[R]), key=lambda z: _Key(z), default=F.rat(0))
        lo = lo if lo.sign() > 0 else F.rat(0)
        hi = min((a for a, _ in ups[R]), key=lambda z: _Key(z), default=None)
        # find a rational q with q >= every lower (q > 0) and q < every strict upper, <= nonstrict
        cand = []
        if hi is None:
            q = _ratceil(lo) + 1
            cand.append(q)
        else:
            if (hi - lo).sign() < 0:
                return None
            # try simple rationals in [lo, hi]
            for den in (1, 2, 4, 5, 8, 10, 16, 20, 40, 100, 1000, 10000, 10**6, 10**9):
                q = _ratceil(lo * den) / Fr(den)
                cand.append(q)
                cand.append(q + Fr(1, den))
        ok = None
        for q in cand:
            qk = F.rat(q)
            if q <= 0:
                continue
            good = all((qk - a).sign() >= 0 for a, _ in lows[R])
            if good:
                for a, st in ups[R]:
                    sgn = (a - qk).sign()
                    if sgn < 0 or (sgn == 0 and st):
                        good = False
                        break
            if good:
                ok = q
                break
        if ok is None:
            return None
        r.append(ok)
    return r


class _Key:
    def __init__(self, z):
        self.z = z

    def __lt__(self, o):
        return (self.z - o.z).sign() < 0


def _ratceil(z):
    """a rational >= z (z in Q(lam)), via bisection on integers scaled."""
    # integer ceiling by search
    lo, hi = -1, 1
    while (z - hi).sign() > 0:
        hi *= 2
    while (z - lo).sign() < 0:
        lo *= 2
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if (z - mid).sign() > 0:
            lo = mid
        else:
            hi = mid
    return Fr(hi)


def find_witness(model, n, Pp, Pm, F, X, w, sg, kmax=40, scale=1):
    for k in range(0, kmax):
        s = Fr(sg * scale, 2 ** k)
        v = [wi * s for wi in w]
        lows, ups = r_interval(model, n, Pp, Pm, F, X, v)
        r = choose_r(lows, ups, n, F)
        if r is not None:
            return s, v, r
    return None


def replay(model, n, Pp, Pm, F, X, v, r, T=200):
    lam = F.gen()
    rk = [F.rat(q) for q in r]
    y = [F.rat(X[i]) + v[i] for i in range(n)]
    u = F.rat(1)
    seen = set()
    for t in range(T):
        if killed():
            raise SystemExit('KILL')
        cf = [F.rat(X[i]) + u * v[i] for i in range(n)]
        if any(not (a - b).iszero() for a, b in zip(y, cf)):
            return 'closed form fails at t=%d' % t
        N = nbhd(model, n, rk, y)
        exp = Pp if t % 2 == 0 else Pm
        if list(N) != list(exp):
            return 'pattern mismatch at t=%d: %s vs %s' % (t, N, exp)
        seen.add(tuple(N))
        y = step(n, N, y)
        u = u * lam
    return 'OK %d steps, %d distinct digraphs' % (T, len(seen))
