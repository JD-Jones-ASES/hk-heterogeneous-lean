"""verify.py -- stdlib-only exact checker for the small constant-digraph systems of the
heterogeneous Hegselmann-Krause note: a 5-agent SBC system and two 6-agent SBI systems whose proximity digraph is the
same at every time while agents oscillate around their limits (x(t) = x_inf + lam^t v, lam < 0).

Arithmetic: Q(sqrt d) as pairs (a, b) meaning a + b sqrt d, a, b Fractions; signs exact
(compare a^2 with d b^2). No floats. No assert statements: every check records a failure message;
the last line is VERDICT: PASS or VERDICT: FAIL and the exit code is nonzero on FAIL.

For each system it checks
  (1) lam is the stated root of its minimal polynomial and -1 < lam < 0;
  (2) the inductive certificate (all t): A_P x_inf = x_inf and A_P v = lam v exactly, and for
      u in {lam, 1} the membership inequalities of the pattern P hold (members |d| <= R at both
      endpoints, non-members on the same side of the band at both endpoints, strictly), so P is the
      neighbourhood pattern at x_inf + u v for every u in [lam, 1]; since lam^t lies in [lam, 1] for
      every t >= 0, induction gives x(t) = x_inf + lam^t v and digraph(x(t)) = P for every t;
  (3) a replay of the real update rule (neighbourhoods by exact comparisons) for t < 200 against the
      closed form and the pattern;
  (4) v != 0, so every agent with v_i != 0 alternates sides of its limit: never frozen, never
      pseudo-stable, while the digraph is constant (Theorem 6.4(iv) fails, both readings);
And forged controls (a moved radius, a perturbed rate, a perturbed limit) must each be REJECTED.
"""
import os
import sys
from fractions import Fraction as Fr

# optional stop file: set HK_KILL to a path; when that file exists every loop stops (and fails)
KILL = os.environ.get('HK_KILL')


class Q2:
    """a + b sqrt(d)"""
    __slots__ = ('a', 'b', 'd')

    def __init__(self, a, b, d):
        self.a, self.b, self.d = Fr(a), Fr(b), d

    def _c(self, o):
        return o if isinstance(o, Q2) else Q2(o, 0, self.d)

    def __add__(self, o):
        o = self._c(o)
        return Q2(self.a + o.a, self.b + o.b, self.d)

    __radd__ = __add__

    def __sub__(self, o):
        o = self._c(o)
        return Q2(self.a - o.a, self.b - o.b, self.d)

    def __rsub__(self, o):
        return self._c(o) - self

    def __neg__(self):
        return Q2(-self.a, -self.b, self.d)

    def __mul__(self, o):
        o = self._c(o)
        return Q2(self.a * o.a + self.d * self.b * o.b, self.a * o.b + self.b * o.a, self.d)

    __rmul__ = __mul__

    def __truediv__(self, o):
        o = self._c(o)
        den = o.a * o.a - self.d * o.b * o.b
        if den == 0:
            raise ZeroDivisionError('Q2 division by zero')
        num = self * Q2(o.a, -o.b, self.d)
        return Q2(num.a / den, num.b / den, self.d)

    def sign(self):
        sa = (self.a > 0) - (self.a < 0)
        sb = (self.b > 0) - (self.b < 0)
        if sb == 0:
            return sa
        if sa == 0:
            return sb
        if sa == sb:
            return sa
        # opposite signs: compare a^2 with d b^2
        c = self.a * self.a - self.d * self.b * self.b
        if c == 0:
            return 0  # only if d is a square; excluded below
        return sa if c > 0 else sb

    def __eq__(self, o):
        o = self._c(o)
        return self.a == o.a and self.b == o.b

    def __repr__(self):
        return '(%s)+(%s)*sqrt(%d)' % (self.a, self.b, self.d)


def absq(x):
    return x if x.sign() >= 0 else -x


def nbhd(model, r, y):
    n = len(y)
    out = []
    for i in range(n):
        s = set()
        for j in range(n):
            R = r[i] if model == 'SBC' else r[j]
            if (R - absq(y[i] - y[j])).sign() >= 0:
                s.add(j)
        out.append(frozenset(s))
    return out


def step(N, y):
    return [sum((y[j] for j in sorted(N[i])), Q2(0, 0, y[0].d)) / len(N[i]) for i in range(len(y))]


def check_system(S, T=200, verbose=True):
    """returns a list of failure messages (empty = the system is certified)."""
    fail = []
    d = S['d']
    lam = S['lam']
    model, P = S['model'], [frozenset(p) for p in S['P']]
    n = len(P)
    xinf = [Q2(x, 0, d) if not isinstance(x, Q2) else x for x in S['xinf']]
    v = [x if isinstance(x, Q2) else Q2(x, 0, d) for x in S['v']]
    r = [Q2(q, 0, d) for q in S['r']]
    # d not a perfect square
    import math
    if math.isqrt(d) ** 2 == d:
        fail.append('d is a square')
    # (1) lam root of minpoly, in (-1, 0)
    mp = S['minpoly']  # coefficients low -> high
    val = Q2(0, 0, d)
    pw = Q2(1, 0, d)
    for c in mp:
        val = val + pw * c
        pw = pw * lam
    if not (val == 0):
        fail.append('lam is not a root of its minimal polynomial')
    if not (lam.sign() < 0 and (lam + 1).sign() > 0):
        fail.append('lam not in (-1, 0)')
    # positivity of radii
    if any(q.sign() <= 0 for q in r):
        fail.append('a radius is not positive')
    # (2) eigen-equations
    for i in range(n):
        Ni = sorted(P[i])
        if i not in P[i]:
            fail.append('pattern row %d misses i' % i)
        mx = sum((xinf[j] for j in Ni), Q2(0, 0, d)) / len(Ni)
        mv = sum((v[j] for j in Ni), Q2(0, 0, d)) / len(Ni)
        if not (mx == xinf[i]):
            fail.append('A x_inf != x_inf at row %d' % i)
        if not (mv == lam * v[i]):
            fail.append('A v != lam v at row %d' % i)
    # (2) membership on the whole interval [lam, 1] via the endpoints
    for i in range(n):
        for j in range(n):
            if i == j:
                continue
            R = r[i] if model == 'SBC' else r[j]
            d1 = xinf[i] - xinf[j] + v[i] - v[j]
            dl = xinf[i] - xinf[j] + lam * (v[i] - v[j])
            if j in P[i]:
                if (R - absq(d1)).sign() < 0 or (R - absq(dl)).sign() < 0:
                    fail.append('member (%d,%d) leaves the band on [lam,1]' % (i, j))
            else:
                above = (d1 - R).sign() > 0 and (dl - R).sign() > 0
                below = (d1 + R).sign() < 0 and (dl + R).sign() < 0
                if not (above or below):
                    fail.append('non-member (%d,%d) not strictly outside on [lam,1]' % (i, j))
    # (4) oscillation
    if all(x == 0 for x in v):
        fail.append('v = 0: no oscillation')
    # (3) replay
    y = [xinf[i] + v[i] for i in range(n)]
    u = Q2(1, 0, d)
    digs = set()
    for t in range(T):
        if t % 50 == 0:
            if KILL and os.path.exists(KILL):
                fail.append('KILL file present: stopped')
                break
        cf = [xinf[i] + u * v[i] for i in range(n)]
        if any(not (a == b) for a, b in zip(y, cf)):
            fail.append('closed form fails at t=%d' % t)
            break
        N = nbhd(model, r, y)
        if N != P:
            fail.append('digraph at t=%d differs from P' % t)
            break
        digs.add(tuple(N))
        # side alternation of oscillating agents
        for i in range(n):
            if not (v[i] == 0):
                s = (y[i] - xinf[i]).sign()
                exp = v[i].sign() * (1 if t % 2 == 0 else -1)
                if s != exp:
                    fail.append('agent %d not on the expected side at t=%d' % (i, t))
        y = step(N, y)
        u = u * lam
    if verbose:
        print('  %s n=%d lam=%r  P=%s' % (model, n, lam, [sorted(p) for p in P]))
        print('    x_inf=%s' % [str(x.a) if x.b == 0 else repr(x) for x in xinf])
        print('    v=%s' % [repr(x) for x in v])
        print('    r=%s' % [str(q.a) for q in r])
        print('    replay t<%d: %d distinct digraph(s); oscillating agents %s' %
              (T, len(digs), [i for i in range(n) if not (v[i] == 0)]))
    return fail


def systems():
    out = {}
    # SBC, n = 5, lam = (1 - sqrt 2)/3, minimal polynomial x^2 - (2/3) x - 1/9
    d = 2
    lam = Q2(Fr(1, 3), Fr(-1, 3), d)
    s2 = Q2(0, 1, d)
    out['SBC-5'] = dict(model='SBC', d=d, lam=lam, minpoly=[Fr(-1, 9), Fr(-2, 3), Fr(1)],
                        P=[{0}, {0, 1, 2}, {1, 2, 3}, {2, 3, 4}, {4}],
                        xinf=[0, 6, 12, 18, 24], v=[Q2(0, 0, d), Q2(1, 0, d), -s2, Q2(1, 0, d), Q2(0, 0, d)],
                        r=[3, 9, 9, 9, 3])
    # SBI, n = 6, lam = (3 - sqrt 17)/8, minimal polynomial x^2 - (3/4) x - 1/8
    d = 17
    lam = Q2(Fr(3, 8), Fr(-1, 8), d)
    w = Q2(1, -1, d)  # 1 - sqrt 17
    sc = Fr(1, 16)
    out['SBI-6a'] = dict(model='SBI', d=d, lam=lam, minpoly=[Fr(-1, 8), Fr(-3, 4), Fr(1)],
                         P=[{0}, {0, 1, 2, 3}, {1, 2, 3, 4}, {1, 2, 3, 4}, {2, 3, 4, 5}, {5}],
                         xinf=[0, 2, 3, 3, 4, 6],
                         v=[Q2(0, 0, d), Q2(4 * sc, 0, d), w * sc, w * sc, Q2(4 * sc, 0, d), Q2(0, 0, d)],
                         r=[Fr(5, 2), Fr(3, 2), Fr(3, 2), Fr(3, 2), Fr(3, 2), Fr(5, 2)])
    # SBI, n = 6, all limits distinct, lam = (13 - sqrt 249)/40, minimal polynomial x^2 - (13/20) x - 1/20
    d = 249
    lam = Q2(Fr(13, 40), Fr(-1, 40), d)
    sc = Fr(1, 16)
    out['SBI-6b'] = dict(model='SBI', d=d, lam=lam, minpoly=[Fr(-1, 20), Fr(-13, 20), Fr(1)],
                         P=[{0}, {0, 1, 2, 3}, {0, 1, 2, 3, 4}, {0, 2, 3, 4, 5}, {2, 3, 4, 5}, {5}],
                         xinf=[0, 25, 31, 44, 55, 90],
                         v=[Q2(0, 0, d), Q2(10 * sc, 0, d), Q2(-5 * sc, -sc, d), Q2(8 * sc, 0, d),
                            Q2(10 * sc, 0, d), Q2(0, 0, d)],
                         r=[45, 18, 27, Fr(45, 2), 27, 54])
    return out


def forged(S):
    """three forgeries per system; each must be rejected."""
    out = []
    F = dict(S)
    F['r'] = list(S['r'])
    F['r'][1] = Fr(S['r'][1]) * 2  # a radius moved across a boundary
    out.append(('radius r_1 doubled', F))
    F = dict(S)
    F['lam'] = Q2(S['lam'].a, 0, S['d'])  # the rate replaced by its rational part
    out.append(('rate replaced by a rational', F))
    F = dict(S)
    xs = list(S['xinf'])
    xs[2] = (Fr(xs[2]) if not isinstance(xs[2], Q2) else xs[2]) + Fr(1, 7)
    F['xinf'] = xs
    out.append(('limit x_2 shifted by 1/7', F))
    return out


def main():
    bad = []
    for name, S in systems().items():
        print(name)
        f = check_system(S)
        if f:
            bad.append('%s: %s' % (name, '; '.join(f[:5])))
            print('    FAILED:', f[:5])
        else:
            print('    certified: constant digraph for every t, oscillation, x(t) -> x_inf')
        for label, Fs in forged(S):
            ff = check_system(Fs, T=40, verbose=False)
            if ff:
                print('    forged (%s): rejected (%s)' % (label, ff[0]))
            else:
                bad.append('%s forged (%s) ACCEPTED' % (name, label))
                print('    forged (%s): ACCEPTED -- control failure' % label)
    if bad:
        for b in bad:
            print('FAIL:', b)
        print('VERDICT: FAIL')
        sys.exit(1)
    print('VERDICT: PASS')


if __name__ == '__main__':
    main()
