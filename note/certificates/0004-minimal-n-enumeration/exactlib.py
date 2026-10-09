"""Exact arithmetic for the minimal-n enumeration.

Fractions; a number field Q(lam) = Q[x]/(m) with m monic irreducible and lam the unique root of m
in a rational isolating interval; signs decided by Sturm counts; polynomials as lists of Fractions
(low degree first). No floats anywhere.
"""
from fractions import Fraction as Fr
import os

# optional stop file: set HK_KILL to a path; when that file exists every loop stops
KILL = os.environ.get('HK_KILL')


def killed():
    return bool(KILL) and os.path.exists(KILL)


# ---------------------------------------------------------------- polynomials over Q
def ptrim(p):
    p = list(p)
    while p and p[-1] == 0:
        p.pop()
    return p


def padd(p, q):
    n = max(len(p), len(q))
    return ptrim([(p[i] if i < len(p) else 0) + (q[i] if i < len(q) else 0) for i in range(n)])


def psub(p, q):
    return padd(p, [-c for c in q])


def pmul(p, q):
    if not p or not q:
        return []
    r = [Fr(0)] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        if a == 0:
            continue
        for j, b in enumerate(q):
            r[i + j] += a * b
    return ptrim(r)


def pdivmod(p, q):
    p = ptrim(p)
    q = ptrim(q)
    if not q:
        raise ZeroDivisionError('poly division by zero')
    quo = [Fr(0)] * max(len(p) - len(q) + 1, 1)
    r = list(p)
    while len(r) >= len(q) and r:
        c = r[-1] / q[-1]
        k = len(r) - len(q)
        quo[k] = c
        for i, b in enumerate(q):
            r[i + k] -= c * b
        r = ptrim(r)
    return ptrim(quo), r


def pderiv(p):
    return ptrim([i * p[i] for i in range(1, len(p))])


def pgcd(p, q):
    p, q = ptrim(p), ptrim(q)
    while q:
        p, q = q, pdivmod(p, q)[1]
    if not p:
        return []
    lc = p[-1]
    return [c / lc for c in p]


def peval(p, x):
    r = Fr(0)
    for c in reversed(p):
        r = r * x + c
    return r


def squarefree(p):
    g = pgcd(p, pderiv(p))
    return pdivmod(p, g)[0] if len(g) > 1 else ptrim(p)


def sturm_seq(p):
    s = [ptrim(p), pderiv(p)]
    while s[-1]:
        r = pdivmod(s[-2], s[-1])[1]
        if not r:
            break
        s.append([-c for c in r])
    return [q for q in s if q]


def sign_changes(seq, x):
    vals = [peval(q, x) for q in seq]
    vals = [v for v in vals if v != 0]
    return sum(1 for a, b in zip(vals, vals[1:]) if (a > 0) != (b > 0))


def count_roots_open(p, a, b):
    """distinct real roots of p in the open interval (a, b), a < b."""
    g = squarefree(p)
    if len(g) <= 1:
        return 0
    s = sturm_seq(g)
    c = sign_changes(s, a) - sign_changes(s, b)  # roots in (a, b]
    if peval(g, b) == 0:
        c -= 1
    return c


# ---------------------------------------------------------------- number field
class Field:
    """Q(lam), lam the unique root of the monic irreducible m in the open interval (lo, hi)."""

    def __init__(self, m, lo, hi):
        self.m = [Fr(c) for c in m]
        self.deg = len(self.m) - 1
        self.lo, self.hi = Fr(lo), Fr(hi)
        if self.deg >= 1 and count_roots_open(self.m, self.lo, self.hi) != 1:
            raise ValueError('interval does not isolate one root')
        self.ms = sturm_seq(self.m)

    def refine(self):
        mid = (self.lo + self.hi) / 2
        vm = peval(self.m, mid)
        if vm == 0:  # rational root: only possible for deg 1
            self.lo = self.hi = mid
            return
        if (peval(self.m, self.lo) > 0) == (vm > 0):
            self.lo = mid
        else:
            self.hi = mid

    def el(self, coeffs):
        return K(self, coeffs)

    def rat(self, q):
        return K(self, [Fr(q)])

    def gen(self):
        return K(self, [Fr(0), Fr(1)])

    def key(self):
        return tuple(self.m)


class K:
    __slots__ = ('F', 'c')

    def __init__(self, F, coeffs):
        self.F = F
        c = ptrim([Fr(x) for x in coeffs])
        if len(c) > F.deg:
            c = pdivmod(c, F.m)[1]
        self.c = c

    def _co(self, o):
        if isinstance(o, K):
            return o
        return K(self.F, [Fr(o)])

    def __add__(self, o):
        return K(self.F, padd(self.c, self._co(o).c))

    __radd__ = __add__

    def __sub__(self, o):
        return K(self.F, psub(self.c, self._co(o).c))

    def __rsub__(self, o):
        return self._co(o) - self

    def __neg__(self):
        return K(self.F, [-x for x in self.c])

    def __mul__(self, o):
        return K(self.F, pmul(self.c, self._co(o).c))

    __rmul__ = __mul__

    def inv(self):
        if not self.c:
            raise ZeroDivisionError('K inverse of 0')
        # extended Euclid: find s with s*c = 1 mod m
        r0, r1 = list(self.F.m), list(self.c)
        s0, s1 = [], [Fr(1)]
        while len(r1) > 1:
            q, r = pdivmod(r0, r1)
            r0, r1 = r1, r
            s0, s1 = s1, psub(s0, pmul(q, s1))
        # r1 is a nonzero constant
        return K(self.F, [x / r1[0] for x in s1])

    def __truediv__(self, o):
        return self * self._co(o).inv()

    def __rtruediv__(self, o):
        return self._co(o) * self.inv()

    def iszero(self):
        return not self.c

    def __eq__(self, o):
        return (self - o).iszero()

    def __hash__(self):
        return hash(tuple(self.c))

    def sign(self):
        if not self.c:
            return 0
        if len(self.c) == 1:
            return 1 if self.c[0] > 0 else -1
        F = self.F
        p = self.c
        for _ in range(400):
            if F.lo == F.hi:
                v = peval(p, F.lo)
                return (v > 0) - (v < 0)
            if count_roots_open(p, F.lo, F.hi) == 0 and peval(p, F.lo) != 0 and peval(p, F.hi) != 0:
                v = peval(p, F.lo)
                return 1 if v > 0 else -1
            F.refine()
        raise RuntimeError('sign undecided')

    def __repr__(self):
        return 'K(%s)' % ','.join(str(x) for x in self.c)


# ---------------------------------------------------------------- linear algebra (generic field)
def iszero(x):
    return x.iszero() if isinstance(x, K) else x == 0


def nullspace(M, ncols, one, zero):
    """basis of {y : M y = 0}; M a list of rows over a field with elements supporting + - * /."""
    A = [list(r) for r in M]
    piv = []
    row = 0
    for col in range(ncols):
        pr = None
        for r in range(row, len(A)):
            if not iszero(A[r][col]):
                pr = r
                break
        if pr is None:
            continue
        A[row], A[pr] = A[pr], A[row]
        inv = one / A[row][col]
        A[row] = [x * inv for x in A[row]]
        for r in range(len(A)):
            if r != row and not iszero(A[r][col]):
                f = A[r][col]
                A[r] = [a - f * b for a, b in zip(A[r], A[row])]
        piv.append(col)
        row += 1
        if row == len(A):
            break
    free = [c for c in range(ncols) if c not in piv]
    basis = []
    for fc in free:
        y = [zero] * ncols
        y[fc] = one
        for i, pc in enumerate(piv):
            y[pc] = zero - A[i][fc]
        basis.append(y)
    return basis


def charpoly(M):
    """characteristic polynomial det(xI - M) (low degree first), Faddeev-LeVerrier over Q."""
    n = len(M)
    if n == 0:
        return [Fr(1)]
    I = [[Fr(int(i == j)) for j in range(n)] for i in range(n)]
    Mk = [row[:] for row in I]  # M_0 = 0 ; we use the standard recursion
    coeffs = [Fr(0)] * (n + 1)
    coeffs[n] = Fr(1)
    Mprev = [[Fr(0)] * n for _ in range(n)]
    c = Fr(1)
    for k in range(1, n + 1):
        # M_k = M * M_{k-1} + c_{n-k+1} I
        Mk = [[sum(M[i][l] * Mprev[l][j] for l in range(n)) + (c if i == j else 0) for j in range(n)]
              for i in range(n)]
        AM = [[sum(M[i][l] * Mk[l][j] for l in range(n)) for j in range(n)] for i in range(n)]
        c = -sum(AM[i][i] for i in range(n)) / k
        coeffs[n - k] = c
        Mprev = Mk
    return coeffs


# ---------------------------------------------------------------- Fourier-Motzkin (exact)
class Ineq:
    """sum a[k] y[k] + b  (> 0 if strict else >= 0); coefficients in a field."""
    __slots__ = ('a', 'b', 'strict')

    def __init__(self, a, b, strict):
        self.a, self.b, self.strict = a, b, strict


def _sgn(x):
    return x.sign() if isinstance(x, K) else ((x > 0) - (x < 0))


def fm_feasible(ineqs, nvars, order=None, maxrows=20000):
    """exact Fourier-Motzkin: is {y : all ineqs} non-empty? returns True/False (or raises)."""
    rows = list(ineqs)
    order = list(range(nvars)) if order is None else order
    for v in order:
        if killed():
            raise SystemExit('KILL')
        pos, neg, rest = [], [], []
        for q in rows:
            s = _sgn(q.a[v])
            (pos if s > 0 else neg if s < 0 else rest).append(q)
        new = rest
        for p in pos:
            for q in neg:
                # p: ap*y + .. >= 0 with ap>0 ; q: aq<0. combine (-aq)*p + ap*q
                fp, fq = -q.a[v], p.a[v]
                a = [fp * x + fq * y for x, y in zip(p.a, q.a)]
                b = fp * p.b + fq * q.b
                new.append(Ineq(a, b, p.strict or q.strict))
        # drop trivial rows and dedupe roughly
        rows = []
        seen = {}
        for q in new:
            if all(iszero(x) for x in q.a):
                s = _sgn(q.b)
                if s < 0 or (s == 0 and q.strict):
                    return False
                continue
            # normalise by first nonzero |coef|
            k0 = next(k for k, x in enumerate(q.a) if not iszero(x))
            sc = q.a[k0] if _sgn(q.a[k0]) > 0 else -q.a[k0]
            a = tuple(x / sc for x in q.a)
            b = q.b / sc
            key = tuple(tuple(x.c) if isinstance(x, K) else x for x in a)
            if key in seen:
                j = seen[key]
                # keep the tighter: smaller b (with strict tie-break)
                o = rows[j]
                d = _sgn(b - o.b)
                if d < 0 or (d == 0 and q.strict and not o.strict):
                    rows[j] = Ineq(list(a), b, q.strict)
            else:
                seen[key] = len(rows)
                rows.append(Ineq(list(a), b, q.strict))
        if len(rows) > maxrows:
            raise RuntimeError('FM blow-up %d' % len(rows))
    for q in rows:
        s = _sgn(q.b)
        if s < 0 or (s == 0 and q.strict):
            return False
    return True
