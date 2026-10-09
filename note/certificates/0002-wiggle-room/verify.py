"""verify.py -- wiggle room (Remark 2.1 of arXiv:2610.03229) for the systems of its sections 2 and 4.

Standard library only, exact (fractions.Fraction), one process, no assert statements.
System (a) is the 7-agent SBC system of section 2, system (c) the 6-agent SBC system of section 4.

For a one-parameter affine family p -> (L(p), v(p), r(p)) with x(t) = L + u v, u = lam^t, the same
two neighbourhood tables (even t / odd t) hold for every t >= 0 iff, for every row i, every j != i and
each parity class C (u_first = 1 for even t, lam for odd t; the class accumulates at u = 0):
  in-arc  (j in N_C(i)):  |a + u_first b| <= R  and  |a| <= R          (|a + u b| is convex in u)
  out-arc (j not in N_C(i)), in the same-sign region s(a) = s fixed, s a > 0:
          s(a + u_first b) > R,  s a >= R,  and where s a = R also s u_first b > 0
with a = L_j - L_i, b = v_j - v_i, R = r_i (SBC).  All are affine in p, so the feasible set is an
interval, computed exactly.  The out-arc test is exact on the same-sign region; the script also checks
that no sign crossing (s(a + u_first b) < -R) is feasible, so the interval is the whole answer.
Every interval is then replayed through the SBC update itself (t < 200) at interior and endpoint
values, and just outside each finite endpoint (the forged controls must show a table change or a
closed-form break).
"""
import os
import sys
from fractions import Fraction as F

# ---------------------------------------------------------------- exact helpers (Fractions only)
# optional stop file: set HK_KILL to a path; when that file exists every loop stops (and fails)
KILL = os.environ.get("HK_KILL")


def killed():
    return bool(KILL) and os.path.exists(KILL)


def neighbors(model, r, y, i):
    n = len(y)
    out = []
    for j in range(n):
        R = r[i] if model == "sbc" else r[j]
        if abs(y[i] - y[j]) <= R:
            out.append(j)
    return tuple(out)


def table(model, r, y):
    return tuple(neighbors(model, r, y, i) for i in range(len(y)))


def step(model, r, y):
    n = len(y)
    z = []
    for i in range(n):
        N = neighbors(model, r, y, i)
        z.append(sum((y[j] for j in N), F(0)) / len(N))
    return z


def matrix_of(tab):
    n = len(tab)
    A = [[F(0)] * n for _ in range(n)]
    for i, N in enumerate(tab):
        for j in N:
            A[i][j] = F(1, len(N))
    return A


def matvec(A, v):
    return [sum((a * b for a, b in zip(row, v)), F(0)) for row in A]


def matmul(A, B):
    n = len(A)
    m = len(B[0])
    return [[sum((A[i][k] * B[k][j] for k in range(len(B))), F(0)) for j in range(m)] for i in range(n)]


def rref(M):
    M = [list(r) for r in M]
    rows = len(M)
    cols = len(M[0]) if rows else 0
    piv = []
    r = 0
    for c in range(cols):
        p = None
        for k in range(r, rows):
            if M[k][c] != 0:
                p = k
                break
        if p is None:
            continue
        M[r], M[p] = M[p], M[r]
        inv = 1 / M[r][c]
        M[r] = [x * inv for x in M[r]]
        for k in range(rows):
            if k != r and M[k][c] != 0:
                f = M[k][c]
                M[k] = [a - f * b for a, b in zip(M[k], M[r])]
        piv.append(c)
        r += 1
        if r == rows:
            break
    return M, piv


def rank(M):
    if not M:
        return 0
    return len(rref(M)[1])


def nullspace(M, ncols=None):
    """Basis of {x : M x = 0} as a list of vectors."""
    if not M:
        return [[F(int(i == j)) for i in range(ncols)] for j in range(ncols)]
    ncols = len(M[0])
    R, piv = rref(M)
    free = [c for c in range(ncols) if c not in piv]
    basis = []
    for f in free:
        v = [F(0)] * ncols
        v[f] = F(1)
        for k, c in enumerate(piv):
            v[c] = -R[k][f]
        basis.append(v)
    return basis


def fail(msg):
    print("FAIL:", msg)
    print("VERDICT: FAIL")
    raise SystemExit(1)


# ---------------------------------------------------------------- the wiggle-room computation

T = 200


class Lin:
    def __init__(self, c0, c1):
        self.c0, self.c1 = F(c0), F(c1)

    def __add__(self, o):
        o = o if isinstance(o, Lin) else Lin(o, 0)
        return Lin(self.c0 + o.c0, self.c1 + o.c1)

    def __sub__(self, o):
        o = o if isinstance(o, Lin) else Lin(o, 0)
        return Lin(self.c0 - o.c0, self.c1 - o.c1)

    def scale(self, k):
        return Lin(self.c0 * k, self.c1 * k)

    def at(self, p):
        return self.c0 + self.c1 * p


class Interval:
    def __init__(self):
        self.lo, self.lo_closed = None, False   # None = -inf
        self.hi, self.hi_closed = None, False
        self.empty = False
        self.excluded = set()

    def add(self, f, strict):
        """impose f(p) >= 0 (or > 0)."""
        if f.c1 == 0:
            if f.c0 < 0 or (strict and f.c0 == 0):
                self.empty = True
            return
        root = -f.c0 / f.c1
        if f.c1 > 0:   # p >= root
            if self.lo is None or root > self.lo or (root == self.lo and strict):
                self.lo, self.lo_closed = root, not strict
        else:          # p <= root
            if self.hi is None or root < self.hi or (root == self.hi and strict):
                self.hi, self.hi_closed = root, not strict

    def contains(self, p):
        if self.empty or p in self.excluded:
            return False
        if self.lo is not None and (p < self.lo or (p == self.lo and not self.lo_closed)):
            return False
        if self.hi is not None and (p > self.hi or (p == self.hi and not self.hi_closed)):
            return False
        return True

    def __str__(self):
        if self.empty or (self.lo is not None and self.hi is not None and
                          (self.lo > self.hi or (self.lo == self.hi and not (self.lo_closed and self.hi_closed)))):
            return "EMPTY"
        if self.lo is not None and self.hi is not None and self.lo == self.hi:
            s = "{%s}" % self.lo
        else:
            l = "(-inf" if self.lo is None else ("[" if self.lo_closed else "(") + str(self.lo)
            h = "+inf)" if self.hi is None else str(self.hi) + ("]" if self.hi_closed else ")")
            s = l + ", " + h
        if self.excluded:
            s += " minus " + str(sorted(self.excluded))
        return s


def sgn(x):
    return (x > 0) - (x < 0)


def feasible(fam, tabs, lam, p0):
    """fam(p) -> (L, v, r) as lists of Lin; tabs = (even table, odd table)."""
    L, v, r = fam
    n = len(L)
    I = Interval()
    eqpts = []
    crossing = []
    for i in range(n):
        I.add(r[i], True)   # r_i > 0
    for C, uf in ((0, F(1)), (1, lam)):
        for i in range(n):
            for j in range(n):
                if j == i:
                    continue
                a = L[j] - L[i]
                b = v[j] - v[i]
                R = r[i]
                if j in tabs[C][i]:
                    # -R <= a + uf b <= R ; -R <= a <= R
                    I.add(R - (a + b.scale(uf)), False)
                    I.add(R + (a + b.scale(uf)), False)
                    I.add(R - a, False)
                    I.add(R + a, False)
                else:
                    s = sgn(a.at(p0))
                    if s == 0:
                        fail("out-arc with coincident limits at p0")
                    I.add(a.scale(s), True)
                    I.add((a + b.scale(uf)).scale(s) - R, True)
                    g = a.scale(s) - R
                    I.add(g, False)
                    eqpts.append((g, (b.scale(s * uf))))
                    crossing.append(((a + b.scale(uf)).scale(-s) - R, a.scale(s) - R))
    # equality points: where s a = R the approach must be from above
    for g, h in eqpts:
        if g.c1 != 0:
            pstar = -g.c0 / g.c1
            if I.contains(pstar) and not h.at(pstar) > 0:
                I.excluded.add(pstar)
        elif g.c0 == 0:
            # identically on the boundary: need h(p) > 0 throughout
            I.add(h, True)
    # crossing region check: exists p in I with -s(a+uf b) - R > 0 and s a - R >= 0 ?
    for f1, f2 in crossing:
        J = Interval()
        J.lo, J.lo_closed, J.hi, J.hi_closed, J.empty = I.lo, I.lo_closed, I.hi, I.hi_closed, I.empty
        J.add(f1, True)
        J.add(f2, False)
        if str(J) != "EMPTY":
            fail("a sign-crossing region is feasible; the same-sign analysis is not the whole answer")
    return I


def replay(model, r, x0, L, v, lam, tabs):
    """True iff the update reproduces L + lam^t v and the parity tables for t < T."""
    x = list(x0)
    u = F(1)
    for t in range(T):
        if killed():
            fail("KILL file present")
        cf = [L[i] + u * v[i] for i in range(len(L))]
        if x != cf:
            return False, "closed form breaks at t=%d" % t
        if table(model, r, x) != tabs[t % 2]:
            return False, "table changes at t=%d" % t
        x = step(model, r, x)
        u *= lam
    return True, "ok"


def run(name, L0, v0, r0, lam):
    n = len(L0)
    L0 = [F(x) for x in L0]; v0 = [F(x) for x in v0]; r0 = [F(x) for x in r0]
    x0 = [L0[i] + v0[i] for i in range(n)]
    tabs = (table("sbc", r0, x0), table("sbc", r0, [L0[i] + lam * v0[i] for i in range(n)]))
    ok, msg = replay("sbc", r0, x0, L0, v0, lam, tabs)
    if not ok:
        fail(name + " base replay: " + msg)
    print("== system", name, " lam =", lam)
    print("   even table:", tabs[0])
    print("   odd  table:", tabs[1])
    # rigidity of single coordinates of x(0) within the ansatz
    AE, AO = matrix_of(tabs[0]), matrix_of(tabs[1])
    I_ = [[F(int(i == j)) for j in range(n)] for i in range(n)]
    fixrows = [[AE[i][j] - I_[i][j] for j in range(n)] for i in range(n)] + \
              [[AO[i][j] - I_[i][j] for j in range(n)] for i in range(n)]
    eigrows = [[AE[i][j] - lam * I_[i][j] for j in range(n)] for i in range(n)] + \
              [[AO[i][j] - lam * I_[i][j] for j in range(n)] for i in range(n)]
    Fix = nullspace(fixrows)
    Eig = nullspace(eigrows)
    W = Fix + Eig
    print("   dim Fix =", len(Fix), " dim E_lam =", len(Eig), " dim W =", rank(W))
    rows = []
    for i in range(n):
        e = [F(int(k == i)) for k in range(n)]
        rigid = rank(W + [e]) > rank(W)
        rows.append(rigid)
        print("   x_%d(0) = %s : %s" % (i + 1, x0[i], "RIGID (e_i not in W; only delta = 0 keeps the closed form)" if rigid else "e_i in W"))
    # forged control for rigidity: a perturbation inside W must keep the closed form (translation)
    # r_i families
    results = []
    def check_family(label, fam, p0, mk):
        I = feasible(fam, tabs, lam, p0)
        if not I.contains(p0):
            fail(label + ": original value not in its interval " + str(I))
        tests = []
        # inside: original, endpoints if closed, midpoint-ish
        cand = [p0]
        if I.lo is not None and I.lo_closed and I.lo not in I.excluded:
            cand.append(I.lo)
        if I.hi is not None and I.hi_closed and I.hi not in I.excluded:
            cand.append(I.hi)
        if I.lo is not None and I.hi is not None and I.lo < I.hi:
            cand.append((I.lo + I.hi) / 2)
        for p in cand:
            r, xx, L, v = mk(p)
            ok, msg = replay("sbc", r, xx, L, v, lam, tabs)
            if not ok:
                fail(label + " inside value %s fails replay: %s" % (p, msg))
        # outside: just beyond each finite endpoint (forged controls)
        outs = []
        eps = F(1, 10**4)
        if I.lo is not None:
            outs.append(I.lo - eps if I.lo_closed else I.lo)
        if I.hi is not None:
            outs.append(I.hi + eps if I.hi_closed else I.hi)
        for p in outs:
            r, xx, L, v = mk(p)
            if any(ri <= 0 for ri in r):
                continue
            ok, msg = replay("sbc", r, xx, L, v, lam, tabs)
            if ok:
                fail(label + " outside value %s passes replay (interval too small?)" % p)
            tests.append("%s -> %s" % (p, msg))
        print("   %-10s %-28s  outside: %s" % (label, str(I), "; ".join(tests) if tests else "none finite"))
        results.append((label, str(I)))

    for k in range(n):
        Lf = [Lin(x, 0) for x in L0]; vf = [Lin(x, 0) for x in v0]
        rf = [Lin(x, 0) for x in r0]; rf[k] = Lin(0, 1)
        def mk(p, k=k):
            r = list(r0); r[k] = p
            return r, x0, L0, v0
        check_family("r_%d" % (k + 1), (Lf, vf, rf), r0[k], mk)
    # dilation of the limit about the first agent: L -> beta L
    Lf = [Lin(0, x) for x in L0]; vf = [Lin(x, 0) for x in v0]; rf = [Lin(x, 0) for x in r0]
    def mkb(p):
        L = [p * x for x in L0]
        return r0, [L[i] + v0[i] for i in range(n)], L, v0
    check_family("beta", (Lf, vf, rf), F(1), mkb)
    # amplitude: v -> gamma v
    Lf = [Lin(x, 0) for x in L0]; vf = [Lin(0, x) for x in v0]
    def mkg(p):
        v = [p * x for x in v0]
        return r0, [L0[i] + v[i] for i in range(n)], L0, v
    check_family("gamma", (Lf, vf, rf), F(1), mkg)
    # translation: every alpha (checked at two values)
    for al in (F(-1000), F(37, 3)):
        L = [x + al for x in L0]
        ok, msg = replay("sbc", r0, [L[i] + v0[i] for i in range(n)], L, v0, lam, tabs)
        if not ok:
            fail("translation fails: " + msg)
    print("   alpha      (-inf, +inf) (translation; replayed at -1000 and 37/3)")
    return results


lam = F(-1, 6)
res_a = run("(a) SBC n=7", [0, 36, 72, 84, 96, 132, 168], [0, 2, -3, 0, 3, -2, 0], [18, 42, 48, 12, 48, 42, 18], lam)
res_c = run("(c) SBC n=6", [0, 20, 40, 100, 120, 140], [0, 2, -3, 3, -2, 0], [10, 70, 70, 70, 70, 10], lam)
# the intervals stated in the note (1-indexed radii); any difference is a failure
STATED_A = {"r_1": "(0, 107/3)", "r_2": "[38, 46)", "r_3": "[221/6, 359/6)", "r_4": "{12}",
            "r_5": "[221/6, 359/6)", "r_6": "[38, 46)", "r_7": "(0, 107/3)", "beta": "{1}", "gamma": "(0, 3)"}
STATED_C = {"r_1": "(0, 59/3)", "r_2": "[22, 479/6)", "r_3": "[66, 479/6)", "r_4": "[66, 479/6)",
            "r_5": "[22, 479/6)", "r_6": "(0, 59/3)", "beta": "(421/480, 16/15]", "gamma": "(-5, 5/3]"}
for name, res, stated in (("(a)", res_a, STATED_A), ("(c)", res_c, STATED_C)):
    got = dict(res)
    if got != stated:
        fail("%s: computed intervals %s differ from the stated ones %s" % (name, got, stated))
print("computed intervals equal the stated intervals for (a) and (c)")
# forged control: a wrong r must be rejected by the base replay
ok, msg = replay("sbc", [F(x) for x in [18, 42, 48, 13, 48, 42, 18]],
                 [F(x) for x in [0, 38, 69, 84, 99, 130, 168]],
                 [F(x) for x in [0, 36, 72, 84, 96, 132, 168]], [F(x) for x in [0, 2, -3, 0, 3, -2, 0]], lam,
                 (table("sbc", [F(x) for x in [18, 42, 48, 12, 48, 42, 18]], [F(x) for x in [0, 38, 69, 84, 99, 130, 168]]),
                  table("sbc", [F(x) for x in [18, 42, 48, 12, 48, 42, 18]], [F(x) for x in [0, 36, 72, 84, 96, 132, 168]])))
if ok:
    fail("forged r_4 = 13 accepted")
print("forged control r_4 = 13 rejected:", msg)
print("VERDICT: PASS")
