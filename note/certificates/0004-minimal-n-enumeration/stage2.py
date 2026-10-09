"""Stage 2/3 of the minimal-n probe: exact eigen data and exact realizability (both models).

For each stage-1 survivor P (a single pattern):
  * the limit space {x : A_P x = x}, normalised x_0 = 0, x_{n-1} = 1 (affine in a parameter c when
    there are three closed clusters);
  * closure filter (u -> 0, rational): some r > 0 and admissible x make the pattern consistent at
    the limit (members |x_i - x_j| <= R, non-members sigma (x_i - x_j) >= R), per model;
  * every lam in (-1, 0) that is a root of an irreducible factor of charpoly(Q): the field Q(lam),
    the eigenspace ker(A_P - lam I) over Q(lam);
  * CONSTANT case: exact Fourier-Motzkin feasibility of the full system (x, v, r) with v != 0:
    members at u in {0, 1, lam}, non-members strict at u in {1, lam} and non-strict at 0;
  * records (model, lam-key, pattern) for the alternating pairing (stage 4, pairs.py).
"""
import os, sys, json, time
from fractions import Fraction as Fr
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from exactlib import (Field, K, nullspace, fm_feasible, Ineq, count_roots_open, killed, squarefree,
                      peval, pdivmod, ptrim, pmul)
from math import gcd


def _divisors(m):
    m = abs(m)
    out = []
    k = 1
    while k * k <= m:
        if m % k == 0:
            out.append(k)
            out.append(m // k)
        k += 1
    return sorted(set(out))


def _full_monic_factors(p):
    """Factor a squarefree monic rational polynomial with the optional SymPy dependency.

    This path is used only when rational-root extraction leaves degree at least four.
    All coefficients crossing the boundary are exact rationals; reconstruction is
    checked below using the certificate's own Fraction polynomial arithmetic.
    """
    try:
        import sympy as sp
    except ImportError as exc:
        raise RuntimeError(
            'degree >= 4 requires the optional n=6 replay dependency: '
            'install it with "python -m pip install sympy", then rerun stage2.py; '
            'the n=5 certificate uses only the standard library') from exc
    x = sp.Symbol('hk_factor_variable')
    poly = sp.Poly.from_list(
        [sp.Rational(c.numerator, c.denominator) for c in reversed(p)], x)
    _, factors = sp.factor_list(poly)
    out = []
    for factor, multiplicity in factors:
        if multiplicity != 1 or factor.degree() < 1:
            raise RuntimeError('full factoriser returned invalid squarefree factors')
        monic = factor.monic()
        co = []
        for c in reversed(monic.all_coeffs()):
            numerator, denominator = c.as_numer_denom()
            co.append(Fr(int(numerator), int(denominator)))
        out.append(ptrim(co))
    reconstructed = [Fr(1)]
    for co in out:
        reconstructed = pmul(reconstructed, co)
    if ptrim(reconstructed) != ptrim(p):
        raise RuntimeError('full factoriser failed exact polynomial reconstruction')
    return out


def factor_over_Q(cp):
    """monic irreducible factors (low degree first) of the rational polynomial cp, without
    multiplicity: rational roots by the rational-root test, and the cofactor, which is irreducible
    when its degree is at most 3 and it has no rational root. A remaining cofactor of degree >= 4
    uses the optional SymPy factoriser, with exact rational conversion and independent product
    reconstruction. Every n = 5 characteristic polynomial has degree 3, so the standard-library
    certificate never imports or requires SymPy."""
    p = ptrim([Fr(c) for c in cp])
    p = [c / p[-1] for c in p]
    p = squarefree(p)
    p = [c / p[-1] for c in p]
    target = list(p)
    out = []
    while len(p) > 1 and p[0] == 0:
        out.append([Fr(0), Fr(1)])
        p = p[1:]
    changed = True
    while changed and len(p) > 2:
        changed = False
        den = 1
        for c in p:
            den = den * c.denominator // gcd(den, c.denominator)
        ints = [int(c * den) for c in p]
        for a in _divisors(ints[0]):
            for b in _divisors(ints[-1]):
                for root in (Fr(a, b), Fr(-a, b)):
                    if peval(p, root) == 0:
                        out.append([-root, Fr(1)])
                        p = pdivmod(p, [-root, Fr(1)])[0]
                        changed = True
                        break
                if changed:
                    break
            if changed:
                break
    if len(p) == 2:
        out.append(p)
    elif len(p) >= 3:
        if len(p) - 1 >= 4:
            out.extend(_full_monic_factors(p))
        else:
            out.append(p)
    uniq = []
    for f in out:
        if f not in uniq:
            uniq.append(f)
    reconstructed = [Fr(1)]
    for f in uniq:
        reconstructed = pmul(reconstructed, f)
    if ptrim(reconstructed) != target:
        raise RuntimeError('factorisation failed exact squarefree polynomial reconstruction')
    return uniq

MODELS = ('SBC', 'SBI')


def amat(N, n):
    A = []
    for i in range(n):
        d = bin(N[i]).count('1')
        A.append([Fr(1, d) if N[i] >> j & 1 else Fr(0) for j in range(n)])
    return A


def limit_family(As, n):
    """{x : A x = x for all A in As}, normalised x_0 = 0, x_{n-1} = 1: returns (X0, [X1, ...])
    or None if no such x exists (e.g. only constants)."""
    rows = []
    for A in As:
        for i in range(n):
            rows.append([A[i][j] - (1 if i == j else 0) for j in range(n)])
    B = nullspace(rows, n, Fr(1), Fr(0))
    # find combination with x0 = 0, x_{n-1} = 1: unknown coefficients a (len(B))
    k = len(B)
    # solve [B0; B_{n-1}] a = [0; 1] -> affine family
    M = [[B[t][0] for t in range(k)] + [Fr(0)], [B[t][n - 1] for t in range(k)] + [Fr(1)]]
    # particular solution + kernel via nullspace of augmented with last column as -rhs
    aug = [[M[r][t] for t in range(k)] + [-M[r][k]] for r in range(2)]
    ker = nullspace(aug, k + 1, Fr(1), Fr(0))
    # elements with last coordinate 1 form the affine family
    part = None
    hom = []
    for y in ker:
        if y[k] != 0:
            if part is None:
                part = [c / y[k] for c in y]
            else:
                hom.append([a - b * y[k] for a, b in zip(y, part)])
        else:
            hom.append(y)
    if part is None:
        return None
    # make hom vectors have last coord 0 (they do), map to x-space
    X0 = [sum(part[t] * B[t][i] for t in range(k)) for i in range(n)]
    Xs = []
    for h in hom:
        Xh = [sum(h[t] * B[t][i] for t in range(k)) for i in range(n)]
        if any(x != 0 for x in Xh):
            Xs.append(Xh)
    return X0, Xs


def lam_roots(cp):
    """[(Field, key)] for every root of charpoly cp in (-1, 0)."""
    out = []
    for co in factor_over_Q(cp):
        if count_roots_open(co, Fr(-1), Fr(0)) == 0:
            continue
        # canonical isolation by bisection of (-1, 0)
        stack = [(Fr(-1), Fr(0))]
        while stack:
            a, b = stack.pop()
            c = count_roots_open(co, a, b)
            if c == 0:
                continue
            if c == 1:
                out.append((co, a, b))
                continue
            m = (a + b) / 2
            if peval(co, m) == 0:
                out.append((co, m - (b - a) / 1024, m + (b - a) / 1024))  # rational root
                # the narrowed interval holds only m; split the rest
                stack.append((a, m - (b - a) / 1024))
                stack.append((m + (b - a) / 1024, b))
            else:
                stack.append((a, m))
                stack.append((m, b))
    res = []
    for co, a, b in out:
        if len(co) == 2:  # rational root
            F = Field(co, a, b)
        else:
            F = Field(co, a, b)
        res.append((F, (tuple(str(c) for c in co), str(a), str(b))))
    return res


def build_ineqs(model, n, Pp, Pm, lam, F, X0, Xs, V, orient):
    """variables: c (len Xs), s (len V), r (n). Returns Ineq list over Q(lam).
    Pp: masks for u in (0,1]; Pm: masks for u in [lam, 0)."""
    nc, ns = len(Xs), len(V)
    nv = nc + ns + n
    one = F.rat(1)
    zero = F.rat(0)

    def dvec(i, j, u):
        """coeff vector and const of d_ij(u) = x_i - x_j + u (v_i - v_j)."""
        a = [zero] * nv
        for k, Xk in enumerate(Xs):
            a[k] = F.rat(Xk[i] - Xk[j])
        for k, Vk in enumerate(V):
            a[nc + k] = u * (Vk[i] - Vk[j])
        b = F.rat(X0[i] - X0[j])
        return a, b

    ineqs = []
    rid = lambda i: nc + ns + i
    for P, us in ((Pp, (F.rat(0), one)), (Pm, (F.rat(0), F.gen()))):
        for i in range(n):
            for j in range(n):
                if i == j:
                    continue
                R = rid(i) if model == 'SBC' else rid(j)
                member = (P[i] >> j) & 1
                sig = -1 if i < j else 1
                for u in us:
                    a, b = dvec(i, j, u)
                    if member:
                        # R - d >= 0 ; R + d >= 0
                        a1 = [-x for x in a]
                        a1[R] = a1[R] + one
                        ineqs.append(Ineq(a1, -b, False))
                        a2 = list(a)
                        a2[R] = a2[R] + one
                        ineqs.append(Ineq(a2, b, False))
                    else:
                        # sig*d - R > 0 (strict unless u == 0)
                        a1 = [x * sig for x in a]
                        a1[R] = a1[R] - one
                        ineqs.append(Ineq(a1, b * sig, not u.iszero()))
    for i in range(n):
        a = [zero] * nv
        a[rid(i)] = one
        ineqs.append(Ineq(a, zero, True))
    for i in range(n - 1):
        a = [zero] * nv
        for k, Xk in enumerate(Xs):
            a[k] = F.rat(Xk[i + 1] - Xk[i])
        if any(not x.iszero() for x in a):
            ineqs.append(Ineq(a, F.rat(X0[i + 1] - X0[i]), False))
        elif X0[i + 1] - X0[i] < 0:
            ineqs.append(Ineq(a, F.rat(-1), False))
    if orient is not None:
        k, sg = orient
        a = [zero] * nv
        a[nc + k] = F.rat(sg)
        ineqs.append(Ineq(a, zero, True))
    order = [nc + ns + i for i in range(n)] + list(range(nc)) + [nc + k for k in range(ns)]
    return ineqs, nv, order


def closure_ok(model, n, Ps, X0, Xs):
    """rational FM at u = 0 for all patterns in Ps with a shared r and x."""
    F = Field([Fr(0), Fr(1)], Fr(-1), Fr(1))  # Q itself (lam = 0 placeholder, unused)
    nc = len(Xs)
    nv = nc + n
    one = F.rat(1)
    zero = F.rat(0)
    ineqs = []
    for P in Ps:
        for i in range(n):
            for j in range(n):
                if i == j:
                    continue
                R = nc + (i if model == 'SBC' else j)
                a = [zero] * nv
                for k, Xk in enumerate(Xs):
                    a[k] = F.rat(Xk[i] - Xk[j])
                b = F.rat(X0[i] - X0[j])
                if (P[i] >> j) & 1:
                    a1 = [-x for x in a]
                    a1[R] = a1[R] + one
                    ineqs.append(Ineq(a1, -b, False))
                    a2 = list(a)
                    a2[R] = a2[R] + one
                    ineqs.append(Ineq(a2, b, False))
                else:
                    sig = -1 if i < j else 1
                    a1 = [x * sig for x in a]
                    a1[R] = a1[R] - one
                    ineqs.append(Ineq(a1, b * sig, False))
    for i in range(n):
        a = [zero] * nv
        a[nc + i] = one
        ineqs.append(Ineq(a, zero, True))
    for i in range(n - 1):
        a = [zero] * nv
        for k, Xk in enumerate(Xs):
            a[k] = F.rat(Xk[i + 1] - Xk[i])
        ineqs.append(Ineq(a, F.rat(X0[i + 1] - X0[i]), False))
    order = [nc + i for i in range(n)] + list(range(nc))
    return fm_feasible(ineqs, nv, order)


def eigenspace(As, F, n):
    lam = F.gen()
    rows = []
    for A in As:
        for i in range(n):
            rows.append([F.rat(A[i][j]) - (lam if i == j else 0) for j in range(n)])
    return nullspace(rows, n, F.rat(1), F.rat(0))


def full_feasible(model, n, Pp, Pm, F, X0, Xs, V):
    for k in range(len(V)):
        for sg in (1, -1):
            ineqs, nv, order = build_ineqs(model, n, Pp, Pm, None, F, X0, Xs, V, (k, sg))
            if fm_feasible(ineqs, nv, order):
                return (k, sg)
    return None


def run(inp, outp, lo=0, hi=None):
    t0 = time.time()
    recs = []
    found = []
    cnt = {'in': 0, 'clos_SBC': 0, 'clos_SBI': 0, 'const_SBC': 0, 'const_SBI': 0}
    with open(inp) as fi:
        lines = fi.readlines()
    for ln, line in enumerate(lines):
        if ln < lo or (hi is not None and ln >= hi):
            continue
        if killed():
            raise SystemExit('KILL')
        d = json.loads(line)
        n, N = d['n'], d['N']
        cnt['in'] += 1
        A = amat(N, n)
        fam = limit_family([A], n)
        if fam is None:
            continue
        X0, Xs = fam
        okm = [m for m in MODELS if closure_ok(m, n, [N], X0, Xs)]
        for m in okm:
            cnt['clos_' + m] += 1
        if not okm:
            continue
        cp = [Fr(c) for c in d['cp']]
        for F, key in lam_roots(cp):
            V = eigenspace([A], F, n)
            if not V:
                continue
            for m in okm:
                recs.append({'model': m, 'n': n, 'N': N, 'key': key, 'layout': d['layout']})
                res = full_feasible(m, n, N, N, F, X0, Xs, V)
                if res is not None:
                    cnt['const_' + m] += 1
                    found.append({'model': m, 'n': n, 'N': N, 'key': key, 'orient': res,
                                  'X0': [str(x) for x in X0], 'Xs': [[str(x) for x in X] for X in Xs],
                                  'V': [[str(x) for x in v] for v in V]})
        if ln % 500 == 0:
            print(ln, cnt, '%.1fs' % (time.time() - t0), flush=True)
    with open(outp, 'w') as fo:
        json.dump({'counts': cnt, 'constant_found': found, 'records': recs}, fo)
    print('done', cnt, '%.1fs' % (time.time() - t0))
    for f in found[:50]:
        print('FOUND', f['model'], f['N'], f['key'][0], f['orient'])


if __name__ == '__main__':
    lo = int(sys.argv[3]) if len(sys.argv) > 3 else 0
    hi = int(sys.argv[4]) if len(sys.argv) > 4 else None
    run(sys.argv[1], sys.argv[2], lo, hi)
