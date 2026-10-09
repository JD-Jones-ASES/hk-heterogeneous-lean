#!/usr/bin/env python3
"""Certificate 0008: constant-digraph systems with at most four agents (corroborates 0006 section 6).

Standard library only, exact arithmetic (Fractions and integers; no float enters a decision),
no assert statements. Agents are indexed from 0. A neighbourhood pattern is a tuple of masks:
bit j of masks[i] means j in N_i, and i is always in N_i. A is the averaging matrix of a pattern.

  1. Every pattern on n = 2, 3, 4 agents (4, 64, 4096 patterns): the exact limit Pi = lim A^t
     (closed-class stationary vectors and the transient solve, identified as the limit by
     A Pi = Pi, Pi A = Pi, Pi^2 = Pi, rank Pi = #closed classes = n - rank(A - I)); the pattern is
     OBSTRUCTED when a non-arc i -> j has equal rows of Pi (then x_i - x_j -> 0, impossible for a
     non-arc held forever with a positive radius, in SBC and in SBI). Expected unobstructed counts
     2, 8, 145. On every unobstructed pattern: all eigenvalues of A real and in [0, 1] (squarefree
     characteristic polynomial, Sturm counts on the line and on [0, 1]), every closed class
     complete, and the pattern complete or with >= 2 closed classes and <= 2 transient agents.
  2. The transient blocks Q of the unobstructed patterns: one transient (a) with 0 < a <= 1/2;
     two transients either [[a, a], [d, d]] (Q^2 = (a + d) Q, 0 < a + d <= 5/6) or triangular
     with a = d. A triangular block with a != d is a failure, and so is any departure from the
     table 54 full, 24 triangular (a = d = 1/3), one-transient a in {1/3, 1/4}.
  3. Exact HK replay, SBC and SBI, n = 2, 3, 4, seeded rational data (300 random systems per cell
     plus two near-limit systems per unobstructed pattern), 400 steps: the digraph recomputed from
     the states is constant on [200, 400], and the tail is fixed, or pseudo-stable as pinned
     (F at its limit, every agent of C strictly monotone towards its limit from one side) towards
     the limit Pi x(200) of the tail pattern. The tail patterns must be exactly the unobstructed
     ones. Rule anchors: the SBC and SBI rules reproduce the published tables of S1 (0001) and of
     the SBI5 system (0006) at their limits, and the other rule does not.
  4. Controls that must be rejected: the five-agent patterns (1,7,14,28,16) and (1,11,31,29,16)
     (structurally unobstructed, spectrally bad); tampered runs that admit obstructed patterns;
     a linear oscillation, a reflected coordinate and a displaced agent fed to the tail test.

The last line printed is VERDICT: PASS or VERDICT: FAIL (exit code 0 / 1).
"""
import random
import sys
import time
from fractions import Fraction as F
from itertools import permutations, product
from math import gcd

T0, T1 = 200, 400
SEED = 20261009
RANDOM_PER_CELL = 300
TARGETED_PER_PATTERN = 2
EXPECTED_UNOBSTRUCTED = {2: 2, 3: 8, 4: 145}
EXPECTED_PATTERNS = {2: 4, 3: 64, 4: 4096}

FAILURES = []


def fail(msg):
    FAILURES.append(msg)
    print('FAIL:', msg)


def lcm2(a, b):
    return a * b // gcd(a, b)


def lcm_all(values):
    out = 1
    for v in values:
        out = lcm2(out, v)
    return out


def popcount(m):
    return bin(m).count('1')


# ---------------------------------------------------------------- exact linear algebra

def pattern_matrix(masks):
    n = len(masks)
    rows = []
    for i in range(n):
        k = popcount(masks[i])
        rows.append([F(1, k) if masks[i] >> j & 1 else F(0) for j in range(n)])
    return rows


def matmul(A, B):
    n, m, p = len(A), len(B), len(B[0])
    return [[sum((A[i][k] * B[k][j] for k in range(m)), F(0)) for j in range(p)] for i in range(n)]


def rank(M):
    M = [list(r) for r in M]
    rows, cols = len(M), len(M[0])
    rk = 0
    for c in range(cols):
        piv = None
        for r in range(rk, rows):
            if M[r][c] != 0:
                piv = r
                break
        if piv is None:
            continue
        M[rk], M[piv] = M[piv], M[rk]
        for r in range(rows):
            if r != rk and M[r][c] != 0:
                f = M[r][c] / M[rk][c]
                M[r] = [a - f * b for a, b in zip(M[r], M[rk])]
        rk += 1
    return rk


def solve(M, B):
    """Exact Gauss-Jordan for a nonsingular square M; B is a matrix of right-hand sides."""
    m = len(M)
    aug = [list(M[i]) + list(B[i]) for i in range(m)]
    for c in range(m):
        piv = None
        for r in range(c, m):
            if aug[r][c] != 0:
                piv = r
                break
        if piv is None:
            raise ValueError('singular system')
        aug[c], aug[piv] = aug[piv], aug[c]
        pv = aug[c][c]
        aug[c] = [v / pv for v in aug[c]]
        for r in range(m):
            if r != c and aug[r][c] != 0:
                f = aug[r][c]
                aug[r] = [a - f * b for a, b in zip(aug[r], aug[c])]
    return [row[m:] for row in aug]


def reach_masks(masks):
    n = len(masks)
    R = list(masks)
    changed = True
    while changed:
        changed = False
        for i in range(n):
            new = R[i]
            for j in range(n):
                if R[i] >> j & 1:
                    new |= R[j]
            if new != R[i]:
                R[i] = new
                changed = True
    return R


def communicating_classes(masks):
    """[(agents, mask, closed)] in order of least member."""
    n = len(masks)
    R = reach_masks(masks)
    seen = 0
    out = []
    for i in range(n):
        if seen >> i & 1:
            continue
        members = [j for j in range(n) if R[i] >> j & 1 and R[j] >> i & 1]
        cm = sum(1 << j for j in members)
        seen |= cm
        out.append((members, cm, (R[i] & ~cm) == 0))
    return out


def limit_projector(A, classes):
    n = len(A)
    Pi = [[F(0)] * n for _ in range(n)]
    closed_agents = []
    for members, _, closed in classes:
        if not closed:
            continue
        closed_agents += members
        k = len(members)
        # stationary row vector: sum_a pi_a A[c_a][c_b] = pi_b, sum pi = 1
        M = [[A[members[a]][members[b]] - (1 if a == b else 0) for a in range(k)] for b in range(k)]
        M[-1] = [F(1)] * k
        rhs = [[F(0)] for _ in range(k)]
        rhs[-1][0] = F(1)
        pi = [row[0] for row in solve(M, rhs)]
        for i in members:
            for a, j in enumerate(members):
                Pi[i][j] = pi[a]
    T = [i for i in range(n) if i not in closed_agents]
    if T:
        IQ = [[(1 if a == b else 0) - A[T[a]][T[b]] for b in range(len(T))] for a in range(len(T))]
        RP = [[sum((A[T[a]][c] * Pi[c][j] for c in closed_agents), F(0)) for j in range(n)]
              for a in range(len(T))]
        X = solve(IQ, RP)
        for a, i in enumerate(T):
            Pi[i] = X[a]
    return Pi, T


def projector_problems(A, Pi, nclosed):
    n = len(A)
    out = []
    if matmul(A, Pi) != Pi:
        out.append('A Pi != Pi')
    if matmul(Pi, A) != Pi:
        out.append('Pi A != Pi')
    if matmul(Pi, Pi) != Pi:
        out.append('Pi^2 != Pi')
    if rank(Pi) != nclosed:
        out.append('rank Pi != #closed classes')
    AmI = [[A[i][j] - (1 if i == j else 0) for j in range(n)] for i in range(n)]
    if n - rank(AmI) != nclosed:
        out.append('dim ker(A - I) != #closed classes')
    if any(sum(row) != 1 or min(row) < 0 for row in Pi):
        out.append('Pi not stochastic')
    return out


# ---------------------------------------------------------------- polynomials (low degree first)

def ptrim(p):
    p = list(p)
    while len(p) > 1 and p[-1] == 0:
        p.pop()
    return p if p else [F(0)]


def pzero(p):
    return len(p) == 1 and p[0] == 0


def pmul_int(p, q):
    r = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            r[i + j] += a * b
    return r


def pderiv(p):
    return ptrim([i * p[i] for i in range(1, len(p))] or [F(0)])


def pdivmod(a, b):
    a = ptrim(a)
    b = ptrim(b)
    if pzero(b):
        raise ValueError('division by the zero polynomial')
    q = [F(0)] * max(1, len(a) - len(b) + 1)
    while len(a) >= len(b) and not pzero(a):
        c = a[-1] / b[-1]
        d = len(a) - len(b)
        q[d] = c
        for k in range(len(b)):
            a[d + k] -= c * b[k]
        a.pop()
        a = ptrim(a)
    return ptrim(q), a


def pgcd(a, b):
    a, b = ptrim(a), ptrim(b)
    while not pzero(b):
        _, r = pdivmod(a, b)
        a, b = b, r
    return [c / a[-1] for c in a]


def peval(p, x):
    s = F(0)
    for c in reversed(p):
        s = s * x + c
    return s


def sgn(x):
    return (x > 0) - (x < 0)


def variations(signs):
    nz = [s for s in signs if s != 0]
    return sum(1 for a, b in zip(nz, nz[1:]) if a != b)


def sturm_sequence(p):
    seq = [ptrim(p), pderiv(p)]
    while not pzero(seq[-1]):
        _, r = pdivmod(seq[-2], seq[-1])
        seq.append([-c for c in r])
    seq.pop()
    return seq


def charpoly(masks):
    """det(sI - A), monic, low degree first: det(diag(k) s - B) / prod(k) by the Leibniz expansion."""
    n = len(masks)
    k = [popcount(m) for m in masks]
    total = [0] * (n + 1)
    for perm in permutations(range(n)):
        inversions = sum(1 for a in range(n) for b in range(a + 1, n) if perm[a] > perm[b])
        poly = [1]
        for i in range(n):
            j = perm[i]
            if i == j:
                poly = pmul_int(poly, [-1, k[i]])
            elif masks[i] >> j & 1:
                poly = pmul_int(poly, [-1])
            else:
                poly = None
                break
        if poly is None:
            continue
        s = -1 if inversions % 2 else 1
        for d, c in enumerate(poly):
            total[d] += s * c
    pk = 1
    for v in k:
        pk *= v
    return [F(c, pk) for c in total]


def spectrum(masks, A):
    """(degree of the squarefree part, its distinct real roots, its distinct roots in [0, 1], problems)."""
    n = len(masks)
    p = charpoly(masks)
    problems = []
    if p[-1] != 1 or len(p) != n + 1:
        problems.append('characteristic polynomial not monic of degree n')
    if peval(p, F(1)) != 0:
        problems.append('1 is not a root of the characteristic polynomial')
    if p[n - 1] != -sum(A[i][i] for i in range(n)):
        problems.append('s^(n-1) coefficient != -trace A')
    g = pgcd(p, pderiv(p))
    sf, rem = pdivmod(p, g)
    if not pzero(rem):
        problems.append('squarefree division left a remainder')
    seq = sturm_sequence(sf)
    deg = len(sf) - 1
    at_minus = variations([sgn(q[-1]) * (1 if (len(q) - 1) % 2 == 0 else -1) for q in seq])
    at_plus = variations([sgn(q[-1]) for q in seq])
    v0 = variations([sgn(peval(q, F(0))) for q in seq])
    v1 = variations([sgn(peval(q, F(1))) for q in seq])
    n_real = at_minus - at_plus
    n_01 = v0 - v1 + (1 if peval(sf, F(0)) == 0 else 0)
    return deg, n_real, n_01, problems


# ---------------------------------------------------------------- pattern analysis

class Pattern:
    def __init__(self, masks):
        self.masks = tuple(masks)
        n = self.n = len(masks)
        self.A = pattern_matrix(masks)
        self.classes = communicating_classes(masks)
        self.closed = [(m, cm) for m, cm, c in self.classes if c]
        self.Pi, self.transients = limit_projector(self.A, self.classes)
        self.projector_problems = projector_problems(self.A, self.Pi, len(self.closed))
        self.obstructed = any(not masks[i] >> j & 1 and self.Pi[i] == self.Pi[j]
                              for i in range(n) for j in range(n) if i != j)
        self.deg, self.n_real, self.n_01, self.spec_problems = spectrum(masks, self.A)
        self.spectral_ok = self.n_real == self.deg and self.n_01 == self.deg
        self.complete = all(m == (1 << n) - 1 for m in masks)

    def structure_problems(self):
        out = []
        if not self.spectral_ok:
            out.append('eigenvalue non-real or outside [0,1] (%d of %d distinct roots real, %d in [0,1])'
                       % (self.n_real, self.deg, self.n_01))
        for members, cm in self.closed:
            if any(self.masks[i] != cm for i in members):
                out.append('closed class %s not complete' % members)
        if not (self.complete or (len(self.closed) >= 2 and len(self.transients) <= 2)):
            out.append('neither complete nor (>= 2 closed classes, <= 2 transients): %d closed, %d transient'
                       % (len(self.closed), len(self.transients)))
        return out

    def block(self):
        """(shape, values, problems) of the transient block Q."""
        T = self.transients
        Q = [[self.A[i][j] for j in T] for i in T]
        out = []
        for a in range(len(T)):
            if not (0 < Q[a][a] <= F(1, 2)):
                out.append('transient diagonal %s not in (0, 1/2]' % Q[a][a])
        if len(T) == 0:
            return 'none', (), out
        if len(T) == 1:
            return 'one', (Q[0][0],), out
        if len(T) == 2:
            a, b, c, d = Q[0][0], Q[0][1], Q[1][0], Q[1][1]
            if b != 0 and c != 0:
                if b != a or c != d:
                    out.append('full block not of the form [[a,a],[d,d]]')
                if matmul(Q, Q) != [[(a + d) * v for v in row] for row in Q]:
                    out.append('Q^2 != (a+d) Q')
                if not (0 < a + d <= F(5, 6)):
                    out.append('a + d not in (0, 5/6]')
                return 'full', (a, d), out
            if a != d:
                out.append('triangular block with a != d (a = %s, d = %s)' % (a, d))
            return ('diagonal' if b == 0 and c == 0 else 'triangular'), (a, d), out
        return 'larger', (), out


def all_patterns(n):
    choices = [[m for m in range(1 << n) if m >> i & 1] for i in range(n)]
    return product(*choices)


def run_part1(n, patterns, obstruction_ignored=False, verbose=True):
    """Classify every pattern; return (unobstructed list, failure messages)."""
    msgs = []
    admitted = []
    n_obstructed = 0
    spec_bad_all = 0
    proj_ok = 0
    for P in patterns:
        if P.projector_problems or P.spec_problems:
            msgs.append('n=%d %s: %s' % (n, P.masks, P.projector_problems + P.spec_problems))
        else:
            proj_ok += 1
        spec_bad_all += not P.spectral_ok
        if P.obstructed:
            n_obstructed += 1
            if not obstruction_ignored:
                continue
        admitted.append(P)
    struct_bad = block_bad = 0
    for P in admitted:
        sp = P.structure_problems()
        _, _, bp = P.block()
        struct_bad += bool(sp)
        block_bad += bool(bp)
        if sp or bp:
            msgs.append('n=%d %s admitted but %s' % (n, P.masks, '; '.join(sp + bp)))
    if len(admitted) != EXPECTED_UNOBSTRUCTED[n]:
        msgs.append('n=%d: %d admitted patterns, expected %d' % (n, len(admitted), EXPECTED_UNOBSTRUCTED[n]))
    if verbose:
        print('  n=%d: %d patterns; Pi = lim A^t identified on %d; obstructed %d, unobstructed %d (expected %d);'
              % (n, len(patterns), proj_ok, n_obstructed, len(patterns) - n_obstructed, EXPECTED_UNOBSTRUCTED[n]))
        print('        admitted patterns failing the spectral/clique/shape checks: %d, the block checks: %d;'
              ' spectrally bad overall: %d' % (struct_bad, block_bad, spec_bad_all))
    return admitted, msgs, struct_bad, block_bad


# ---------------------------------------------------------------- exact HK replay (integer form)

def to_int_state(xs):
    D = lcm_all([x.denominator for x in xs])
    X = tuple(x.numerator * (D // x.denominator) for x in xs)
    g = gcd(D, *X)
    return tuple(v // g for v in X), D // g


def hk_masks(model, rn, rd, state):
    X, D = state
    n = len(X)
    out = []
    for i in range(n):
        m = 0
        xi = X[i]
        for j in range(n):
            b = i if model == 'sbc' else j
            if abs(xi - X[j]) * rd[b] <= rn[b] * D:
                m |= 1 << j
        out.append(m)
    return tuple(out)


def hk_step(masks, state):
    X, D = state
    n = len(X)
    sizes = [popcount(m) for m in masks]
    K = lcm_all(sizes)
    Y = []
    for i in range(n):
        s = 0
        for j in range(n):
            if masks[i] >> j & 1:
                s += X[j]
        Y.append(s * (K // sizes[i]))
    D2 = D * K
    g = gcd(D2, *Y)
    return tuple(y // g for y in Y), D2 // g


def replay(model, r, x0, T=T1):
    """States x(0..T) of the HK update; a state equal to its successor is fixed for ever."""
    rn = [v.numerator for v in r]
    rd = [v.denominator for v in r]
    s = to_int_state(x0)
    states = [s]
    for _ in range(T):
        s2 = hk_step(hk_masks(model, rn, rd, s), s)
        if s2 == s:
            states.extend([s] * (T + 1 - len(states)))
            break
        s = s2
        states.append(s)
    return states


def tail_digraph(model, r, states):
    """The digraph recomputed from the states on [T0, T1]: (masks, None) if constant, else (None, t)."""
    rn = [v.numerator for v in r]
    rd = [v.denominator for v in r]
    m0 = hk_masks(model, rn, rd, states[T0])
    prev = states[T0]
    for t in range(T0 + 1, T1 + 1):
        if states[t] == prev:
            continue
        if hk_masks(model, rn, rd, states[t]) != m0:
            return None, t
        prev = states[t]
    return m0, None


def classify_tail(P, xs):
    """xs = x(T0), ..., x(T1) as Fractions; P = the tail pattern. Fixed / pseudo-stable / violation."""
    n = P.n
    L = [sum((P.Pi[i][j] * xs[0][j] for j in range(n)), F(0)) for i in range(n)]
    if all(x == xs[0] for x in xs):
        if L != xs[0]:
            return 'violation', 'fixed tail state differs from its limit'
        return 'fixed', None
    Fset = [i for i in range(n) if all(x[i] == L[i] for x in xs)]
    C = [i for i in range(n) if i not in Fset]
    if not Fset:
        return 'violation', 'no agent sits at its limit (F empty)'
    for i in C:
        for t in range(len(xs) - 1):
            a, b = xs[t][i], xs[t + 1][i]
            if not ((a < b < L[i]) or (a > b > L[i])):
                return 'violation', 'agent %d not strictly monotone to its limit from one side at t=%d' % (i, T0 + t)
    return 'pseudo-stable', (Fset, C)


def tail_fractions(states):
    out = []
    cache = {}
    for s in states[T0:T1 + 1]:
        if s not in cache:
            X, D = s
            cache[s] = [F(v, D) for v in X]
        out.append(cache[s])
    return out


def random_system(rng, n):
    scale = rng.choice([10, 30, 60])
    x0 = [F(rng.randint(0, 4 * scale), rng.choice([1, 1, 2, 3])) for _ in range(n)]
    r = [F(rng.randint(1, scale), rng.choice([1, 1, 2, 3])) for _ in range(n)]
    return r, x0


def targeted_system(rng, P, model, attempts=60):
    """Rational radii and a start near a limit at which P holds strictly (the replay decides the rest)."""
    n = P.n
    m = P.masks
    for _ in range(attempts):
        x0 = [F(rng.randint(0, 40)) for _ in range(n)]
        L = [sum((P.Pi[i][j] * x0[j] for j in range(n)), F(0)) for i in range(n)]
        r = []
        for k in range(n):
            if model == 'sbc':
                arcs = [abs(L[k] - L[j]) for j in range(n) if j != k and m[k] >> j & 1]
                non = [abs(L[k] - L[j]) for j in range(n) if not m[k] >> j & 1]
            else:
                arcs = [abs(L[i] - L[k]) for i in range(n) if i != k and m[i] >> k & 1]
                non = [abs(L[i] - L[k]) for i in range(n) if not m[i] >> k & 1]
            lo = max(arcs) if arcs else F(0)
            if not non:
                r.append(lo + 1)
            elif lo < min(non):
                r.append((lo + min(non)) / 2)
            else:
                r = None
                break
        if r is None:
            continue
        bound = (lambda i, j: r[i]) if model == 'sbc' else (lambda i, j: r[j])
        slack = min(abs(abs(L[i] - L[j]) - bound(i, j)) for i in range(n) for j in range(n) if i != j)
        eps = slack / 8
        y0 = [L[i] + eps * F(rng.randint(-10, 10), 10) for i in range(n)]
        return r, y0
    return None


def run_part3(patterns_by_mask, unobstructed_by_n):
    rng = random.Random(SEED)
    all_tail = {}
    sample_pseudo = None
    for model in ('sbc', 'sbi'):
        for n in (2, 3, 4):
            systems = []
            for _ in range(RANDOM_PER_CELL):
                systems.append(('random',) + random_system(rng, n))
            n_target = 0
            for P in unobstructed_by_n[n]:
                for _ in range(TARGETED_PER_PATTERN):
                    got = targeted_system(rng, P, model)
                    if got is not None:
                        systems.append(('targeted',) + got)
                        n_target += 1
            counts = {'fixed': 0, 'pseudo-stable': 0, 'violation': 0, 'tail digraph not constant': 0,
                      'tail pattern obstructed': 0}
            tails = set()
            for kind, r, x0 in systems:
                states = replay(model, r, x0)
                masks, t_change = tail_digraph(model, r, states)
                if masks is None:
                    counts['tail digraph not constant'] += 1
                    fail('%s n=%d %s r=%s x0=%s: digraph changes at t=%d in [%d, %d]'
                         % (model, n, kind, [str(v) for v in r], [str(v) for v in x0], t_change, T0, T1))
                    continue
                P = patterns_by_mask[masks]
                tails.add(masks)
                if P.obstructed:
                    counts['tail pattern obstructed'] += 1
                    fail('%s n=%d tail pattern %s is obstructed' % (model, n, masks))
                verdict, info = classify_tail(P, tail_fractions(states))
                counts[verdict] += 1
                if verdict == 'violation':
                    fail('%s n=%d %s r=%s x0=%s: %s' % (model, n, kind, [str(v) for v in r],
                                                         [str(v) for v in x0], info))
                elif verdict == 'pseudo-stable':
                    closed_agents = [i for mem, _ in P.closed for i in mem]
                    if any(i not in info[0] for i in closed_agents):
                        counts['violation'] += 1
                        fail('%s n=%d: a closed-class agent is not frozen on the tail' % (model, n))
                    if sample_pseudo is None and n == 4:
                        sample_pseudo = (model, r, x0, states, masks)
                all_tail.setdefault(masks, set()).add(model)
            n_tr = [len(patterns_by_mask[m].transients) for m in tails]
            print('  %s n=%d: %d systems (%d random, %d near-limit); fixed %d, pseudo-stable %d, violations %d, '
                  'tail digraph not constant %d, obstructed tail patterns %d'
                  % (model.upper(), n, len(systems), RANDOM_PER_CELL, n_target, counts['fixed'],
                     counts['pseudo-stable'], counts['violation'], counts['tail digraph not constant'],
                     counts['tail pattern obstructed']))
            print('        distinct tail patterns %d (with 0/1/2 transient agents: %d/%d/%d)'
                  % (len(tails), n_tr.count(0), n_tr.count(1), n_tr.count(2)))
    return all_tail, sample_pseudo


# ---------------------------------------------------------------- main

def main():
    t_start = time.perf_counter()
    print('Certificate 0008: constant-digraph systems with at most four agents (exact).')

    print('[1] Every neighbourhood pattern, n = 2, 3, 4')
    patterns_by_mask = {}
    unobstructed_by_n = {}
    all_by_n = {}
    for n in (2, 3, 4):
        pats = [Pattern(m) for m in all_patterns(n)]
        if len(pats) != EXPECTED_PATTERNS[n]:
            fail('n=%d: %d patterns enumerated, expected %d' % (n, len(pats), EXPECTED_PATTERNS[n]))
        for P in pats:
            patterns_by_mask[P.masks] = P
        all_by_n[n] = pats
        admitted, msgs, _, _ = run_part1(n, pats)
        for msg in msgs:
            fail(msg)
        unobstructed_by_n[n] = admitted
        shapes = {}
        for P in admitted:
            key = 'complete' if P.complete else '%d closed + %d transient' % (len(P.closed), len(P.transients))
            shapes[key] = shapes.get(key, 0) + 1
        print('        unobstructed by shape:', ', '.join('%s: %d' % kv for kv in sorted(shapes.items())))
    print('  time %.1fs' % (time.perf_counter() - t_start))

    print('[2] Transient blocks of the unobstructed patterns')
    for n in (2, 3, 4):
        groups = {}
        for P in unobstructed_by_n[n]:
            shape, vals, _ = P.block()
            groups.setdefault(shape, {}).setdefault(tuple(str(v) for v in vals), 0)
            groups[shape][tuple(str(v) for v in vals)] += 1
        parts = []
        for shape in sorted(groups):
            g = groups[shape]
            label = {'full': 'full [[a,a],[d,d]]', 'triangular': 'triangular', 'diagonal': 'diagonal',
                     'one': 'one transient (a)', 'none': 'no transient', 'larger': 'larger'}[shape]
            parts.append('%s %d%s' % (label, sum(g.values()), '' if shape == 'none' else ' [' + ', '.join(
                '(%s) x%d' % (', '.join(k), c) for k, c in sorted(g.items())) + ']'))
        print('  n=%d: %s' % (n, '; '.join(parts)))
    print('  (values listed as (a, d) for two transients: a = Q[0][0], d = Q[1][1])')
    tri_bad = [P.masks for n in (2, 3, 4) for P in unobstructed_by_n[n]
               if P.block()[0] in ('triangular', 'diagonal') and P.block()[1][0] != P.block()[1][1]]
    print('  triangular two-transient blocks with a != d: %d' % len(tri_bad))
    if tri_bad:
        fail('triangular blocks with a != d occur: %s' % tri_bad[:5])
    # the block table stated in NOTES.md: 54 full, 24 triangular (all a = d = 1/3), one transient a in {1/3, 1/4}
    blocks = [P.block() for n in (2, 3, 4) for P in unobstructed_by_n[n]]
    n_full = sum(1 for s, _, _ in blocks if s == 'full')
    tri_vals = [v for s, v, _ in blocks if s in ('triangular', 'diagonal')]
    one_vals = set(v[0] for s, v, _ in blocks if s == 'one')
    if (n_full != 54 or len(tri_vals) != 24 or any(v != (F(1, 3), F(1, 3)) for v in tri_vals)
            or not one_vals <= {F(1, 3), F(1, 4)}):
        fail('block table differs from NOTES.md: %d full, %d triangular/diagonal, one-transient a in %s'
             % (n_full, len(tri_vals), sorted(str(v) for v in one_vals)))

    print('[3] Exact HK replay, both models, %d steps, tail [%d, %d], seed %d' % (T1, T0, T1, SEED))
    t3 = time.perf_counter()
    # rule anchors: the neighbourhood rule reproduces the published tables of S1 (SBC, 0001) and of
    # the SBI5 system (0006) at their limits, and the two models differ on each
    for model, xs, r, want in [('sbc', (0, 6, 12, 18, 24), (3, 9, 9, 9, 3), (1, 7, 14, 28, 16)),
                               ('sbi', (0, 10, 18, 20, 42), (31, 9, 5, 15, 28), (1, 11, 31, 29, 16))]:
        other = 'sbi' if model == 'sbc' else 'sbc'
        got = hk_masks(model, list(r), [1] * 5, (xs, 1))
        got_other = hk_masks(other, list(r), [1] * 5, (xs, 1))
        if got != want or got_other == want:
            fail('rule anchor %s r=%s: masks %s (expected %s), %s rule gives %s'
                 % (model.upper(), r, got, want, other.upper(), got_other))
        else:
            print('  rule anchor %s r=%s at its limit: masks %s; the %s rule gives %s'
                  % (model.upper(), r, got, other.upper(), got_other))
    all_tail, sample_pseudo = run_part3(patterns_by_mask, unobstructed_by_n)
    two = sorted(m for m in all_tail if len(patterns_by_mask[m].transients) == 2)
    shape_count = {}
    for m in two:
        s = patterns_by_mask[m].block()[0]
        shape_count[s] = shape_count.get(s, 0) + 1
    print('  distinct tail patterns over all cells: %d; two-transient tail patterns: %d (%s)'
          % (len(all_tail), len(two), ', '.join('%s %d' % kv for kv in sorted(shape_count.items()))))
    unob = set(P.masks for n in (2, 3, 4) for P in unobstructed_by_n[n])
    for model in ('sbc', 'sbi'):
        got = set(m for m, ms in all_tail.items() if model in ms)
        print('  %s tail patterns cover %d of the %d unobstructed patterns' % (model.upper(), len(got & unob), len(unob)))
    print('  both models together cover %d of %d; tail patterns outside the unobstructed set: %d'
          % (len(set(all_tail) & unob), len(unob), len(set(all_tail) - unob)))
    if set(all_tail) != unob:
        fail('tail patterns are not exactly the unobstructed patterns (%d unrealized, %d outside)'
             % (len(unob - set(all_tail)), len(set(all_tail) - unob)))
    print('  time %.1fs' % (time.perf_counter() - t3))

    print('[4] Controls (each must be rejected)')
    rejected = 0
    expected_rejections = 0
    for masks in [(1, 7, 14, 28, 16), (1, 11, 31, 29, 16)]:
        expected_rejections += 1
        P = Pattern(masks)
        structural = (not P.obstructed and not P.projector_problems and len(P.closed) >= 2
                      and all(all(P.masks[i] == cm for i in mem) for mem, cm in P.closed))
        if not structural:
            fail('control %s should be structurally unobstructed (obstructed=%s, closed=%s)'
                 % (masks, P.obstructed, [c for c, _ in P.closed]))
        elif P.spectral_ok:
            fail('control %s accepted by the spectral test' % (masks,))
        else:
            rejected += 1
            print('  n=5 %s: unobstructed, closed classes %s complete, %d transients; spectral test rejects it:'
                  ' %d of %d distinct roots real, %d in [0,1]'
                  % (masks, [c for c, _ in P.closed], len(P.transients), P.n_real, P.deg, P.n_01))

    for n in (3, 4):
        expected_rejections += 1
        admitted, msgs, sb, bb = run_part1(n, all_by_n[n], obstruction_ignored=True, verbose=False)
        if msgs:
            rejected += 1
            print('  tampered run n=%d (obstruction test switched off): rejected; %d patterns admitted '
                  '(expected %d), %d fail spectral/clique/shape, %d fail the block checks, %d pass both'
                  % (n, len(admitted), EXPECTED_UNOBSTRUCTED[n], sb, bb,
                     sum(1 for P in admitted if not P.structure_problems() and not P.block()[2])))
        else:
            fail('tampered run n=%d accepted' % n)

    for masks, label in [((3, 6, 5), 'three-cycle'), ((1, 11, 5, 8), 'triangular a=1/3, d=1/2')]:
        expected_rejections += 1
        P = patterns_by_mask[masks]
        probs = P.structure_problems() + P.block()[2]
        if not P.obstructed:
            fail('control %s should be obstructed' % (masks,))
        elif probs:
            rejected += 1
            print('  obstructed %s %s treated as admissible: rejected (%s)' % (label, masks, '; '.join(probs)))
        else:
            fail('obstructed control %s passes every admissibility check' % (masks,))

    # linear oscillation: a frozen agent beside a closed three-cycle (complex eigenvalues), iterated by A
    expected_rejections += 1
    P = patterns_by_mask[(3, 6, 5, 8)]
    x = [F(0), F(1), F(5), F(9)]
    xs = [x]
    for _ in range(T1):
        x = [sum((P.A[i][j] * x[j] for j in range(4)), F(0)) for i in range(4)]
        xs.append(x)
    v, info = classify_tail(P, xs[T0:T1 + 1])
    if v == 'violation':
        rejected += 1
        print('  x(t+1) = A x(t) for the pattern (3, 6, 5, 8) from (0,1,5,9): tail test rejects it (%s)' % info)
    else:
        fail('linear oscillation classified %s' % v)

    if sample_pseudo is None:
        fail('no pseudo-stable n=4 run to forge from')
    else:
        model, r, x0, states, masks = sample_pseudo
        P = patterns_by_mask[masks]
        xs = [list(x) for x in tail_fractions(states)]
        _, (Fset, C) = classify_tail(P, xs)
        i = C[0]
        L = [sum((P.Pi[a][j] * xs[0][j] for j in range(P.n)), F(0)) for a in range(P.n)]
        k = T1 - T0 - 100
        forged = [list(x) for x in xs]
        forged[k][i] = 2 * L[i] - forged[k][i]
        forged_states = list(states[:T0]) + [to_int_state(x) for x in forged]
        expected_rejections += 1
        m2, _ = tail_digraph(model, r, forged_states)
        v, info = classify_tail(P, forged)
        if m2 == masks and v == 'violation':
            rejected += 1
            print('  %s n=4 run %s, agent %d reflected across its limit at t=%d (digraph unchanged): '
                  'tail test rejects it (%s)' % (model.upper(), masks, i, T0 + k, info))
        else:
            fail('reflected forgery not rejected by the tail test (digraph same: %s, verdict %s)' % (m2 == masks, v))
        expected_rejections += 1
        moved = [list(x) for x in xs]
        moved[k][0] = moved[k][0] + 1000
        moved_states = list(states[:T0]) + [to_int_state(x) for x in moved]
        m3, t_change = tail_digraph(model, r, moved_states)
        if m3 is None:
            rejected += 1
            print('  same run, agent 0 displaced by 1000 at t=%d: rejected (tail digraph changes at t=%d)'
                  % (T0 + k, t_change))
        else:
            fail('displaced forgery not detected')
    print('  controls rejected: %d of %d' % (rejected, expected_rejections))

    total = time.perf_counter() - t_start
    print('genuine failures: %d; total time %.1fs' % (len(FAILURES), total))
    if FAILURES:
        print('VERDICT: FAIL')
        sys.exit(1)
    print('VERDICT: PASS')


if __name__ == '__main__':
    main()
