#!/usr/bin/env python3
"""Exact stdlib certificate: a five-agent constant-digraph SBI oscillation.

The all-time argument is in NOTES.md.  Arithmetic is Q(rho), with
60 rho^3 - 47 rho^2 + 9 rho - 1 = 0 and 57/100 < rho < 29/50.
No floating-point decisions and no assert statements are used.
"""
from fractions import Fraction as F
from itertools import product

POLY = (F(-1), F(9), F(-47), F(60))
ROOT_LO, ROOT_HI = F(57, 100), F(29, 50)


def require(ok, message):
    if not ok:
        raise ValueError(message)


def peval(coeffs, x):
    y = F(0)
    for c in reversed(coeffs):
        y = y * x + c
    return y


class K:
    """A polynomial of degree at most two in the specified real root."""
    def __init__(self, values=0):
        if isinstance(values, K):
            self.c = values.c
            return
        if not isinstance(values, (tuple, list)):
            values = [values]
        coeffs = [F(x) for x in values]
        while len(coeffs) > 3:
            a = coeffs.pop()
            k = len(coeffs) - 3
            # rho^3 = (1 - 9 rho + 47 rho^2)/60
            coeffs[k] += a / 60
            coeffs[k + 1] -= a * 9 / 60
            coeffs[k + 2] += a * 47 / 60
        coeffs += [F(0)] * (3 - len(coeffs))
        self.c = tuple(coeffs)

    def __add__(self, other):
        other = K(other)
        return K([a + b for a, b in zip(self.c, other.c)])
    __radd__ = __add__

    def __neg__(self):
        return K([-a for a in self.c])

    def __sub__(self, other):
        return self + (-K(other))

    def __rsub__(self, other):
        return K(other) - self

    def __mul__(self, other):
        other = K(other)
        coeffs = [F(0)] * 5
        for i, a in enumerate(self.c):
            for j, b in enumerate(other.c):
                coeffs[i + j] += a * b
        return K(coeffs)
    __rmul__ = __mul__

    def __truediv__(self, rational):
        return self * (F(1) / F(rational))

    def __pow__(self, n):
        require(isinstance(n, int) and n >= 0, 'only nonnegative powers')
        out = K(1)
        for _ in range(n):
            out *= self
        return out

    def __eq__(self, other):
        return self.c == K(other).c

    def interval(self):
        lo = hi = F(0)
        for c in reversed(self.c):
            corners = [lo * ROOT_LO, lo * ROOT_HI,
                       hi * ROOT_LO, hi * ROOT_HI]
            lo, hi = min(corners) + c, max(corners) + c
        return lo, hi

    def sign(self):
        global ROOT_LO, ROOT_HI
        if all(c == 0 for c in self.c):
            return 0
        for _ in range(4096):
            lo, hi = self.interval()
            if lo > 0:
                return 1
            if hi < 0:
                return -1
            mid = (ROOT_LO + ROOT_HI) / 2
            s = peval(POLY, mid)
            require(s != 0, 'unexpected rational root')
            if s < 0:
                ROOT_LO = mid
            else:
                ROOT_HI = mid
        raise ValueError('root interval did not resolve a nonzero field sign')

    def __repr__(self):
        return 'K' + repr(self.c)


def mv(A, v):
    return [sum((a * x for a, x in zip(row, v)), K(0)) for row in A]


def vadd(v, w):
    return [a + b for a, b in zip(v, w)]


def scale(a, v):
    return [a * x for x in v]


def matpow_vec(A, v, n):
    for _ in range(n):
        v = mv(A, v)
    return v


LIMIT = [0, 10, 18, 20, 42]
RADII = [31, 9, 5, 15, 28]
MASKS = [1, 11, 31, 29, 16]
Q = [[F(1, 3), 0, F(1, 3)],
     [F(1, 5), F(1, 5), F(1, 5)],
     [0, F(1, 4), F(1, 4)]]
A = [[F(1, bin(mask).count('1')) if (mask >> j) & 1 else F(0)
      for j in range(5)] for mask in MASKS]
RHO = K([0, 1])
INITIAL_DEVIATION = [K(F(1, 3)) - RHO, K(F(1, 5)), K(0)]
ALPHA = F(47, 60) - RHO
BETA = RHO * RHO - F(47, 60) * RHO + F(3, 20)


def verify_root():
    require(ROOT_LO == F(57, 100) and ROOT_HI == F(29, 50), 'root bracket is the stated one')
    require(peval(POLY, ROOT_LO) == F(-359, 12500), 'left endpoint')
    require(peval(POLY, ROOT_HI) == F(1449, 12500), 'right endpoint')
    a, b, c, d = 60, -47, 9, -1
    disc = b*b*c*c - 4*a*c*c*c - 4*b*b*b*d - 27*a*a*d*d + 18*a*b*c*d
    require(disc == -51683, 'cubic discriminant')
    # A cubic with no rational root is irreducible over Q.
    for denominator in range(1, 61):
        if 60 % denominator == 0:
            for s in (-1, 1):
                require(peval(POLY, F(s, denominator)) != 0, 'rational root')
    require(60 * RHO**3 - 47 * RHO**2 + 9 * RHO - 1 == 0, 'cubic reduction')
    require(60 * RHO * BETA == 1, 'beta product identity')
    require((ALPHA - F(61, 300)).sign() > 0, 'alpha lower bound')
    require((F(16, 75) - ALPHA).sign() > 0, 'alpha upper bound')
    require((BETA - F(5, 174)).sign() > 0, 'beta lower bound')
    require((F(5, 171) - BETA).sign() > 0, 'beta upper bound')
    require(F(61, 300)**2 - F(5, 171) == F(20699, 1710000), 'beta < alpha squared margin')
    require(2*F(5, 174) - F(16, 75)**2 == F(1951, 163125), 'alpha squared < 2 beta margin')
    require((ALPHA**2 - BETA).sign() > 0, 'beta < alpha squared')
    require((2*BETA - ALPHA**2).sign() > 0, 'alpha squared < 2 beta')


def verify_symbolic(radii=RADII, deviation=INITIAL_DEVIATION):
    require(all(r > 0 for r in radii), 'positive radii')
    require(mv(A, list(map(K, LIMIT))) == list(map(K, LIMIT)), 'harmonic limit')
    min_slack = None
    for i, j in product(range(5), repeat=2):
        if i == j:
            continue
        d = abs(LIMIT[i] - LIMIT[j])
        member = (MASKS[i] >> j) & 1
        slack = radii[j] - d if member else d - radii[j]
        require(slack > F(2, 3), 'strict cube membership margin')
        min_slack = slack if min_slack is None else min(min_slack, slack)
    require(min_slack == 1, 'minimum limit slack')
    for i, row in enumerate(Q):
        require(all(x >= 0 for x in row), 'Q nonnegative')
        require(sum(row) <= F(2, 3), 'Q contraction row bound')
        require(row == [A[i + 1][j] for j in (1, 2, 3)], 'transient submatrix')
    for x in deviation:
        require((F(1, 3) - x).sign() > 0, 'initial cube upper bound')
        require((F(1, 3) + x).sign() > 0, 'initial cube lower bound')
    first = mv(Q, deviation)
    second = mv(Q, first)
    require(second == vadd(scale(ALPHA, first), scale(-BETA, deviation)), 'quadratic recurrence seed')
    coeff1 = ALPHA * (ALPHA**2 - 2*BETA)
    coeff0 = BETA * (BETA - ALPHA**2)
    require(coeff1.sign() < 0 and coeff0.sign() < 0, 'strict negative four-step coefficients')
    require(matpow_vec(Q, deviation, 4) == vadd(scale(coeff1, first), scale(coeff0, deviation)), 'four-step identity')
    for j in range(3):
        require(deviation[j] != 0 or first[j] != 0, 'nonzero adjacent initial pair')
    require(first[2] == F(1, 20), 'third coordinate first step')


def independent_step(x):
    out = []
    masks = []
    for i in range(5):
        ns = []
        for j in range(5):
            delta = x[i] - x[j]
            if (K(RADII[j]) - delta).sign() >= 0 and (K(RADII[j]) + delta).sign() >= 0:
                ns.append(j)
        require(ns, 'empty neighborhood')
        out.append(sum((x[j] for j in ns), K(0)) / len(ns))
        masks.append(sum(1 << j for j in ns))
    return out, masks


def replay(T=200, deviation=INITIAL_DEVIATION, check_windows=True):
    expected = deviation
    x = [K(LIMIT[0])] + [K(LIMIT[j+1]) + expected[j] for j in range(3)] + [K(LIMIT[4])]
    signs = [[] for _ in range(3)]
    for t in range(T + 1):
        require(x[0] == LIMIT[0] and x[4] == LIMIT[4], 'anchors frozen')
        for j in range(3):
            actual = x[j+1] - LIMIT[j+1]
            require(actual == expected[j], 'independent update versus claimed recurrence')
            signs[j].append(actual.sign())
        x, masks = independent_step(x)
        require(masks == MASKS, 'constant digraph in independent replay')
        expected = mv(Q, expected)
    if not check_windows:
        return signs
    for j in range(3):
        for start in range(T - 3):
            window = signs[j][start:start+5]
            require(1 in window and -1 in window,
                    'five-window sign theorem replay: agent %d, window [%d, %d]'
                    % (j + 1, start, start + 4))
    print('Exact SBI update replay through t=%d; every five-window has both signs.' % T)
    print('First 25 signs, agents 1-3:', [''.join('+' if s > 0 else '-' if s < 0 else '0' for s in ss[:25]) for ss in signs])
    return signs


STATED = ([0, 10, 18, 20, 42], [31, 9, 5, 15, 28], [1, 11, 31, 29, 16])


def main():
    require((LIMIT, RADII, MASKS) == STATED, 'data differ from the system stated in NOTES.md')
    require(INITIAL_DEVIATION == [F(1, 3) - K([0, 1]), K(F(1, 5)), K(0)], 'x(0) differs from the one stated in NOTES.md')
    print('System: L =', LIMIT, '| r =', RADII, '| masks =', MASKS, '| x(0) = (0, 31/3 - rho, 91/5, 20, 42)')
    verify_root()
    verify_symbolic()
    print('All-time certificate: strict invariant cube, contraction, recurrence, four-step signs.')
    replay()
    controls = [('radius r1 changed to 15', [31, 15, 5, 15, 28], INITIAL_DEVIATION),
                ('initial first deviation shifted by 1/100', RADII,
                 [INITIAL_DEVIATION[0] + F(1, 100), INITIAL_DEVIATION[1], INITIAL_DEVIATION[2]])]
    for label, radii, deviation in controls:
        try:
            verify_symbolic(radii, deviation)
        except ValueError as e:
            print('Forged control rejected:', label, '->', e)
        else:
            raise ValueError('forged control accepted: ' + label)
    # Replay control: rho replaced by the rational 4/7, inside the root bracket.
    # The deviation stays in the strict cube, so the digraph and the recurrence
    # replay still hold; the Perron mode is no longer cancelled, and the
    # five-window sign check of the replay itself must reject the run.
    label = 'rho replaced by the rational 4/7 in the replay'
    forged_rho = K(F(4, 7))
    try:
        replay(deviation=[K(F(1, 3)) - forged_rho, K(F(1, 5)), K(0)])
    except ValueError as e:
        require(str(e).startswith('five-window sign theorem replay'),
                'replay control rejected for another reason: ' + str(e))
        print('Forged control rejected:', label, '->', e)
    else:
        raise ValueError('forged control accepted: ' + label)
    signs = replay(deviation=[K(F(1, 3)) - forged_rho, K(F(1, 5)), K(0)], check_windows=False)
    starts = []
    for j in range(3):
        last = signs[j][-1]
        start = len(signs[j])
        while start > 0 and signs[j][start - 1] == last:
            start -= 1
        require(last != 0 and start <= 10, 'rho = 4/7: agent %d not one-sided from t <= 10' % (j + 1))
        starts.append((j + 1, '+' if last > 0 else '-', start))
    print('rho = 4/7 (same digraph, exact): agent, sign, one-sided from t through 200:', starts)
    print('VERDICT: PASS')


if __name__ == '__main__':
    try:
        main()
    except Exception as e:
        print('FAIL:', e)
        print('VERDICT: FAIL')
        raise SystemExit(1)
