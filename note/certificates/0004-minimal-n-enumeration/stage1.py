"""Stage 1 of the minimal-n probe: algebraic filter on single neighbourhood patterns.

A pattern on n agents (labels 0..n-1 sorted by the limit x_inf, ties allowed) is a tuple of
bitmasks N[i] with bit i set. Proven reductions (Lemma 1 of the note):
  * every closed class of the pattern is a cluster of agents with equal limit, complete, frozen;
  * the min cluster and the max cluster are closed classes; the eigenvalue lam lives in the
    transient block Q, which needs at least 3 agents; at least two closed classes.
So a pattern is given by a layout (the closed clusters, as label blocks) plus arbitrary rows for
the transient agents. Filters, all exact:
  F1 every transient agent reaches a closed cluster (so the closed classes are exactly the layout);
  F2 the harmonic limit (min cluster 0, max cluster 1, a middle cluster c free) can be
     non-decreasing in label order with transient values strictly inside (0,1);
  F3 the characteristic polynomial of Q has a root in (-1, 0).
Output: one line per survivor: n, layout, masks, charpoly(Q) coefficients.
"""
import os, sys, itertools, time, json
from fractions import Fraction as Fr
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from exactlib import charpoly, count_roots_open, killed, peval, squarefree


def layouts(n):
    """closed clusters as lists of label blocks; total closed agents <= n-3."""
    out = []
    # two clusters: [0..a-1] and [b..n-1]
    for a in range(1, n):
        for bsz in range(1, n):
            if a + bsz <= n - 3:
                out.append([list(range(a)), list(range(n - bsz, n))])
    # three clusters, middle block anywhere strictly inside, all with total <= n-3
    for a in range(1, n):
        for bsz in range(1, n):
            for msz in range(1, n):
                if a + bsz + msz > n - 3:
                    continue
                for start in range(a + 1, n - bsz - msz):  # at least one transient on each side? no: allow adjacency
                    pass
    # middle cluster: any block of labels strictly between, not adjacent constraint-free
    for a in range(1, n):
        for bsz in range(1, n):
            for msz in range(1, n):
                if a + bsz + msz > n - 3:
                    continue
                for start in range(a, n - bsz - msz + 1):
                    mid = list(range(start, start + msz))
                    out.append([list(range(a)), mid, list(range(n - bsz, n))])
    # four or more closed clusters need n >= 7 (4 + 3)
    return out


def solve(M, rhs_list):
    """solve M y = rhs for several rhs, M square nonsingular over Q (Gauss-Jordan)."""
    n = len(M)
    A = [list(M[i]) + [r[i] for r in rhs_list] for i in range(n)]
    for col in range(n):
        p = next((r for r in range(col, n) if A[r][col] != 0), None)
        if p is None:
            return None
        A[col], A[p] = A[p], A[col]
        iv = 1 / A[col][col]
        A[col] = [x * iv for x in A[col]]
        for r in range(n):
            if r != col and A[r][col] != 0:
                f = A[r][col]
                A[r] = [a - f * b for a, b in zip(A[r], A[col])]
    return [[A[i][n + k] for i in range(n)] for k in range(len(rhs_list))]


def run(n, out_path):
    t0 = time.time()
    total = surv = 0
    stats = {}
    with open(out_path, 'w') as fo:
        for lay in layouts(n):
            closed = sorted(sum(lay, []))
            cl_of = {}
            for k, blk in enumerate(lay):
                for i in blk:
                    cl_of[i] = k
            T = [i for i in range(n) if i not in cl_of]
            tidx = {i: k for k, i in enumerate(T)}
            others = {i: [j for j in range(n) if j != i] for i in T}
            opts = {}
            for i in T:
                lst = []
                for bits in range(1 << (n - 1)):
                    m = 1 << i
                    for k, j in enumerate(others[i]):
                        if bits >> k & 1:
                            m |= 1 << j
                    lst.append(m)
                opts[i] = lst
            closedmask = 0
            for i in closed:
                closedmask |= 1 << i
            nmid = len(lay) == 3
            cnt_lay = [0, 0, 0, 0]
            for rows in itertools.product(*[opts[i] for i in T]):
                total += 1
                if total % 20000 == 0 and killed():
                    raise SystemExit('KILL')
                N = [0] * n
                for blk in lay:
                    m = 0
                    for i in blk:
                        m |= 1 << i
                    for i in blk:
                        N[i] = m
                for i, m in zip(T, rows):
                    N[i] = m
                # F1: reach closed set from every transient agent
                reach = {i: N[i] for i in T}
                changed = True
                while changed:
                    changed = False
                    for i in T:
                        r = reach[i]
                        nr = r
                        for j in T:
                            if r >> j & 1:
                                nr |= reach[j]
                        if nr != r:
                            reach[i] = nr
                            changed = True
                if any(reach[i] & closedmask == 0 for i in T):
                    continue
                cnt_lay[0] += 1
                # F2: harmonic limit. (I - Q) xT = A_TR xR ; xR: cluster0 -> 0, last -> 1, middle -> c
                t = len(T)
                IQ = []
                b0 = []
                b1 = []
                for i in T:
                    deg = bin(N[i]).count('1')
                    row = [Fr(0)] * t
                    s0 = Fr(0)
                    s1 = Fr(0)
                    for j in range(n):
                        if N[i] >> j & 1:
                            if j in tidx:
                                row[tidx[j]] -= Fr(1, deg)
                            else:
                                k = cl_of[j]
                                if k == len(lay) - 1:
                                    s0 += Fr(1, deg)
                                elif nmid and k == 1:
                                    s1 += Fr(1, deg)
                    row[tidx[i]] += 1
                    IQ.append(row)
                    b0.append(s0)
                    b1.append(s1)
                sol = solve(IQ, [b0, b1])
                if sol is None:
                    continue  # cannot happen when F1 holds (I-Q invertible)
                x0, x1 = sol
                # full limit vector as affine in c: X = X0 + c X1
                X0 = [Fr(0)] * n
                X1 = [Fr(0)] * n
                for i in range(n):
                    if i in tidx:
                        X0[i], X1[i] = x0[tidx[i]], x1[tidx[i]]
                    else:
                        k = cl_of[i]
                        if k == len(lay) - 1:
                            X0[i] = Fr(1)
                        elif nmid and k == 1:
                            X1[i] = Fr(1)
                # constraints on c: lo < c < hi  (only when nmid), X non-decreasing,
                # transient values strictly inside (0,1)
                lo, hi = (Fr(0), Fr(1)) if nmid else (None, None)
                lo_strict = hi_strict = True
                ok = True
                cons = []  # (a, b, strict): a*c + b >= 0 or > 0
                for i in range(n - 1):
                    cons.append((X1[i + 1] - X1[i], X0[i + 1] - X0[i], False))
                for i in T:
                    cons.append((X1[i], X0[i], True))
                    cons.append((-X1[i], 1 - X0[i], True))
                if nmid:
                    cons.append((Fr(1), Fr(0), True))
                    cons.append((Fr(-1), Fr(1), True))
                    L, Ls, H, Hs = None, False, None, False
                    for a, b, st in cons:
                        if a == 0:
                            if b < 0 or (b == 0 and st):
                                ok = False
                                break
                        elif a > 0:
                            v = -b / a
                            if L is None or v > L or (v == L and st):
                                L, Ls = v, st if (L is None or v > L) else (Ls or st)
                        else:
                            v = -b / a
                            if H is None or v < H or (v == H and st):
                                H, Hs = v, st if (H is None or v < H) else (Hs or st)
                    if ok and L is not None and H is not None:
                        if L > H or (L == H and (Ls or Hs)):
                            ok = False
                else:
                    for a, b, st in cons:
                        if b < 0 or (b == 0 and st):
                            ok = False
                            break
                if not ok:
                    continue
                cnt_lay[1] += 1
                # F3: eigenvalue of Q in (-1, 0)
                Q = [[-IQ[a][b] if a != b else 1 - IQ[a][b] for b in range(t)] for a in range(t)]
                cp = charpoly(Q)
                if count_roots_open(cp, Fr(-1), Fr(0)) == 0:
                    continue
                cnt_lay[2] += 1
                surv += 1
                fo.write(json.dumps({'n': n, 'layout': lay, 'N': N,
                                     'cp': [str(c) for c in cp]}) + '\n')
            stats[str(lay)] = cnt_lay
            print('layout', lay, 'F1', cnt_lay[0], 'F2', cnt_lay[1], 'F3', cnt_lay[2],
                  'elapsed %.1fs' % (time.time() - t0), flush=True)
    print('n', n, 'patterns', total, 'survivors', surv, 'time %.1fs' % (time.time() - t0))
    return total, surv, stats


if __name__ == '__main__':
    n = int(sys.argv[1])
    run(n, sys.argv[2])
