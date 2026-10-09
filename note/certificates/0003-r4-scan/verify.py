"""verify.py -- the middle radius of the 7-agent SBC system of arXiv:2610.03229, section 2.

System (a): x(0) = (0, 38, 69, 84, 99, 130, 168), r = (18, 42, 48, r_4, 48, 42, 18), SBC model
(agent i hears j iff |x_i - x_j| <= r_i), x(t+1)_i = mean of x(t)_j over the neighbourhood.
The paper takes r_4 = 12. Agents are 1-indexed in prose (agent 4 is the middle one) and
0-indexed in the code (index 3).

Claims checked, exactly (fractions.Fraction; standard library only; one process; no asserts):
  1. (every r_4 > 0, by an exact argument) the closed form x(t) = L + (-1/6)^t v with
     L = (0,36,72,84,96,132,168), v = (0,2,-3,0,3,-2,0) does not depend on r_4: rows other than
     the middle one do not involve r_4 (SBC), and L, v are mirror-symmetric about index 3
     (L_j + L_{6-j} = 168, v_j + v_{6-j} = 0), so the middle agent's neighbourhood is a mirror-
     symmetric set and its mean is 84 = x_4(t) whatever r_4 is. The script checks the symmetry
     and replays the update for t < 200 at every r_4 of a grid.
  2. (every r_4 > 0, by an exact argument) the digraph is eventually non-constant exactly when
     r_4 is in {12, 48}: |x_j(t) - 84| = d_j + c_j u with u = (-1/6)^t; agent j's membership in
     the middle row is eventually constant when r_4 != d_j, and alternates with the parity of t
     when r_4 = d_j and c_j != 0. The script computes {d_j : c_j != 0} = {12, 48} exactly and
     confirms the classification on the grid r_4 = k/2, k = 1..200, and at 47 and 4801/100.
  3. at r_4 = 48 the middle row is {1,...,5} at even t and {2,3,4} at odd t (0-indexed).
Forged controls, each of which must FAIL: an initial state moved off the mirror symmetry
(38 -> 39) must break the r_4-independence; a forged non-constancy set {12, 47} must be rejected.
The last line is VERDICT: PASS or VERDICT: FAIL (exit code 0 / 1).
"""
import os
import sys
from fractions import Fraction as F

# optional stop file: set HK_KILL to a path; when that file exists every loop stops (and fails)
KILL = os.environ.get("HK_KILL")

X0 = [F(x) for x in (0, 38, 69, 84, 99, 130, 168)]
L = [F(x) for x in (0, 36, 72, 84, 96, 132, 168)]
V = [F(x) for x in (0, 2, -3, 0, 3, -2, 0)]
LAM = F(-1, 6)
T = 200
failures = []


def radii(r4):
    return [F(18), F(42), F(48), F(r4), F(48), F(42), F(18)]


def table(r, x):
    return tuple(tuple(j for j in range(7) if abs(x[i] - x[j]) <= r[i]) for i in range(7))


def step(r, x):
    tb = table(r, x)
    return [sum((x[j] for j in tb[i]), F(0)) / len(tb[i]) for i in range(7)], tb


def replay(r4, x0=X0):
    """returns (closed form holds for t < T, list of tables, list of states)."""
    r = radii(r4)
    x = list(x0)
    u = F(1)
    ok = True
    tabs, states = [], []
    for t in range(T):
        if KILL and os.path.exists(KILL):
            print("FAIL: KILL file present: stopped")
            print("VERDICT: FAIL")
            sys.exit(1)
        if x != [L[i] + u * V[i] for i in range(7)]:
            ok = False
        states.append(x)
        x, tb = step(r, x)
        tabs.append(tb)
        u *= LAM
    return ok, tabs, states


def tail_kind(tabs):
    """'constant' if one table on t in [T/2, T), 'alternating' if two tables alternating by parity."""
    tail = tabs[T // 2:]
    distinct = set(tail)
    if len(distinct) == 1:
        return "constant"
    ev = set(tail[k] for k in range(0, len(tail), 2))
    od = set(tail[k] for k in range(1, len(tail), 2))
    if len(ev) == 1 and len(od) == 1 and ev != od:
        return "alternating"
    return "other"


# 1. mirror symmetry of L and v about index 3
if any(L[j] + L[6 - j] != 168 or V[j] + V[6 - j] != 0 for j in range(7)):
    failures.append("L, v are not mirror-symmetric about index 3")
else:
    print("L and v are mirror-symmetric about index 3 (L_j + L_{6-j} = 168, v_j + v_{6-j} = 0)")

# 2. thresholds of the middle row: |x_j - 84| = d_j + c_j u for u near 0
thr = set()
for j in range(7):
    if j == 3:
        continue
    a, b = L[j] - L[3], V[j] - V[3]
    s = 1 if a > 0 else -1
    d, c = s * a, s * b
    print("  agent %d: |x_j - x_4| = %s + (%s) u" % (j + 1, d, c))
    if c != 0:
        thr.add(d)
STATED = {F(12), F(48)}
if thr != STATED:
    failures.append("thresholds with c_j != 0 are %s, not {12, 48}" % sorted(thr))
else:
    print("eventually non-constant exactly at r_4 in {12, 48} (thresholds d_j with c_j != 0)")

# 3. the grid replay
grid = [F(k, 2) for k in range(1, 201)] + [F(47), F(4801, 100)]
nonconst = set()
for r4 in grid:
    ok, tabs, _ = replay(r4)
    if not ok:
        failures.append("closed form breaks at r_4 = %s" % r4)
        continue
    kind = tail_kind(tabs)
    if kind == "other":
        failures.append("r_4 = %s: tail neither constant nor 2-periodic" % r4)
    if kind == "alternating":
        nonconst.add(r4)
print("grid r_4 = k/2 (k = 1..200), 47, 4801/100: closed form at every t < %d for all %d values"
      % (T, len(grid)))
print("  eventually non-constant at r_4 in %s" % sorted(str(q) for q in nonconst))
if nonconst != STATED:
    failures.append("grid classification %s != {12, 48}" % sorted(nonconst))

ok, tabs, _ = replay(48)
mid = (tabs[T - 2][3], tabs[T - 1][3])
print("r_4 = 48: middle row at even t %s, at odd t %s" % (mid[0], mid[1]))
if mid != ((1, 2, 3, 4, 5), (2, 3, 4)):
    failures.append("r_4 = 48 middle rows %s" % (mid,))
ok, tabs, _ = replay(12)
mid = (tabs[T - 2][3], tabs[T - 1][3])
print("r_4 = 12: middle row at even t %s, at odd t %s" % (mid[0], mid[1]))
if mid != ((3,), (2, 3, 4)):
    failures.append("r_4 = 12 middle rows %s" % (mid,))

# forged controls
x_forged = list(X0)
x_forged[1] = F(39)
_, _, s30 = replay(30, x_forged)
_, _, s60 = replay(60, x_forged)
if s30 == s60:
    failures.append("forged control ACCEPTED: the asymmetric start gives the same trajectory at r_4 = 30, 60")
else:
    t1 = next(t for t in range(T) if s30[t] != s60[t])
    print("forged control [x_2(0) = 39, r_4 = 30 vs 60]: rejected (trajectories differ from t = %d)" % t1)
if nonconst == {F(12), F(47)}:
    failures.append("forged control ACCEPTED: the set {12, 47}")
else:
    print("forged control [non-constancy set {12, 47}]: rejected")

if failures:
    for f in failures:
        print("FAIL:", f)
    print("VERDICT: FAIL")
    sys.exit(1)
print("VERDICT: PASS")
