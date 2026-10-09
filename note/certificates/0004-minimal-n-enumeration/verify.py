"""verify.py -- re-run of the n = 5 enumeration of the minimal-n note (both models), with controls.

Standard library only (the modules beside this file: exactlib, stage1, stage2, pairs, extract),
exact arithmetic (Fractions, Q(lam) with Sturm signs, exact Fourier-Motzkin), one process, no
assert statements. Outputs go to ./output/ beside this file.

Class (the note's section B): systems eventually of the form x(t) = x_inf + lam^t v, lam real in
(-1, 0), v != 0, neighbourhood pattern P+ when lam^t > 0 and P- when lam^t < 0; agents labelled in
non-decreasing order of x_inf (ties allowed); every real algebraic lam (roots of irreducible factors
of the transient block's characteristic polynomial).

What it re-runs and checks against the stated counts:
  stage 1 (n = 5): 4,096 patterns; F1 3,312; F2 633; F3 51;
  stage 2 (n = 5): closure SBC 12, SBI 12; constant-digraph systems SBC 4, SBI 0, the four SBC
          patterns [1,7,14,28,16], [1,7,15,28,16], [1,7,30,28,16], [1,7,31,28,16] with minimal
          polynomials x^2 - (2/3)x - 1/9, x^2 - (7/12)x - 1/12 (twice), x^2 - (8/15)x - 1/15;
  pairs   (n = 5, alternating): 16 pairs considered, 16 with a common limit, 12 pass closure,
          0 with a common eigenvector, 0 found;
  replay: each of the four SBC systems, with a witness (rational radii, a scaled eigenvector),
          replays the real update rule exactly for t < 200 with one constant digraph.
Controls: the four 7- and 6-agent systems of arXiv:2610.03229 (patterns read off an exact replay)
must be ACCEPTED by the same functions with the right alternating / constant flag (positive
controls), and every forged one-membership flip of their row 3 must be REJECTED.
The last line is VERDICT: PASS or VERDICT: FAIL (exit code 0 / 1).
"""
import json
import os
import sys
import time
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import stage1  # noqa: E402
import stage2  # noqa: E402
import pairs  # noqa: E402
from exactlib import Field, K  # noqa: E402
from extract import nbhd, step, find_witness, replay  # noqa: E402
from stage2 import amat, limit_family, closure_ok, eigenspace, full_feasible  # noqa: E402

failures = []
t0 = time.time()
OUT = os.path.join(HERE, 'output')
os.makedirs(OUT, exist_ok=True)
s1 = os.path.join(OUT, 's1_n5.jsonl')
s2 = os.path.join(OUT, 's2_n5.json')
p5 = os.path.join(OUT, 'p_n5.json')

# ---------------------------------------------------------------- stage 1
total, surv, stats = stage1.run(5, s1)
lay = stats.get('[[0], [4]]')
print('stage 1: patterns %d, F1/F2/F3 per layout %s' % (total, stats))
if total != 4096 or surv != 51 or lay is None or lay[:3] != [3312, 633, 51] or len(stats) != 1:
    failures.append('stage 1 counts differ from 4096 / 3312 / 633 / 51 (one layout)')

# ---------------------------------------------------------------- stage 2
stage2.run(s1, s2)
with open(s2) as fh:
    d2 = json.load(fh)
want = {'in': 51, 'clos_SBC': 12, 'clos_SBI': 12, 'const_SBC': 4, 'const_SBI': 0}
if d2['counts'] != want:
    failures.append('stage 2 counts %s != %s' % (d2['counts'], want))
found = sorted((f['model'], tuple(f['N']), tuple(f['key'][0])) for f in d2['constant_found'])
want_found = sorted([
    ('SBC', (1, 7, 14, 28, 16), ('-1/9', '-2/3', '1')),
    ('SBC', (1, 7, 15, 28, 16), ('-1/12', '-7/12', '1')),
    ('SBC', (1, 7, 30, 28, 16), ('-1/12', '-7/12', '1')),
    ('SBC', (1, 7, 31, 28, 16), ('-1/15', '-8/15', '1')),
])
if found != want_found:
    failures.append('stage 2 constant systems %s != %s' % (found, want_found))
else:
    print('stage 2: the four SBC constant-digraph patterns and their minimal polynomials as stated')

# ---------------------------------------------------------------- pairs (alternating)
pairs.main(p5, [s2])
with open(p5) as fh:
    dp = json.load(fh)
wantp = {'pairs_considered': 16, 'common_limit': 16, 'closure': 12, 'eigen': 0, 'found': 0}
if dp['counts'] != wantp:
    failures.append('pairs counts %s != %s' % (dp['counts'], wantp))


# ---------------------------------------------------------------- replay of the four finds
def parseK(F, s):
    body = s[2:-1]
    return K(F, [Fr(x) for x in body.split(',')] if body else [])


for f in d2['constant_found']:
    co, lo, hi = f['key']
    F = Field([Fr(c) for c in co], Fr(lo), Fr(hi))
    n, N = f['n'], f['N']
    if f['Xs']:
        failures.append('%s: a c-parameter family, not replayed' % N)
        continue
    X = [Fr(x) for x in f['X0']]
    k, sg = f['orient']
    w = [parseK(F, s) for s in f['V'][k]]
    wit = find_witness(f['model'], n, N, N, F, X, w, sg)
    if wit is None:
        failures.append('%s: no witness found' % N)
        continue
    s, v, r = wit
    res = replay(f['model'], n, N, N, F, X, v, r, 200)
    print('replay %s %s minpoly %s r %s -> %s' % (f['model'], N, co, [str(q) for q in r], res))
    if not res.startswith('OK 200 steps, 1 distinct'):
        failures.append('%s: replay %s' % (N, res))


# ---------------------------------------------------------------- the recorded n = 6 results
# NOT re-run here (stage 2 at n = 6 took several minutes in four slices and needs a factoriser
# for degree-4 factors). This only checks that the recorded result files add up to the stated counts.
REC = os.path.join(HERE, 'n6-recorded')
tot = {}
degs = {}
for part in 'abcd':
    with open(os.path.join(REC, 's2_n6_%s.json' % part)) as fh:
        d = json.load(fh)
    for key, val in d['counts'].items():
        tot[key] = tot.get(key, 0) + val
    for f in d['constant_found']:
        kd = (f['model'], len(f['key'][0]) - 1)
        degs[kd] = degs.get(kd, 0) + 1
with open(os.path.join(REC, 'p_n6.json')) as fh:
    p6 = json.load(fh)['counts']
want6 = {'in': 19906, 'clos_SBC': 397, 'clos_SBI': 487, 'const_SBC': 96, 'const_SBI': 47}
wantdeg = {('SBC', 1): 3, ('SBC', 2): 19, ('SBC', 3): 72, ('SBC', 4): 2,
           ('SBI', 2): 13, ('SBI', 3): 32, ('SBI', 4): 2}
wantp6 = {'pairs_considered': 4606, 'common_limit': 2034, 'closure': 1236, 'eigen': 272, 'found': 0}
print('recorded n = 6 (not re-run): %s; rate degrees %s; pairs %s'
      % (tot, sorted(degs.items()), p6))
if tot != want6 or degs != wantdeg or p6 != wantp6:
    failures.append('the recorded n = 6 files do not add up to the stated counts')


# ---------------------------------------------------------------- controls
def control(name, model, F, x0, r, expect_alt):
    n = len(x0)
    y = list(x0)
    rk = [F.rat(q) for q in r]
    pats = []
    for _t in range(4):
        N = nbhd(model, n, rk, y)
        pats.append(N)
        y = step(n, N, y)
    Pp, Pm = pats[0], pats[1]
    alt = Pp != Pm
    A1, A2 = amat(Pp, n), amat(Pm, n)
    X0, Xs = limit_family([A1, A2], n)
    clo = closure_ok(model, n, [Pp, Pm], X0, Xs)
    V = eigenspace([A1, A2], F, n)
    res = full_feasible(model, n, Pp, Pm, F, X0, Xs, V) if V else None
    accepted = alt == expect_alt and clo and bool(V) and res is not None
    print('positive control %s: P+ %s P- %s alternating %s -> %s'
          % (name, Pp, Pm, alt, 'ACCEPTED' if accepted else 'REJECTED'))
    if not accepted:
        failures.append('positive control %s rejected' % name)
    i = 3
    rejected = 0
    for jj in range(n):
        if jj == i:
            continue
        Pf = list(Pp)
        Pf[i] ^= (1 << jj)
        A3 = amat(Pf, n)
        fam3 = limit_family([A3, A2], n)
        ok3 = False
        if fam3 is not None:
            X3, Xs3 = fam3
            if closure_ok(model, n, [Pf, Pm], X3, Xs3):
                V3 = eigenspace([A3, A2], F, n)
                ok3 = bool(V3) and full_feasible(model, n, Pf, Pm, F, X3, Xs3, V3) is not None
        if ok3:
            failures.append('forged flip (%d,%d) of %s ACCEPTED' % (i, jj, name))
        else:
            rejected += 1
    print('  forged flips of row 3: %d of %d rejected' % (rejected, n - 1))


Fq = Field([Fr(1, 6), Fr(1)], Fr(-1), Fr(0))               # x + 1/6: lam = -1/6
F5 = Field([Fr(-1, 16), Fr(-1, 4), Fr(1)], Fr(-1), Fr(0))  # lam = (1 - sqrt5)/8
lam = F5.gen()
phi = 1 - 4 * lam
control('SBC-7 (section 2)', 'SBC', Fq, [Fq.rat(q) for q in (0, 38, 69, 84, 99, 130, 168)],
        [18, 42, 48, 12, 48, 42, 18], True)
control('SBC-6 (section 4)', 'SBC', Fq, [Fq.rat(q) for q in (0, 22, 37, 103, 118, 140)],
        [10, 70, 70, 70, 70, 10], False)
control('SBI-7 (section 3)', 'SBI', F5, [F5.rat(0), F5.rat(Fr(15, 2)), 10 - phi / 2, F5.rat(11),
                                         12 + phi / 2, F5.rat(Fr(29, 2)), F5.rat(22)],
        [8, 4, 4, 8, 4, 4, 8], True)
control('SBI-7 (section 5)', 'SBI', F5, [F5.rat(0), F5.rat(71), 100 - phi, F5.rat(110), 120 + phi,
                                         F5.rat(149), F5.rat(220)],
        [85, 35, 35, 75, 35, 35, 85], False)

print('total time %.1fs' % (time.time() - t0))
if failures:
    for f in failures:
        print('FAIL:', f)
    print('VERDICT: FAIL')
    sys.exit(1)
print('VERDICT: PASS')
