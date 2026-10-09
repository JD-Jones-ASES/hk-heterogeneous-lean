"""Stage 4 of the minimal-n probe: the ALTERNATING case.

Input: stage-2 records (model, pattern, lam-key) = single patterns that pass the u -> 0 closure
filter for that model and have an eigenvalue lam in (-1, 0) with a nonzero eigenspace. An
alternating system needs P+ != P- with the same lam, a common limit (A+ x = x = A- x), a common
eigenvector (A+ v = lam v = A- v), and the full exact system. Pairs are formed inside each
(model, lam) group; patterns whose normalised limit is unique are also bucketed by that limit.
"""
import os, sys, json, time
from fractions import Fraction as Fr
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from exactlib import Field, killed
from stage2 import amat, limit_family, closure_ok, eigenspace, full_feasible


def main(outp, files):
    t0 = time.time()
    recs = []
    for fn in files:
        recs.extend(json.load(open(fn))['records'])
    groups = {}
    for r in recs:
        groups.setdefault((r['model'], json.dumps(r['key'])), []).append(r)
    print('records', len(recs), 'groups', len(groups),
          'max group', max((len(g) for g in groups.values()), default=0), flush=True)
    cnt = {'pairs_considered': 0, 'common_limit': 0, 'closure': 0, 'eigen': 0, 'found': 0}
    found = []
    for (model, keyj), g in groups.items():
        if killed():
            raise SystemExit('KILL')
        key = json.loads(keyj)
        n = g[0]['n']
        # unique-limit bucketing
        info = []
        for r in g:
            A = amat(r['N'], n)
            fam = limit_family([A], n)
            info.append((r, A, fam))
        buckets = {}
        for r, A, fam in info:
            X0, Xs = fam
            b = 'free' if Xs else tuple(str(x) for x in X0)
            buckets.setdefault(b, []).append((r, A, fam))
        F = None
        keys = list(buckets)
        for b1 in keys:
            for b2 in keys:
                if b1 != b2 and b1 != 'free' and b2 != 'free':
                    continue
                for (r1, A1, f1) in buckets[b1]:
                    for (r2, A2, f2) in buckets[b2]:
                        if r1['N'] == r2['N']:
                            continue
                        cnt['pairs_considered'] += 1
                        fam = limit_family([A1, A2], n)
                        if fam is None:
                            continue
                        X0, Xs = fam
                        cnt['common_limit'] += 1
                        if not closure_ok(model, n, [r1['N'], r2['N']], X0, Xs):
                            continue
                        cnt['closure'] += 1
                        if F is None:
                            co, lo, hi = key
                            F = Field([Fr(c) for c in co], Fr(lo), Fr(hi))
                        V = eigenspace([A1, A2], F, n)
                        if not V:
                            continue
                        cnt['eigen'] += 1
                        res = full_feasible(model, n, r1['N'], r2['N'], F, X0, Xs, V)
                        if res is not None:
                            cnt['found'] += 1
                            found.append({'model': model, 'n': n, 'Pp': r1['N'], 'Pm': r2['N'],
                                          'key': key, 'orient': res,
                                          'X0': [str(x) for x in X0],
                                          'Xs': [[str(x) for x in X] for X in Xs],
                                          'V': [[repr(x) for x in v] for v in V]})
                            print('FOUND', model, r1['N'], r2['N'], key[0], flush=True)
    json.dump({'counts': cnt, 'found': found}, open(outp, 'w'))
    print('done', cnt, '%.1fs' % (time.time() - t0))


if __name__ == '__main__':
    main(sys.argv[1], sys.argv[2:])
