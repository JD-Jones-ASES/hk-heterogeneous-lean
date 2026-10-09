"""Compare a fresh n = 6 replay of certificate 0004 against n6-recorded/ (stdlib, read-only).

usage: python -I compare_n6.py FRESH_DIR RECORDED_DIR [ORIGINAL_S1]
ORIGINAL_S1 (optional): the bench's original s1_n6.jsonl (Claude-Math-Station, rt-067 lane `minimal`),
compared line by line after JSON parsing (robust to CRLF/LF).
FRESH_DIR holds s1_n6.jsonl, p_n6.json and either s2_n6.json (one run) or s2_n6_{a,b,c,d}.json
(the recorded slicing 0-5000-10000-15000-end). Exit 0 and "COMPARE: PASS" on full agreement.
"""
import sys, os, json, hashlib, collections
fresh, rec = sys.argv[1], sys.argv[2]
fails = []
def canon(x): return json.dumps(x, sort_keys=True)
def load(p): 
    with open(p) as fh: return json.load(fh)
def sha(p):
    with open(p, 'rb') as fh: return hashlib.sha256(fh.read()).hexdigest()

R = [load(os.path.join(rec, 's2_n6_%s.json' % s)) for s in 'abcd']
sliced = all(os.path.exists(os.path.join(fresh, 's2_n6_%s.json' % s)) for s in 'abcd')
F = [load(os.path.join(fresh, 's2_n6_%s.json' % s)) for s in 'abcd'] if sliced else [load(os.path.join(fresh, 's2_n6.json'))]

# stage 1
with open(os.path.join(fresh, 's1_n6.jsonl')) as fh:
    s1 = [json.loads(l) for l in fh]
print('stage 1 survivors', len(s1))
if len(s1) != 19906: fails.append('stage 1: %d survivors, recorded 19906' % len(s1))
s1pat = set((tuple(d['N']), canon(d['layout'])) for d in s1)
missing = [r for d in R for r in d['records'] if (tuple(r['N']), canon(r['layout'])) not in s1pat]
if missing: fails.append('stage 1: %d recorded stage-2 patterns absent from the fresh stage 1' % len(missing))
if len(sys.argv) > 3:
    with open(sys.argv[3]) as fh:
        orig = [json.loads(l) for l in fh]
    same = [canon(a) for a in s1] == [canon(b) for b in orig]
    print('stage 1 identical to the original s1_n6.jsonl (parsed, in order): %s' % same)
    if not same: fails.append('stage 1 differs from the original s1_n6.jsonl')

# stage 2: counts (summed), records and constant_found (multisets, then order)
def summed(ds):
    c = collections.Counter()
    for d in ds: c.update(d['counts'])
    return dict(c)
cr, cf = summed(R), summed(F)
print('stage 2 counts fresh', cf, '| recorded', cr)
if cf != cr: fails.append('stage 2 counts differ')
for fld in ('records', 'constant_found'):
    a = [canon(x) for d in F for x in d[fld]]
    b = [canon(x) for d in R for x in d[fld]]
    if collections.Counter(a) != collections.Counter(b):
        fails.append('stage 2 %s differ as multisets (fresh %d, recorded %d; %d only fresh, %d only recorded)'
                     % (fld, len(a), len(b), len(collections.Counter(a) - collections.Counter(b)),
                        len(collections.Counter(b) - collections.Counter(a))))
    else:
        print('stage 2 %s: %d entries, equal as multisets; same order: %s' % (fld, len(a), a == b))
if sliced:
    for s in 'abcd':
        p, q = os.path.join(fresh, 's2_n6_%s.json' % s), os.path.join(rec, 's2_n6_%s.json' % s)
        print('slice %s byte-identical: %s' % (s, sha(p) == sha(q)))

# pairs
pf, pr = load(os.path.join(fresh, 'p_n6.json')), load(os.path.join(rec, 'p_n6.json'))
print('pairs fresh', pf['counts'], 'found', len(pf['found']), '| recorded', pr['counts'], 'found', len(pr['found']))
if pf['counts'] != pr['counts'] or canon(pf['found']) != canon(pr['found']): fails.append('pairs differ')

for f in fails: print('FAIL:', f)
print('COMPARE: %s' % ('FAIL' if fails else 'PASS'))
sys.exit(1 if fails else 0)
