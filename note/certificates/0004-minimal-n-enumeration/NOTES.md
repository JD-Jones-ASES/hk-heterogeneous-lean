# 0004 minimal-n enumeration

**Class.** SBC or SBI systems whose trajectory is eventually x(t) = x_inf + lam^t v with lam real
in (-1, 0), v != 0, pattern P+ when lam^t > 0 and P- when lam^t < 0; agents in non-decreasing
order of x_inf, ties allowed; every closed-cluster layout allowed by Lemma 1 of the note, with
arbitrary transient rows; every real lam in (-1, 0) that is a root of an irreducible factor of the
transient block's characteristic polynomial, handled exactly in Q(lam). Feasibility is exact
Fourier-Motzkin over Q(lam) with Sturm signs; v != 0 is one strict orientation constraint per
eigenspace basis vector.

**Statement, n = 5 (re-run here).** 4,096 patterns; F1 keeps 3,312, F2 633, F3 51; closure passes
SBC 12, SBI 12. Constant digraph: SBC 4, SBI 0. Alternating: 16 pairs considered, 16 with a common
limit, 12 pass closure, 0 with a common eigenvector, 0 found. The four SBC patterns (bit j of N_i
means j in N_i) are [1,7,14,28,16] (x^2 - (2/3)x - 1/9), [1,7,15,28,16] and its mirror
[1,7,30,28,16] (x^2 - (7/12)x - 1/12), [1,7,31,28,16] (x^2 - (8/15)x - 1/15); each replays
exactly for t < 200 with one digraph.

**Statement, n = 6 (recorded; re-run 2026-10-09, byte-identical).** 1,245,184 patterns, 19,906 survive F1-F3; closure
SBC 397, SBI 487. Constant digraph: SBC 96 (3 with lam = -1/6, among them the section 4 pattern
[1,7,15,60,56,32]), SBI 47 (13 quadratic, 32 cubic, 2 quartic rates; none rational).
Alternating: 4,606 pairs, 2,034 with a common limit, 1,236 pass closure, 272 with a common
eigenvector, 0 found. Files: `n6-recorded/s2_n6_{a,b,c,d}.json` (stage 2 in four slices),
`n6-recorded/log_s2_{a,b,c,d}.txt` (their logs), `n6-recorded/p_n6.json` (the pairs).

**Artifact.** `stage1.py` (filters F1-F3), `stage2.py` (closure, lam, eigenspace, full FM),
`pairs.py` (alternating pairs), `extract.py` (witness and replay), `exactlib.py` (exact
arithmetic), and `verify.py`, which re-runs n = 5 into `output/`, compares every count and pattern
above, replays the four finds, checks that the recorded n = 6 files add up to the stated counts,
and runs the controls: the four source systems of sections 2-5 must be accepted by the same
functions (positive controls) and every one-membership flip of their row 3 must be rejected.

**Re-run.** `python verify.py` (about 8 s; standard library only). The original n = 5 run
factored characteristic polynomials with sympy; here a rational-root factoriser replaces it, exact
up to degree 3 (every n = 5 polynomial has degree 3), and the outputs are identical. The n = 6
stage 2 meets cofactors of degree 4 without rational roots and sends only those to SymPy
(`factor_over_Q` in `stage2.py`): the coefficients cross as exact rationals, and the returned monic
factors are multiplied back in `Fraction` arithmetic and must reproduce the squarefree input. The
irreducibility of the returned factors is SymPy's (on the n = 6 workload every returned quadratic
and quartic was also checked irreducible independently: no rational root, and a factorisation
pattern modulo a prime that excludes a split into two quadratics). Without SymPy a degree-4
cofactor stops the run with an explicit message.

To reproduce the n = 6 search, work in a copy of this folder with SymPy importable in the
interpreter that runs `stage2.py` (`python -m pip install sympy==1.14.0`; `python -I` ignores the
user site, so run these without `-I`):

```sh
python stage1.py 6 s1_n6.jsonl                        # about 4 min; 19,906 lines
python stage2.py s1_n6.jsonl s2_n6_a.json 0 5000      # the four slices of the recorded run,
python stage2.py s1_n6.jsonl s2_n6_b.json 5000 10000  # independent; 160, 100, 50 and 620 s
python stage2.py s1_n6.jsonl s2_n6_c.json 10000 15000
python stage2.py s1_n6.jsonl s2_n6_d.json 15000
python pairs.py p_n6.json s2_n6_a.json s2_n6_b.json s2_n6_c.json s2_n6_d.json   # about 1 min
python compare_n6.py . n6-recorded                    # the JSON files, not the logs
```

The logs print at most 50 FOUND lines and carry timings, so the comparison is on the JSON files:
the summed `counts`, and `records` and `constant_found` as multisets. Re-run on 2026-10-09 on this
PC with these commands: stage 1 identical line for line, every slice and the pairs file
byte-identical to `n6-recorded/` (sha256 ceca0387…, 47def54b…, 5f6ff3c8…, 42c70b9c…, ab7ff2d3…).

**Labels.** n = 5: BOUNDED-NEGATIVE-SEARCH within the class (SBI constant, both alternating) and
COMPUTED (the four SBC finds), re-runnable. n = 6: COMPUTED, re-run (the recorded files were
produced once at the bench and reproduced byte for byte on 2026-10-09 with the shipped scripts and
SymPy 1.14.0). A float cross-check with an independent formulation agreed at n = 5 and n = 6; it
is not shipped and no verdict rests on it.

Last lines of the run:

```
positive control SBI-7 (section 5): P+ [1, 15, 30, 28, 60, 120, 64] P- [1, 15, 30, 28, 60, 120, 64] alternating False -> ACCEPTED
  forged flips of row 3: 6 of 6 rejected
total time 8.2s
VERDICT: PASS
```
