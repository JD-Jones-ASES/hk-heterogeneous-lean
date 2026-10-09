# Heterogeneous Hegselmann-Krause systems: the note

License: CC BY-SA 4.0 (this note and its certificates). The Lean files carry their own license.

What is established on paper or by exact certificate but not stated in Lean. Models
(arXiv:1103.2829v2): SBC (i hears j iff |x_i - x_j| <= r_i) and SBI (iff <= r_j); x(t+1)_i is the
mean of x(t)_j over N_i. Systems of sections 2-5: arXiv:2610.03229 (its section 7 says Claude Opus
5.5 found them). Agents are indexed from 0 as in Lean (the source's agent i is index i - 1);
lambda = (1 - sqrt5)/8, phi = (1 + sqrt5)/2. Each certificate (`certificates/NNNN-*/`) has a
standard-library `verify.py` (exact, no asserts, forged controls that must fail, last line
`VERDICT: PASS`) and a `NOTES.md` with its label.

## A. The six source systems, replayed exactly (0005, PROVEN-BY-CERTIFICATE)

(a) SBC-7 (section 2), (b) SBI-7 (section 3), (c) SBC-6 (section 4), (d) SBI-7 (section 5) are
pinned in Lean, and so are the two spectator systems (their closed forms, tables and the spectator's side):
- (e) SBC-9: x(0) = (0,22,37,103,118,140,210,280,300), r = (10,70,70,70,70,10,100,10,10); agents
  0-5 follow (c), x_6 = 210 + (12/11)((-1/6)^t - 5^-t), x_7 = 280, x_8 = 300.
- (f) SBI-8: x(0) = (0,60,71,100-phi,110,120+phi,149,220), r = (85,1,35,35,75,35,35,85); the
  spectator x_1 = 60 + phi^-1 (4^-t - lambda^t); the other agents follow (d).

All six match their closed forms and per-parity tables at every t < 60 (t < 200 with `--T=200`), with no boundary tie. For
every t, by induction: positions are affine in u = rate^t (and w = 5^-t or 4^-t); each membership
keeps a strict sign on the parity box; the row means are exact; u -> rate * u swaps the boxes.
- Widest u-intervals of each table: (a) even (0, 3), odd [-6/5, 0]; (b) even (0, sqrt5 - 1], odd
  [sqrt5 - 3, 0), so the odd step needs u >= sqrt5 - 3, not just u >= -1; (c) one table on
  (-5, 5/3]; (d) one table on [-15/2 + 5sqrt5/2, 15(sqrt5 - 1)/4]; (e), (f) one table on the
  closed box |u| <= 1, 0 <= w <= 1.
- Equi-topology distances (Definition 4.1) at the limits: (a) (3,3,0,0,0,3,3);
  (b) (1/2,0,1/2,0,1/2,0,1/2); (c) all 5; (d) (15/2,5/2,5/2,5/2,5/2,5/2,15/2).
- Per-step factors (Definition 6.1), t = 0..5: (c) -1/6 at 1-4, 0/0 at 0 and 5; (d) lambda at
  1, 2, 4, 5, 0/0 at 0, 3, 6. fvct(x(t)) = x_inf since A x_inf = x_inf and A v = rate * v.

## B. Smaller constant-digraph systems and minimality (0001, 0004)

The class: trajectories eventually x_inf + lambda^t v, lambda real in (-1, 0), v != 0, pattern P+
when lambda^t > 0 and P- when lambda^t < 0 (alternating if P+ != P-, constant otherwise).

**Lemma 1.** Every system in the class, in either model, has n >= 5.
*Proof.* Let P be either pattern, A = A_P. P holds at infinitely many distinct u = lambda^t, so
A x_inf = x_inf and A v = lambda v.
1. On a closed class C of P, x_inf is constant (maximum principle, A_CC irreducible). Agents sharing
   that limit are within |u||v_i - v_j| -> 0 of each other and every radius is positive, so for
   small |u| each i in C hears its whole cluster; closedness gives N_i = C = cluster, A_CC = J/|C|
   with eigenvalues 1 and 0, so v_C = 0. Closed classes are frozen cliques.
2. With one closed class, x_inf is constant (harmonic extension), so by step 1 that class is every
   agent and A = J/n, with no eigenvalue in (-1, 0): there are at least two closed classes. The
   minimum and maximum clusters are closed (an agent at the minimum averages limits >= it); no
   transient agent shares a closed cluster's limit.
3. With T the transient agents, v_T != 0 and Q v_T = lambda v_T for Q = A_TT. If |T| = 1, Q > 0.
   If |T| = 2, Q = [[a,b],[c,d]] with a, d > 0, b in {0,a}, c in {0,d}: triangular (eigenvalues
   a, d > 0) or [[a,a],[d,d]] (eigenvalues 0, a + d). So |T| >= 3 and n >= 2 + 3 = 5.

**Enumeration within the class**, BOUNDED-NEGATIVE-SEARCH (limits sorted, ties allowed; every layout
Lemma 1 allows; any transient rows; every real algebraic lambda; exact Fourier-Motzkin in Q(lambda)):
- n = 5 (re-run by 0004 in 8 s): four SBC constant patterns, no SBI constant system, no alternating
  system. Patterns (bit j of entry i: j in N_i) and rates: [1,7,14,28,16], (1 - sqrt2)/3;
  [1,7,15,28,16] and its mirror [1,7,30,28,16], (7 - sqrt97)/24; [1,7,31,28,16], (4 - sqrt31)/15.
- n = 6 (recorded files in 0004, not re-run here): 96 SBC constant systems (3 with rate -1/6) and
  47 SBI (rates 13 quadratic, 32 cubic, 2 quartic, none rational); no alternating system.
- Hence, within the class: no alternating system at n <= 6 in either model; the least n is 7 for
  alternating digraphs (the source's systems), 5 for SBC constant and 6 for SBI constant.
- PROVEN-BY-CERTIFICATE for all t (0001): S1, SBC, x_inf = (0,6,12,18,24), v = (0,1,-sqrt2,1,0),
  r = (3,9,9,9,3), rate (1 - sqrt2)/3. S2, SBI, x_inf = (0,2,3,3,4,6),
  v = (0,4,1-sqrt17,1-sqrt17,4,0)/16, r = (5/2,3/2,3/2,3/2,3/2,5/2), rate (3 - sqrt17)/8; agents
  2 and 3 coincide forever.
  S3, SBI, x_inf = (0,25,31,44,55,90), v = (0,10,-5-sqrt249,8,10,0)/16, r = (45,18,27,45/2,27,54),
  rate (13 - sqrt249)/40; all limits distinct. S1 and S3 are also pinned in Lean.
- Not covered: trajectories outside the class (two geometric modes, parity-dependent offsets that
  are not a common eigenvector, complex rates, digraph periods >= 3); n = 7 was not enumerated.

## C. Wiggle room, the middle radius, two bounded searches (0002, 0003)

- Wiggle room (Remark 2.1), one parameter at a time, COMPUTED exactly. (a): r_0 = r_6 in
  (0, 107/3), r_1 = r_5 in [38, 46), r_2 = r_4 in [221/6, 359/6), r_3 = 12 exactly; dilation
  beta = 1 only; amplitude gamma in (0, 3). (c): r_0 = r_5 in (0, 59/3), r_1 = r_4 in [22, 479/6),
  r_2 = r_3 in [66, 479/6); beta in (421/480, 16/15]; gamma in (-5, 5/3], gamma != 0. Translation
  is free; each single coordinate of x(0) is rigid.
- The middle radius r_3 of (a) (the source's r_4), by an exact argument with a replayed grid: the
  trajectory does not depend on it (mirror symmetry); the digraph is eventually non-constant exactly
  when r_3 is 12 or 48. At 48 the middle agent hears {1,...,5} at even t and {2,3,4} at odd t.

Two recorded search results (their scripts are not shipped here):
- No rational SBI alternating system in the class: BOUNDED-NEGATIVE-SEARCH, fully resolved for
  mirror-symmetric n = 5, 6 (span <= 40), 7 (<= 30), 8 (<= 16) and any order n = 4 (<= 30),
  5 (<= 12), 6 (<= 7). Not covered: symmetric n = 8 spans 17-24, any order n = 5 spans 13-20 and
  n = 6 spans 8-12, non-symmetric n = 7, 8; irrational leaves were not sign-checked. A two-step
  extension (symmetric n = 7, span <= 22) found nothing, but 3,508 multi-dimensional leaves were
  checked only heuristically: UNKNOWN residue.
- No digraph of period 3 (x(3m + k) = L + mu^m w(k), rational mu in (0, 1)): BOUNDED-NEGATIVE-SEARCH
  for SBC and SBI, symmetric n = 5 (span <= 16), n = 6 (SBC <= 16, SBI <= 14), any order n = 4
  (<= 12, fully resolved). UNKNOWN: irrational-mu leaves (SBC 276 at n = 5 and 1,122 at n = 6; SBI
  276 and 1,161), multi-dimensional leaves, mu < 0, n >= 7. No impossibility argument is known.

The computations used Python with exact Fraction arithmetic (sympy for one factorisation step of
the n = 6 enumeration) and were carried out by Claude Opus 5.5.
