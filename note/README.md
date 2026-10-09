# Heterogeneous Hegselmann-Krause systems: the note

License: CC BY-SA 4.0 (this note and its certificates). The Lean files carry their own license.

Additional mathematical results and exact certificates, with Lean coverage identified below. Models
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
All minimality statements in this section concern this single-negative-mode class. In particular,
the least SBI constant order of six does not exclude the five-agent complex-mode example in D.

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

The computations in A-C used Python with exact Fraction arithmetic (sympy for one factorisation step
of the n = 6 enumeration).

## D. Five SBI agents with complex modes; the least count under an eventually constant digraph (0006)

**PROVEN-BY-CERTIFICATE for all t, and in Lean** (`HK/SBI5Complex.lean`). Let rho be the real root of
`60 rho^3 - 47 rho^2 + 9 rho - 1 = 0` in `(57/100, 29/50)` (the cubic's only real root). Take
`L = (0,10,18,20,42)`, `r = (31,9,5,15,28)`, `x(0) = (0,31/3-rho,91/5,20,42)`. The SBI masks are
`[1,11,31,29,16]` at every t: every membership inequality at L has slack at least 1, the offsets of
agents 1, 2, 3 follow `Q = [[1/3,0,1/3],[1/5,1/5,1/5],[0,1/4,1/4]]` from `z = (1/3-rho,1/5,0) =
(Q-rho I)e_1`, and `||Q^t z||_infinity < (2/3)^t/3`, so the table persists and x(t) converges to L.
Each offset obeys `y(t+2) = alpha y(t+1) - beta y(t)` with `alpha = 47/60-rho`, `beta = 1/(60 rho)`,
`0 < beta < alpha^2 < 2 beta`; hence `y(t+4) = alpha(alpha^2-2 beta) y(t+1) + beta(beta-alpha^2) y(t)`
with two negative coefficients and no zero adjacent pair, so every five consecutive times contain both
strict signs, for each of agents 1, 2, 3, while agents 0 and 4 are frozen: convergence with a constant
digraph, neither eventually fixed nor eventually pseudo-stable, outside the single-negative-mode class
of B. The proof and the exact replay (t < 200, forged controls) are in
[0006-sbi5-complex](certificates/0006-sbi5-complex/NOTES.md).

**Lower bound, PROVEN-ON-PAPER** (section 6 of that certificate's notes). In either model, every
trajectory on at most four agents with an eventually constant digraph is eventually fixed or
pseudo-stable: the eventual averaging matrix has positive diagonal, so its powers converge; positive
radii make each closed class a frozen clique and keep every other agent away from its limit; unless
the whole system freezes there are at least two closed classes and at most two transient agents, whose
block is triangular with positive diagonal or of the form `[[a,a],[d,d]]`, so each offset is eventually
zero or strictly monotone on one side. With S1 of B (`HK.not_theorem64iv_sbc_five`) and the system
above (`HK.not_theorem64iv_sbi_five`): **five is the least number of agents, in each model, for a
counterexample to Conjecture 2.3, or to Theorem 6.4(iv) in the reading admitting fixed states, whose
digraph is eventually constant**. This is of a different scope from Lemma 1 of B (any modes, but only
eventually constant digraphs; Lemma 1 covers alternating patterns in its class). Nothing is claimed for
digraphs that keep changing, and the bound is not a Lean theorem; certificate 0008 checks its structural
consequences exhaustively on every neighbourhood pattern with at most four agents (COMPUTED).

## E. Arbitrarily weak heterogeneity; connected path families (0007)

Full derivations: [near-homogeneity-and-paths.md](near-homogeneity-and-paths.md).

**The SBC5 family, in Lean** (`HK/SBC5Family.lean`). For `0 < d <= 1`: `r(d) = (6-3d,6+3d,6+3d,6+3d,6-3d)`
and `x(0) = x_inf + d v` with the data of S1 (d = 1 is S1). The table of S1 and the rate `(1-sqrt2)/3`
persist; the trajectory converges, never freezes, and is never eventually pseudo-stable. The radius
ratio is `(2+d)/(2-d)`, so `d = min(1/2, eta/4)` puts it below `1 + eta` for every `eta > 0`: no
positive bound on the relative spread of the radii restores eventual pseudo-stability, already for five
SBC agents (`HK.sbc5_near_homogeneous`). The table holds exactly for `d < 6/(3+sqrt2)`; `d <= 1` is the
crude bound. Replayed exactly for several d by certificate 0007.

**The path family and an SBI6 family, PROVEN-ON-PAPER, replayed by 0007** (the SBI6 family exactly; the path family in 260-digit arithmetic, COMPUTED). For every `n >= 5`,
`m = n-1`, endpoints of radius `1-delta` and interior agents of radius `1+delta` (`0 < delta < 1/2`),
the sine modes of the nearest-neighbour path give `x_i(t) = i + (delta/4) lambda_k^t sin(i k pi/m)`,
`lambda_k = (1+2 cos(k pi/m))/3`, `2m/3 < k <= m-1`: a constant, weakly connected digraph (endpoints
alone, interior `{i-1,i,i+1}`), convergence, and alternation at every agent with a nonzero mode (all
interior agents for k = m-1); the rates are dense in `(-1/3, 0)`, and n = 5, k = 3 has the rate and mode of S1. A six-agent
SBI family built on the limit and mode of S2 (`r = (2+delta,2-delta,2-delta,2-delta,2-delta,2+delta)`,
amplitude `delta/16`, `0 < delta < 1/2`; S2 itself is not a member) has four alternating interior
agents, a coincident pair, and radius ratio `(2+delta)/(2-delta)`.

Along their trajectories, the constant-digraph SBC systems with two frozen endpoints (the section 4
system of the source, S1, the SBC5 family, the path family) are homogeneous HK systems with two
closed-minded agents in the sense of Chazelle and Wang (IEEE Trans. Automat. Control 62 (2017)
3905-3913), who prove convergence and an eventually constant network for that class and note that it
need not freeze; the failure of pseudo-stability and the counts above are not there.
