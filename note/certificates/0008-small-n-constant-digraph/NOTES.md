# 0008 small-n constant-digraph systems

**Statement.** Corroborates the theorem of [0006 section 6](../0006-sbi5-complex/NOTES.md) (SBC or SBI, at most
four agents, eventually constant digraph: eventually fixed or pseudo-stable). Agents 0-indexed; bit j of
mask i means j in N_i. (1) Of the 4, 64, 4096 patterns on n = 2, 3, 4 agents, exactly 2, 8, 145 are
unobstructed: no non-arc i -> j has equal rows of Pi = lim A^t (such a pattern is never an eventual
digraph with positive radii, since x_i - x_j -> 0). Each unobstructed pattern has every eigenvalue of A
real and in [0, 1], complete closed classes, and is complete or has >= 2 closed classes and <= 2
transient agents. (2) Two-transient blocks: 54 of the form [[a,a],[d,d]], 24 triangular with
a = d = 1/3, none triangular with a != d; one-transient blocks have a in {1/3, 1/4}. (3) An exact HK
replay (seed 20261009; SBC and SBI, n = 2, 3, 4; 2,220 systems, at least 300 per cell; 400 steps)
has its digraph constant on [200, 400] and a fixed or pseudo-stable tail towards Pi x(200) in every
run, 0 violations; its 155 distinct tail patterns are exactly the unobstructed ones (SBC 107, SBI 103).

**Artifact.** `verify.py` (standard library; Fractions and integers, no assert). Pi from the closed
classes' stationary vectors and the transient solve, identified as lim A^t by A Pi = Pi A = Pi^2 = Pi
and rank Pi = #closed classes = dim ker(A - I) (a positive diagonal keeps every other eigenvalue
inside the unit disc). Characteristic polynomial by the Leibniz expansion of det(diag(k) s - B)/prod k,
checked monic with root 1 and trace coefficient; Sturm counts of its squarefree part on the line and
on [0, 1]. The replay keeps integer numerators over a common denominator, recomputes neighbourhoods
from the states on the tail, and treats a state equal to its successor as fixed from then on; rule
anchors check that the SBC and SBI rules give the published tables of S1 (0001) and of the SBI5
system (0006) at their limits. Enforced: the counts of (1)-(2) and the tail set of (3). Controls,
each rejected: (1,7,14,28,16), (1,11,31,29,16) (unobstructed, spectrally bad); the obstruction test
off at n = 3, 4; the obstructed (3,6,5), (1,11,5,8) admitted; x(t+1) = A x(t) on (3,6,5,8); a
reflected coordinate and a displaced agent in a genuine tail.

**Re-run.** `python -I verify.py` and `python -I -O verify.py` here (Python 3.9+; about 5 s each).

**Label.** COMPUTED. It corroborates the paper proof and does not replace it: the exhaustive part
checks linear consequences of the theorem's structural lemmas, and the replay is finite. Not
covered: Lean, n >= 5, trajectories whose digraph never becomes constant.

Last lines of the run:

```
  controls rejected: 9 of 9
genuine failures: 0; total time 5.4s
VERDICT: PASS
```
