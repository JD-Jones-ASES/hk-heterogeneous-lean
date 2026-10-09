# 0003 r_4 scan

**Statement.** In system (a) of section 2 (SBC, n = 7), with every datum fixed except the middle
radius r_4 > 0 (1-indexed; index 3 in code):

1. the trajectory x(t) = (0,36,72,84,96,132,168) + (-1/6)^t (0,2,-3,0,3,-2,0) does not depend
   on r_4;
2. the proximity digraph is eventually non-constant exactly when r_4 is 12 or 48;
3. at r_4 = 48 the middle agent hears {1,...,5} at even t and {2,3,4} at odd t (0-indexed): a
   second alternating SBC system on seven agents. For other r_4 the digraph is eventually
   constant while agents 2, 3, 5, 6 (1-indexed) keep oscillating.

**Why (exact).** Rows other than the middle one use their own radii (SBC). L and v are
mirror-symmetric about the middle index, so the middle neighbourhood is a mirror-symmetric set and
its mean is 84 = x_4(t) for every r_4. The middle agent's distances are 84 (agents 1, 7, no
oscillating part), 48 - 2u (agents 2, 6) and 12 + 3u (agents 3, 5), with u = (-1/6)^t; a
membership alternates with the parity of t only when r_4 equals 12 or 48.

**Artifact.** `verify.py` (standard library, Fractions). It checks the symmetry, computes the
thresholds {d_j : c_j != 0} = {12, 48}, replays t < 200 at r_4 = k/2 for k = 1..200 and at 47 and
4801/100, and classifies the tail of each run. Forged controls: an asymmetric start (38 -> 39)
must make the trajectory depend on r_4 (r_4 = 30 against 60); a forged set {12, 47} must be
rejected.

**Re-run.** `python verify.py` (about 5 s).

**Label.** Items 1 and 2 for every r_4 > 0: by the exact argument above, with the script's
checks of its ingredients. The grid replay: COMPUTED (t < 200). Not in Lean.

Last lines of the run:

```
  eventually non-constant at r_4 in ['12', '48']
r_4 = 48: middle row at even t (1, 2, 3, 4, 5), at odd t (2, 3, 4)
r_4 = 12: middle row at even t (3,), at odd t (2, 3, 4)
forged control [x_2(0) = 39, r_4 = 30 vs 60]: rejected (trajectories differ from t = 1)
forged control [non-constancy set {12, 47}]: rejected
VERDICT: PASS
```
