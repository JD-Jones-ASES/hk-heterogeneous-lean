# 0002 wiggle room

**Statement.** For system (a) (section 2: SBC, n = 7, x(0) = (0,38,69,84,99,130,168),
r = (18,42,48,12,48,42,18)) and system (c) (section 4: SBC, n = 6, x(0) = (0,22,37,103,118,140),
r = (10,70,70,70,70,10)), both with rate -1/6, varying one parameter at a time with the rest
fixed (radii 1-indexed as in the source), the same per-parity tables hold for every t exactly on:

| parameter | (a) | (c) |
|---|---|---|
| r_1 = r_n | (0, 107/3) | (0, 59/3) |
| r_2 = r_(n-1) | [38, 46) | [22, 479/6) |
| r_3 | [221/6, 359/6) | [66, 479/6) |
| r_4 | {12} | [66, 479/6) |
| r_5 | [221/6, 359/6) | [22, 479/6) |
| dilation beta (L -> beta L) | {1} | (421/480, 16/15] |
| amplitude gamma (v -> gamma v) | (0, 3) | (-5, 5/3], gamma != 0 to oscillate |
| translation alpha | all reals | all reals |

Every single coordinate of x(0) is rigid: the one-term closed form survives exactly on the
three-dimensional family alpha 1 + beta L + gamma v (dim Fix = 2, dim E_lam = 1).

**Artifact.** `verify.py` (standard library, Fractions). Per-arc conditions are affine in the
parameter, so each feasible set is an interval computed exactly; the script rules out the
sign-crossing alternative, replays the update for t < 200 at the original value, the closed
endpoints and a midpoint, and requires a failure just outside every finite endpoint (the forged
controls), plus a forged r_4 = 13. It then compares every interval with the table above.
`wiggle.out` is the output of the original run; the new run reproduces it line for line.

**Re-run.** `python verify.py` (about 2 s).

**Label.** COMPUTED (exact). Not in Lean.

Last lines of the run:

```
   gamma      (-5, 5/3]                     outside: -5 -> table changes at t=0; 50003/30000 -> table changes at t=0
   alpha      (-inf, +inf) (translation; replayed at -1000 and 37/3)
computed intervals equal the stated intervals for (a) and (c)
forged control r_4 = 13 rejected: table changes at t=2
VERDICT: PASS
```
