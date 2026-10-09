# 0007 near-homogeneous families

**Statement.** The families of [near-homogeneity-and-paths.md](../../near-homogeneity-and-paths.md) keep
their tables and closed forms, with no boundary tie, for the replayed parameters (agents 0-indexed):
- (A) section 4, SBC5: r(d) = (6-3d,6+3d,6+3d,6+3d,6-3d), x(0) = L + d v, L = (0,6,12,18,24),
  v = (0,1,-sqrt2,1,0), lam = (1-sqrt2)/3. For d in {1, 1/2, 1/10, 1/100, 1/1000} and d = min(1/2, eps/4),
  eps in {1, 1/10, 1/1000} (r_i < (1+eps) r_j for all i, j), t < 200: table {0},{0,1,2},{1,2,3},{2,3,4},{4},
  x(t) = L + d lam^t v, agents 1, 2, 3 alternate. Threshold 6/(3+sqrt2): d = 1699/1250 keeps the table
  (t < 200); at 6/(3+sqrt2) agent 2 ties with agent 0 at t = 0; at 34/25 the table fails at t = 0.
- (B) section 5, SBI6: s = sqrt17, lam = (3-s)/8, L = (0,2,3,3,4,6), v = (0,4,1-s,1-s,4,0),
  r = (2+delta, 2-delta x4, 2+delta), amplitude delta/16. For delta in {1/4, 1/10, 1/100}, t < 200: table
  {0},{0,1,2,3},{1,2,3,4},{1,2,3,4},{2,3,4,5},{5}, closed form, agents 1-4 alternate, every distance bullet
  of section 5, ratio (2+delta)/(2-delta). S2 (r = (5/2,3/2,3/2,3/2,3/2,5/2), amplitude 1/16) replays with
  the same table but is not a member: the family needs delta < 1/2 and would have amplitude 1/32 there.
  Threshold 16/(19+s) at t = 0: 6919/10000 keeps the table (also t < 200), 16/(19+s) ties, 173/250 fails.
- (C) sections 1-3, the path family: n = 5..12, every k with 2m/3 < k <= m-1 (15 pairs), delta in
  {1/4, 1/10}, eps = delta/4, t < 100: endpoints alone, interior {i-1,i,i+1}; the closed form within 1e-250;
  lam_k in (-1/3, 0); v_{i-1}+v_i+v_{i+1} = 3 lam_k v_i; alternation at every agent with m not dividing ik
  (all interior agents for k = m-1), the others fixed; (5,3) has lam = (1-sqrt2)/3, v ~ (0,1,-sqrt2,1,0).
- (D) the choices d = min(1/2, eta/4) and delta < min(1/2, eta/(2+eta)) give ratio < 1+eta (2,332 etas).

**Artifact.** `verify.py`, standard library. Neighbourhoods come from the update rule at every step;
tables and closed forms are compared, never assumed. (A), (B), (D) are exact (Q(sqrt2), Q(sqrt17) as
Fraction pairs, exact signs). (C) uses decimal at 260 digits: values stay below 100, so an operation
rounds by at most 5e-259; averaging is non-expansive, so the replay stays within eps*e0 + (2+3T)*5e-259
< 1e-250 of the exact trajectory, e0 < 1e-255 being the gap to a 320-digit evaluation of sin and cos (a
cross-check, not interval arithmetic). Every table decision has slack above delta/2, so computed and
exact tables agree; offsets are signed only above 2e-250. Forged controls, each rejected: (A) at
d = 34/25; (A) with r_1 = 6-3d; (B) at delta = 3/4; (C) with interior radius 1-delta; and four detector
checks (the tie at 6/(3+sqrt2), a wrong rate in each closed form, S2 against the bullets).

**Re-run.** From this folder: `python -I verify.py` and `python -I -O verify.py` (Python 3.9+; about 3.5 s).

**Label.** PROVEN-BY-CERTIFICATE for the exact replays (A, B: t < 200) and scan (D); COMPUTED for (C), its
sin, cos and pi cross-checked at 320 digits, not enclosed. All-t claims are the note's paper proofs (section 4
also in `HK/SBC5Family.lean`); not certified: all t, section 2's density, n > 12. Last lines of the run:
```
genuine failures: 0; total time 3.4 s
VERDICT: PASS
```
