# 0001 small systems

**Statement.** Three constant-digraph systems oscillate around their limits forever
(agents 0-indexed; x(t) = x_inf + lam^t v, lam in (-1, 0)):

- S1, SBC, n = 5: x_inf = (0,6,12,18,24), v = (0,1,-sqrt2,1,0), r = (3,9,9,9,3),
  lam = (1-sqrt2)/3; N = {0},{0,1,2},{1,2,3},{2,3,4},{4} at every t.
- S2, SBI, n = 6: x_inf = (0,2,3,3,4,6), v = (0,4,1-sqrt17,1-sqrt17,4,0)/16,
  r = (5/2,3/2,3/2,3/2,3/2,5/2), lam = (3-sqrt17)/8. Agents 2 and 3 coincide for all t.
- S3, SBI, n = 6: x_inf = (0,25,31,44,55,90), v = (0,10,-5-sqrt249,8,10,0)/16,
  r = (45,18,27,45/2,27,54), lam = (13-sqrt249)/40; all limits distinct.

**Artifact.** `verify.py` (standard library; Q(sqrt d) as pairs of Fractions with exact signs).
For each system it checks: lam is a root of its minimal polynomial and lies in (-1, 0);
A_P x_inf = x_inf and A_P v = lam v exactly; every membership inequality holds (members) or
fails strictly on one side (non-members) at u = lam and u = 1, hence on all of [lam, 1], which
contains lam^t for every t, so induction gives the closed form and the constant digraph for every
t; v != 0; and an exact replay of the update rule for t < 200 with the side alternation of every
oscillating agent. Forged controls: radius r_1 doubled, the rate replaced by its rational part,
x_2 of the limit shifted by 1/7. Each must be rejected.

**Re-run.** `python verify.py` (Python 3.9 or later; under 1 s on Python 3.14.2).

**Label.** PROVEN-BY-CERTIFICATE (all t, by the endpoint test and induction).
S1 and S3 are also pinned in the Lean entry (`sbc5_*`, `sbi6_*`); S2 is not.

**Independently verified.** The replay applies the update rule from the initial state without
using the claimed table; the closed form and table are compared, not assumed.

Last lines of the run:

```
SBI-6b
    certified: constant digraph for every t, oscillation, x(t) -> x_inf
    forged (radius r_1 doubled): rejected (non-member (0,1) not strictly outside on [lam,1])
    forged (rate replaced by a rational): rejected (lam is not a root of its minimal polynomial)
    forged (limit x_2 shifted by 1/7): rejected (A x_inf != x_inf at row 1)
VERDICT: PASS
```
