# 0005 replay of the six source systems

**Statement.** The six systems of arXiv:2610.03229 sections 2-5 (SBC-7, SBI-7, SBC-6, SBI-7, and
the spectator systems SBC-9 and SBI-8) follow their closed forms and per-parity neighbourhood
tables for every t, with no boundary tie at any step; the equi-topology distances at the four core
limits and the per-step factors of the two constant-digraph systems are as the note states.

**Artifact.** `verify.py` (standard library; Q(sqrt5) as pairs of Fractions). It replays the
update rule for t < T (60 by default) and checks the closed form, the full table and the absence
of ties at every step; the section 4 and 5 arc lists and Claim 1 of both spectator systems; the
spectators strictly on one side for t >= 1. For all t: positions are affine in u = lam^t (and
w = 5^-t or 4^-t), every membership inequality keeps a strict sign on the parity boxes (exact
corner test), the update identities hold exactly, and u -> lam u maps each box into the other.
Seven forged controls (a moved x0, swapped parity tables on the replay and on both boxes, a
changed radius, a boundary tie, a wrong rate) must each be rejected. `--T=200` replays longer;
`--explore` also prints the widest intervals.

**Re-run.** `python verify.py` (under 1 s), `python verify.py --T=200` (about 1.5 s).

**Label.** PROVEN-BY-CERTIFICATE (all t, by the box induction). The four core systems are also
pinned in the Lean entry; the spectator systems (e), (f) and the widest intervals are not.

**Not certified.** Anything in Lean; Theorem 6.4(iii) of arXiv:1103.2829 (spectral radii);
genericity (section 6 of the source); Conjecture 2.1.

Last lines of the run:

```
forged control [tie detector: c_sbc6 with r_0 = 22]: rejected (FAIL as required); first: c_sbc6 t=0: boundary ties [(0, 1, 22), (1, 0, 22)]
forged control [update identities: c_sbc6 with rate -1/5]: rejected (FAIL as required); first: (1, 'offset rate -1/5')
time forged controls: 0.01s
genuine failures: 0; total time 0.40s
VERDICT: PASS
```
