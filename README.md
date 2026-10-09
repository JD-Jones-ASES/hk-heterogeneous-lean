# Heterogeneous Hegselmann–Krause dynamics: explicit systems whose proximity digraph is never eventually constant, and constant-digraph systems whose convergence is never pseudo-stable

Mirtabatabaei and Bullo (*Opinion dynamics in heterogeneous networks: convergence conjectures and theorems*,
SIAM J. Control Optim. 50 (2012) 2763–2785; the text read is arXiv:1103.2829v2) study `n` agents with real
opinions and positive bounds `rᵢ` that move synchronously to the mean of their out-neighbours,
`{j : |xᵢ − xⱼ| ≤ rᵢ}` in the SBC model (the heterogeneous Hegselmann–Krause model of Lorenz) and
`{j : |xᵢ − xⱼ| ≤ rⱼ}` in the SBI model. Their Conjecture 2.2: the proximity digraph is constant after a finite
time. Conjecture 2.3: every trajectory freezes or becomes pseudo-stable (two non-empty classes of agents, one at
its limits, the other approaching them monotonically from one side). Theorem 6.4(iv): an eventually constant
digraph gives eventual pseudo-stability. Hegarty, Ognissanti and Wedin (arXiv:2610.03229v1) refute all three with
four explicit systems; by their §7 these "were found by Claude Opus 5.5, upon prompting by the authors", who
verified them by hand; the text of the paper is the authors' own.

[Challenge.lean](Challenge.lean) restates the definitions (Mirtabatabaei–Bullo's, with `≤`; agents are indexed
`0, …, n − 1`, the paper's agent `i` being index `i − 1`) and states seventy-six theorems, and
[Solution.lean](Solution.lean) proves them, kernel-only; the table in [VERIFICATION.md](VERIFICATION.md) names each:

- the four systems' closed forms `x(t) = x_∞ + c λᵗ v` (`λ = −1/6` for SBC, `(1 − √5)/8` for SBI) and complete
  neighbourhood tables at every `t`: in the two alternating 7-agent systems the middle agent's neighbourhood
  changes with the parity of `t`; in the 6-agent SBC and the second 7-agent SBI system the table never changes;
- none of the four is ever frozen or pseudo-stable after any time towards any vector, as four agents alternate
  sides of their limits; so Conjecture 2.2 fails in each model with seven agents, and Conjecture 2.3 and Theorem
  6.4(iv) fail in each model;
- two smaller constant-digraph systems found in this development (five SBC agents, rate `(1 − √2)/3`; six SBI
  agents, rate `(13 − √249)/40`): Conjecture 2.3 and Theorem 6.4(iv) fail already at those agent counts, and
  along them too `fvct` is the limit and the per-step factor is the rate;
- a five-agent SBI system with a constant digraph whose three moving agents are each strictly above and strictly
  below their limits in every five consecutive times (the offsets follow a rational averaging map with a complex
  pair of modes; an algebraic initial offset cancels the real mode): Conjecture 2.3 and Theorem 6.4(iv) fail with
  five agents in either model;
- a five-agent SBC family with radii `(6 − 3δ, 6 + 3δ, 6 + 3δ, 6 + 3δ, 6 − 3δ)`, `0 < δ ≤ 1`: constant digraph,
  convergence, never frozen or pseudo-stable; so for every `ε > 0` such a system exists with `rᵢ < (1 + ε) rⱼ` for
  all `i, j`;
- the source's two spectator systems (nine SBC agents with a spectator and two beacons; eight SBI agents with a
  spectator): closed forms with two geometric terms, constant tables, the spectator strictly on one side of its
  limit for every `t ≥ 1` while its leader component's agents alternate sides;
- along all four systems the final value at constant topology (`fvct`, their Definition 3.1) of `x(t)` is `x_∞`,
  and in the two constant-digraph systems each agent with nonzero offset has per-step convergence factor
  (Definition 6.1) identically `λ < 0`, which converges to no non-negative number;
- their Lemmas 4.2 and 4.8, proved without assuming `r > 0`; the two constant-digraph systems of the source satisfy Lemma 4.8's
  hypothesis (every equi-topology distance of the limit positive), the alternating ones violate it.

In the accompanying note ([note/](note/README.md), with standard-library certificates), not in Lean: within the
class of trajectories eventually `x_∞ + λᵗ v` (`λ ∈ (−1, 0)` real, `v ≠ 0`, one neighbourhood pattern per sign of
`λᵗ`), every system has at least five agents, and exact searches at five and six agents find no SBI system with
five agents and no alternating system with five or six agents in either model (the five-agent SBI system above
has complex modes and lies outside that class); on paper, every trajectory on at most four agents whose digraph
is eventually constant is eventually frozen or pseudo-stable, so five is the least agent count for a
constant-digraph counterexample in either model; and, on paper, weakly connected SBC systems of this kind at every
`n ≥ 5` from the sine modes of a path, with rates dense in `(−1/3, 0)`, and a six-agent SBI family whose radii
are arbitrarily close to equal.

Not claimed: Theorem 6.4(iii) (only the reduced statement above; components and spectral radii are not
formalized); anything beyond the trivial from the literal 6.4(iv), which one frozen agent violates, so the content
is the refutation of the reading admitting fixed states; Conjecture 2.1 (every trajectory converges), open and
untouched; Theorem 6.4(iii)(b) itself (its two spectator systems are proved: closed forms, tables, the spectator
strictly on one side of its limit; the statement about leader components is not formalized); the source's
genericity discussion; the note's results as Lean theorems; a counterexample with equal radii.

> As of 2026-10-09 (UTC), no formalization of the heterogeneous Hegselmann–Krause models (SBC or SBI), of
> Mirtabatabaei and Bullo's conjectures, definitions or theorems, or of the counterexamples of arXiv:2610.03229
> was located in the Palomar registry, formal-conjectures (its tree, issues and pull requests), Mathlib, Lean
> Pool, openai/math, Hexagon, the Isabelle AFP, the Rocq opam index, the public archive of the Lean Zulip, or
> GitHub's Lean, Isabelle and Rocq code, and arXiv lists no follow-up to arXiv:2610.03229. Submissions under
> review at Palomar are not visible in its data API.

Lean `v4.35.0-rc2` and Mathlib `v4.35.0-rc2` (commit `065356127b1dc0016f66b7283ce0ce2c4055aa55`) are pinned by
the committed manifest; there are no GitHub Actions workflows. `python scripts/verify.py --fetch-cache` runs every
check (pins, source guard, definition and statement comparisons, the standard-library checker and the note's
certificates, the build with the axiom audit, module resolution, the elaboration check of the sixty-two
definitions, Palomar's core-notation audit); [VERIFICATION.md](VERIFICATION.md) lists them and their limits,
[PROOF.md](PROOF.md) gives the mathematics with the Lean name of every step, and [DISCLOSURE.md](DISCLOSURE.md)
the assistance statement.

License: [MIT](LICENSE) for the Lean files and scripts; the note in [note/](note/README.md) is CC BY-SA 4.0;
`scripts/core_notation_audit.lean` is Palomar's, under its MIT licence
([LICENSES/PalomarSubmission-MIT.txt](LICENSES/PalomarSubmission-MIT.txt)).
