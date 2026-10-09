# Verification

All sixty-three statements of Challenge.lean have proofs. The local build, the axiom audit, the source guard, the
definition and statement checks, the standard-library checker, the module-resolution check, the elaboration check
and Palomar's core-notation audit of the statements pass; `python scripts/verify.py` runs them all and ends with
`VERIFY: PASS`. The checks below were last run on the tree of the final commit; a build log is evidence for that
tree only. Theorems are numbered as in `comparator.json`, which is also their order in Challenge.lean.
`comparator.json` lists no `definition_names`: a name there is a definition hole whose value the Solution
supplies; the fifty-four definitions and the inductive `Model` here are fully specified in the Challenge, so the comparator checks the
Solution's values against them.

## Formal scope

| # | Statement | Proved in |
| --- | --- | --- |
| 1 | `sbc7_closed_form` — x(t) = (0, 36, 72, 84, 96, 132, 168) + (-1/6)^t (0, 2, -3, 0, 3, -2, 0) for every t | HK/SBC7.lean |
| 2 | `sbc7_neighbors` — The neighbourhood table at every t; the middle agent (index 3) listens to itself alone at even t and also to indices 2 and 4 at odd t | HK/SBC7.lean |
| 3 | `sbi7_closed_form` — x(t) = (0, 7, 10, 11, 12, 15, 22) + (lambda^t / 2) (0, 1, -phi, 0, phi, -1, 0), lambda = (1 - sqrt 5)/8, for every t | HK/SBI7.lean |
| 4 | `sbi7_neighbors` — The neighbourhood table at every t; the middle agent listens to indices 1 to 5 at even t and to 2, 3, 4 at odd t | HK/SBI7.lean |
| 5 | `sbc6_closed_form` — x(t) = (0, 20, 40, 100, 120, 140) + (-1/6)^t (0, 2, -3, 3, -2, 0) for every t | HK/SBC6.lean |
| 6 | `sbc6_neighbors` — The neighbourhood table, the same at every t | HK/SBC6.lean |
| 7 | `sbi7b_closed_form` — x(t) = (0, 70, 100, 110, 120, 150, 220) + lambda^t (0, 1, -phi, 0, phi, -1, 0) for every t | HK/SBI7b.lean |
| 8 | `sbi7b_neighbors` — The neighbourhood table, the same at every t | HK/SBI7b.lean |
| 9 | `tendsto_limits` — Each of the four trajectories converges to its limit | HK/Refute.lean |
| 10 | `sbc7_digraph_not_eventually_constant` — The proximity digraph of the seven-agent SBC system is not constant on any tail | HK/SBC7.lean |
| 11 | `sbi7_digraph_not_eventually_constant` — The proximity digraph of the seven-agent SBI system is not constant on any tail | HK/SBI7.lean |
| 12 | `sbc6_digraph_constant` — The proximity digraph of the six-agent SBC system is the same at every t | HK/SBC6.lean |
| 13 | `sbi7b_digraph_constant` — The proximity digraph of the second seven-agent SBI system is the same at every t | HK/SBI7b.lean |
| 14 | `not_fixedFrom` — None of the four trajectories is in a fixed state from any time on | HK/Refute.lean |
| 15 | `not_pseudoStableAfter` — None of the four trajectories is pseudo-stable after any time towards any vector | HK/Refute.lean |
| 16 | `not_conjecture22_sbc` — Conjecture 2.2 fails for the SBC model | HK/Refute.lean |
| 17 | `not_conjecture22_sbi` — Conjecture 2.2 fails for the SBI model | HK/Refute.lean |
| 18 | `not_conjecture22` — Conjecture 2.2 fails | HK/Refute.lean |
| 19 | `not_conjecture23_sbc` — Conjecture 2.3 fails for the SBC model | HK/Refute.lean |
| 20 | `not_conjecture23_sbi` — Conjecture 2.3 fails for the SBI model | HK/Refute.lean |
| 21 | `not_conjecture23` — Conjecture 2.3 fails | HK/Refute.lean |
| 22 | `not_theorem64iv_sbc` — Theorem 6.4(iv) fails for the SBC model, in the reading that admits fixed states | HK/Refute.lean |
| 23 | `not_theorem64iv_sbi` — Theorem 6.4(iv) fails for the SBI model, in the reading that admits fixed states | HK/Refute.lean |
| 24 | `not_theorem64iv` — Theorem 6.4(iv) fails in the reading that admits fixed states | HK/Refute.lean |
| 25 | `not_theorem64iv_literal_sbc` — Theorem 6.4(iv) fails for the SBC model in its literal reading (implied by its failure in the reading admitting fixed states) | HK/Refute.lean |
| 26 | `not_theorem64iv_literal_sbi` — Theorem 6.4(iv) fails for the SBI model in its literal reading (implied by its failure in the reading admitting fixed states) | HK/Refute.lean |
| 27 | `not_theorem64iv_literal` — Theorem 6.4(iv) fails in its literal reading (implied by its failure in the reading admitting fixed states) | HK/Refute.lean |
| 28 | `sbc5_closed_form` — Five SBC agents: x(t) = (0, 6, 12, 18, 24) + ((1 - sqrt 2)/3)^t (0, 1, -sqrt 2, 1, 0) for every t | HK/SBC5.lean |
| 29 | `sbc5_neighbors` — Five SBC agents: the neighbourhood table, the same at every t | HK/SBC5.lean |
| 30 | `sbi6_closed_form` — Six SBI agents: x(t) = (0, 25, 31, 44, 55, 90) + ((13 - sqrt 249)/40)^t v for every t | HK/SBI6.lean |
| 31 | `sbi6_neighbors` — Six SBI agents: the neighbourhood table, the same at every t | HK/SBI6.lean |
| 32 | `small_tendsto` — Both smaller systems converge to their limits | HK/Refute.lean |
| 33 | `small_digraph_constant` — Both smaller systems have a proximity digraph that is the same at every t | HK/Refute.lean |
| 34 | `small_not_fixedFrom` — Neither smaller system is in a fixed state from any time on | HK/Refute.lean |
| 35 | `small_not_pseudoStableAfter` — Neither smaller system is pseudo-stable after any time towards any vector | HK/Refute.lean |
| 36 | `not_conjecture22_sbc_seven` — Conjecture 2.2 fails for the SBC model with seven agents | HK/Refute.lean |
| 37 | `not_conjecture22_sbi_seven` — Conjecture 2.2 fails for the SBI model with seven agents | HK/Refute.lean |
| 38 | `not_conjecture23_sbc_five` — Conjecture 2.3 fails for the SBC model with five agents | HK/SBC5.lean |
| 39 | `not_conjecture23_sbi_six` — Conjecture 2.3 fails for the SBI model with six agents | HK/SBI6.lean |
| 40 | `not_theorem64iv_sbc_five` — Theorem 6.4(iv) fails for the SBC model with five agents, in the reading that admits fixed states | HK/SBC5.lean |
| 41 | `not_theorem64iv_sbi_six` — Theorem 6.4(iv) fails for the SBI model with six agents, in the reading that admits fixed states | HK/SBI6.lean |
| 42 | `sbc5_fvct` — Five SBC agents: the final value at constant topology of every x(t) is the limit | HK/SBC5.lean |
| 43 | `sbc5_perStepFactor` — Five SBC agents: the per-step convergence factor of indices 1, 2, 3 is (1 - sqrt 2)/3 at every t | HK/SBC5.lean |
| 44 | `sbi6_fvct` — Six SBI agents: the final value at constant topology of every x(t) is the limit | HK/SBI6.lean |
| 45 | `sbi6_perStepFactor` — Six SBI agents: the per-step convergence factor of indices 1 to 4 is (13 - sqrt 249)/40 at every t | HK/SBI6.lean |
| 46 | `sbc9_closed_form` — Nine SBC agents with a spectator and two beacons: the closed form with the two geometric terms (-1/6)^t and (1/5)^t for every t | HK/SpectatorSBC.lean |
| 47 | `sbc9_neighbors` — Nine SBC agents: the neighbourhood table, the same at every t; nobody listens to the spectator | HK/SpectatorSBC.lean |
| 48 | `sbc9_spectator_lt` — The spectator is strictly left of 210 for every t >= 1 | HK/SpectatorSBC.lean |
| 49 | `sbi8_closed_form` — Eight SBI agents with a spectator: the closed form with the two geometric terms lambda^t and (1/4)^t for every t | HK/SpectatorSBI.lean |
| 50 | `sbi8_neighbors` — Eight SBI agents: the neighbourhood table, the same at every t; nobody listens to the spectator | HK/SpectatorSBI.lean |
| 51 | `sbi8_spectator_gt` — The spectator is strictly right of 60 for every t >= 1 | HK/SpectatorSBI.lean |
| 52 | `alternating_fvct` — Along the two alternating systems the final value at constant topology of every x(t) is the limit | HK/Refute.lean |
| 53 | `sbc6_fvct` — Along the six-agent SBC system the final value at constant topology of every x(t) is the limit | HK/SBC6.lean |
| 54 | `sbc6_perStepFactor` — The per-step convergence factor of indices 1 to 4 is -1/6 at every t | HK/SBC6.lean |
| 55 | `sbc6_perStepFactor_not_tendsto` — That factor converges to no non-negative number | HK/SBC6.lean |
| 56 | `sbi7b_fvct` — Along the second seven-agent SBI system the final value at constant topology of every x(t) is the limit | HK/SBI7b.lean |
| 57 | `sbi7b_perStepFactor` — The per-step convergence factor of indices 1, 2, 4, 5 is (1 - sqrt 5)/8 at every t (index 3 sits at its limit) | HK/SBI7b.lean |
| 58 | `sbi7b_perStepFactor_not_tendsto` — That factor converges to no non-negative number | HK/SBI7b.lean |
| 59 | `proximityDigraph_eq_of_equiTopologyNbhd` — A point of the equi-topology neighbourhood of z has the proximity digraph of z (no positivity of the bounds assumed) | HK/Generic.lean |
| 60 | `eventually_constant_of_tendsto` — A convergent trajectory whose limit has every equi-topology distance positive eventually has the proximity digraph of its limit | HK/Generic.lean |
| 61 | `fvct_eq_and_equilibrium_of_tendsto` — Under the same hypotheses the limit is eventually the final value at constant topology of x(t), and an equilibrium | HK/Generic.lean |
| 62 | `equiTopologyDistance_pos` — Every equi-topology distance of the limits of the two constant-digraph source systems is positive | HK/Refute.lean |
| 63 | `equiTopologyDistance_eq_zero` — The limits of the two alternating systems have equi-topology distance 0 at indices 2, 3, 4 (SBC) and 1, 3, 5 (SBI) | HK/Refute.lean |

Each statement is restated verbatim in Solution.lean and closed by the internal theorem of the same name with the
suffix `_internal`; every module above imports `HK/Basic.lean`. PROOF.md names the lemma behind each step.

## Local checks

```sh
python scripts/verify.py --fetch-cache
```

runs, in order: the pins (`lean-toolchain` and the Mathlib revision of `lake-manifest.json` are the committed ones),
`scripts/check-source.py`, `scripts/check_definitions.py`, `scripts/check_statements.py`, the standard-library
checker `scripts/check_hk.py`, `lake build` of the four targets `HK`, `Challenge`, `Solution`, `Test`,
`lake env python scripts/check_module_resolution.py`, the elaboration check (every definition printed with `pp.all`
from the Challenge and from `HK.Defs`; the outputs must be identical), and Palomar's
`scripts/core_notation_audit.lean` on the hundred and seventeen declarations of the statement surface (the sixty-three
compared theorems and the fifty-four definitions other than the inductive `Model`); the last line is `VERIFY: PASS` or `VERIFY: FAIL`.
`--skip-build` leaves out the four Lean steps.

The `Test` target imports `Solution` and audits every constant of its environment whose name begins with `HK.`,
`_private.HK.` or `_private.Solution.` (449 constants on the tree of the final commit; the audit fails
below 120), permits only `propext`, `Classical.choice` and `Quot.sound`, and fails if any of the sixty-three compared
theorems is missing. A placeholder in a proof compiles with a warning; this audit is what fails the build.
Challenge.lean intentionally contains sixty-three proof placeholders; Solution.lean and the modules it imports contain
none, and Solution.lean does not import Challenge.lean. The source guard rejects `sorry`, `sorryAx`, `admit`,
`axiom`, `unsafe`, `partial`, `mutual`, `opaque`, `csimp`, `native_decide`, `implemented_by`, `extern`,
`ofReduceBool`, `ofReduceNat` and the kernel-bypass options `debug.skipKernelTC` and `debug.byAsSorry` in `HK/`,
`HK.lean`, Solution.lean, Test.lean and `Test/`, the same tokens except `sorry` in Challenge.lean, and any `debug.`
option in the `[leanOptions]` table of lakefile.toml. `check_definitions.py` compares the fifty-five definition blocks of
Challenge.lean and `HK/Defs.lean` character for character and the two files' import lines; `check_statements.py`
compares every theorem header of Challenge.lean with Solution.lean. Palomar's `scripts/core_notation_audit.lean` is
an unmodified copy from github.com/PalomarRegistry/PalomarSubmission (fetched 2026-10-07 UTC; MIT, see
`LICENSES/`); it needs about 4 GB of memory, so run it with no other Lean process active.

Lean `v4.35.0-rc2` and Mathlib `v4.35.0-rc2` (commit `065356127b1dc0016f66b7283ce0ce2c4055aa55`) are pinned by the
committed manifest; `lake update` is never run. Every `.lean` file of the repository carries a `module` header.
`HK/Defs.lean` imports exactly what the Challenge imports (`Mathlib`), so that the definitions elaborate to identical
terms in both environments. With the modules built, `python scripts/verify.py` takes about five minutes on this machine (the core-notation audit is most of it); each module builds in 12–29 s.

## The finite computations

There is no `native_decide` and no large kernel computation: each neighbourhood table is a finite case split
(`fin_cases` over the agent pairs, at most 81) closed by linear arithmetic over the reals, and each irrational rate
enters through `φ² = φ + 1`, `√2² = 2` or `√249² = 249` and rational bounds on the square root. Everything else is
induction on `t`, `ring`/`linear_combination` identities, limits of geometric sequences, and the infimum of a finite
set of reals.

`scripts/check_hk.py` (Python 3.9+, standard library, a few seconds) is a cross-check no Lean proof depends on: it
replays the eight systems of Challenge.lean (the six of the source, the two spectator systems among them, and the two smaller systems) with exact arithmetic in `ℚ(√d)` for `t < 60` by default (`--T=N` for longer)
under the update rule itself (the table at each step computed from the state, not assumed), checks every closed form,
every table and the absence of boundary ties, decides each table on its interval of the atom by an exact corner
test, checks the update identities, the equi-topology distance vectors at the limits and the per-step factors, and
rejects a set of forged inputs; it ends with `VERDICT: PASS`.

## What is and is not claimed

- Claimed, in Lean: the sixty-three statements above, kernel-checked, on the definitions of Challenge.lean.
- Mirtabatabaei and Bullo's text read is arXiv:1103.2829v2; the published SIAM text was not read. The pinned
  definitions follow that text with `≤` in the neighbourhoods and agents indexed from `0`.
- `perStepFactor` is total (`x/0 = 0` in Lean); it is used only at agents and times where the denominator is nonzero.
  For `n = 1` the equi-topology distance is `sInf ∅ = 0` by Lean's convention.
- Theorem 6.4(iii) is not formalized; only the reduced (iii)(a) statement is proved: along the two constant-digraph
  systems the per-step factor of every agent with nonzero offset is identically `λ < 0`, so it converges to no
  non-negative number.
- The literal Theorem 6.4(iv) is trivially false (one frozen agent); the content is the refutation of the reading
  admitting fixed states, which implies it.
- Conjecture 2.1 (every trajectory converges) is open and untouched.
- Not claimed in Lean: Theorem 6.4(iii)(b) itself (the spectator systems' closed forms, tables and the spectator's side are
  proved; the statement about leader components is not formalized); the source's §6 genericity discussion; the note's results (at least
  five agents within the eigenvector class; the exact searches at five and six agents), which are certificates in
  `note/` and are stated only within that class.
