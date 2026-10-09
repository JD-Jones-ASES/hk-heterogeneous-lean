# Verification

All fifty-one statements of Challenge.lean have proofs. The local build, the axiom audit, the source guard, the
definition and statement checks, the standard-library checker, the module-resolution check, the elaboration check
and Palomar's core-notation audit of the statements pass; `python scripts/verify.py` runs them all and ends with
`VERIFY: PASS`. The checks below were last run on the tree of the final commit; a build log is evidence for that
tree only. Theorems are numbered as in `comparator.json`, which is also their order in Challenge.lean.
`comparator.json` lists no `definition_names`: a name there is a definition hole whose value the Solution
supplies; the fifty-one definitions here are fully specified in the Challenge, so the comparator checks the
Solution's values against them.

## Formal scope

| # | Statement | Proved in |
| --- | --- | --- |
| 1 | `sbc7_closed_form` — §2: `x(t) = x_∞ + (−1/6)ᵗ v` | HK/SBC7.lean |
| 2 | `sbc7_neighbors` — §2: the table at every `t`, row 3 by parity | HK/SBC7.lean |
| 3 | `sbi7_closed_form` — §3: `x(t) = x_∞ + (λᵗ/2) v`, `λ = (1 − √5)/8` | HK/SBI7.lean |
| 4 | `sbi7_neighbors` — §3: the table at every `t`, row 3 by parity | HK/SBI7.lean |
| 5 | `sbc6_closed_form` — §4: `x(t) = x_∞ + (−1/6)ᵗ v` | HK/SBC6.lean |
| 6 | `sbc6_neighbors` — §4: the same table at every `t` | HK/SBC6.lean |
| 7 | `sbi7b_closed_form` — §5: `x(t) = x_∞ + λᵗ v` | HK/SBI7b.lean |
| 8 | `sbi7b_neighbors` — §5: the same table at every `t` | HK/SBI7b.lean |
| 9 | `tendsto_limits` — the four trajectories converge to their limits | HK/Refute.lean (with SBC7, SBI7, SBC6, SBI7b) |
| 10 | `sbc7_digraph_not_eventually_constant` — §2: not constant on any tail | HK/SBC7.lean |
| 11 | `sbi7_digraph_not_eventually_constant` — §3: not constant on any tail | HK/SBI7.lean |
| 12 | `sbc6_digraph_constant` — §4: the digraph at `t` is that at `0` | HK/SBC6.lean |
| 13 | `sbi7b_digraph_constant` — §5: the digraph at `t` is that at `0` | HK/SBI7b.lean |
| 14 | `not_fixedFrom` — none of the four is in a fixed state from any `τ` | HK/Refute.lean (with Basic) |
| 15 | `not_pseudoStableAfter` — none of the four is pseudo-stable after any `τ`, towards any vector | HK/Refute.lean (with Basic) |
| 16 | `not_conjecture22_sbc` — Conjecture 2.2 fails for SBC | HK/Refute.lean |
| 17 | `not_conjecture22_sbi` — Conjecture 2.2 fails for SBI | HK/Refute.lean |
| 18 | `not_conjecture22` — Conjecture 2.2 fails | HK/Refute.lean |
| 19 | `not_conjecture23_sbc` — Conjecture 2.3 fails for SBC | HK/Refute.lean |
| 20 | `not_conjecture23_sbi` — Conjecture 2.3 fails for SBI | HK/Refute.lean |
| 21 | `not_conjecture23` — Conjecture 2.3 fails | HK/Refute.lean |
| 22 | `not_theorem64iv_sbc` — Theorem 6.4(iv), reading admitting fixed states, fails for SBC | HK/Refute.lean |
| 23 | `not_theorem64iv_sbi` — the same for SBI | HK/Refute.lean |
| 24 | `not_theorem64iv` — the same for both models | HK/Refute.lean |
| 25 | `not_theorem64iv_literal` — the literal reading fails | HK/Refute.lean |
| 26 | `sbc5_closed_form` — five SBC agents: `x(t) = x_∞ + ((1 − √2)/3)ᵗ v` | HK/SBC5.lean |
| 27 | `sbc5_neighbors` — five SBC agents: the same table at every `t` | HK/SBC5.lean |
| 28 | `sbi6_closed_form` — six SBI agents: `x(t) = x_∞ + ((13 − √249)/40)ᵗ v` | HK/SBI6.lean |
| 29 | `sbi6_neighbors` — six SBI agents: the same table at every `t` | HK/SBI6.lean |
| 30 | `small_tendsto` — both smaller systems converge | HK/Refute.lean (with SBC5, SBI6) |
| 31 | `small_digraph_constant` — both have a constant digraph | HK/Refute.lean (with SBC5, SBI6) |
| 32 | `small_not_fixedFrom` — neither is ever in a fixed state | HK/Refute.lean (with SBC5, SBI6) |
| 33 | `small_not_pseudoStableAfter` — neither is ever pseudo-stable | HK/Refute.lean (with SBC5, SBI6) |
| 34 | `not_conjecture22_sbc_seven` — Conjecture 2.2 fails for SBC with seven agents | HK/Refute.lean (with SBC7) |
| 35 | `not_conjecture22_sbi_seven` — Conjecture 2.2 fails for SBI with seven agents | HK/Refute.lean (with SBI7) |
| 36 | `not_conjecture23_sbc_five` — Conjecture 2.3 fails for SBC with five agents | HK/SBC5.lean |
| 37 | `not_conjecture23_sbi_six` — Conjecture 2.3 fails for SBI with six agents | HK/SBI6.lean |
| 38 | `not_theorem64iv_sbc_five` — Theorem 6.4(iv) fails for SBC with five agents | HK/SBC5.lean |
| 39 | `not_theorem64iv_sbi_six` — Theorem 6.4(iv) fails for SBI with six agents | HK/SBI6.lean |
| 40 | `alternating_fvct` — §2, §3: `fvct(x(t)) = x_∞` at every `t` | HK/Refute.lean (with SBC7, SBI7) |
| 41 | `sbc6_fvct` — §4: `fvct(x(t)) = x_∞` at every `t` | HK/SBC6.lean |
| 42 | `sbc6_perStepFactor` — §4: the factor of agents 1–4 is `−1/6` at every `t` | HK/SBC6.lean |
| 43 | `sbc6_perStepFactor_not_tendsto` — §4: it tends to no `ρ ≥ 0` | HK/SBC6.lean |
| 44 | `sbi7b_fvct` — §5: `fvct(x(t)) = x_∞` at every `t` | HK/SBI7b.lean |
| 45 | `sbi7b_perStepFactor` — §5: the factor of agents 1, 2, 4, 5 is `λ` at every `t` | HK/SBI7b.lean |
| 46 | `sbi7b_perStepFactor_not_tendsto` — §5: it tends to no `ρ ≥ 0` | HK/SBI7b.lean |
| 47 | `proximityDigraph_eq_of_equiTopologyNbhd` — MB Lemma 4.2 | HK/Generic.lean |
| 48 | `eventually_constant_of_tendsto` — MB Lemma 4.8(i) | HK/Generic.lean |
| 49 | `fvct_eq_and_equilibrium_of_tendsto` — MB Lemma 4.8(ii) | HK/Generic.lean |
| 50 | `equiTopologyDistance_pos` — every equi-topology distance at the limits of §4 and §5 is positive | HK/Refute.lean |
| 51 | `equiTopologyDistance_eq_zero` — zero at indices 2, 3, 4 (§2) and 1, 3, 5 (§3) | HK/Refute.lean (with Generic) |

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
`scripts/core_notation_audit.lean` on the hundred and two declarations of the statement surface (the fifty-one
compared theorems and the fifty-one definitions); the last line is `VERIFY: PASS` or `VERIFY: FAIL`.
`--skip-build` leaves out the four Lean steps.

The `Test` target imports `Solution` and audits every constant of its environment whose name begins with `HK.`,
`_private.HK.` or `_private.Solution.` ([DESK: count] constants on the tree of the final commit; the audit fails
below 120), permits only `propext`, `Classical.choice` and `Quot.sound`, and fails if any of the fifty-one compared
theorems is missing. A placeholder in a proof compiles with a warning; this audit is what fails the build.
Challenge.lean intentionally contains fifty-one proof placeholders; Solution.lean and the modules it imports contain
none, and Solution.lean does not import Challenge.lean. The source guard rejects `sorry`, `sorryAx`, `admit`,
`axiom`, `unsafe`, `partial`, `mutual`, `opaque`, `csimp`, `native_decide`, `implemented_by`, `extern`,
`ofReduceBool`, `ofReduceNat` and the kernel-bypass options `debug.skipKernelTC` and `debug.byAsSorry` in `HK/`,
`HK.lean`, Solution.lean, Test.lean and `Test/`, the same tokens except `sorry` in Challenge.lean, and any `debug.`
option in the `[leanOptions]` table of lakefile.toml. `check_definitions.py` compares the fifty-one definitions of
Challenge.lean and `HK/Defs.lean` character for character and the two files' import lines; `check_statements.py`
compares every theorem header of Challenge.lean with Solution.lean. Palomar's `scripts/core_notation_audit.lean` is
an unmodified copy from github.com/PalomarRegistry/PalomarSubmission (fetched 2026-10-07 UTC; MIT, see
`LICENSES/`); it needs about 4 GB of memory, so run it with no other Lean process active.

Lean `v4.35.0-rc2` and Mathlib `v4.35.0-rc2` (commit `065356127b1dc0016f66b7283ce0ce2c4055aa55`) are pinned by the
committed manifest; `lake update` is never run. Every `.lean` file of the repository carries a `module` header.
`HK/Defs.lean` imports exactly what the Challenge imports (`Mathlib`), so that the definitions elaborate to identical
terms in both environments. [DESK: build time of the four targets from an empty `.lake/build` after
`lake exe cache get`, and of `verify.py`.]

## The finite computations

There is no `native_decide` and no large kernel computation: each neighbourhood table is a finite case split
(`fin_cases` over the agent pairs, at most 49) closed by linear arithmetic over the reals, and each irrational rate
enters through `φ² = φ + 1`, `√2² = 2` or `√249² = 249` and rational bounds on the square root. Everything else is
induction on `t`, `ring`/`linear_combination` identities, limits of geometric sequences, and the infimum of a finite
set of reals.

`scripts/check_hk.py` (Python 3.9+, standard library, a few seconds) is a cross-check no Lean proof depends on: it
replays the four systems of the source and the two smaller systems with exact arithmetic in `ℚ(√d)` for `t < 200`
under the update rule itself (the table at each step computed from the state, not assumed), checks every closed form,
every table and the absence of boundary ties, decides each table on its interval of the atom by an exact corner
test, checks the update identities, the equi-topology distance vectors at the limits and the per-step factors, and
rejects a set of forged inputs; it ends with `VERDICT: PASS`. [DESK: confirm the checker's final name and scope.]

## What is and is not claimed

- Claimed, in Lean: the fifty-one statements above, kernel-checked, on the definitions of Challenge.lean.
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
- Not claimed in Lean: the source's spectator systems and its §6 genericity discussion; the note's results (at least
  five agents within the eigenvector class; the exact searches at five and six agents), which are certificates in
  `note/` and are stated only within that class.
