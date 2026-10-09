module

import Solution
import Lean.Util.CollectAxioms

/-!
# Axiom audit

A module file importing `Solution` (not `Challenge.lean`). Walks every constant of the environment
whose name begins with `HK.`, `_private.HK.` or `_private.Solution.` (the public declarations of
this development; the private auxiliaries that Lean generates are not enumerated under the module
system, but `collectAxioms` reaches every private constant a public proof refers to, including a
private `axiom`), and collects the axioms each depends on. Anything outside `propext`,
`Classical.choice`, `Quot.sound` is reported with `logError`, which fails `lake build`. The audit
also fails if it matched fewer constants than the floor below (so a renamed namespace cannot make it
pass vacuously) or if any of the compared theorems is missing from the environment.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut checked : Nat := 0
  let mut rejected : Nat := 0
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for (name, _) in env.constants.toList do
    let label := name.toString
    if label.startsWith "HK." || label.startsWith "_private.HK." ||
        label.startsWith "_private.Solution." then
      checked := checked + 1
      let axs ← collectAxioms name
      for ax in axs do
        unless allowed.contains ax do
          rejected := rejected + 1
          logError m!"Unexpected axiom dependency: {name} -> {ax}"
  unless checked ≥ 120 do
    logError m!"Axiom audit matched only {checked} project constants; expected at least 120"
  for n in [`HK.sbc7_closed_form, `HK.sbc7_neighbors, `HK.sbi7_closed_form, `HK.sbi7_neighbors,
      `HK.sbc6_closed_form, `HK.sbc6_neighbors, `HK.sbi7b_closed_form, `HK.sbi7b_neighbors,
      `HK.tendsto_limits, `HK.sbc7_digraph_not_eventually_constant,
      `HK.sbi7_digraph_not_eventually_constant, `HK.sbc6_digraph_constant,
      `HK.sbi7b_digraph_constant, `HK.not_fixedFrom, `HK.not_pseudoStableAfter,
      `HK.not_conjecture22_sbc, `HK.not_conjecture22_sbi, `HK.not_conjecture22,
      `HK.not_conjecture23_sbc, `HK.not_conjecture23_sbi, `HK.not_conjecture23,
      `HK.not_theorem64iv_sbc, `HK.not_theorem64iv_sbi, `HK.not_theorem64iv,
      `HK.not_theorem64iv_literal_sbc, `HK.not_theorem64iv_literal_sbi,
      `HK.not_theorem64iv_literal, `HK.sbc5_closed_form, `HK.sbc5_neighbors,
      `HK.sbi6_closed_form, `HK.sbi6_neighbors, `HK.small_tendsto, `HK.small_digraph_constant,
      `HK.small_not_fixedFrom, `HK.small_not_pseudoStableAfter, `HK.not_conjecture22_sbc_seven,
      `HK.not_conjecture22_sbi_seven, `HK.not_conjecture23_sbc_five,
      `HK.not_conjecture23_sbi_six, `HK.not_theorem64iv_sbc_five, `HK.not_theorem64iv_sbi_six,
      `HK.sbc5_fvct, `HK.sbc5_perStepFactor, `HK.sbi6_fvct, `HK.sbi6_perStepFactor,
      `HK.sbc9_closed_form, `HK.sbc9_neighbors, `HK.sbc9_spectator_lt, `HK.sbi8_closed_form,
      `HK.sbi8_neighbors, `HK.sbi8_spectator_gt, `HK.alternating_fvct, `HK.sbc6_fvct,
      `HK.sbc6_perStepFactor, `HK.sbc6_perStepFactor_not_tendsto, `HK.sbi7b_fvct,
      `HK.sbi7b_perStepFactor, `HK.sbi7b_perStepFactor_not_tendsto,
      `HK.proximityDigraph_eq_of_equiTopologyNbhd, `HK.eventually_constant_of_tendsto,
      `HK.fvct_eq_and_equilibrium_of_tendsto, `HK.equiTopologyDistance_pos,
      `HK.equiTopologyDistance_eq_zero] do
    unless env.contains n do
      logError m!"Compared theorem is missing from the environment: {n}"
  logInfo m!"Audited {checked} project constants; unexpected axiom dependencies: {rejected}."
