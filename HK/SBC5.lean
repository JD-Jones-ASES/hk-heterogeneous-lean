module

public import HK.Basic

/-!
# Five SBC agents with a constant digraph and oscillating convergence (this development)

`x(0) = (0, 7, 12 − √2, 19, 24)`, `r = (3, 9, 9, 9, 3)`;
`x(t) = (0, 6, 12, 18, 24) + ((1 − √2)/3)ᵗ (0, 1, −√2, 1, 0)`. The neighbourhood table
`{0}, {0, 1, 2}, {1, 2, 3}, {2, 3, 4}, {4}` is the same at every `t`, yet agents 1, 2, 3 alternate sides
of their limits. Hence Theorem 6.4(iv) and Conjecture 2.3 fail already with five SBC agents. The
identities used: `√2² = 2`; `3λ − 1 = −√2`; `λ√2 = (√2 − 2)/3`; the rate lies in `(−1/6, 0)`
(`1.4 < √2 < 1.5`), so `λ ≤ λᵗ ≤ 1` for every `t` and one table serves both parities.
-/

@[expose] public section

namespace HK

open Filter Topology

theorem sbc5_r_pos : ∀ i, 0 < sbc5_r i := sorry

theorem sbc5Rate_neg : sbc5Rate < 0 := sorry

theorem abs_sbc5Rate_lt_one : |sbc5Rate| < 1 := sorry

theorem sbc5_closed_form_internal (t : ℕ) :
    traj .sbc sbc5_r sbc5_x0 t = fun i => sbc5_lim i + sbc5Rate ^ t * sbc5_v i := sorry

theorem sbc5_neighbors_internal (t : ℕ) :
    neighbors .sbc sbc5_r (traj .sbc sbc5_r sbc5_x0 t) =
      ![{0}, {0, 1, 2}, {1, 2, 3}, {2, 3, 4}, {4}] := sorry

theorem sbc5_tendsto : Tendsto (traj .sbc sbc5_r sbc5_x0) atTop (𝓝 sbc5_lim) := sorry

theorem sbc5_digraph_constant (t : ℕ) :
    proximityDigraph .sbc sbc5_r (traj .sbc sbc5_r sbc5_x0 t) =
      proximityDigraph .sbc sbc5_r sbc5_x0 := sorry

theorem sbc5_not_fixedFrom (τ : ℕ) : ¬ FixedFrom (traj .sbc sbc5_r sbc5_x0) τ := sorry

theorem sbc5_not_pseudoStableAfter (xinf : Fin 5 → ℝ) (τ : ℕ) :
    ¬ PseudoStableAfter (traj .sbc sbc5_r sbc5_x0) xinf τ := sorry

theorem not_conjecture23_sbc_five_internal : ¬ Conjecture23ForAgents .sbc 5 := sorry

theorem not_theorem64iv_sbc_five_internal : ¬ Theorem64ivForAgents .sbc 5 := sorry

end HK
