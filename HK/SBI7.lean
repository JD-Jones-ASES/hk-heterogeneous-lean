module

public import HK.Basic

/-!
# The 7-agent SBI system (Hegarty–Ognissanti–Wedin §3)

`x(0) = (0, 15/2, 10 − φ/2, 11, 12 + φ/2, 29/2, 22)`, `r = (8, 4, 4, 8, 4, 4, 8)`, `φ = (1 + √5)/2`,
`λ = (1 − √5)/8`; `x(t) = (0, 7, 10, 11, 12, 15, 22) + (λᵗ/2) (0, 1, −φ, 0, φ, −1, 0)`. The middle
agent (index 3) listens to indices 1–5 at even `t` and to 2, 3, 4 at odd `t`; the proximity digraph
is never eventually constant; agents 1, 2, 4, 5 alternate sides of their limits. The identities used
are `φ² = φ + 1`, `4λ = 1 − φ` and `4λφ = −1` (the source's (3.1)); at odd `t` the tables need the
bound `λ ≤ λᵗ`, not only `−1 ≤ λᵗ`.
-/

@[expose] public section

namespace HK

open Filter Topology

theorem sbi7_r_pos : ∀ i, 0 < sbi7_r i := sorry

theorem sbi7_closed_form_internal (t : ℕ) :
    traj .sbi sbi7_r sbi7_x0 t = fun i => sbi7_lim i + sbiRate ^ t / 2 * sbi_v i := sorry

theorem sbi7_neighbors_internal (t : ℕ) :
    neighbors .sbi sbi7_r (traj .sbi sbi7_r sbi7_x0 t) =
      ![{0}, {0, 1, 2, 3}, {1, 2, 3, 4}, if Even t then {1, 2, 3, 4, 5} else {2, 3, 4},
        {2, 3, 4, 5}, {3, 4, 5, 6}, {6}] := sorry

theorem sbi7_tendsto : Tendsto (traj .sbi sbi7_r sbi7_x0) atTop (𝓝 sbi7_lim) := sorry

theorem sbi7_digraph_not_eventually_constant_internal (τ : ℕ) :
    ∃ t, τ ≤ t ∧ proximityDigraph .sbi sbi7_r (traj .sbi sbi7_r sbi7_x0 t) ≠
      proximityDigraph .sbi sbi7_r (traj .sbi sbi7_r sbi7_x0 τ) := sorry

theorem sbi7_not_fixedFrom (τ : ℕ) : ¬ FixedFrom (traj .sbi sbi7_r sbi7_x0) τ := sorry

theorem sbi7_not_pseudoStableAfter (xinf : Fin 7 → ℝ) (τ : ℕ) :
    ¬ PseudoStableAfter (traj .sbi sbi7_r sbi7_x0) xinf τ := sorry

end HK
