module

public import HK.Basic

/-!
# The 7-agent SBC system (Hegarty–Ognissanti–Wedin §2)

`x(0) = (0, 38, 69, 84, 99, 130, 168)`, `r = (18, 42, 48, 12, 48, 42, 18)`;
`x(t) = (0, 36, 72, 84, 96, 132, 168) + (−1/6)ᵗ (0, 2, −3, 0, 3, −2, 0)`. The middle agent (index 3)
listens to itself alone at even `t` and to indices 2, 3, 4 at odd `t`; the proximity digraph is
never eventually constant; agents 1, 2, 4, 5 alternate sides of their limits.
-/

@[expose] public section

namespace HK

open Filter Topology

theorem sbc7_r_pos : ∀ i, 0 < sbc7_r i := sorry

theorem sbc7_closed_form_internal (t : ℕ) :
    traj .sbc sbc7_r sbc7_x0 t = fun i => sbc7_lim i + (-1 / 6 : ℝ) ^ t * sbc7_v i := sorry

theorem sbc7_neighbors_internal (t : ℕ) :
    neighbors .sbc sbc7_r (traj .sbc sbc7_r sbc7_x0 t) =
      ![{0}, {0, 1, 2}, {1, 2, 3, 4}, if Even t then {3} else {2, 3, 4}, {2, 3, 4, 5},
        {4, 5, 6}, {6}] := sorry

theorem sbc7_tendsto : Tendsto (traj .sbc sbc7_r sbc7_x0) atTop (𝓝 sbc7_lim) := sorry

theorem sbc7_digraph_not_eventually_constant_internal (τ : ℕ) :
    ∃ t, τ ≤ t ∧ proximityDigraph .sbc sbc7_r (traj .sbc sbc7_r sbc7_x0 t) ≠
      proximityDigraph .sbc sbc7_r (traj .sbc sbc7_r sbc7_x0 τ) := sorry

theorem sbc7_not_fixedFrom (τ : ℕ) : ¬ FixedFrom (traj .sbc sbc7_r sbc7_x0) τ := sorry

theorem sbc7_not_pseudoStableAfter (xinf : Fin 7 → ℝ) (τ : ℕ) :
    ¬ PseudoStableAfter (traj .sbc sbc7_r sbc7_x0) xinf τ := sorry

end HK
