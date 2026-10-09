module

public import HK.Basic

/-!
# The 6-agent SBC system (Hegarty–Ognissanti–Wedin §4)

`x(0) = (0, 22, 37, 103, 118, 140)`, `r = (10, 70, 70, 70, 70, 10)`;
`x(t) = (0, 20, 40, 100, 120, 140) + (−1/6)ᵗ (0, 2, −3, 3, −2, 0)`. The neighbourhood table is the
same at every `t` (so the proximity digraph is constant), yet agents 1–4 alternate sides of their
limits; their per-step convergence factor (Definition 6.1, with the final value at constant topology
of Definition 3.1 equal to the limit) is `−1/6` at every `t`.
-/

@[expose] public section

namespace HK

open Filter Topology

theorem sbc6_r_pos : ∀ i, 0 < sbc6_r i := sorry

theorem sbc6_closed_form_internal (t : ℕ) :
    traj .sbc sbc6_r sbc6_x0 t = fun i => sbc6_lim i + (-1 / 6 : ℝ) ^ t * sbc6_v i := sorry

theorem sbc6_neighbors_internal (t : ℕ) :
    neighbors .sbc sbc6_r (traj .sbc sbc6_r sbc6_x0 t) =
      ![{0}, {0, 1, 2}, {0, 1, 2, 3}, {2, 3, 4, 5}, {3, 4, 5}, {5}] := sorry

theorem sbc6_tendsto : Tendsto (traj .sbc sbc6_r sbc6_x0) atTop (𝓝 sbc6_lim) := sorry

theorem sbc6_digraph_constant_internal (t : ℕ) :
    proximityDigraph .sbc sbc6_r (traj .sbc sbc6_r sbc6_x0 t) =
      proximityDigraph .sbc sbc6_r sbc6_x0 := sorry

theorem sbc6_not_fixedFrom (τ : ℕ) : ¬ FixedFrom (traj .sbc sbc6_r sbc6_x0) τ := sorry

theorem sbc6_not_pseudoStableAfter (yinf : Fin 6 → ℝ) (τ : ℕ) :
    ¬ PseudoStableAfter (traj .sbc sbc6_r sbc6_x0) yinf τ := sorry

theorem sbc6_fvct_internal (t : ℕ) :
    fvct .sbc sbc6_r (traj .sbc sbc6_r sbc6_x0 t) = sbc6_lim := sorry

theorem sbc6_perStepFactor_internal (t : ℕ) (i : Fin 6) (hi : i ∈ ({1, 2, 3, 4} : Finset (Fin 6))) :
    perStepFactor .sbc sbc6_r (traj .sbc sbc6_r sbc6_x0) i t = -1 / 6 := sorry

theorem sbc6_perStepFactor_not_tendsto_internal (i : Fin 6)
    (hi : i ∈ ({1, 2, 3, 4} : Finset (Fin 6))) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ¬ Tendsto (fun t => perStepFactor .sbc sbc6_r (traj .sbc sbc6_r sbc6_x0) i t) atTop (𝓝 ρ) :=
  sorry

end HK
