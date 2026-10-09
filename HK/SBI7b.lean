module

public import HK.Basic

/-!
# The second 7-agent SBI system (Hegarty–Ognissanti–Wedin §5)

`x(0) = (0, 71, 100 − φ, 110, 120 + φ, 149, 220)`, `r = (85, 35, 35, 75, 35, 35, 85)`,
`λ = (1 − √5)/8`; `x(t) = (0, 70, 100, 110, 120, 150, 220) + λᵗ (0, 1, −φ, 0, φ, −1, 0)`. The
neighbourhood table is the same at every `t`, yet agents 1, 2, 4, 5 alternate sides of their limits;
their per-step convergence factor is `λ` at every `t`. Agent 3 sits at its limit. The identities
used are those of `HK/SBI7.lean`.
-/

@[expose] public section

namespace HK

open Filter Topology

theorem sbi7b_r_pos : ∀ i, 0 < sbi7b_r i := sorry

theorem sbi7b_closed_form_internal (t : ℕ) :
    traj .sbi sbi7b_r sbi7b_x0 t = fun i => sbi7b_lim i + sbiRate ^ t * sbi_v i := sorry

theorem sbi7b_neighbors_internal (t : ℕ) :
    neighbors .sbi sbi7b_r (traj .sbi sbi7b_r sbi7b_x0 t) =
      ![{0}, {0, 1, 2, 3}, {1, 2, 3, 4}, {2, 3, 4}, {2, 3, 4, 5}, {3, 4, 5, 6}, {6}] := sorry

theorem sbi7b_tendsto : Tendsto (traj .sbi sbi7b_r sbi7b_x0) atTop (𝓝 sbi7b_lim) := sorry

theorem sbi7b_digraph_constant_internal (t : ℕ) :
    proximityDigraph .sbi sbi7b_r (traj .sbi sbi7b_r sbi7b_x0 t) =
      proximityDigraph .sbi sbi7b_r sbi7b_x0 := sorry

theorem sbi7b_not_fixedFrom (τ : ℕ) : ¬ FixedFrom (traj .sbi sbi7b_r sbi7b_x0) τ := sorry

theorem sbi7b_not_pseudoStableAfter (xinf : Fin 7 → ℝ) (τ : ℕ) :
    ¬ PseudoStableAfter (traj .sbi sbi7b_r sbi7b_x0) xinf τ := sorry

theorem sbi7b_fvct_internal (t : ℕ) :
    fvct .sbi sbi7b_r (traj .sbi sbi7b_r sbi7b_x0 t) = sbi7b_lim := sorry

theorem sbi7b_perStepFactor_internal (t : ℕ) (i : Fin 7)
    (hi : i ∈ ({1, 2, 4, 5} : Finset (Fin 7))) :
    perStepFactor .sbi sbi7b_r (traj .sbi sbi7b_r sbi7b_x0) i t = sbiRate := sorry

theorem sbi7b_perStepFactor_not_tendsto_internal (i : Fin 7)
    (hi : i ∈ ({1, 2, 4, 5} : Finset (Fin 7))) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ¬ Tendsto (fun t => perStepFactor .sbi sbi7b_r (traj .sbi sbi7b_r sbi7b_x0) i t) atTop (𝓝 ρ) :=
  sorry

end HK
