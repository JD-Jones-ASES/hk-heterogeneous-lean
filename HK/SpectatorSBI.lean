module

public import HK.Basic

/-!
# The 8-agent SBI spectator system (Hegarty–Ognissanti–Wedin §5), a stretch

The seven agents of §5 with a spectator at `60` (`r = 1`), which becomes index 1 when the opinions
are listed increasingly; for all `t` the other agents evolve as in §5 and
`x₁(t) = 60 + φ⁻¹ ((1/4)ᵗ − λᵗ)`, so it is strictly right of `60` for every `t ≥ 1`; the
neighbourhood table is the same at every `t`. Two atoms: `u = λᵗ ∈ [λ, 1]` and `w = (1/4)ᵗ ∈ (0, 1]`;
the table holds on the closed box `|u| ≤ 1`, `0 ≤ w ≤ 1` with no parity split (the product atom
`u φ` needs its own bounds, as in `HK/SBI7.lean`). If these close, the desk lifts the data and the
theorems into the Challenge.
-/

@[expose] public section

namespace HK

open Filter Topology

/-- §5 with the spectator: the initial opinions, listed increasingly. -/
noncomputable def sbi8_x0 : Fin 8 → ℝ :=
  ![0, 60, 71, 100 - Real.goldenRatio, 110, 120 + Real.goldenRatio, 149, 220]
/-- §5 with the spectator: the influence bounds. -/
noncomputable def sbi8_r : Fin 8 → ℝ := ![85, 1, 35, 35, 75, 35, 35, 85]

theorem sbi8_closed_form (t : ℕ) :
    traj .sbi sbi8_r sbi8_x0 t =
      ![0, 60 + Real.goldenRatio⁻¹ * ((1 / 4 : ℝ) ^ t - sbiRate ^ t), 70 + sbiRate ^ t,
        100 - Real.goldenRatio * sbiRate ^ t, 110, 120 + Real.goldenRatio * sbiRate ^ t,
        150 - sbiRate ^ t, 220] := sorry

theorem sbi8_neighbors (t : ℕ) :
    neighbors .sbi sbi8_r (traj .sbi sbi8_r sbi8_x0 t) =
      ![{0}, {0, 1, 2, 4}, {0, 2, 3, 4}, {2, 3, 4, 5}, {3, 4, 5}, {3, 4, 5, 6}, {4, 5, 6, 7}, {7}] :=
  sorry

theorem sbi8_spectator_gt (t : ℕ) (ht : 1 ≤ t) : 60 < traj .sbi sbi8_r sbi8_x0 t 1 := sorry

end HK
