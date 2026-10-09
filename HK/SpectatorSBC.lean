module

public import HK.Basic

/-!
# The 9-agent SBC spectator system (Hegarty–Ognissanti–Wedin §4), a stretch

The six agents of §4 with a spectator at `210` (`r = 100`) and two beacons at `280` and `300`
(`r = 10`); for all `t`, agents 0–5 evolve as in §4, the beacons are fixed, and the spectator (index 6)
satisfies `x₆(t) = 210 + (12/11) ((−1/6)ᵗ − (1/5)ᵗ)`, so it is strictly left of `210` for every
`t ≥ 1`; the neighbourhood table is the same at every `t`. Two atoms: `u = (−1/6)ᵗ ∈ [−1/6, 1]` and
`w = (1/5)ᵗ ∈ (0, 1]`; the table holds on the closed box `|u| ≤ 1`, `0 ≤ w ≤ 1` with no parity split.
If these close, the desk lifts the data and the theorems into the Challenge.
-/

@[expose] public section

namespace HK

open Filter Topology

/-- §4 with the spectator and the beacons: the initial opinions. -/
noncomputable def sbc9_x0 : Fin 9 → ℝ := ![0, 22, 37, 103, 118, 140, 210, 280, 300]
/-- §4 with the spectator and the beacons: the confidence bounds. -/
noncomputable def sbc9_r : Fin 9 → ℝ := ![10, 70, 70, 70, 70, 10, 100, 10, 10]

theorem sbc9_closed_form (t : ℕ) :
    traj .sbc sbc9_r sbc9_x0 t =
      ![0, 20 + 2 * (-1 / 6 : ℝ) ^ t, 40 - 3 * (-1 / 6 : ℝ) ^ t, 100 + 3 * (-1 / 6 : ℝ) ^ t,
        120 - 2 * (-1 / 6 : ℝ) ^ t, 140, 210 + 12 / 11 * ((-1 / 6 : ℝ) ^ t - (1 / 5 : ℝ) ^ t),
        280, 300] := sorry

theorem sbc9_neighbors (t : ℕ) :
    neighbors .sbc sbc9_r (traj .sbc sbc9_r sbc9_x0 t) =
      ![{0}, {0, 1, 2}, {0, 1, 2, 3}, {2, 3, 4, 5}, {3, 4, 5}, {5}, {4, 5, 6, 7, 8}, {7}, {8}] :=
  sorry

theorem sbc9_spectator_lt (t : ℕ) (ht : 1 ≤ t) : traj .sbc sbc9_r sbc9_x0 t 6 < 210 := sorry

end HK
