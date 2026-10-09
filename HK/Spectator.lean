module

public import HK.Basic

/-!
# The two spectator systems (Hegarty–Ognissanti–Wedin §4 and §5), a stretch

The 9-agent SBC system: the six agents of §4 with a spectator at `210` (`r = 100`) and two beacons
at `280` and `300` (`r = 10`); for all `t`, agents 0–5 evolve as in §4, the beacons are fixed, and
the spectator (index 6) satisfies `x₆(t) = 210 + (12/11) ((−1/6)ᵗ − (1/5)ᵗ)`, so it is strictly
left of `210` for every `t ≥ 1`; the neighbourhood table is the same at every `t`.

The 8-agent SBI system: the seven agents of §5 with a spectator at `60` (`r = 1`), which becomes
index 1 when the opinions are listed increasingly; for all `t` the other agents evolve as in §5 and
`x₁(t) = 60 + φ⁻¹ ((1/4)ᵗ − λᵗ)`, so it is strictly right of `60` for every `t ≥ 1`; the
neighbourhood table is the same at every `t`.

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
