module

public import HK.Basic

/-!
# The 9-agent SBC spectator system (Hegarty–Ognissanti–Wedin §4)

The six agents of §4 with a spectator at `210` (`r = 100`) and two beacons at `280` and `300`
(`r = 10`); for all `t`, agents 0–5 evolve as in §4, the beacons are fixed, and the spectator (index 6)
satisfies `x₆(t) = 210 + (12/11) ((−1/6)ᵗ − (1/5)ᵗ)`, so it is strictly left of `210` for every
`t ≥ 1`; the neighbourhood table is the same at every `t`. Two atoms: `u = (−1/6)ᵗ ∈ [−1/6, 1]` and
`w = (1/5)ᵗ ∈ (0, 1]`; the table holds on the closed box `|u| ≤ 1`, `0 ≤ w ≤ 1` with no parity split.
-/

@[expose] public section

namespace HK

open Filter Topology


/-- The SBC-9 opinion vector at the atoms `u` (the `(−1/6)ᵗ` offset) and `w` (the `(1/5)ᵗ` offset). -/
noncomputable def spe_sbc9_vec (u w : ℝ) : Fin 9 → ℝ :=
  ![0, 20 + 2 * u, 40 - 3 * u, 100 + 3 * u, 120 - 2 * u, 140, 210 + 12 / 11 * (u - w), 280, 300]

/-- The SBC-9 table on the box `-1/6 ≤ u ≤ 1`, `0 ≤ w ≤ 1`. -/
theorem spe_sbc9_table (u w : ℝ) (h0 : -1 / 6 ≤ u) (h1 : u ≤ 1) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    neighbors .sbc sbc9_r (spe_sbc9_vec u w) =
      ![{0}, {0, 1, 2}, {0, 1, 2, 3}, {2, 3, 4, 5}, {3, 4, 5}, {5}, {4, 5, 6, 7, 8}, {7}, {8}] := by
  funext i
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [neighbors, Model.bound, sbc9_r, spe_sbc9_vec, abs_le] <;>
    (try constructor) <;> (try intro) <;> linarith

theorem spe_sbc9_step (u w : ℝ) (h0 : -1 / 6 ≤ u) (h1 : u ≤ 1) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    step .sbc sbc9_r (spe_sbc9_vec u w) = spe_sbc9_vec (-1 / 6 * u) (1 / 5 * w) := by
  funext i
  rw [step_apply, spe_sbc9_table u w h0 h1 hw0 hw1]
  fin_cases i <;> simp [Finset.sum_insert, spe_sbc9_vec] <;> ring

theorem spe_sbc9_traj (t : ℕ) :
    traj .sbc sbc9_r sbc9_x0 t = spe_sbc9_vec ((-1 / 6 : ℝ) ^ t) ((1 / 5 : ℝ) ^ t) := by
  induction t with
  | zero =>
    funext i
    fin_cases i <;> simp [traj, sbc9_x0, spe_sbc9_vec] <;> norm_num
  | succ t ih =>
    have h : traj .sbc sbc9_r sbc9_x0 (t + 1) = step .sbc sbc9_r (traj .sbc sbc9_r sbc9_x0 t) := by
      simp only [traj]
      exact Function.iterate_succ_apply' _ _ _
    obtain ⟨h0, h1⟩ := pow_bounds t
    have hw0 : (0 : ℝ) ≤ (1 / 5 : ℝ) ^ t := pow_nonneg (by norm_num) t
    have hw1 : (1 / 5 : ℝ) ^ t ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    rw [h, ih, spe_sbc9_step _ _ h0 h1 hw0 hw1, pow_succ, pow_succ, mul_comm _ (-1 / 6 : ℝ),
      mul_comm _ (1 / 5 : ℝ)]

theorem sbc9_closed_form_internal (t : ℕ) :
    traj .sbc sbc9_r sbc9_x0 t =
      ![0, 20 + 2 * (-1 / 6 : ℝ) ^ t, 40 - 3 * (-1 / 6 : ℝ) ^ t, 100 + 3 * (-1 / 6 : ℝ) ^ t,
        120 - 2 * (-1 / 6 : ℝ) ^ t, 140, 210 + 12 / 11 * ((-1 / 6 : ℝ) ^ t - (1 / 5 : ℝ) ^ t),
        280, 300] := by
  rw [spe_sbc9_traj]
  rfl

theorem sbc9_neighbors_internal (t : ℕ) :
    neighbors .sbc sbc9_r (traj .sbc sbc9_r sbc9_x0 t) =
      ![{0}, {0, 1, 2}, {0, 1, 2, 3}, {2, 3, 4, 5}, {3, 4, 5}, {5}, {4, 5, 6, 7, 8}, {7}, {8}] := by
  obtain ⟨h0, h1⟩ := pow_bounds t
  rw [spe_sbc9_traj, spe_sbc9_table _ _ h0 h1 (pow_nonneg (by norm_num) t)
    (pow_le_one₀ (by norm_num) (by norm_num))]

theorem sbc9_spectator_lt_internal (t : ℕ) (ht : 1 ≤ t) : traj .sbc sbc9_r sbc9_x0 t 6 < 210 := by
  have ht0 : t ≠ 0 := by omega
  have habs : |(-1 / 6 : ℝ) ^ t| < (1 / 5 : ℝ) ^ t := by
    rw [abs_pow, abs_of_neg (by norm_num : (-1 / 6 : ℝ) < 0)]
    exact pow_lt_pow_left₀ (by norm_num) (by norm_num) ht0
  have hle := le_abs_self ((-1 / 6 : ℝ) ^ t)
  have h6 : spe_sbc9_vec ((-1 / 6 : ℝ) ^ t) ((1 / 5 : ℝ) ^ t) 6 =
      210 + 12 / 11 * ((-1 / 6 : ℝ) ^ t - (1 / 5 : ℝ) ^ t) := rfl
  rw [spe_sbc9_traj, h6]
  linarith

end HK
