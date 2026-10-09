module

public import HK.Basic

/-!
# The 8-agent SBI spectator system (Hegarty–Ognissanti–Wedin §5), a stretch

The seven agents of §5 with a spectator at `60` (`r = 1`), which becomes index 1 when the opinions
are listed increasingly; for all `t` the other agents evolve as in §5 and
`x₁(t) = 60 + φ⁻¹ ((1/4)ᵗ − λᵗ)`, so it is strictly right of `60` for every `t ≥ 1`; the
neighbourhood table is the same at every `t`. Two atoms: `u = λᵗ ∈ [λ, 1]` and `w = (1/4)ᵗ ∈ (0, 1]`;
the table holds on the closed box `|u| ≤ 1`, `0 ≤ w ≤ 1` with no parity split (the product atom
`u φ` needs its own bounds, as in `HK/SBI7.lean`).
-/

@[expose] public section

namespace HK

open Filter Topology

/-- §5 with the spectator: the initial opinions, listed increasingly. -/
noncomputable def sbi8_x0 : Fin 8 → ℝ :=
  ![0, 60, 71, 100 - Real.goldenRatio, 110, 120 + Real.goldenRatio, 149, 220]
/-- §5 with the spectator: the influence bounds. -/
noncomputable def sbi8_r : Fin 8 → ℝ := ![85, 1, 35, 35, 75, 35, 35, 85]

/-- The state on the box: `u = λᵗ`, `w = (1/4)ᵗ`. -/
noncomputable def spe_x (u w : ℝ) : Fin 8 → ℝ :=
  ![0, 60 + (Real.goldenRatio - 1) * (w - u), 70 + u, 100 - Real.goldenRatio * u, 110,
    120 + Real.goldenRatio * u, 150 - u, 220]

theorem spe_inv : Real.goldenRatio⁻¹ = Real.goldenRatio - 1 :=
  inv_eq_of_mul_eq_one_right (by linear_combination Real.goldenRatio_sq)

/-- The table on the closed box `(1 − φ)/4 ≤ u ≤ 1`, `0 ≤ w ≤ 1`. -/
theorem spe_table (u w : ℝ) (hu0 : (1 - Real.goldenRatio) / 4 ≤ u) (hu1 : u ≤ 1)
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    neighbors .sbi sbi8_r (spe_x u w) =
      ![{0}, {0, 1, 2, 4}, {0, 2, 3, 4}, {2, 3, 4, 5}, {3, 4, 5}, {3, 4, 5, 6}, {4, 5, 6, 7}, {7}] := by
  have hφ1 := Real.one_lt_goldenRatio
  have hφ2 := Real.goldenRatio_lt_two
  have hsq := Real.goldenRatio_sq
  have hφ0 : 0 ≤ Real.goldenRatio := by linarith
  have hm0 := mul_le_mul_of_nonneg_right hu0 hφ0
  have hm1 := mul_le_mul_of_nonneg_right hu1 hφ0
  have hp0 : -1 / 4 ≤ u * Real.goldenRatio := by nlinarith
  have hp1 : u * Real.goldenRatio ≤ 2 := by nlinarith
  have hq0 : 0 ≤ w * Real.goldenRatio := mul_nonneg hw0 hφ0
  have hq1 : w * Real.goldenRatio ≤ 2 := by nlinarith
  funext i
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [neighbors, Model.bound, sbi8_r, spe_x, abs_le] <;>
    (try constructor) <;> (try intro) <;> linarith

theorem spe_step (u w : ℝ) (hu0 : (1 - Real.goldenRatio) / 4 ≤ u) (hu1 : u ≤ 1)
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    step .sbi sbi8_r (spe_x u w) = spe_x (u * sbiRate) (w * (1 / 4)) := by
  have hsq := Real.goldenRatio_sq
  funext i
  rw [step_apply, spe_table u w hu0 hu1 hw0 hw1, sbiRate_eq]
  fin_cases i
  · simp [spe_x]
  · simp [Finset.sum_insert, spe_x]; linear_combination (-u / 4) * hsq
  · simp [Finset.sum_insert, spe_x]; ring
  · simp [Finset.sum_insert, spe_x]; linear_combination (-u / 4) * hsq
  · simp [Finset.sum_insert, spe_x]; ring
  · simp [Finset.sum_insert, spe_x]; linear_combination (u / 4) * hsq
  · simp [Finset.sum_insert, spe_x]; ring
  · simp [spe_x]

theorem spe_closed (t : ℕ) :
    traj .sbi sbi8_r sbi8_x0 t = spe_x (sbiRate ^ t) ((1 / 4 : ℝ) ^ t) := by
  induction t with
  | zero =>
    funext i
    fin_cases i <;> simp [traj, sbi8_x0, spe_x] <;> ring
  | succ t ih =>
    have h : traj .sbi sbi8_r sbi8_x0 (t + 1) =
        step .sbi sbi8_r (traj .sbi sbi8_r sbi8_x0 t) := by
      simp only [traj]
      exact Function.iterate_succ_apply' _ _ _
    obtain ⟨h0, h1⟩ := sbiRate_pow_bounds t
    have hw0 : 0 ≤ (1 / 4 : ℝ) ^ t := pow_nonneg (by norm_num) t
    have hw1 : (1 / 4 : ℝ) ^ t ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    rw [h, ih, spe_step _ _ h0 h1 hw0 hw1, pow_succ, pow_succ]

theorem sbi8_closed_form (t : ℕ) :
    traj .sbi sbi8_r sbi8_x0 t =
      ![0, 60 + Real.goldenRatio⁻¹ * ((1 / 4 : ℝ) ^ t - sbiRate ^ t), 70 + sbiRate ^ t,
        100 - Real.goldenRatio * sbiRate ^ t, 110, 120 + Real.goldenRatio * sbiRate ^ t,
        150 - sbiRate ^ t, 220] := by
  rw [spe_closed, spe_inv]; rfl

theorem sbi8_neighbors (t : ℕ) :
    neighbors .sbi sbi8_r (traj .sbi sbi8_r sbi8_x0 t) =
      ![{0}, {0, 1, 2, 4}, {0, 2, 3, 4}, {2, 3, 4, 5}, {3, 4, 5}, {3, 4, 5, 6}, {4, 5, 6, 7}, {7}] := by
  obtain ⟨h0, h1⟩ := sbiRate_pow_bounds t
  have hw0 : 0 ≤ (1 / 4 : ℝ) ^ t := pow_nonneg (by norm_num) t
  have hw1 : (1 / 4 : ℝ) ^ t ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  rw [spe_closed, spe_table _ _ h0 h1 hw0 hw1]

theorem spe_abs_rate : |sbiRate| < 1 / 4 := by
  have hφ1 := Real.one_lt_goldenRatio
  have hφ2 := Real.goldenRatio_lt_two
  rw [abs_lt, sbiRate_eq]
  constructor <;> linarith

theorem sbi8_spectator_gt (t : ℕ) (ht : 1 ≤ t) : 60 < traj .sbi sbi8_r sbi8_x0 t 1 := by
  rw [spe_closed]
  have h0 : spe_x (sbiRate ^ t) ((1 / 4 : ℝ) ^ t) 1 =
      60 + (Real.goldenRatio - 1) * ((1 / 4 : ℝ) ^ t - sbiRate ^ t) := rfl
  rw [h0, ← spe_inv]
  have h1 : |sbiRate| ^ t < (1 / 4 : ℝ) ^ t :=
    pow_lt_pow_left₀ spe_abs_rate (abs_nonneg _) (by omega)
  have h2 : sbiRate ^ t ≤ |sbiRate| ^ t := by
    rw [← abs_pow]; exact le_abs_self _
  have h3 : 0 < Real.goldenRatio⁻¹ := inv_pos.mpr Real.goldenRatio_pos
  have h4 : 0 < (1 / 4 : ℝ) ^ t - sbiRate ^ t := by linarith
  have := mul_pos h3 h4
  linarith

end HK
