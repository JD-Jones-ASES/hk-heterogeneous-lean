module

public import HK.Basic

/-!
# The second 7-agent SBI system (Hegarty–Ognissanti–Wedin §5)

`x(0) = (0, 71, 100 − φ, 110, 120 + φ, 149, 220)`, `r = (85, 35, 35, 75, 35, 35, 85)`,
`λ = (1 − √5)/8`; `x(t) = (0, 70, 100, 110, 120, 150, 220) + λᵗ (0, 1, −φ, 0, φ, −1, 0)`. The
neighbourhood table is the same at every `t`, yet agents 1, 2, 4, 5 alternate sides of their limits;
their per-step convergence factor is `λ` at every `t`. Index 3 (the paper's agent 4) sits at its
limit.
-/

@[expose] public section

namespace HK

open Filter Topology

/-- The SBI-7b table for every offset `(1 − φ)/4 ≤ w ≤ 1`. -/
theorem sbi7b_table (w : ℝ) (hw0 : (1 - Real.goldenRatio) / 4 ≤ w) (hw1 : w ≤ 1) :
    neighbors .sbi sbi7b_r (fun i => sbi7b_lim i + w * sbi_v i) =
      ![{0}, {0, 1, 2, 3}, {1, 2, 3, 4}, {2, 3, 4}, {2, 3, 4, 5}, {3, 4, 5, 6}, {6}] := by
  have hφ1 := Real.one_lt_goldenRatio
  have hφ2 := Real.goldenRatio_lt_two
  have hsq := Real.goldenRatio_sq
  have hφ0 : 0 ≤ Real.goldenRatio := by linarith
  have hm0 := mul_le_mul_of_nonneg_right hw0 hφ0
  have hm1 := mul_le_mul_of_nonneg_right hw1 hφ0
  have hp0 : -1 / 4 ≤ w * Real.goldenRatio := by nlinarith
  have hp1 : w * Real.goldenRatio ≤ 2 := by nlinarith
  funext i
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [neighbors, Model.bound, sbi7b_r, sbi7b_lim, sbi_v, abs_le] <;>
    (try constructor) <;> (try intro) <;> linarith

theorem sbi7b_step (w : ℝ) (hw0 : (1 - Real.goldenRatio) / 4 ≤ w) (hw1 : w ≤ 1) :
    step .sbi sbi7b_r (fun i => sbi7b_lim i + w * sbi_v i) =
      fun i => sbi7b_lim i + ((1 - Real.goldenRatio) / 4 * w) * sbi_v i := by
  have hsq := Real.goldenRatio_sq
  funext i
  rw [step_apply, sbi7b_table w hw0 hw1]
  fin_cases i
  · simp [sbi7b_lim, sbi_v]
  · simp [Finset.sum_insert, sbi7b_lim, sbi_v]; ring
  · simp [Finset.sum_insert, sbi7b_lim, sbi_v]; linear_combination (-w / 4) * hsq
  · simp [Finset.sum_insert, sbi7b_lim, sbi_v]; ring
  · simp [Finset.sum_insert, sbi7b_lim, sbi_v]; linear_combination (w / 4) * hsq
  · simp [Finset.sum_insert, sbi7b_lim, sbi_v]; ring
  · simp [sbi7b_lim, sbi_v]

/-- §5: the closed form. -/
theorem sbi7b_closed_form_internal (t : ℕ) :
    traj .sbi sbi7b_r sbi7b_x0 t = fun i => sbi7b_lim i + sbiRate ^ t * sbi_v i := by
  induction t with
  | zero =>
    funext i
    fin_cases i <;> simp [traj, sbi7b_x0, sbi7b_lim, sbi_v] <;> ring
  | succ t ih =>
    have h : traj .sbi sbi7b_r sbi7b_x0 (t + 1) =
        step .sbi sbi7b_r (traj .sbi sbi7b_r sbi7b_x0 t) := by
      simp only [traj]
      exact Function.iterate_succ_apply' _ _ _
    obtain ⟨h0, h1⟩ := sbiRate_pow_bounds t
    rw [h, ih, sbi7b_step _ h0 h1]
    funext i; rw [pow_succ, sbiRate_eq]; ring

/-- §5: the neighbourhood table, the same at every `t`. -/
theorem sbi7b_neighbors_internal (t : ℕ) :
    neighbors .sbi sbi7b_r (traj .sbi sbi7b_r sbi7b_x0 t) =
      ![{0}, {0, 1, 2, 3}, {1, 2, 3, 4}, {2, 3, 4}, {2, 3, 4, 5}, {3, 4, 5, 6}, {6}] := by
  obtain ⟨h0, h1⟩ := sbiRate_pow_bounds t
  rw [sbi7b_closed_form_internal, sbi7b_table _ h0 h1]

theorem sbi7b_closed_form_internal' (t : ℕ) :
    traj .sbi sbi7b_r sbi7b_x0 t = fun i => sbi7b_lim i + sbiRate ^ t * 1 * sbi_v i := by
  rw [sbi7b_closed_form_internal]; funext i; ring

theorem sbi7b_r_pos : ∀ i, 0 < sbi7b_r i := by
  intro i
  fin_cases i <;> simp [sbi7b_r]

theorem sbi7b_adj_lim (t : ℕ) :
    (adjMatrix .sbi sbi7b_r (traj .sbi sbi7b_r sbi7b_x0 t)).mulVec sbi7b_lim = sbi7b_lim := by
  funext i
  rw [adj_mulVec, sbi7b_neighbors_internal]
  fin_cases i <;> simp [Finset.sum_insert, sbi7b_lim] <;> norm_num

theorem sbi7b_adj_v (t : ℕ) :
    (adjMatrix .sbi sbi7b_r (traj .sbi sbi7b_r sbi7b_x0 t)).mulVec sbi_v = sbiRate • sbi_v := by
  have hsq := Real.goldenRatio_sq
  funext i
  rw [adj_mulVec, sbi7b_neighbors_internal, sbiRate_eq]
  fin_cases i
  · simp [sbi_v]
  · simp [Finset.sum_insert, sbi_v]; ring
  · simp [Finset.sum_insert, sbi_v]; linear_combination (-1 / 4 : ℝ) * hsq
  · simp [Finset.sum_insert, sbi_v]
  · simp [Finset.sum_insert, sbi_v]; linear_combination (1 / 4 : ℝ) * hsq
  · simp [Finset.sum_insert, sbi_v]; ring
  · simp [sbi_v]

theorem sbi7b_adj_pow (t k : ℕ) (c : ℝ) :
    (adjMatrix .sbi sbi7b_r (traj .sbi sbi7b_r sbi7b_x0 t) ^ k).mulVec (sbi7b_lim + c • sbi_v) =
      sbi7b_lim + (sbiRate ^ k * c) • sbi_v := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_add, Matrix.mulVec_smul,
      sbi7b_adj_lim, sbi7b_adj_v, smul_smul, pow_succ]
    congr 2
    ring

theorem sbi7b_fvct_internal (t : ℕ) : fvct .sbi sbi7b_r (traj .sbi sbi7b_r sbi7b_x0 t) = sbi7b_lim := by
  have hx : traj .sbi sbi7b_r sbi7b_x0 t = sbi7b_lim + (sbiRate ^ t) • sbi_v := by
    rw [sbi7b_closed_form_internal]; funext i; simp
  have h1 : Tendsto (fun k : ℕ => sbi7b_lim + (sbiRate ^ k * sbiRate ^ t) • sbi_v)
      atTop (𝓝 sbi7b_lim) := by
    have h0 := ((tendsto_pow_atTop_nhds_zero_of_abs_lt_one sbiRate_abs_lt_one).mul_const
      (sbiRate ^ t)).smul_const sbi_v
    have h2 := h0.const_add sbi7b_lim
    rwa [zero_mul, zero_smul, add_zero] at h2
  have hA := sbi7b_adj_pow t
  unfold fvct
  set A := adjMatrix .sbi sbi7b_r (traj .sbi sbi7b_r sbi7b_x0 t) with hAdef
  have hf : (fun k : ℕ => (A ^ k).mulVec (traj .sbi sbi7b_r sbi7b_x0 t)) =
      fun k => sbi7b_lim + (sbiRate ^ k * sbiRate ^ t) • sbi_v := by
    funext k; rw [hx, hA]
  rw [hf]
  exact h1.limUnder_eq

theorem sbi7b_perStepFactor_internal (t : ℕ) (i : Fin 7) (hi : i ∈ ({1, 2, 4, 5} : Finset (Fin 7))) :
    perStepFactor .sbi sbi7b_r (traj .sbi sbi7b_r sbi7b_x0) i t = sbiRate := by
  have hv : sbi_v i ≠ 0 := by
    have := Real.goldenRatio_pos.ne'
    fin_cases i <;> simp_all [sbi_v]
  have hp : sbiRate ^ t ≠ 0 := pow_ne_zero _ sbiRate_neg.ne
  rw [perStepFactor, sbi7b_fvct_internal, sbi7b_closed_form_internal, sbi7b_closed_form_internal]
  simp only [add_sub_cancel_left, pow_succ]
  field_simp

theorem sbi7b_perStepFactor_not_tendsto_internal (i : Fin 7) (hi : i ∈ ({1, 2, 4, 5} : Finset (Fin 7)))
    (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ¬ Tendsto (fun t => perStepFactor .sbi sbi7b_r (traj .sbi sbi7b_r sbi7b_x0) i t) atTop
      (𝓝 ρ) := by
  intro h
  simp only [sbi7b_perStepFactor_internal _ i hi] at h
  have := tendsto_nhds_unique h tendsto_const_nhds
  linarith [sbiRate_neg]

theorem sbi7b_digraph_constant_internal (t : ℕ) :
    proximityDigraph .sbi sbi7b_r (traj .sbi sbi7b_r sbi7b_x0 t) =
      proximityDigraph .sbi sbi7b_r sbi7b_x0 := by
  have h0 : traj .sbi sbi7b_r sbi7b_x0 0 = sbi7b_x0 := rfl
  have := sbi7b_neighbors_internal 0
  rw [h0] at this
  simp only [proximityDigraph, sbi7b_neighbors_internal, this]

end HK
