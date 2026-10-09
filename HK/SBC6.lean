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

/-- The SBC-6 table for every offset `-1/6 ≤ u ≤ 1`. -/
theorem sbc6_table (u : ℝ) (h0 : -1 / 6 ≤ u) (h1 : u ≤ 1) :
    neighbors .sbc sbc6_r (fun i => sbc6_lim i + u * sbc6_v i) =
      ![{0}, {0, 1, 2}, {0, 1, 2, 3}, {2, 3, 4, 5}, {3, 4, 5}, {5}] := by
  funext i
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [neighbors, Model.bound, sbc6_r, sbc6_lim, sbc6_v, abs_le] <;>
    (try constructor) <;> (try intro) <;> linarith

theorem sbc6_step (u : ℝ) (h0 : -1 / 6 ≤ u) (h1 : u ≤ 1) :
    step .sbc sbc6_r (fun i => sbc6_lim i + u * sbc6_v i) =
      fun i => sbc6_lim i + (-1 / 6 * u) * sbc6_v i := by
  funext i
  rw [step_apply, sbc6_table u h0 h1]
  fin_cases i <;> simp [Finset.sum_insert, sbc6_lim, sbc6_v] <;> ring

/-- §4: the closed form. -/
theorem sbc6_closed_form_internal (t : ℕ) :
    traj .sbc sbc6_r sbc6_x0 t = fun i => sbc6_lim i + (-1 / 6 : ℝ) ^ t * sbc6_v i := by
  induction t with
  | zero =>
    funext i
    fin_cases i <;> simp [traj, sbc6_x0, sbc6_lim, sbc6_v] <;> norm_num
  | succ t ih =>
    have h : traj .sbc sbc6_r sbc6_x0 (t + 1) = step .sbc sbc6_r (traj .sbc sbc6_r sbc6_x0 t) := by
      simp only [traj]
      exact Function.iterate_succ_apply' _ _ _
    obtain ⟨h0, h1⟩ := pow_bounds t
    rw [h, ih, sbc6_step _ h0 h1]
    funext i; rw [pow_succ]; ring

/-- §4: the neighbourhood table, the same at every `t`. -/
theorem sbc6_neighbors_internal (t : ℕ) :
    neighbors .sbc sbc6_r (traj .sbc sbc6_r sbc6_x0 t) =
      ![{0}, {0, 1, 2}, {0, 1, 2, 3}, {2, 3, 4, 5}, {3, 4, 5}, {5}] := by
  obtain ⟨h0, h1⟩ := pow_bounds t
  rw [sbc6_closed_form_internal, sbc6_table _ h0 h1]

theorem sbc6_closed_form_internal' (t : ℕ) :
    traj .sbc sbc6_r sbc6_x0 t = fun i => sbc6_lim i + (-1 / 6 : ℝ) ^ t * 1 * sbc6_v i := by
  rw [sbc6_closed_form_internal]; funext i; ring

theorem sbc6_r_pos : ∀ i, 0 < sbc6_r i := by
  intro i
  fin_cases i <;> simp [sbc6_r]

theorem sbc6_digraph_constant_internal (t : ℕ) :
    proximityDigraph .sbc sbc6_r (traj .sbc sbc6_r sbc6_x0 t) =
      proximityDigraph .sbc sbc6_r sbc6_x0 := by
  have h0 : traj .sbc sbc6_r sbc6_x0 0 = sbc6_x0 := rfl
  have := sbc6_neighbors_internal 0
  rw [h0] at this
  simp only [proximityDigraph, sbc6_neighbors_internal, this]

theorem sbc6_adj_lim (t : ℕ) :
    (adjMatrix .sbc sbc6_r (traj .sbc sbc6_r sbc6_x0 t)).mulVec sbc6_lim = sbc6_lim := by
  funext i
  rw [adj_mulVec, sbc6_neighbors_internal]
  fin_cases i <;> simp [Finset.sum_insert, sbc6_lim] <;> norm_num

theorem sbc6_adj_v (t : ℕ) :
    (adjMatrix .sbc sbc6_r (traj .sbc sbc6_r sbc6_x0 t)).mulVec sbc6_v = (-1 / 6 : ℝ) • sbc6_v := by
  funext i
  rw [adj_mulVec, sbc6_neighbors_internal]
  fin_cases i <;> simp [Finset.sum_insert, sbc6_v] <;> norm_num

theorem sbc6_adj_pow (t k : ℕ) (c : ℝ) :
    (adjMatrix .sbc sbc6_r (traj .sbc sbc6_r sbc6_x0 t) ^ k).mulVec (sbc6_lim + c • sbc6_v) =
      sbc6_lim + ((-1 / 6 : ℝ) ^ k * c) • sbc6_v := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_add, Matrix.mulVec_smul,
      sbc6_adj_lim, sbc6_adj_v, smul_smul, pow_succ]
    congr 2
    ring

theorem sbc6_fvct_internal (t : ℕ) : fvct .sbc sbc6_r (traj .sbc sbc6_r sbc6_x0 t) = sbc6_lim := by
  have hx : traj .sbc sbc6_r sbc6_x0 t = sbc6_lim + ((-1 / 6 : ℝ) ^ t) • sbc6_v := by
    rw [sbc6_closed_form_internal]; funext i; simp
  have hq : |(-1 / 6 : ℝ)| < 1 := by rw [abs_of_neg (by norm_num)]; norm_num
  have h1 : Tendsto (fun k : ℕ => sbc6_lim + ((-1 / 6 : ℝ) ^ k * (-1 / 6 : ℝ) ^ t) • sbc6_v)
      atTop (𝓝 sbc6_lim) := by
    have h0 := ((tendsto_pow_atTop_nhds_zero_of_abs_lt_one hq).mul_const
      ((-1 / 6 : ℝ) ^ t)).smul_const sbc6_v
    have h2 := h0.const_add sbc6_lim
    rwa [zero_mul, zero_smul, add_zero] at h2
  have hA := sbc6_adj_pow t
  unfold fvct
  set A := adjMatrix .sbc sbc6_r (traj .sbc sbc6_r sbc6_x0 t) with hAdef
  have hf : (fun k : ℕ => (A ^ k).mulVec (traj .sbc sbc6_r sbc6_x0 t)) =
      fun k => sbc6_lim + ((-1 / 6 : ℝ) ^ k * (-1 / 6 : ℝ) ^ t) • sbc6_v := by
    funext k; rw [hx, hA]
  rw [hf]
  exact h1.limUnder_eq

theorem sbc6_perStepFactor_internal (t : ℕ) (i : Fin 6) (hi : i ∈ ({1, 2, 3, 4} : Finset (Fin 6))) :
    perStepFactor .sbc sbc6_r (traj .sbc sbc6_r sbc6_x0) i t = -1 / 6 := by
  have hv : sbc6_v i ≠ 0 := by
    fin_cases i <;> simp_all [sbc6_v]
  have hp : (-1 / 6 : ℝ) ^ t ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [perStepFactor, sbc6_fvct_internal, sbc6_closed_form_internal, sbc6_closed_form_internal]
  simp only [add_sub_cancel_left, pow_succ]
  field_simp

theorem sbc6_perStepFactor_not_tendsto_internal (i : Fin 6) (hi : i ∈ ({1, 2, 3, 4} : Finset (Fin 6)))
    (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ¬ Tendsto (fun t => perStepFactor .sbc sbc6_r (traj .sbc sbc6_r sbc6_x0) i t) atTop (𝓝 ρ) := by
  intro h
  simp only [sbc6_perStepFactor_internal _ i hi] at h
  have := tendsto_nhds_unique h tendsto_const_nhds
  linarith

end HK
