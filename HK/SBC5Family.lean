module

public import HK.SBC5

/-!
# Perpetual SBC oscillation with arbitrarily small radius spread

For `0 < δ ≤ 1`, the five-agent system has initial state `sbc5_lim + δ • sbc5_v`
and radii `(6-3δ, 6+3δ, 6+3δ, 6+3δ, 6-3δ)`. Its constant neighborhood table is
the same as that of `sbc5_x0`, and its offset at time `t` is `sbc5Rate^t * δ • sbc5_v`.
Thus the radius ratio can be arbitrarily close to one while the three interior agents
continue crossing their limits forever.
-/

@[expose] public section

namespace HK

open Filter Topology

theorem sbc5Family_r_pos (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    ∀ i, 0 < sbc5Family_r δ i := by
  intro i
  fin_cases i <;> simp [sbc5Family_r] <;> linarith

/-- The family is genuinely heterogeneous whenever the amplitude is positive. -/
theorem sbc5Family_r_strict (δ : ℝ) (hδ0 : 0 < δ) :
    sbc5Family_r δ 0 < sbc5Family_r δ 1 := by
  simp only [sbc5Family_r, Matrix.cons_val_zero, Matrix.cons_val_one]
  linarith

/-- The fixed table holds throughout the whole interval `-δ ≤ u ≤ δ`. -/
theorem sbc5Family_table (δ u : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hu0 : -δ ≤ u) (hu1 : u ≤ δ) :
    neighbors .sbc (sbc5Family_r δ) (fun i => sbc5_lim i + u * sbc5_v i) =
      ![{0}, {0, 1, 2}, {1, 2, 3}, {2, 3, 4}, {4}] := by
  obtain ⟨hs1, hs2⟩ := sbc_sqrt_two_bounds
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hmul0 := mul_le_mul_of_nonneg_right hu0 hs0
  have hmul1 := mul_le_mul_of_nonneg_right hu1 hs0
  have hδs := mul_le_mul_of_nonneg_left hs2.le hδ0.le
  have hp0 : -(3 / 2) * δ ≤ u * Real.sqrt 2 := by nlinarith
  have hp1 : u * Real.sqrt 2 ≤ (3 / 2) * δ := by nlinarith
  funext i
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [neighbors, Model.bound, sbc5Family_r, sbc5_lim, sbc5_v, abs_le] <;>
    (try constructor) <;> (try intro) <;> linarith

theorem sbc5Family_step (δ u : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hu0 : -δ ≤ u) (hu1 : u ≤ δ) :
    step .sbc (sbc5Family_r δ) (fun i => sbc5_lim i + u * sbc5_v i) =
      fun i => sbc5_lim i + (sbc5Rate * u) * sbc5_v i := by
  have h2 := sbc_sqrt_two_sq
  funext i
  rw [step_apply, sbc5Family_table δ u hδ0 hδ1 hu0 hu1]
  fin_cases i
  · simp [sbc5_lim, sbc5_v]
  · simp [Finset.sum_insert, sbc5_lim, sbc5_v, sbc5Rate]; ring
  · simp [Finset.sum_insert, sbc5_lim, sbc5_v, sbc5Rate]
    linear_combination (-u / 3) * h2
  · simp [Finset.sum_insert, sbc5_lim, sbc5_v, sbc5Rate]; ring
  · simp [sbc5_lim, sbc5_v]

theorem sbc5Family_pow_bounds (δ : ℝ) (hδ0 : 0 < δ) (t : ℕ) :
    -δ ≤ sbc5Rate ^ t * δ ∧ sbc5Rate ^ t * δ ≤ δ := by
  obtain ⟨h0, h1⟩ := sbc_pow_bounds t
  have hr := sbc_rate_gt
  have hlo : -1 ≤ sbc5Rate ^ t := by linarith
  constructor <;> nlinarith

theorem sbc5Family_closed_form_internal (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (t : ℕ) :
    traj .sbc (sbc5Family_r δ) (sbc5Family_x0 δ) t =
      fun i => sbc5_lim i + (sbc5Rate ^ t * δ) * sbc5_v i := by
  induction t with
  | zero =>
    funext i
    simp [traj, sbc5Family_x0]
  | succ t ih =>
    have h : traj .sbc (sbc5Family_r δ) (sbc5Family_x0 δ) (t + 1) =
        step .sbc (sbc5Family_r δ)
          (traj .sbc (sbc5Family_r δ) (sbc5Family_x0 δ) t) := by
      simp only [traj]
      exact Function.iterate_succ_apply' _ _ _
    obtain ⟨h0, h1⟩ := sbc5Family_pow_bounds δ hδ0 t
    rw [h, ih, sbc5Family_step δ _ hδ0 hδ1 h0 h1]
    funext i
    rw [pow_succ]
    ring

theorem sbc5Family_neighbors_internal (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (t : ℕ) :
    neighbors .sbc (sbc5Family_r δ)
      (traj .sbc (sbc5Family_r δ) (sbc5Family_x0 δ) t) =
      ![{0}, {0, 1, 2}, {1, 2, 3}, {2, 3, 4}, {4}] := by
  obtain ⟨h0, h1⟩ := sbc5Family_pow_bounds δ hδ0 t
  rw [sbc5Family_closed_form_internal δ hδ0 hδ1,
    sbc5Family_table δ _ hδ0 hδ1 h0 h1]

theorem sbc5Family_rate_tendsto (δ : ℝ) :
    Tendsto (fun t : ℕ => sbc5Rate ^ t * δ) atTop (𝓝 0) := by
  simpa using
    (tendsto_pow_atTop_nhds_zero_of_abs_lt_one abs_sbc5Rate_lt_one).mul_const δ

theorem sbc5Family_tendsto (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    Tendsto (traj .sbc (sbc5Family_r δ) (sbc5Family_x0 δ)) atTop (𝓝 sbc5_lim) :=
  tendsto_of_closed_form _ _ sbc5_v _ (sbc5Family_rate_tendsto δ)
    (sbc5Family_closed_form_internal δ hδ0 hδ1)

theorem sbc5Family_digraph_constant (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (t : ℕ) :
    proximityDigraph .sbc (sbc5Family_r δ)
        (traj .sbc (sbc5Family_r δ) (sbc5Family_x0 δ) t) =
      proximityDigraph .sbc (sbc5Family_r δ) (sbc5Family_x0 δ) := by
  have h0 : traj .sbc (sbc5Family_r δ) (sbc5Family_x0 δ) 0 = sbc5Family_x0 δ := rfl
  have ht0 := sbc5Family_neighbors_internal δ hδ0 hδ1 0
  rw [h0] at ht0
  simp only [proximityDigraph, sbc5Family_neighbors_internal δ hδ0 hδ1, ht0]

theorem sbc5Family_not_fixedFrom (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (τ : ℕ) :
    ¬ FixedFrom (traj .sbc (sbc5Family_r δ) (sbc5Family_x0 δ)) τ :=
  not_fixedFrom_of_closed_form _ _ sbc5_v _
    (sbc5Family_closed_form_internal δ hδ0 hδ1)
    (alternating _ _ sbc5Rate_neg hδ0.ne') 1 (by simp [sbc5_v]) τ

theorem sbc5Family_not_pseudoStableAfter (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (xinf : Fin 5 → ℝ) (τ : ℕ) :
    ¬ PseudoStableAfter (traj .sbc (sbc5Family_r δ) (sbc5Family_x0 δ)) xinf τ :=
  not_pseudoStable_of_closed_form _ _ sbc5_v _ (sbc5Family_rate_tendsto δ)
    (sbc5Family_closed_form_internal δ hδ0 hδ1)
    (alternating _ _ sbc5Rate_neg hδ0.ne') xinf τ

/-- No positive bound on relative radius spread restores eventual pseudo-stability, even
for a constant-digraph SBC system on five agents. The pairwise inequalities express that
the largest radius divided by the smallest is strictly below `1+ε`. -/
theorem sbc5_near_homogeneous_internal (ε : ℝ) (hε : 0 < ε) :
    ∃ r x₀ : Fin 5 → ℝ,
      (∀ i, 0 < r i) ∧
      (∀ i j, r i < (1 + ε) * r j) ∧
      r 0 < r 1 ∧
      (∀ t, proximityDigraph .sbc r (traj .sbc r x₀ t) =
        proximityDigraph .sbc r x₀) ∧
      Tendsto (traj .sbc r x₀) atTop (𝓝 sbc5_lim) ∧
      (∀ τ, ¬ FixedFrom (traj .sbc r x₀) τ) ∧
      (∀ xinf τ, ¬ PseudoStableAfter (traj .sbc r x₀) xinf τ) := by
  let δ : ℝ := min (1 / 2) (ε / 4)
  have hδ0 : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδhalf : δ ≤ 1 / 2 := min_le_left _ _
  have hδε : δ ≤ ε / 4 := min_le_right _ _
  have hδ1 : δ ≤ 1 := by linarith
  have hεδ := mul_le_mul_of_nonneg_left hδhalf hε.le
  have hspread : 6 + 3 * δ < (1 + ε) * (6 - 3 * δ) := by nlinarith
  refine ⟨sbc5Family_r δ, sbc5Family_x0 δ, sbc5Family_r_pos δ hδ0 hδ1, ?_,
    sbc5Family_r_strict δ hδ0, sbc5Family_digraph_constant δ hδ0 hδ1,
    sbc5Family_tendsto δ hδ0 hδ1, sbc5Family_not_fixedFrom δ hδ0 hδ1,
    sbc5Family_not_pseudoStableAfter δ hδ0 hδ1⟩
  intro i j
  have hi : sbc5Family_r δ i ≤ 6 + 3 * δ := by
    fin_cases i <;> simp [sbc5Family_r] <;> linarith
  have hj : 6 - 3 * δ ≤ sbc5Family_r δ j := by
    fin_cases j <;> simp [sbc5Family_r] <;> linarith
  have hm := mul_le_mul_of_nonneg_left hj (show 0 ≤ 1 + ε by linarith)
  exact lt_of_le_of_lt hi (lt_of_lt_of_le hspread hm)

end HK
