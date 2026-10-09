module

public import HK.Basic

/-!
# Six SBI agents with a constant digraph and oscillating convergence (this development)

`x_∞ = (0, 25, 31, 44, 55, 90)`, `v = (0, 10, −5 − √249, 8, 10, 0)/16`, `r = (45, 18, 27, 45/2, 27, 54)`,
`x(0) = x_∞ + v`, `x(t) = x_∞ + ((13 − √249)/40)ᵗ v`. The neighbourhood table
`{0}, {0, 1, 2, 3}, {0, 1, 2, 3, 4}, {0, 2, 3, 4, 5}, {2, 3, 4, 5}, {5}` is the same at every `t`, yet
agents 1–4 alternate sides of their limits. Hence Theorem 6.4(iv) and Conjecture 2.3 fail already with
six SBI agents. The identities used: `√249² = 249`; the rate `λ = (13 − √249)/40` satisfies
`40λ = 13 − √249` and `λ² = (13/20)λ + 1/20`; `15 < √249 < 16` gives `−3/40 < λ < −1/20`, so
`λ ≤ λᵗ ≤ 1` for every `t` and one table serves both parities.
-/

@[expose] public section

namespace HK

open Filter Topology

/-- `15 < √249 < 16`. -/
theorem sbi_sqrt249_bounds : 15 < Real.sqrt 249 ∧ Real.sqrt 249 < 16 := by
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

theorem sbi_sqrt249_sq : Real.sqrt 249 ^ 2 = 249 := Real.sq_sqrt (by norm_num)

/-- `−3/40 < λ < −1/20`. -/
theorem sbi_sbi6Rate_bounds : -3 / 40 < sbi6Rate ∧ sbi6Rate < -1 / 20 := by
  obtain ⟨h0, h1⟩ := sbi_sqrt249_bounds
  unfold sbi6Rate
  constructor <;> linarith

theorem sbi6_r_pos : ∀ i, 0 < sbi6_r i := by
  intro i
  fin_cases i <;> simp [sbi6_r]

theorem sbi6Rate_neg : sbi6Rate < 0 := by
  linarith [sbi_sbi6Rate_bounds.2]

theorem abs_sbi6Rate_lt_one : |sbi6Rate| < 1 := by
  obtain ⟨h0, h1⟩ := sbi_sbi6Rate_bounds
  rw [abs_lt]
  constructor <;> linarith

/-- `λ ≤ λᵗ ≤ 1` for every `t`. -/
theorem si_pow_bounds (t : ℕ) : sbi6Rate ≤ sbi6Rate ^ t ∧ sbi6Rate ^ t ≤ 1 := by
  obtain ⟨h0, h1⟩ := sbi_sbi6Rate_bounds
  induction t with
  | zero => simp; linarith
  | succ t ih =>
    obtain ⟨ih0, ih1⟩ := ih
    rw [pow_succ]
    constructor <;> nlinarith

/-- The table for every offset `λ ≤ u ≤ 1`. -/
theorem sbi_sbi6_table (u : ℝ) (h0 : sbi6Rate ≤ u) (h1 : u ≤ 1) :
    neighbors .sbi sbi6_r (fun i => sbi6_lim i + u * sbi6_v i) =
      ![{0}, {0, 1, 2, 3}, {0, 1, 2, 3, 4}, {0, 2, 3, 4, 5}, {2, 3, 4, 5}, {5}] := by
  obtain ⟨hs0, hs1⟩ := sbi_sqrt249_bounds
  obtain ⟨hl0, hl1⟩ := sbi_sbi6Rate_bounds
  have hsq := sbi_sqrt249_sq
  have hs : 0 ≤ Real.sqrt 249 := Real.sqrt_nonneg _
  have hm0 := mul_le_mul_of_nonneg_right h0 hs
  have hm1 := mul_le_mul_of_nonneg_right h1 hs
  have hl : sbi6Rate * Real.sqrt 249 = (13 * Real.sqrt 249 - 249) / 40 := by
    unfold sbi6Rate; linear_combination (-1 / 40 : ℝ) * hsq
  have hp0 : -27 / 20 ≤ u * Real.sqrt 249 := by nlinarith
  have hp1 : u * Real.sqrt 249 ≤ 16 := by nlinarith
  have hu0 : -3 / 40 ≤ u := by linarith
  funext i
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [neighbors, Model.bound, sbi6_r, sbi6_lim, sbi6_v, abs_le] <;>
    (try constructor) <;> (try intro) <;> linarith

theorem sbi_sbi6_step (u : ℝ) (h0 : sbi6Rate ≤ u) (h1 : u ≤ 1) :
    step .sbi sbi6_r (fun i => sbi6_lim i + u * sbi6_v i) =
      fun i => sbi6_lim i + (sbi6Rate * u) * sbi6_v i := by
  have hsq := sbi_sqrt249_sq
  funext i
  rw [step_apply, sbi_sbi6_table u h0 h1]
  unfold sbi6Rate
  fin_cases i
  · simp [sbi6_lim, sbi6_v]
  · simp [Finset.sum_insert, sbi6_lim, sbi6_v]; ring
  · simp [Finset.sum_insert, sbi6_lim, sbi6_v]; linear_combination (-u / 640) * hsq
  · simp [Finset.sum_insert, sbi6_lim, sbi6_v]; ring
  · simp [Finset.sum_insert, sbi6_lim, sbi6_v]; ring
  · simp [sbi6_lim, sbi6_v]

theorem sbi6_closed_form_internal (t : ℕ) :
    traj .sbi sbi6_r sbi6_x0 t = fun i => sbi6_lim i + sbi6Rate ^ t * sbi6_v i := by
  induction t with
  | zero =>
    funext i
    fin_cases i <;> simp [traj, sbi6_x0, sbi6_lim, sbi6_v]
  | succ t ih =>
    have h : traj .sbi sbi6_r sbi6_x0 (t + 1) = step .sbi sbi6_r (traj .sbi sbi6_r sbi6_x0 t) := by
      simp only [traj]
      exact Function.iterate_succ_apply' _ _ _
    obtain ⟨h0, h1⟩ := si_pow_bounds t
    rw [h, ih, sbi_sbi6_step _ h0 h1]
    funext i; rw [pow_succ]; ring

theorem sbi_sbi6_closed_form' (t : ℕ) :
    traj .sbi sbi6_r sbi6_x0 t = fun i => sbi6_lim i + sbi6Rate ^ t * 1 * sbi6_v i := by
  rw [sbi6_closed_form_internal]; funext i; ring

theorem sbi6_neighbors_internal (t : ℕ) :
    neighbors .sbi sbi6_r (traj .sbi sbi6_r sbi6_x0 t) =
      ![{0}, {0, 1, 2, 3}, {0, 1, 2, 3, 4}, {0, 2, 3, 4, 5}, {2, 3, 4, 5}, {5}] := by
  obtain ⟨h0, h1⟩ := si_pow_bounds t
  rw [sbi6_closed_form_internal, sbi_sbi6_table _ h0 h1]

theorem sbi_sbi6_rate_tendsto : Tendsto (fun t : ℕ => sbi6Rate ^ t * 1) atTop (𝓝 0) := by
  simpa using tendsto_pow_atTop_nhds_zero_of_abs_lt_one abs_sbi6Rate_lt_one

theorem sbi6_tendsto : Tendsto (traj .sbi sbi6_r sbi6_x0) atTop (𝓝 sbi6_lim) :=
  tendsto_of_closed_form _ _ sbi6_v _ sbi_sbi6_rate_tendsto sbi_sbi6_closed_form'

theorem sbi6_digraph_constant (t : ℕ) :
    proximityDigraph .sbi sbi6_r (traj .sbi sbi6_r sbi6_x0 t) =
      proximityDigraph .sbi sbi6_r sbi6_x0 := by
  have h0 : traj .sbi sbi6_r sbi6_x0 0 = sbi6_x0 := rfl
  have := sbi6_neighbors_internal 0
  rw [h0] at this
  simp only [proximityDigraph, sbi6_neighbors_internal, this]

theorem sbi6_not_fixedFrom (τ : ℕ) : ¬ FixedFrom (traj .sbi sbi6_r sbi6_x0) τ :=
  not_fixedFrom_of_closed_form _ _ sbi6_v _ sbi_sbi6_closed_form'
    (alternating _ _ sbi6Rate_neg one_ne_zero) 1 (by simp [sbi6_v]) τ

theorem sbi6_not_pseudoStableAfter (yinf : Fin 6 → ℝ) (τ : ℕ) :
    ¬ PseudoStableAfter (traj .sbi sbi6_r sbi6_x0) yinf τ :=
  not_pseudoStable_of_closed_form _ _ sbi6_v _ sbi_sbi6_rate_tendsto sbi_sbi6_closed_form'
    (alternating _ _ sbi6Rate_neg one_ne_zero) yinf τ

theorem not_conjecture23_sbi_six_internal : ¬ Conjecture23ForAgents .sbi 6 := by
  intro h
  obtain ⟨τ, hf | ⟨xinf, hps⟩⟩ := h sbi6_r sbi6_x0 sbi6_r_pos
  · exact sbi6_not_fixedFrom τ hf
  · exact sbi6_not_pseudoStableAfter xinf τ hps

theorem not_theorem64iv_sbi_six_internal : ¬ Theorem64ivForAgents .sbi 6 := by
  intro h
  obtain ⟨t₂, -, hf | ⟨xinf, hps⟩⟩ := h sbi6_r sbi6_x0 sbi6_r_pos 0
    (fun t _ => by simp only [proximityDigraph, sbi6_neighbors_internal])
  · exact sbi6_not_fixedFrom t₂ hf
  · exact sbi6_not_pseudoStableAfter xinf t₂ hps

theorem si_adj_lim (t : ℕ) :
    (adjMatrix .sbi sbi6_r (traj .sbi sbi6_r sbi6_x0 t)).mulVec sbi6_lim = sbi6_lim := by
  funext i
  rw [adj_mulVec, sbi6_neighbors_internal]
  fin_cases i <;> simp [Finset.sum_insert, sbi6_lim] <;> norm_num

theorem si_adj_v (t : ℕ) :
    (adjMatrix .sbi sbi6_r (traj .sbi sbi6_r sbi6_x0 t)).mulVec sbi6_v = sbi6Rate • sbi6_v := by
  have hsq := sbi_sqrt249_sq
  funext i
  rw [adj_mulVec, sbi6_neighbors_internal]
  unfold sbi6Rate
  fin_cases i
  · simp [sbi6_v]
  · simp [Finset.sum_insert, sbi6_v]; ring
  · simp [Finset.sum_insert, sbi6_v]; linear_combination (-1 / 640 : ℝ) * hsq
  · simp [Finset.sum_insert, sbi6_v]; ring
  · simp [Finset.sum_insert, sbi6_v]; ring
  · simp [sbi6_v]

theorem si_adj_pow (t k : ℕ) (c : ℝ) :
    (adjMatrix .sbi sbi6_r (traj .sbi sbi6_r sbi6_x0 t) ^ k).mulVec (sbi6_lim + c • sbi6_v) =
      sbi6_lim + (sbi6Rate ^ k * c) • sbi6_v := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_add, Matrix.mulVec_smul,
      si_adj_lim, si_adj_v, smul_smul, pow_succ]
    congr 2
    ring

/-- The final value at constant topology (Definition 3.1) is the limit at every `t`. -/
theorem sbi6_fvct_internal (t : ℕ) : fvct .sbi sbi6_r (traj .sbi sbi6_r sbi6_x0 t) = sbi6_lim := by
  have hx : traj .sbi sbi6_r sbi6_x0 t = sbi6_lim + (sbi6Rate ^ t) • sbi6_v := by
    rw [sbi6_closed_form_internal]; funext i; simp
  have h1 : Tendsto (fun k : ℕ => sbi6_lim + (sbi6Rate ^ k * sbi6Rate ^ t) • sbi6_v)
      atTop (𝓝 sbi6_lim) := by
    have h0 := ((tendsto_pow_atTop_nhds_zero_of_abs_lt_one abs_sbi6Rate_lt_one).mul_const
      (sbi6Rate ^ t)).smul_const sbi6_v
    have h2 := h0.const_add sbi6_lim
    rwa [zero_mul, zero_smul, add_zero] at h2
  have hA := si_adj_pow t
  unfold fvct
  set A := adjMatrix .sbi sbi6_r (traj .sbi sbi6_r sbi6_x0 t) with hAdef
  have hf : (fun k : ℕ => (A ^ k).mulVec (traj .sbi sbi6_r sbi6_x0 t)) =
      fun k => sbi6_lim + (sbi6Rate ^ k * sbi6Rate ^ t) • sbi6_v := by
    funext k; rw [hx, hA]
  rw [hf]
  exact h1.limUnder_eq

/-- The per-step convergence factor (Definition 6.1) of agents 1–4 is the rate at every `t`. -/
theorem sbi6_perStepFactor_internal (t : ℕ) (i : Fin 6) (hi : i ∈ ({1, 2, 3, 4} : Finset (Fin 6))) :
    perStepFactor .sbi sbi6_r (traj .sbi sbi6_r sbi6_x0) i t = sbi6Rate := by
  have hv : sbi6_v i ≠ 0 := by
    have hs : (0 : ℝ) ≤ Real.sqrt 249 := Real.sqrt_nonneg _
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> simp [sbi6_v]
    all_goals (intro h; linarith)
  have hp : sbi6Rate ^ t ≠ 0 := pow_ne_zero _ sbi6Rate_neg.ne
  rw [perStepFactor, sbi6_fvct_internal, sbi6_closed_form_internal, sbi6_closed_form_internal]
  simp only [add_sub_cancel_left, pow_succ]
  field_simp

end HK
