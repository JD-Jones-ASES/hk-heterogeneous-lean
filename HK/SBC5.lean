module

public import HK.Basic

/-!
# Five SBC agents with a constant digraph and oscillating convergence (this development)

`x(0) = (0, 7, 12 − √2, 19, 24)`, `r = (3, 9, 9, 9, 3)`;
`x(t) = (0, 6, 12, 18, 24) + ((1 − √2)/3)ᵗ (0, 1, −√2, 1, 0)`. The neighbourhood table
`{0}, {0, 1, 2}, {1, 2, 3}, {2, 3, 4}, {4}` is the same at every `t`, yet agents 1, 2, 3 alternate sides
of their limits. Hence Theorem 6.4(iv) and Conjecture 2.3 fail already with five SBC agents. The
identities used: `√2² = 2`; `3λ − 1 = −√2`; `λ√2 = (√2 − 2)/3`; the rate lies in `(−1/6, 0)`
(`1.4 < √2 < 1.5`), so `λ ≤ λᵗ ≤ 1` for every `t` and one table serves both parities.
-/

@[expose] public section

namespace HK

open Filter Topology

theorem sbc5_r_pos : ∀ i, 0 < sbc5_r i := by
  intro i
  fin_cases i <;> simp [sbc5_r]

theorem sbc_sqrt_two_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)

theorem sbc_sqrt_two_bounds : 1.4 < Real.sqrt 2 ∧ Real.sqrt 2 < 1.5 := by
  constructor
  · exact (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  · exact (Real.sqrt_lt' (by norm_num)).2 (by norm_num)

theorem sbc5Rate_neg : sbc5Rate < 0 := by
  obtain ⟨h1, -⟩ := sbc_sqrt_two_bounds
  unfold sbc5Rate
  linarith

theorem abs_sbc5Rate_lt_one : |sbc5Rate| < 1 := by
  obtain ⟨h1, h2⟩ := sbc_sqrt_two_bounds
  unfold sbc5Rate
  rw [abs_lt]
  constructor <;> linarith

theorem sbc_rate_gt : -1 / 6 < sbc5Rate := by
  obtain ⟨-, h2⟩ := sbc_sqrt_two_bounds
  unfold sbc5Rate
  linarith

/-- `λ ≤ λᵗ ≤ 1` for every `t`. -/
theorem sbc_pow_bounds (t : ℕ) : sbc5Rate ≤ sbc5Rate ^ t ∧ sbc5Rate ^ t ≤ 1 := by
  obtain ⟨h1, h2⟩ := sbc_sqrt_two_bounds
  have h : sbc5Rate = -((Real.sqrt 2 - 1) / 3) := by unfold sbc5Rate; ring
  rw [h]
  have hc0 : 0 < (Real.sqrt 2 - 1) / 3 := by linarith
  have hc1 : (Real.sqrt 2 - 1) / 3 ≤ 1 := by linarith
  rcases Nat.even_or_odd t with ht | ht
  · rw [ht.neg_pow]
    have h0 : 0 < ((Real.sqrt 2 - 1) / 3) ^ t := pow_pos hc0 t
    have h1 : ((Real.sqrt 2 - 1) / 3) ^ t ≤ 1 := pow_le_one₀ hc0.le hc1
    constructor <;> linarith
  · rw [ht.neg_pow]
    have h0 : 0 < ((Real.sqrt 2 - 1) / 3) ^ t := pow_pos hc0 t
    have h1 : ((Real.sqrt 2 - 1) / 3) ^ t ≤ (Real.sqrt 2 - 1) / 3 :=
      pow_le_of_le_one hc0.le hc1 (by rintro rfl; simp at ht)
    constructor <;> linarith

/-- The five-agent table for every offset `λ ≤ u ≤ 1`. -/
theorem sbc_table (u : ℝ) (hu0 : sbc5Rate ≤ u) (hu1 : u ≤ 1) :
    neighbors .sbc sbc5_r (fun i => sbc5_lim i + u * sbc5_v i) =
      ![{0}, {0, 1, 2}, {1, 2, 3}, {2, 3, 4}, {4}] := by
  obtain ⟨hs1, hs2⟩ := sbc_sqrt_two_bounds
  have hr := sbc_rate_gt
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hp0 : -1 / 2 ≤ u * Real.sqrt 2 := by nlinarith
  have hp1 : u * Real.sqrt 2 ≤ 3 / 2 := by nlinarith
  funext i
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [neighbors, Model.bound, sbc5_r, sbc5_lim, sbc5_v, abs_le] <;>
    (try constructor) <;> (try intro) <;> linarith

theorem sbc_step (u : ℝ) (hu0 : sbc5Rate ≤ u) (hu1 : u ≤ 1) :
    step .sbc sbc5_r (fun i => sbc5_lim i + u * sbc5_v i) =
      fun i => sbc5_lim i + (sbc5Rate * u) * sbc5_v i := by
  have h2 := sbc_sqrt_two_sq
  funext i
  rw [step_apply, sbc_table u hu0 hu1]
  fin_cases i
  · simp [sbc5_lim, sbc5_v]
  · simp [Finset.sum_insert, sbc5_lim, sbc5_v, sbc5Rate]; ring
  · simp [Finset.sum_insert, sbc5_lim, sbc5_v, sbc5Rate]; linear_combination (-u / 3) * h2
  · simp [Finset.sum_insert, sbc5_lim, sbc5_v, sbc5Rate]; ring
  · simp [sbc5_lim, sbc5_v]

theorem sbc5_closed_form_internal (t : ℕ) :
    traj .sbc sbc5_r sbc5_x0 t = fun i => sbc5_lim i + sbc5Rate ^ t * sbc5_v i := by
  induction t with
  | zero =>
    funext i
    fin_cases i <;> simp [traj, sbc5_x0, sbc5_lim, sbc5_v] <;> ring
  | succ t ih =>
    have h : traj .sbc sbc5_r sbc5_x0 (t + 1) = step .sbc sbc5_r (traj .sbc sbc5_r sbc5_x0 t) := by
      simp only [traj]
      exact Function.iterate_succ_apply' _ _ _
    obtain ⟨h0, h1⟩ := sbc_pow_bounds t
    rw [h, ih, sbc_step _ h0 h1]
    funext i; rw [pow_succ]; ring

theorem sbc5_neighbors_internal (t : ℕ) :
    neighbors .sbc sbc5_r (traj .sbc sbc5_r sbc5_x0 t) =
      ![{0}, {0, 1, 2}, {1, 2, 3}, {2, 3, 4}, {4}] := by
  obtain ⟨h0, h1⟩ := sbc_pow_bounds t
  rw [sbc5_closed_form_internal, sbc_table _ h0 h1]

theorem sbc_closed_form' (t : ℕ) :
    traj .sbc sbc5_r sbc5_x0 t = fun i => sbc5_lim i + sbc5Rate ^ t * 1 * sbc5_v i := by
  rw [sbc5_closed_form_internal]; funext i; ring

theorem sbc_rate_tendsto : Tendsto (fun t : ℕ => sbc5Rate ^ t * 1) atTop (𝓝 0) := by
  simpa using tendsto_pow_atTop_nhds_zero_of_abs_lt_one abs_sbc5Rate_lt_one

theorem sbc5_tendsto : Tendsto (traj .sbc sbc5_r sbc5_x0) atTop (𝓝 sbc5_lim) :=
  tendsto_of_closed_form _ _ sbc5_v _ sbc_rate_tendsto sbc_closed_form'

theorem sbc5_digraph_constant (t : ℕ) :
    proximityDigraph .sbc sbc5_r (traj .sbc sbc5_r sbc5_x0 t) =
      proximityDigraph .sbc sbc5_r sbc5_x0 := by
  have h0 : traj .sbc sbc5_r sbc5_x0 0 = sbc5_x0 := rfl
  have := sbc5_neighbors_internal 0
  rw [h0] at this
  simp only [proximityDigraph, sbc5_neighbors_internal, this]

theorem sbc5_not_fixedFrom (τ : ℕ) : ¬ FixedFrom (traj .sbc sbc5_r sbc5_x0) τ :=
  not_fixedFrom_of_closed_form _ _ sbc5_v _ sbc_closed_form'
    (alternating _ _ sbc5Rate_neg one_ne_zero) 1 (by simp [sbc5_v]) τ

theorem sbc5_not_pseudoStableAfter (xinf : Fin 5 → ℝ) (τ : ℕ) :
    ¬ PseudoStableAfter (traj .sbc sbc5_r sbc5_x0) xinf τ :=
  not_pseudoStable_of_closed_form _ _ sbc5_v _ sbc_rate_tendsto sbc_closed_form'
    (alternating _ _ sbc5Rate_neg one_ne_zero) xinf τ

theorem not_conjecture23_sbc_five_internal : ¬ Conjecture23ForAgents .sbc 5 := by
  intro h
  obtain ⟨τ, hf | ⟨xinf, hps⟩⟩ := h sbc5_r sbc5_x0 sbc5_r_pos
  · exact sbc5_not_fixedFrom τ hf
  · exact sbc5_not_pseudoStableAfter xinf τ hps

theorem not_theorem64iv_sbc_five_internal : ¬ Theorem64ivForAgents .sbc 5 := by
  intro h
  obtain ⟨t₂, -, hf | ⟨xinf, hps⟩⟩ := h sbc5_r sbc5_x0 sbc5_r_pos 0
    (fun t _ => by simp only [proximityDigraph, sbc5_neighbors_internal])
  · exact sbc5_not_fixedFrom t₂ hf
  · exact sbc5_not_pseudoStableAfter xinf t₂ hps

theorem sbc_adj_lim (t : ℕ) :
    (adjMatrix .sbc sbc5_r (traj .sbc sbc5_r sbc5_x0 t)).mulVec sbc5_lim = sbc5_lim := by
  funext i
  rw [adj_mulVec, sbc5_neighbors_internal]
  fin_cases i <;> simp [Finset.sum_insert, sbc5_lim] <;> norm_num

theorem sbc_adj_v (t : ℕ) :
    (adjMatrix .sbc sbc5_r (traj .sbc sbc5_r sbc5_x0 t)).mulVec sbc5_v = sbc5Rate • sbc5_v := by
  have h2 := sbc_sqrt_two_sq
  funext i
  rw [adj_mulVec, sbc5_neighbors_internal]
  fin_cases i
  · simp [sbc5_v]
  · simp [Finset.sum_insert, sbc5_v, sbc5Rate]; ring
  · simp [Finset.sum_insert, sbc5_v, sbc5Rate]; linear_combination (-1 / 3 : ℝ) * h2
  · simp [Finset.sum_insert, sbc5_v, sbc5Rate]; ring
  · simp [sbc5_v]

theorem sbc_adj_pow (t k : ℕ) (c : ℝ) :
    (adjMatrix .sbc sbc5_r (traj .sbc sbc5_r sbc5_x0 t) ^ k).mulVec (sbc5_lim + c • sbc5_v) =
      sbc5_lim + (sbc5Rate ^ k * c) • sbc5_v := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_add, Matrix.mulVec_smul,
      sbc_adj_lim, sbc_adj_v, smul_smul, pow_succ]
    congr 2
    ring

/-- The final value at constant topology along the trajectory is the limit at every `t`. -/
theorem sbc_fvct (t : ℕ) : fvct .sbc sbc5_r (traj .sbc sbc5_r sbc5_x0 t) = sbc5_lim := by
  have hx : traj .sbc sbc5_r sbc5_x0 t = sbc5_lim + (sbc5Rate ^ t) • sbc5_v := by
    rw [sbc5_closed_form_internal]; funext i; simp
  have h1 : Tendsto (fun k : ℕ => sbc5_lim + (sbc5Rate ^ k * sbc5Rate ^ t) • sbc5_v)
      atTop (𝓝 sbc5_lim) := by
    have h0 := ((tendsto_pow_atTop_nhds_zero_of_abs_lt_one abs_sbc5Rate_lt_one).mul_const
      (sbc5Rate ^ t)).smul_const sbc5_v
    have h2 := h0.const_add sbc5_lim
    rwa [zero_mul, zero_smul, add_zero] at h2
  have hA := sbc_adj_pow t
  unfold fvct
  set A := adjMatrix .sbc sbc5_r (traj .sbc sbc5_r sbc5_x0 t) with hAdef
  have hf : (fun k : ℕ => (A ^ k).mulVec (traj .sbc sbc5_r sbc5_x0 t)) =
      fun k => sbc5_lim + (sbc5Rate ^ k * sbc5Rate ^ t) • sbc5_v := by
    funext k; rw [hx, hA]
  rw [hf]
  exact h1.limUnder_eq

/-- The per-step convergence factor of agents 1, 2, 3 is `λ` at every `t`. -/
theorem sbc_perStepFactor (t : ℕ) (i : Fin 5) (hi : i ∈ ({1, 2, 3} : Finset (Fin 5))) :
    perStepFactor .sbc sbc5_r (traj .sbc sbc5_r sbc5_x0) i t = sbc5Rate := by
  have hv : sbc5_v i ≠ 0 := by
    fin_cases i <;> simp_all [sbc5_v]
  have hp : sbc5Rate ^ t ≠ 0 := pow_ne_zero _ sbc5Rate_neg.ne
  rw [perStepFactor, sbc_fvct, sbc5_closed_form_internal, sbc5_closed_form_internal]
  simp only [add_sub_cancel_left, pow_succ]
  field_simp

end HK
