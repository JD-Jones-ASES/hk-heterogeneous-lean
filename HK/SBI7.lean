module

public import HK.Basic

/-!
# The 7-agent SBI system (Hegarty–Ognissanti–Wedin §3)

`x(0) = (0, 15/2, 10 − φ/2, 11, 12 + φ/2, 29/2, 22)`, `r = (8, 4, 4, 8, 4, 4, 8)`, `φ = (1 + √5)/2`,
`λ = (1 − √5)/8`; `x(t) = (0, 7, 10, 11, 12, 15, 22) + (λᵗ/2) (0, 1, −φ, 0, φ, −1, 0)`. The middle
agent (index 3) listens to indices 1–5 at even `t` and to 2, 3, 4 at odd `t`; the proximity digraph
is never eventually constant; agents 1, 2, 4, 5 alternate sides of their limits. The tables need the
bounds on the product atom `w φ` (from `1 < φ < 2` and `φ² = φ + 1`); at odd `t` the bound is
`λ ≤ λᵗ`, not only `−1 ≤ λᵗ`.
-/

@[expose] public section

namespace HK

open Filter Topology

/-- The SBI-7 table at an even-time offset `0 < w ≤ 1/2`. -/
theorem sbi7_table_even (w : ℝ) (hw0 : 0 < w) (hw1 : w ≤ 1 / 2) :
    neighbors .sbi sbi7_r (fun i => sbi7_lim i + w * sbi_v i) =
      ![{0}, {0, 1, 2, 3}, {1, 2, 3, 4}, {1, 2, 3, 4, 5}, {2, 3, 4, 5}, {3, 4, 5, 6}, {6}] := by
  have hφ1 := Real.one_lt_goldenRatio
  have hφ2 := Real.goldenRatio_lt_two
  have hp0 : 0 < w * Real.goldenRatio := mul_pos hw0 (by linarith)
  have hp1 : w * Real.goldenRatio ≤ 1 := by nlinarith
  funext i
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [neighbors, Model.bound, sbi7_r, sbi7_lim, sbi_v, abs_le] <;>
    (try constructor) <;> (try intro) <;> linarith

/-- The SBI-7 table at an odd-time offset `(1 − φ)/8 ≤ w < 0`. -/
theorem sbi7_table_odd (w : ℝ) (hw0 : (1 - Real.goldenRatio) / 8 ≤ w) (hw1 : w < 0) :
    neighbors .sbi sbi7_r (fun i => sbi7_lim i + w * sbi_v i) =
      ![{0}, {0, 1, 2, 3}, {1, 2, 3, 4}, {2, 3, 4}, {2, 3, 4, 5}, {3, 4, 5, 6}, {6}] := by
  have hφ1 := Real.one_lt_goldenRatio
  have hφ2 := Real.goldenRatio_lt_two
  have hsq := Real.goldenRatio_sq
  have hp1 : w * Real.goldenRatio < 0 := mul_neg_of_neg_of_pos hw1 (by linarith)
  have hm := mul_le_mul_of_nonneg_right hw0 (le_of_lt (lt_trans one_pos hφ1))
  have hp0 : -1 / 8 ≤ w * Real.goldenRatio := by nlinarith
  funext i
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [neighbors, Model.bound, sbi7_r, sbi7_lim, sbi_v, abs_le] <;>
    (try constructor) <;> (try intro) <;> linarith

/-- The SBI-7 step, given its table (either parity). -/
theorem sbi7_step_of_table (w : ℝ) (S3 : Finset (Fin 7))
    (hS : S3 = {1, 2, 3, 4, 5} ∨ S3 = {2, 3, 4})
    (htab : neighbors .sbi sbi7_r (fun i => sbi7_lim i + w * sbi_v i) =
      ![{0}, {0, 1, 2, 3}, {1, 2, 3, 4}, S3, {2, 3, 4, 5}, {3, 4, 5, 6}, {6}]) :
    step .sbi sbi7_r (fun i => sbi7_lim i + w * sbi_v i) =
      fun i => sbi7_lim i + ((1 - Real.goldenRatio) / 4 * w) * sbi_v i := by
  have hsq := Real.goldenRatio_sq
  funext i
  rw [step_apply, htab]
  fin_cases i
  · simp [sbi7_lim, sbi_v]
  · simp [Finset.sum_insert, sbi7_lim, sbi_v]; ring
  · simp [Finset.sum_insert, sbi7_lim, sbi_v]; linear_combination (-w / 4) * hsq
  · rcases hS with rfl | rfl <;> simp [Finset.sum_insert, sbi7_lim, sbi_v] <;> ring
  · simp [Finset.sum_insert, sbi7_lim, sbi_v]; linear_combination (w / 4) * hsq
  · simp [Finset.sum_insert, sbi7_lim, sbi_v]; ring
  · simp [sbi7_lim, sbi_v]

/-- §3: the closed form. -/
theorem sbi7_closed_form_internal (t : ℕ) :
    traj .sbi sbi7_r sbi7_x0 t = fun i => sbi7_lim i + sbiRate ^ t / 2 * sbi_v i := by
  induction t with
  | zero =>
    funext i
    fin_cases i <;> simp [traj, sbi7_x0, sbi7_lim, sbi_v] <;> ring
  | succ t ih =>
    have h : traj .sbi sbi7_r sbi7_x0 (t + 1) = step .sbi sbi7_r (traj .sbi sbi7_r sbi7_x0 t) := by
      simp only [traj]
      exact Function.iterate_succ_apply' _ _ _
    rw [h, ih]
    rcases Nat.even_or_odd t with ht | ht
    · obtain ⟨h0, h1⟩ := sbiRate_pow_even ht
      rw [sbi7_step_of_table _ _ (Or.inl rfl) (sbi7_table_even _ h0 h1)]
      funext i; rw [pow_succ, sbiRate_eq]; ring
    · obtain ⟨h0, h1⟩ := sbiRate_pow_odd ht
      rw [sbi7_step_of_table _ _ (Or.inr rfl) (sbi7_table_odd _ h0 h1)]
      funext i; rw [pow_succ, sbiRate_eq]; ring

/-- §3: the neighbourhood table at every `t`. -/
theorem sbi7_neighbors_internal (t : ℕ) :
    neighbors .sbi sbi7_r (traj .sbi sbi7_r sbi7_x0 t) =
      ![{0}, {0, 1, 2, 3}, {1, 2, 3, 4}, if Even t then {1, 2, 3, 4, 5} else {2, 3, 4},
        {2, 3, 4, 5}, {3, 4, 5, 6}, {6}] := by
  rw [sbi7_closed_form_internal]
  rcases Nat.even_or_odd t with ht | ht
  · obtain ⟨h0, h1⟩ := sbiRate_pow_even ht
    rw [ite_eq_left ht, sbi7_table_even _ h0 h1]
  · obtain ⟨h0, h1⟩ := sbiRate_pow_odd ht
    rw [ite_eq_right (Nat.not_even_iff_odd.mpr ht), sbi7_table_odd _ h0 h1]

theorem sbi7_digraph_not_eventually_constant_internal (τ : ℕ) :
    ∃ t, τ ≤ t ∧ proximityDigraph .sbi sbi7_r (traj .sbi sbi7_r sbi7_x0 t) ≠
      proximityDigraph .sbi sbi7_r (traj .sbi sbi7_r sbi7_x0 τ) := by
  refine ⟨τ + 1, Nat.le_succ τ, fun h => ?_⟩
  have h2 := congrFun (congrFun (congrArg Digraph.Adj h) 3) 1
  simp only [proximityDigraph, sbi7_neighbors_internal] at h2
  rcases Nat.even_or_odd τ with ht | ht
  · have h' : ¬ Even (τ + 1) := Nat.not_even_iff_odd.mpr ht.add_one
    simp [h', ht] at h2
  · have h' : Even (τ + 1) := ht.add_one
    have h'' : ¬ Even τ := Nat.not_even_iff_odd.mpr ht
    simp [h', h''] at h2

theorem sbi7_closed_form_internal' (t : ℕ) :
    traj .sbi sbi7_r sbi7_x0 t = fun i => sbi7_lim i + sbiRate ^ t * (1 / 2) * sbi_v i := by
  rw [sbi7_closed_form_internal]; funext i; ring

theorem sbi7_rate_tendsto :
    Tendsto (fun t : ℕ => sbiRate ^ t * (1 / 2)) atTop (𝓝 0) := by
  have h := (tendsto_pow_atTop_nhds_zero_of_abs_lt_one sbiRate_abs_lt_one).mul_const (1 / 2 : ℝ)
  simpa using h

theorem sbi7_tendsto : Tendsto (traj .sbi sbi7_r sbi7_x0) atTop (𝓝 sbi7_lim) :=
  tendsto_of_closed_form _ _ sbi_v (fun t => sbiRate ^ t * (1 / 2))
    sbi7_rate_tendsto
    sbi7_closed_form_internal'

theorem sbi7_not_fixedFrom (τ : ℕ) : ¬ FixedFrom (traj .sbi sbi7_r sbi7_x0) τ :=
  not_fixedFrom_of_closed_form _ _ sbi_v _ sbi7_closed_form_internal'
    (alternating _ _ sbiRate_neg (by norm_num)) 1 (by simp [sbi_v]) τ

theorem sbi7_not_pseudoStableAfter (xinf : Fin 7 → ℝ) (τ : ℕ) :
    ¬ PseudoStableAfter (traj .sbi sbi7_r sbi7_x0) xinf τ :=
  not_pseudoStable_of_closed_form _ _ sbi_v _
    sbi7_rate_tendsto
    sbi7_closed_form_internal' (alternating _ _ sbiRate_neg (by norm_num)) xinf τ

theorem sbi7_r_pos : ∀ i, 0 < sbi7_r i := by
  intro i
  fin_cases i <;> simp [sbi7_r]

/-- Either parity matrix fixes the limit. -/
theorem ref_sbi7_adj_lim (t : ℕ) :
    (adjMatrix .sbi sbi7_r (traj .sbi sbi7_r sbi7_x0 t)).mulVec sbi7_lim = sbi7_lim := by
  funext i
  rw [adj_mulVec, sbi7_neighbors_internal]
  rcases Nat.even_or_odd t with ht | ht
  · rw [ite_eq_left ht]
    fin_cases i <;> simp [Finset.sum_insert, sbi7_lim] <;> norm_num
  · rw [ite_eq_right (Nat.not_even_iff_odd.mpr ht)]
    fin_cases i <;> simp [Finset.sum_insert, sbi7_lim] <;> norm_num

/-- Either parity matrix scales the offset direction by `λ`. -/
theorem ref_sbi7_adj_v (t : ℕ) :
    (adjMatrix .sbi sbi7_r (traj .sbi sbi7_r sbi7_x0 t)).mulVec sbi_v = sbiRate • sbi_v := by
  have hsq := Real.goldenRatio_sq
  funext i
  rw [adj_mulVec, sbi7_neighbors_internal, sbiRate_eq]
  rcases Nat.even_or_odd t with ht | ht
  · rw [ite_eq_left ht]
    fin_cases i
    · simp [sbi_v]
    · simp [Finset.sum_insert, sbi_v]; ring
    · simp [Finset.sum_insert, sbi_v]; linear_combination (-1 / 4 : ℝ) * hsq
    · simp [Finset.sum_insert, sbi_v]
    · simp [Finset.sum_insert, sbi_v]; linear_combination (1 / 4 : ℝ) * hsq
    · simp [Finset.sum_insert, sbi_v]; ring
    · simp [sbi_v]
  · rw [ite_eq_right (Nat.not_even_iff_odd.mpr ht)]
    fin_cases i
    · simp [sbi_v]
    · simp [Finset.sum_insert, sbi_v]; ring
    · simp [Finset.sum_insert, sbi_v]; linear_combination (-1 / 4 : ℝ) * hsq
    · simp [Finset.sum_insert, sbi_v]
    · simp [Finset.sum_insert, sbi_v]; linear_combination (1 / 4 : ℝ) * hsq
    · simp [Finset.sum_insert, sbi_v]; ring
    · simp [sbi_v]

theorem ref_sbi7_adj_pow (t k : ℕ) (c : ℝ) :
    (adjMatrix .sbi sbi7_r (traj .sbi sbi7_r sbi7_x0 t) ^ k).mulVec (sbi7_lim + c • sbi_v) =
      sbi7_lim + (sbiRate ^ k * c) • sbi_v := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_add, Matrix.mulVec_smul,
      ref_sbi7_adj_lim, ref_sbi7_adj_v, smul_smul, pow_succ]
    congr 2
    ring

/-- Each parity matrix fixes the limit and scales the offset by `λ`, so the final value at constant
topology of every `x(t)` is the limit (the route of `sbi7b_fvct_internal`, one table per parity). -/
theorem sbi7_fvct (t : ℕ) : fvct .sbi sbi7_r (traj .sbi sbi7_r sbi7_x0 t) = sbi7_lim := by
  have hx : traj .sbi sbi7_r sbi7_x0 t = sbi7_lim + (sbiRate ^ t / 2) • sbi_v := by
    rw [sbi7_closed_form_internal]; funext i; simp
  have h1 : Tendsto (fun k : ℕ => sbi7_lim + (sbiRate ^ k * (sbiRate ^ t / 2)) • sbi_v)
      atTop (𝓝 sbi7_lim) := by
    have h0 := ((tendsto_pow_atTop_nhds_zero_of_abs_lt_one sbiRate_abs_lt_one).mul_const
      (sbiRate ^ t / 2)).smul_const sbi_v
    have h2 := h0.const_add sbi7_lim
    rwa [zero_mul, zero_smul, add_zero] at h2
  have hA := ref_sbi7_adj_pow t
  unfold fvct
  set A := adjMatrix .sbi sbi7_r (traj .sbi sbi7_r sbi7_x0 t) with hAdef
  have hf : (fun k : ℕ => (A ^ k).mulVec (traj .sbi sbi7_r sbi7_x0 t)) =
      fun k => sbi7_lim + (sbiRate ^ k * (sbiRate ^ t / 2)) • sbi_v := by
    funext k; rw [hx, hA]
  rw [hf]
  exact h1.limUnder_eq

end HK
