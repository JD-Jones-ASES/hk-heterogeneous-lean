module

public import HK.Basic

/-!
# The 7-agent SBC system (Hegarty–Ognissanti–Wedin §2)

`x(0) = (0, 38, 69, 84, 99, 130, 168)`, `r = (18, 42, 48, 12, 48, 42, 18)`;
`x(t) = (0, 36, 72, 84, 96, 132, 168) + (−1/6)ᵗ (0, 2, −3, 0, 3, −2, 0)`. The middle agent (index 3)
listens to itself alone at even `t` and to indices 2, 3, 4 at odd `t`; the proximity digraph is
never eventually constant; agents 1, 2, 4, 5 alternate sides of their limits.
-/

@[expose] public section

namespace HK

open Filter Topology

/-- The SBC-7 table at an even-time offset `0 < u ≤ 1`. -/
theorem sbc7_table_even (u : ℝ) (h0 : 0 < u) (h1 : u ≤ 1) :
    neighbors .sbc sbc7_r (fun i => sbc7_lim i + u * sbc7_v i) =
      ![{0}, {0, 1, 2}, {1, 2, 3, 4}, {3}, {2, 3, 4, 5}, {4, 5, 6}, {6}] := by
  funext i
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [neighbors, Model.bound, sbc7_r, sbc7_lim, sbc7_v, abs_le] <;>
    (try constructor) <;> (try intro) <;> linarith

/-- The SBC-7 table at an odd-time offset `-1/6 ≤ u < 0`. -/
theorem sbc7_table_odd (u : ℝ) (h0 : -1 / 6 ≤ u) (h1 : u < 0) :
    neighbors .sbc sbc7_r (fun i => sbc7_lim i + u * sbc7_v i) =
      ![{0}, {0, 1, 2}, {1, 2, 3, 4}, {2, 3, 4}, {2, 3, 4, 5}, {4, 5, 6}, {6}] := by
  funext i
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [neighbors, Model.bound, sbc7_r, sbc7_lim, sbc7_v, abs_le] <;>
    (try constructor) <;> (try intro) <;> linarith

/-- The SBC-7 step at an even-time offset. -/
theorem sbc7_step_even (u : ℝ) (h0 : 0 < u) (h1 : u ≤ 1) :
    step .sbc sbc7_r (fun i => sbc7_lim i + u * sbc7_v i) =
      fun i => sbc7_lim i + (-1 / 6 * u) * sbc7_v i := by
  funext i
  rw [step_apply, sbc7_table_even u h0 h1]
  fin_cases i <;> simp [Finset.sum_insert, sbc7_lim, sbc7_v] <;> ring

/-- The SBC-7 step at an odd-time offset. -/
theorem sbc7_step_odd (u : ℝ) (h0 : -1 / 6 ≤ u) (h1 : u < 0) :
    step .sbc sbc7_r (fun i => sbc7_lim i + u * sbc7_v i) =
      fun i => sbc7_lim i + (-1 / 6 * u) * sbc7_v i := by
  funext i
  rw [step_apply, sbc7_table_odd u h0 h1]
  fin_cases i <;> simp [Finset.sum_insert, sbc7_lim, sbc7_v] <;> ring

/-- §2: the closed form. -/
theorem sbc7_closed_form_internal (t : ℕ) :
    traj .sbc sbc7_r sbc7_x0 t = fun i => sbc7_lim i + (-1 / 6 : ℝ) ^ t * sbc7_v i := by
  induction t with
  | zero =>
    funext i
    fin_cases i <;> simp [traj, sbc7_x0, sbc7_lim, sbc7_v] <;> norm_num
  | succ t ih =>
    have h : traj .sbc sbc7_r sbc7_x0 (t + 1) = step .sbc sbc7_r (traj .sbc sbc7_r sbc7_x0 t) := by
      simp only [traj]
      exact Function.iterate_succ_apply' _ _ _
    rw [h, ih, pow_succ]
    rcases Nat.even_or_odd t with ht | ht
    · obtain ⟨h0, h1⟩ := pow_even ht
      rw [sbc7_step_even _ h0 h1]
      funext i; ring
    · obtain ⟨h0, h1⟩ := pow_odd ht
      rw [sbc7_step_odd _ h0 h1]
      funext i; ring

/-- §2: the neighbourhood table at every `t`. -/
theorem sbc7_neighbors_internal (t : ℕ) :
    neighbors .sbc sbc7_r (traj .sbc sbc7_r sbc7_x0 t) =
      ![{0}, {0, 1, 2}, {1, 2, 3, 4}, if Even t then {3} else {2, 3, 4}, {2, 3, 4, 5},
        {4, 5, 6}, {6}] := by
  rw [sbc7_closed_form_internal]
  rcases Nat.even_or_odd t with ht | ht
  · obtain ⟨h0, h1⟩ := pow_even ht
    rw [ite_eq_left ht, sbc7_table_even _ h0 h1]
  · obtain ⟨h0, h1⟩ := pow_odd ht
    rw [ite_eq_right (Nat.not_even_iff_odd.mpr ht), sbc7_table_odd _ h0 h1]

/-- §2: the proximity digraph is never eventually constant (`t = τ + 1` differs from `τ`). -/
theorem sbc7_digraph_not_eventually_constant_internal (τ : ℕ) :
    ∃ t, τ ≤ t ∧ proximityDigraph .sbc sbc7_r (traj .sbc sbc7_r sbc7_x0 t) ≠
      proximityDigraph .sbc sbc7_r (traj .sbc sbc7_r sbc7_x0 τ) := by
  refine ⟨τ + 1, Nat.le_succ τ, fun h => ?_⟩
  have h2 := congrFun (congrFun (congrArg Digraph.Adj h) 3) 2
  simp only [proximityDigraph, sbc7_neighbors_internal] at h2
  rcases Nat.even_or_odd τ with ht | ht
  · have h' : ¬ Even (τ + 1) := Nat.not_even_iff_odd.mpr ht.add_one
    simp [h', ht] at h2
  · have h' : Even (τ + 1) := ht.add_one
    have h'' : ¬ Even τ := Nat.not_even_iff_odd.mpr ht
    simp [h', h''] at h2

/-- §2: convergence to the limit. -/
theorem sbc7_tendsto : Tendsto (traj .sbc sbc7_r sbc7_x0) atTop (𝓝 sbc7_lim) := by
  have h0 : Tendsto (fun t : ℕ => (-1 / 6 : ℝ) ^ t) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by rw [abs_of_neg (by norm_num)]; norm_num)
  rw [tendsto_pi_nhds]
  intro i
  have := (h0.mul_const (sbc7_v i)).const_add (sbc7_lim i)
  simpa [sbc7_closed_form_internal] using this

/-- §2: never in a fixed state. -/
theorem sbc7_not_fixedFrom (τ : ℕ) : ¬ FixedFrom (traj .sbc sbc7_r sbc7_x0) τ := by
  intro h
  have h1 := congrFun (h (τ + 1) (Nat.le_succ τ)) 1
  rw [sbc7_closed_form_internal, sbc7_closed_form_internal] at h1
  have hne : (-1 / 6 : ℝ) ^ τ ≠ 0 := pow_ne_zero _ (by norm_num)
  simp [sbc7_lim, sbc7_v, pow_succ] at h1
  apply hne
  linarith

/-- §2: never pseudo-stable, towards any `xinf`, after any `τ`. -/
theorem sbc7_not_pseudoStableAfter (xinf : Fin 7 → ℝ) (τ : ℕ) :
    ¬ PseudoStableAfter (traj .sbc sbc7_r sbc7_x0) xinf τ := by
  rintro ⟨hlim, F, C, -, ⟨i, hi⟩, -, -, h⟩
  have hx : xinf = sbc7_lim := tendsto_nhds_unique hlim sbc7_tendsto
  subst hx
  have hc := (h τ le_rfl).2 i hi
  rw [sbc7_closed_form_internal, sbc7_closed_form_internal] at hc
  simp only [pow_succ] at hc
  fin_cases i <;> simp [sbc7_lim, sbc7_v] at hc <;> rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith

theorem sbc7_r_pos : ∀ i, 0 < sbc7_r i := by
  intro i
  fin_cases i <;> simp [sbc7_r]

/-- Each parity matrix fixes the limit and scales the offset by `−1/6`, so the final value at constant
topology of every `x(t)` is the limit (the route of `sbc6_fvct_internal`, one table per parity). -/
theorem sbc7_fvct (t : ℕ) : fvct .sbc sbc7_r (traj .sbc sbc7_r sbc7_x0 t) = sbc7_lim := sorry

end HK
