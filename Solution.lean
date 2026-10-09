module

public import HK

/-!
# Solution

Each statement of `Challenge.lean`, restated verbatim and closed by the internal theorem of the same
name with the suffix `_internal` (`HK/SBC7.lean`, `SBI7.lean`, `SBC6.lean`, `SBI7b.lean`,
`Generic.lean`, `Refute.lean`). This module does not import `Challenge.lean`; the definitions come from
`HK/Defs.lean`, which restates those of the Challenge character for character.
-/

@[expose] public section

namespace HK

open Filter Topology

theorem sbc7_closed_form (t : ℕ) :
    traj .sbc sbc7_r sbc7_x0 t = fun i => sbc7_lim i + (-1 / 6 : ℝ) ^ t * sbc7_v i :=
  sbc7_closed_form_internal t

theorem sbc7_neighbors (t : ℕ) :
    neighbors .sbc sbc7_r (traj .sbc sbc7_r sbc7_x0 t) =
      ![{0}, {0, 1, 2}, {1, 2, 3, 4}, if Even t then {3} else {2, 3, 4}, {2, 3, 4, 5},
        {4, 5, 6}, {6}] :=
  sbc7_neighbors_internal t

theorem sbi7_closed_form (t : ℕ) :
    traj .sbi sbi7_r sbi7_x0 t = fun i => sbi7_lim i + sbiRate ^ t / 2 * sbi_v i :=
  sbi7_closed_form_internal t

theorem sbi7_neighbors (t : ℕ) :
    neighbors .sbi sbi7_r (traj .sbi sbi7_r sbi7_x0 t) =
      ![{0}, {0, 1, 2, 3}, {1, 2, 3, 4}, if Even t then {1, 2, 3, 4, 5} else {2, 3, 4},
        {2, 3, 4, 5}, {3, 4, 5, 6}, {6}] :=
  sbi7_neighbors_internal t

theorem sbc6_closed_form (t : ℕ) :
    traj .sbc sbc6_r sbc6_x0 t = fun i => sbc6_lim i + (-1 / 6 : ℝ) ^ t * sbc6_v i :=
  sbc6_closed_form_internal t

theorem sbc6_neighbors (t : ℕ) :
    neighbors .sbc sbc6_r (traj .sbc sbc6_r sbc6_x0 t) =
      ![{0}, {0, 1, 2}, {0, 1, 2, 3}, {2, 3, 4, 5}, {3, 4, 5}, {5}] :=
  sbc6_neighbors_internal t

theorem sbi7b_closed_form (t : ℕ) :
    traj .sbi sbi7b_r sbi7b_x0 t = fun i => sbi7b_lim i + sbiRate ^ t * sbi_v i :=
  sbi7b_closed_form_internal t

theorem sbi7b_neighbors (t : ℕ) :
    neighbors .sbi sbi7b_r (traj .sbi sbi7b_r sbi7b_x0 t) =
      ![{0}, {0, 1, 2, 3}, {1, 2, 3, 4}, {2, 3, 4}, {2, 3, 4, 5}, {3, 4, 5, 6}, {6}] :=
  sbi7b_neighbors_internal t

theorem tendsto_limits :
    Tendsto (traj .sbc sbc7_r sbc7_x0) atTop (𝓝 sbc7_lim) ∧
    Tendsto (traj .sbi sbi7_r sbi7_x0) atTop (𝓝 sbi7_lim) ∧
    Tendsto (traj .sbc sbc6_r sbc6_x0) atTop (𝓝 sbc6_lim) ∧
    Tendsto (traj .sbi sbi7b_r sbi7b_x0) atTop (𝓝 sbi7b_lim) :=
  tendsto_limits_internal

theorem sbc7_digraph_not_eventually_constant (τ : ℕ) :
    ∃ t, τ ≤ t ∧ proximityDigraph .sbc sbc7_r (traj .sbc sbc7_r sbc7_x0 t) ≠
      proximityDigraph .sbc sbc7_r (traj .sbc sbc7_r sbc7_x0 τ) :=
  sbc7_digraph_not_eventually_constant_internal τ

theorem sbi7_digraph_not_eventually_constant (τ : ℕ) :
    ∃ t, τ ≤ t ∧ proximityDigraph .sbi sbi7_r (traj .sbi sbi7_r sbi7_x0 t) ≠
      proximityDigraph .sbi sbi7_r (traj .sbi sbi7_r sbi7_x0 τ) :=
  sbi7_digraph_not_eventually_constant_internal τ

theorem sbc6_digraph_constant (t : ℕ) :
    proximityDigraph .sbc sbc6_r (traj .sbc sbc6_r sbc6_x0 t) =
      proximityDigraph .sbc sbc6_r sbc6_x0 :=
  sbc6_digraph_constant_internal t

theorem sbi7b_digraph_constant (t : ℕ) :
    proximityDigraph .sbi sbi7b_r (traj .sbi sbi7b_r sbi7b_x0 t) =
      proximityDigraph .sbi sbi7b_r sbi7b_x0 :=
  sbi7b_digraph_constant_internal t

theorem not_fixedFrom (τ : ℕ) :
    ¬ FixedFrom (traj .sbc sbc7_r sbc7_x0) τ ∧ ¬ FixedFrom (traj .sbi sbi7_r sbi7_x0) τ ∧
    ¬ FixedFrom (traj .sbc sbc6_r sbc6_x0) τ ∧ ¬ FixedFrom (traj .sbi sbi7b_r sbi7b_x0) τ :=
  not_fixedFrom_internal τ

theorem not_pseudoStableAfter (xinf : Fin 7 → ℝ) (yinf : Fin 6 → ℝ) (τ : ℕ) :
    ¬ PseudoStableAfter (traj .sbc sbc7_r sbc7_x0) xinf τ ∧
    ¬ PseudoStableAfter (traj .sbi sbi7_r sbi7_x0) xinf τ ∧
    ¬ PseudoStableAfter (traj .sbc sbc6_r sbc6_x0) yinf τ ∧
    ¬ PseudoStableAfter (traj .sbi sbi7b_r sbi7b_x0) xinf τ :=
  not_pseudoStableAfter_internal xinf yinf τ

theorem not_conjecture22_sbc : ¬ Conjecture22For .sbc :=
  not_conjecture22_sbc_internal

theorem not_conjecture22_sbi : ¬ Conjecture22For .sbi :=
  not_conjecture22_sbi_internal

theorem not_conjecture22 : ¬ Conjecture22 :=
  not_conjecture22_internal

theorem not_conjecture23_sbc : ¬ Conjecture23For .sbc :=
  not_conjecture23_sbc_internal

theorem not_conjecture23_sbi : ¬ Conjecture23For .sbi :=
  not_conjecture23_sbi_internal

theorem not_conjecture23 : ¬ Conjecture23 :=
  not_conjecture23_internal

theorem not_theorem64iv_sbc : ¬ Theorem64ivFor .sbc :=
  not_theorem64iv_sbc_internal

theorem not_theorem64iv_sbi : ¬ Theorem64ivFor .sbi :=
  not_theorem64iv_sbi_internal

theorem not_theorem64iv : ¬ Theorem64iv :=
  not_theorem64iv_internal

theorem not_theorem64iv_literal : ¬ Theorem64ivLiteral :=
  not_theorem64iv_literal_internal

theorem alternating_fvct (t : ℕ) :
    fvct .sbc sbc7_r (traj .sbc sbc7_r sbc7_x0 t) = sbc7_lim ∧
    fvct .sbi sbi7_r (traj .sbi sbi7_r sbi7_x0 t) = sbi7_lim :=
  alternating_fvct_internal t

theorem sbc6_fvct (t : ℕ) : fvct .sbc sbc6_r (traj .sbc sbc6_r sbc6_x0 t) = sbc6_lim :=
  sbc6_fvct_internal t

theorem sbc6_perStepFactor (t : ℕ) (i : Fin 6) (hi : i ∈ ({1, 2, 3, 4} : Finset (Fin 6))) :
    perStepFactor .sbc sbc6_r (traj .sbc sbc6_r sbc6_x0) i t = -1 / 6 :=
  sbc6_perStepFactor_internal t i hi

theorem sbc6_perStepFactor_not_tendsto (i : Fin 6) (hi : i ∈ ({1, 2, 3, 4} : Finset (Fin 6)))
    (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ¬ Tendsto (fun t => perStepFactor .sbc sbc6_r (traj .sbc sbc6_r sbc6_x0) i t) atTop (𝓝 ρ) :=
  sbc6_perStepFactor_not_tendsto_internal i hi ρ hρ

theorem sbi7b_fvct (t : ℕ) : fvct .sbi sbi7b_r (traj .sbi sbi7b_r sbi7b_x0 t) = sbi7b_lim :=
  sbi7b_fvct_internal t

theorem sbi7b_perStepFactor (t : ℕ) (i : Fin 7) (hi : i ∈ ({1, 2, 4, 5} : Finset (Fin 7))) :
    perStepFactor .sbi sbi7b_r (traj .sbi sbi7b_r sbi7b_x0) i t = sbiRate :=
  sbi7b_perStepFactor_internal t i hi

theorem sbi7b_perStepFactor_not_tendsto (i : Fin 7) (hi : i ∈ ({1, 2, 4, 5} : Finset (Fin 7)))
    (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ¬ Tendsto (fun t => perStepFactor .sbi sbi7b_r (traj .sbi sbi7b_r sbi7b_x0) i t) atTop (𝓝 ρ) :=
  sbi7b_perStepFactor_not_tendsto_internal i hi ρ hρ

theorem proximityDigraph_eq_of_equiTopologyNbhd (m : Model) {n : ℕ} (r z y : Fin n → ℝ)
    (h : EquiTopologyNbhd r z y) : proximityDigraph m r y = proximityDigraph m r z :=
  proximityDigraph_eq_of_equiTopologyNbhd_internal m r z y h

theorem eventually_constant_of_tendsto (m : Model) {n : ℕ} (r x₀ xinf : Fin n → ℝ)
    (hconv : Tendsto (traj m r x₀) atTop (𝓝 xinf))
    (hε : ∀ i, 0 < equiTopologyDistance r xinf i) :
    ∃ T, ∀ t, T ≤ t → proximityDigraph m r (traj m r x₀ t) = proximityDigraph m r xinf :=
  eventually_constant_of_tendsto_internal m r x₀ xinf hconv hε

theorem fvct_eq_and_equilibrium_of_tendsto (m : Model) {n : ℕ} (r x₀ xinf : Fin n → ℝ)
    (hconv : Tendsto (traj m r x₀) atTop (𝓝 xinf))
    (hε : ∀ i, 0 < equiTopologyDistance r xinf i) :
    (∃ T, ∀ t, T ≤ t → fvct m r (traj m r x₀ t) = xinf) ∧ step m r xinf = xinf :=
  fvct_eq_and_equilibrium_of_tendsto_internal m r x₀ xinf hconv hε

theorem equiTopologyDistance_pos :
    (∀ i, 0 < equiTopologyDistance sbc6_r sbc6_lim i) ∧
    (∀ i, 0 < equiTopologyDistance sbi7b_r sbi7b_lim i) :=
  equiTopologyDistance_pos_internal

theorem equiTopologyDistance_eq_zero :
    (∀ i ∈ ({2, 3, 4} : Finset (Fin 7)), equiTopologyDistance sbc7_r sbc7_lim i = 0) ∧
    (∀ i ∈ ({1, 3, 5} : Finset (Fin 7)), equiTopologyDistance sbi7_r sbi7_lim i = 0) :=
  equiTopologyDistance_eq_zero_internal

end HK
