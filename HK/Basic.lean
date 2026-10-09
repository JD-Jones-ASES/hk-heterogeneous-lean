module

public import HK.Defs

/-!
# Generic lemmas about the models

The mean form of a step, the trajectory recursion, convergence of a geometric closed form, the two
ways an alternating agent defeats a fixed state and pseudo-stability, the final value at constant
topology along a trajectory whose neighbourhoods are constant, the per-step factor of a geometric
closed form, the implication from the literal reading of Theorem 6.4(iv) to the reading admitting
fixed states, and the facts about `sbiRate = (1 − √5)/8`.
-/

@[expose] public section

namespace HK

open Filter Topology

/-- The mean form of (2.1): `step m r y i` is the average of `y` over `N_i(y)`. -/
theorem step_apply (m : Model) {n : ℕ} (r y : Fin n → ℝ) (i : Fin n) :
    step m r y i = (∑ j ∈ neighbors m r y i, y j) / ((neighbors m r y i).card : ℝ) := sorry

theorem traj_zero (m : Model) {n : ℕ} (r x₀ : Fin n → ℝ) : traj m r x₀ 0 = x₀ := sorry

theorem traj_succ (m : Model) {n : ℕ} (r x₀ : Fin n → ℝ) (t : ℕ) :
    traj m r x₀ (t + 1) = step m r (traj m r x₀ t) := sorry

/-- Equal neighbourhood functions give equal proximity digraphs. -/
theorem proximityDigraph_eq_of_neighbors_eq (m : Model) {n : ℕ} (r y z : Fin n → ℝ)
    (h : neighbors m r y = neighbors m r z) : proximityDigraph m r y = proximityDigraph m r z := sorry

/-- Equal proximity digraphs give equal neighbourhood functions. -/
theorem neighbors_eq_of_proximityDigraph_eq (m : Model) {n : ℕ} (r y z : Fin n → ℝ)
    (h : proximityDigraph m r y = proximityDigraph m r z) : neighbors m r y = neighbors m r z := sorry

/-- Equal neighbourhood functions give equal adjacency matrices. -/
theorem adjMatrix_eq_of_neighbors_eq (m : Model) {n : ℕ} (r y z : Fin n → ℝ)
    (h : neighbors m r y = neighbors m r z) : adjMatrix m r y = adjMatrix m r z := sorry

/-- A trajectory with the closed form `L + cᵗ v`, `|c| < 1`, converges to `L`. -/
theorem tendsto_of_closed_form {n : ℕ} (x : ℕ → Fin n → ℝ) (L v : Fin n → ℝ) (c : ℝ)
    (hc : |c| < 1) (hx : ∀ t, x t = fun i => L i + c ^ t * v i) :
    Tendsto x atTop (𝓝 L) := sorry

/-- An agent with a nonzero offset `cᵗ v i`, `c < 0`, is never in a fixed state. -/
theorem not_fixedFrom_of_alternating {n : ℕ} (x : ℕ → Fin n → ℝ) (L v : Fin n → ℝ) (c : ℝ)
    (hc : c < 0) (i : Fin n) (hv : v i ≠ 0) (hx : ∀ t, x t i = L i + c ^ t * v i) (τ : ℕ) :
    ¬ FixedFrom x τ := sorry

/-- A trajectory converging to `L` with an agent whose offset `cᵗ v i`, `c < 0`, `v i ≠ 0`,
alternates sign is pseudo-stable after no time towards no vector. -/
theorem not_pseudoStableAfter_of_alternating {n : ℕ} (x : ℕ → Fin n → ℝ) (L v : Fin n → ℝ) (c : ℝ)
    (hc : c < 0) (hL : Tendsto x atTop (𝓝 L)) (i : Fin n) (hv : v i ≠ 0)
    (hx : ∀ t, x t i = L i + c ^ t * v i) (xinf : Fin n → ℝ) (τ : ℕ) :
    ¬ PseudoStableAfter x xinf τ := sorry

/-- Along a trajectory whose neighbourhoods are constant from time `t` on, the final value at
constant topology of `x(t)` is the limit of the trajectory. -/
theorem fvct_eq_of_constant_neighbors (m : Model) {n : ℕ} (r x₀ L : Fin n → ℝ) (t : ℕ)
    (hN : ∀ s, neighbors m r (traj m r x₀ (t + s)) = neighbors m r (traj m r x₀ t))
    (hL : Tendsto (traj m r x₀) atTop (𝓝 L)) : fvct m r (traj m r x₀ t) = L := sorry

/-- The per-step factor of an agent with the closed form `L i + cˢ v i`, `v i ≠ 0`, `c ≠ 0`, at a
time where the final value at constant topology is `L`, is `c`. -/
theorem perStepFactor_of_closed_form (m : Model) {n : ℕ} (r x₀ L v : Fin n → ℝ) (c : ℝ)
    (hc : c ≠ 0) (i : Fin n) (hv : v i ≠ 0) (t : ℕ) (hf : fvct m r (traj m r x₀ t) = L)
    (hx : ∀ s, traj m r x₀ s i = L i + c ^ s * v i) :
    perStepFactor m r (traj m r x₀) i t = c := sorry

/-- A sequence constantly equal to a negative number converges to no non-negative number. -/
theorem not_tendsto_of_const_neg (f : ℕ → ℝ) (c ρ : ℝ) (hc : c < 0) (hρ : 0 ≤ ρ)
    (hf : ∀ t, f t = c) : ¬ Tendsto f atTop (𝓝 ρ) := sorry

/-- The literal reading of Theorem 6.4(iv) implies the reading admitting fixed states. -/
theorem theorem64ivFor_of_literal (m : Model) : Theorem64ivLiteralFor m → Theorem64ivFor m := sorry

/-- `sbiRate = ψ / 4` with `ψ = (1 − √5)/2` the golden ratio conjugate. -/
theorem sbiRate_eq : sbiRate = Real.goldenConj / 4 := sorry

theorem sbiRate_neg : sbiRate < 0 := sorry

theorem neg_one_div_four_lt_sbiRate : -1 / 4 < sbiRate := sorry

theorem abs_sbiRate_lt_one : |sbiRate| < 1 := sorry

/-- `4 λ φ = −1`: the identity (3.1) of the source. -/
theorem four_mul_sbiRate_mul_goldenRatio : 4 * sbiRate * Real.goldenRatio = -1 := sorry

/-- `4 λ = 1 − φ`: the identity (3.1) of the source. -/
theorem four_mul_sbiRate : 4 * sbiRate = 1 - Real.goldenRatio := sorry

end HK
