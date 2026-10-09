module

public import Mathlib

/-!
# Heterogeneous Hegselmann–Krause dynamics: explicit systems whose proximity digraph is never eventually constant, and constant-digraph systems whose convergence is never pseudo-stable

Mirtabatabaei and Bullo (*Opinion dynamics in heterogeneous networks: convergence conjectures and
theorems*, SIAM J. Control Optim. 50 (2012) 2763–2785; arXiv:1103.2829v2, the text read) study `n` agents with real
opinions and positive bounds `r₁, …, rₙ` that update synchronously by averaging, their (2.1):
`x(t+1) = A(x(t)) x(t)`, where row `i` of `A(y)` is the uniform average over the out-neighbours
`N_i(y)` of `i`. In the **SBC** model (synchronized bounded confidence, the heterogeneous
Hegselmann–Krause model of Lorenz) `N_i(y) = {j : |y_i − y_j| ≤ r_i}`; in the **SBI** model
(synchronized bounded influence) `N_i(y) = {j : |y_i − y_j| ≤ r_j}`. The *proximity digraph*
`G_r(y)` has an arc `(i, j)` iff `j ∈ N_i(y)`. A trajectory converging to `x_∞` is *pseudo-stable
after* `τ` (their (2.2)) if the agents split into two non-empty classes, the fixed ones with
`x_i(t) = x_{∞,i}` and the converging ones with `x_i(t) < x_i(t+1) < x_{∞,i}` or
`x_i(t) > x_i(t+1) > x_{∞,i}`, for every `t ≥ τ`.

Their Conjecture 2.2: for every SBC or SBI system the proximity digraph is constant after a finite
time. Conjecture 2.3: every trajectory reaches a fixed state or is eventually pseudo-stable.
Theorem 6.4(iv): if the proximity digraph is constant from some `τ` on, the trajectory is pseudo-stable
from some `t₂ ≥ τ` on (read literally; the reading that also admits a trajectory frozen from `t₂` on is
stated too, and refuted too — the literal reading already fails for a single frozen agent, since both
classes of (2.2) must be non-empty, so the content is the refutation of the reading admitting fixed
states). Hegarty, Ognissanti and Wedin (arXiv:2610.03229v1) give explicit systems
refuting all three; this file states, and `Solution.lean` proves, the following about their four
systems (the agents are indexed `0, …, n − 1` here, agent `i` of the paper being index `i − 1`):

* the closed forms of the trajectories for every `t`: `x(t) = x_∞ + c λᵗ v` with `λ = −1/6` for the
  SBC systems and `λ = (1 − √5)/8` for the SBI systems (`c = 1/2` for the first SBI system, `1`
  otherwise; so every trajectory converges to `x_∞`);
* the complete neighbourhood tables: in the 7-agent SBC and SBI systems the middle agent's
  neighbourhood alternates with the parity of `t` (the digraph is never eventually constant), while
  in the 6-agent SBC and the second 7-agent SBI system the digraph is the same for every `t`;
* no trajectory of the four is ever frozen, and none is pseudo-stable after any `τ` towards any
  vector, since four agents alternate sides of their limits;
* hence Conjecture 2.2 and Conjecture 2.3 fail in each model, and Theorem 6.4(iv) fails in each
  model under both readings;
* with `fvct` (their Definition 3.1, the limit of `A(y)ᵗ y`) and the per-step convergence factor
  (their Definition 6.1): along all four systems the final value at constant topology of every
  `x(t)` is the limit `x_∞`; the agents with nonzero offset in the two constant-digraph systems (all
  four agents of the open-minded component of the 6-agent system; the open-minded component of the
  second 7-agent SBI system less its middle agent, which sits at its limit) have per-step factor
  identically `λ < 0`, which converges to no non-negative number (their Theorem 6.4(iii)(a) asserts
  convergence to a spectral radius; the classification of components it needs is not formalized
  here);
* the positive side, their Lemma 4.2 and Lemma 4.8: a point of the equi-topology neighbourhood of
  `z` (Definition 4.1) has the proximity digraph of `z`; a convergent trajectory whose limit has every
  equi-topology distance positive has an eventually constant proximity digraph, equal to that of the
  limit, with the limit its final value at constant topology and an equilibrium; the two
  constant-digraph systems satisfy that hypothesis (every equi-topology distance of their limits is
  positive); and the sharpness of the hypothesis for the digraph conclusion: in the two alternating
  systems the limit has equi-topology distance `0` at the middle agent and at the agents on whose
  bound it sits (indices `2, 3, 4` in the SBC system, `1, 3, 5` in the SBI system).

Conjecture 2.1 of the same paper (every trajectory converges) is open and nothing here bears on it.

This Mathlib-only file intentionally contains placeholders; the corresponding Solution declarations
are proved in a separate environment.
-/

@[expose] public section

namespace HK

open Filter Topology

/-! ### The models (Mirtabatabaei–Bullo §2) -/

/-- The two models: synchronized bounded confidence and synchronized bounded influence. -/
inductive Model
  | sbc
  | sbi

/-- The bound deciding whether `j` is an out-neighbour of `i`: `r i` (SBC) or `r j` (SBI). -/
def Model.bound (m : Model) {n : ℕ} (r : Fin n → ℝ) (i j : Fin n) : ℝ :=
  match m with
  | .sbc => r i
  | .sbi => r j

/-- `N_i(y)`: the out-neighbours of `i` at the opinion vector `y`, `{j : |y_i − y_j| ≤ r_i}` in the
SBC model and `{j : |y_i − y_j| ≤ r_j}` in the SBI model. -/
noncomputable def neighbors (m : Model) {n : ℕ} (r y : Fin n → ℝ) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun j => |y i - y j| ≤ m.bound r i j)

/-- The proximity digraph `G_r(y)`: an arc from `i` to `j` iff `j ∈ N_i(y)`. -/
noncomputable def proximityDigraph (m : Model) {n : ℕ} (r y : Fin n → ℝ) : Digraph (Fin n) :=
  ⟨fun i j => j ∈ neighbors m r y i⟩

/-- The adjacency matrix `A(y)`: `a_ij = 1/|N_i(y)|` if `j ∈ N_i(y)`, else `0`. -/
noncomputable def adjMatrix (m : Model) {n : ℕ} (r y : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => if j ∈ neighbors m r y i then 1 / ((neighbors m r y i).card : ℝ) else 0

/-- One synchronous update, (2.1): `y ↦ A(y) y`. -/
noncomputable def step (m : Model) {n : ℕ} (r y : Fin n → ℝ) : Fin n → ℝ :=
  (adjMatrix m r y).mulVec y

/-- The trajectory from the initial opinion vector `x₀`: `x(t) = stepᵗ x₀`. -/
noncomputable def traj (m : Model) {n : ℕ} (r x₀ : Fin n → ℝ) (t : ℕ) : Fin n → ℝ :=
  (step m r)^[t] x₀

/-- `x` is in a fixed state from `τ` on: `x(t) = x(τ)` for every `t ≥ τ`. -/
def FixedFrom {n : ℕ} (x : ℕ → Fin n → ℝ) (τ : ℕ) : Prop :=
  ∀ t, τ ≤ t → x t = x τ

/-- Pseudo-stable behaviour after `τ` towards `xinf` (Mirtabatabaei–Bullo (2.2)): `x` converges to
`xinf`, and the agents split into two non-empty classes `F` and `C` such that for every `t ≥ τ` the
agents of `F` sit at their limits and each agent of `C` moves strictly towards its limit from one
side: `x_i(t) < x_i(t+1) < xinf_i` or `x_i(t) > x_i(t+1) > xinf_i`. -/
def PseudoStableAfter {n : ℕ} (x : ℕ → Fin n → ℝ) (xinf : Fin n → ℝ) (τ : ℕ) : Prop :=
  Tendsto x atTop (𝓝 xinf) ∧
    ∃ F C : Finset (Fin n), F.Nonempty ∧ C.Nonempty ∧ Disjoint F C ∧ F ∪ C = Finset.univ ∧
      ∀ t, τ ≤ t →
        (∀ i ∈ F, x t i = xinf i) ∧
        ∀ i ∈ C, (x t i < x (t + 1) i ∧ x (t + 1) i < xinf i) ∨
          (x t i > x (t + 1) i ∧ x (t + 1) i > xinf i)

/-! ### The conjectures and the theorem, as statements about one model and about both -/

/-- Conjecture 2.2 (constant topology in finite time) for the model `m`: for every number of agents,
every positive bounds vector and every initial opinion vector there is a finite time after which the
proximity digraph is constant. -/
def Conjecture22For (m : Model) : Prop :=
  ∀ (n : ℕ) (r x₀ : Fin n → ℝ), (∀ i, 0 < r i) →
    ∃ τ, ∀ t, τ ≤ t →
      proximityDigraph m r (traj m r x₀ t) = proximityDigraph m r (traj m r x₀ τ)

/-- Conjecture 2.2 for any SBC or SBI system. -/
def Conjecture22 : Prop := ∀ m : Model, Conjecture22For m

/-- Conjecture 2.3 (pseudo-stable behaviour) for the model `m`: every trajectory reaches a fixed
state in finite time or is pseudo-stable after some finite time. -/
def Conjecture23For (m : Model) : Prop :=
  ∀ (n : ℕ) (r x₀ : Fin n → ℝ), (∀ i, 0 < r i) →
    ∃ τ, FixedFrom (traj m r x₀) τ ∨ ∃ xinf, PseudoStableAfter (traj m r x₀) xinf τ

/-- Conjecture 2.3 for any SBC or SBI system. -/
def Conjecture23 : Prop := ∀ m : Model, Conjecture23For m

/-- Theorem 6.4(iv) for the model `m`, read literally: if the proximity digraph of a trajectory is
constant from `τ` on, the trajectory is pseudo-stable from some `t₂ ≥ τ` on (already false for a
trajectory frozen from the start, since both classes of (2.2) must be non-empty). -/
def Theorem64ivLiteralFor (m : Model) : Prop :=
  ∀ (n : ℕ) (r x₀ : Fin n → ℝ), (∀ i, 0 < r i) →
    ∀ τ, (∀ t, τ ≤ t →
        proximityDigraph m r (traj m r x₀ t) = proximityDigraph m r (traj m r x₀ τ)) →
      ∃ t₂, τ ≤ t₂ ∧ ∃ xinf, PseudoStableAfter (traj m r x₀) xinf t₂

/-- Theorem 6.4(iv) for the model `m`, the reading that also admits a trajectory in a fixed state
from `t₂` on. -/
def Theorem64ivFor (m : Model) : Prop :=
  ∀ (n : ℕ) (r x₀ : Fin n → ℝ), (∀ i, 0 < r i) →
    ∀ τ, (∀ t, τ ≤ t →
        proximityDigraph m r (traj m r x₀ t) = proximityDigraph m r (traj m r x₀ τ)) →
      ∃ t₂, τ ≤ t₂ ∧
        (FixedFrom (traj m r x₀) t₂ ∨ ∃ xinf, PseudoStableAfter (traj m r x₀) xinf t₂)

/-- Theorem 6.4(iv), literal reading, for any SBC or SBI system. -/
def Theorem64ivLiteral : Prop := ∀ m : Model, Theorem64ivLiteralFor m

/-- Theorem 6.4(iv), the reading admitting fixed states, for any SBC or SBI system. -/
def Theorem64iv : Prop := ∀ m : Model, Theorem64ivFor m

/-! ### Final value, per-step factor, equi-topology distance (Definitions 3.1, 6.1, 4.1) -/

/-- Definition 3.1: the final value at constant topology, `fvct(y) = lim_{t→∞} A(y)ᵗ y` (the limit
of the trajectory from `y` whose topology is held fixed; `limUnder` is that limit when it exists). -/
noncomputable def fvct (m : Model) {n : ℕ} (r y : Fin n → ℝ) : Fin n → ℝ :=
  limUnder atTop (fun t : ℕ => (adjMatrix m r y ^ t).mulVec y)

/-- Definition 6.1: the per-step convergence factor of agent `i` at time `t` along `x`,
`(x_i(t+1) − fvct_i(x(t))) / (x_i(t) − fvct_i(x(t)))`. -/
noncomputable def perStepFactor (m : Model) {n : ℕ} (r : Fin n → ℝ) (x : ℕ → Fin n → ℝ)
    (i : Fin n) (t : ℕ) : ℝ :=
  (x (t + 1) i - fvct m r (x t) i) / (x t i - fvct m r (x t) i)

/-- Definition 4.1(i): the equi-topology distance
`ε_i(z) = ½ · min {||z_i − z_j| − R| : j ≠ i, R ∈ {r_i, r_j}}` (for `n = 1` the set is empty and
`sInf ∅ = 0` on `ℝ`). -/
noncomputable def equiTopologyDistance {n : ℕ} (r z : Fin n → ℝ) (i : Fin n) : ℝ :=
  (1 / 2) * sInf {d : ℝ | ∃ j, j ≠ i ∧ (d = |(|z i - z j|) - r i| ∨ d = |(|z i - z j|) - r j|)}

/-- `y` lies in the equi-topology neighbourhood of `z` (Definition 4.1(i)): `|y_i − z_i| < ε_i(z)`
where `ε_i(z) > 0`, and `|y_i − z_i| = ε_i(z)` where `ε_i(z) = 0`. -/
def EquiTopologyNbhd {n : ℕ} (r z y : Fin n → ℝ) : Prop :=
  ∀ i, (0 < equiTopologyDistance r z i → |y i - z i| < equiTopologyDistance r z i) ∧
    (equiTopologyDistance r z i = 0 → |y i - z i| = equiTopologyDistance r z i)

/-! ### The four systems of Hegarty–Ognissanti–Wedin (their §2–§5) -/

/-- Their §2, SBC, seven agents: the initial opinions. -/
noncomputable def sbc7_x0 : Fin 7 → ℝ := ![0, 38, 69, 84, 99, 130, 168]
/-- Their §2: the confidence bounds. -/
noncomputable def sbc7_r : Fin 7 → ℝ := ![18, 42, 48, 12, 48, 42, 18]
/-- Their §2: the limit. -/
noncomputable def sbc7_lim : Fin 7 → ℝ := ![0, 36, 72, 84, 96, 132, 168]
/-- Their §2: the offset direction, `x(t) = x_∞ + (−1/6)ᵗ v`. -/
noncomputable def sbc7_v : Fin 7 → ℝ := ![0, 2, -3, 0, 3, -2, 0]

/-- Their §3: `λ = (1 − √5)/8`, the rate of the two SBI systems. -/
noncomputable def sbiRate : ℝ := (1 - Real.sqrt 5) / 8

/-- Their §3, SBI, seven agents: the initial opinions, with `φ = (1 + √5)/2`. -/
noncomputable def sbi7_x0 : Fin 7 → ℝ :=
  ![0, 15 / 2, 10 - Real.goldenRatio / 2, 11, 12 + Real.goldenRatio / 2, 29 / 2, 22]
/-- Their §3: the influence bounds. -/
noncomputable def sbi7_r : Fin 7 → ℝ := ![8, 4, 4, 8, 4, 4, 8]
/-- Their §3: the limit. -/
noncomputable def sbi7_lim : Fin 7 → ℝ := ![0, 7, 10, 11, 12, 15, 22]
/-- Their §3 and §5: the offset direction, `x(t) = x_∞ + (λᵗ/2) v` in §3 and `x_∞ + λᵗ v` in §5. -/
noncomputable def sbi_v : Fin 7 → ℝ :=
  ![0, 1, -Real.goldenRatio, 0, Real.goldenRatio, -1, 0]

/-- Their §4, SBC, six agents: the initial opinions. -/
noncomputable def sbc6_x0 : Fin 6 → ℝ := ![0, 22, 37, 103, 118, 140]
/-- Their §4: the confidence bounds. -/
noncomputable def sbc6_r : Fin 6 → ℝ := ![10, 70, 70, 70, 70, 10]
/-- Their §4: the limit. -/
noncomputable def sbc6_lim : Fin 6 → ℝ := ![0, 20, 40, 100, 120, 140]
/-- Their §4: the offset direction, `x(t) = x_∞ + (−1/6)ᵗ v`. -/
noncomputable def sbc6_v : Fin 6 → ℝ := ![0, 2, -3, 3, -2, 0]

/-- Their §5, SBI, seven agents: the initial opinions. -/
noncomputable def sbi7b_x0 : Fin 7 → ℝ :=
  ![0, 71, 100 - Real.goldenRatio, 110, 120 + Real.goldenRatio, 149, 220]
/-- Their §5: the influence bounds. -/
noncomputable def sbi7b_r : Fin 7 → ℝ := ![85, 35, 35, 75, 35, 35, 85]
/-- Their §5: the limit. -/
noncomputable def sbi7b_lim : Fin 7 → ℝ := ![0, 70, 100, 110, 120, 150, 220]

/-! ### The closed forms and the neighbourhood tables -/

/-- §2: `x(t) = (0, 36, 72, 84, 96, 132, 168) + (−1/6)ᵗ (0, 2, −3, 0, 3, −2, 0)`. -/
theorem sbc7_closed_form (t : ℕ) :
    traj .sbc sbc7_r sbc7_x0 t = fun i => sbc7_lim i + (-1 / 6 : ℝ) ^ t * sbc7_v i := sorry

/-- §2: the neighbourhood table at every `t`; the middle agent (index `3`) listens to itself alone
at even `t` and to its two neighbours too at odd `t`. -/
theorem sbc7_neighbors (t : ℕ) :
    neighbors .sbc sbc7_r (traj .sbc sbc7_r sbc7_x0 t) =
      ![{0}, {0, 1, 2}, {1, 2, 3, 4}, if Even t then {3} else {2, 3, 4}, {2, 3, 4, 5},
        {4, 5, 6}, {6}] := sorry

/-- §3: `x(t) = (0, 7, 10, 11, 12, 15, 22) + (λᵗ/2) (0, 1, −φ, 0, φ, −1, 0)`. -/
theorem sbi7_closed_form (t : ℕ) :
    traj .sbi sbi7_r sbi7_x0 t = fun i => sbi7_lim i + sbiRate ^ t / 2 * sbi_v i := sorry

/-- §3: the neighbourhood table at every `t`; the middle agent listens to agents `1, …, 5` at even
`t` and to `2, 3, 4` at odd `t`. -/
theorem sbi7_neighbors (t : ℕ) :
    neighbors .sbi sbi7_r (traj .sbi sbi7_r sbi7_x0 t) =
      ![{0}, {0, 1, 2, 3}, {1, 2, 3, 4}, if Even t then {1, 2, 3, 4, 5} else {2, 3, 4},
        {2, 3, 4, 5}, {3, 4, 5, 6}, {6}] := sorry

/-- §4: `x(t) = (0, 20, 40, 100, 120, 140) + (−1/6)ᵗ (0, 2, −3, 3, −2, 0)`. -/
theorem sbc6_closed_form (t : ℕ) :
    traj .sbc sbc6_r sbc6_x0 t = fun i => sbc6_lim i + (-1 / 6 : ℝ) ^ t * sbc6_v i := sorry

/-- §4: the neighbourhood table, the same at every `t`. -/
theorem sbc6_neighbors (t : ℕ) :
    neighbors .sbc sbc6_r (traj .sbc sbc6_r sbc6_x0 t) =
      ![{0}, {0, 1, 2}, {0, 1, 2, 3}, {2, 3, 4, 5}, {3, 4, 5}, {5}] := sorry

/-- §5: `x(t) = (0, 70, 100, 110, 120, 150, 220) + λᵗ (0, 1, −φ, 0, φ, −1, 0)`. -/
theorem sbi7b_closed_form (t : ℕ) :
    traj .sbi sbi7b_r sbi7b_x0 t = fun i => sbi7b_lim i + sbiRate ^ t * sbi_v i := sorry

/-- §5: the neighbourhood table, the same at every `t`. -/
theorem sbi7b_neighbors (t : ℕ) :
    neighbors .sbi sbi7b_r (traj .sbi sbi7b_r sbi7b_x0 t) =
      ![{0}, {0, 1, 2, 3}, {1, 2, 3, 4}, {2, 3, 4}, {2, 3, 4, 5}, {3, 4, 5, 6}, {6}] := sorry

/-! ### Convergence, non-freezing, non-pseudo-stability -/

/-- Every one of the four trajectories converges to its limit. -/
theorem tendsto_limits :
    Tendsto (traj .sbc sbc7_r sbc7_x0) atTop (𝓝 sbc7_lim) ∧
    Tendsto (traj .sbi sbi7_r sbi7_x0) atTop (𝓝 sbi7_lim) ∧
    Tendsto (traj .sbc sbc6_r sbc6_x0) atTop (𝓝 sbc6_lim) ∧
    Tendsto (traj .sbi sbi7b_r sbi7b_x0) atTop (𝓝 sbi7b_lim) := sorry

/-- §2: the proximity digraph of the 7-agent SBC system is not constant on any tail. -/
theorem sbc7_digraph_not_eventually_constant (τ : ℕ) :
    ∃ t, τ ≤ t ∧ proximityDigraph .sbc sbc7_r (traj .sbc sbc7_r sbc7_x0 t) ≠
      proximityDigraph .sbc sbc7_r (traj .sbc sbc7_r sbc7_x0 τ) := sorry

/-- §3: the proximity digraph of the 7-agent SBI system is not constant on any tail. -/
theorem sbi7_digraph_not_eventually_constant (τ : ℕ) :
    ∃ t, τ ≤ t ∧ proximityDigraph .sbi sbi7_r (traj .sbi sbi7_r sbi7_x0 t) ≠
      proximityDigraph .sbi sbi7_r (traj .sbi sbi7_r sbi7_x0 τ) := sorry

/-- §4: the proximity digraph of the 6-agent SBC system is the same at every `t`. -/
theorem sbc6_digraph_constant (t : ℕ) :
    proximityDigraph .sbc sbc6_r (traj .sbc sbc6_r sbc6_x0 t) =
      proximityDigraph .sbc sbc6_r sbc6_x0 := sorry

/-- §5: the proximity digraph of the second 7-agent SBI system is the same at every `t`. -/
theorem sbi7b_digraph_constant (t : ℕ) :
    proximityDigraph .sbi sbi7b_r (traj .sbi sbi7b_r sbi7b_x0 t) =
      proximityDigraph .sbi sbi7b_r sbi7b_x0 := sorry

/-- None of the four trajectories is in a fixed state from any time on. -/
theorem not_fixedFrom (τ : ℕ) :
    ¬ FixedFrom (traj .sbc sbc7_r sbc7_x0) τ ∧ ¬ FixedFrom (traj .sbi sbi7_r sbi7_x0) τ ∧
    ¬ FixedFrom (traj .sbc sbc6_r sbc6_x0) τ ∧ ¬ FixedFrom (traj .sbi sbi7b_r sbi7b_x0) τ := sorry

/-- None of the four trajectories is pseudo-stable after any time towards any vector. -/
theorem not_pseudoStableAfter (xinf : Fin 7 → ℝ) (yinf : Fin 6 → ℝ) (τ : ℕ) :
    ¬ PseudoStableAfter (traj .sbc sbc7_r sbc7_x0) xinf τ ∧
    ¬ PseudoStableAfter (traj .sbi sbi7_r sbi7_x0) xinf τ ∧
    ¬ PseudoStableAfter (traj .sbc sbc6_r sbc6_x0) yinf τ ∧
    ¬ PseudoStableAfter (traj .sbi sbi7b_r sbi7b_x0) xinf τ := sorry

/-! ### The refutations -/

/-- Conjecture 2.2 fails for the SBC model. -/
theorem not_conjecture22_sbc : ¬ Conjecture22For .sbc := sorry

/-- Conjecture 2.2 fails for the SBI model. -/
theorem not_conjecture22_sbi : ¬ Conjecture22For .sbi := sorry

/-- Conjecture 2.2 fails. -/
theorem not_conjecture22 : ¬ Conjecture22 := sorry

/-- Conjecture 2.3 fails for the SBC model. -/
theorem not_conjecture23_sbc : ¬ Conjecture23For .sbc := sorry

/-- Conjecture 2.3 fails for the SBI model. -/
theorem not_conjecture23_sbi : ¬ Conjecture23For .sbi := sorry

/-- Conjecture 2.3 fails. -/
theorem not_conjecture23 : ¬ Conjecture23 := sorry

/-- Theorem 6.4(iv) fails for the SBC model, even in the reading that admits fixed states. -/
theorem not_theorem64iv_sbc : ¬ Theorem64ivFor .sbc := sorry

/-- Theorem 6.4(iv) fails for the SBI model, even in the reading that admits fixed states. -/
theorem not_theorem64iv_sbi : ¬ Theorem64ivFor .sbi := sorry

/-- Theorem 6.4(iv) fails in the reading that admits fixed states. -/
theorem not_theorem64iv : ¬ Theorem64iv := sorry

/-- Theorem 6.4(iv) fails in its literal reading (which the reading admitting fixed states implies). -/
theorem not_theorem64iv_literal : ¬ Theorem64ivLiteral := sorry

/-! ### The final value at constant topology and the per-step convergence factor -/

/-- §2 and §3: along the two alternating systems the final value at constant topology of every
`x(t)` is the limit (each of the two parity matrices fixes the limit and scales the offset by `λ`),
so the conclusion of Lemma 4.8(ii) holds for them although that of Lemma 4.8(i) fails. -/
theorem alternating_fvct (t : ℕ) :
    fvct .sbc sbc7_r (traj .sbc sbc7_r sbc7_x0 t) = sbc7_lim ∧
    fvct .sbi sbi7_r (traj .sbi sbi7_r sbi7_x0 t) = sbi7_lim := sorry

/-- §4: along the 6-agent SBC system, the final value at constant topology of every `x(t)` is the
limit `(0, 20, 40, 100, 120, 140)`. -/
theorem sbc6_fvct (t : ℕ) : fvct .sbc sbc6_r (traj .sbc sbc6_r sbc6_x0 t) = sbc6_lim := sorry

/-- §4: the per-step convergence factor of each of the agents `1, 2, 3, 4` (the paper's `2`–`5`) is
`−1/6` at every `t`. -/
theorem sbc6_perStepFactor (t : ℕ) (i : Fin 6) (hi : i ∈ ({1, 2, 3, 4} : Finset (Fin 6))) :
    perStepFactor .sbc sbc6_r (traj .sbc sbc6_r sbc6_x0) i t = -1 / 6 := sorry

/-- §4: that factor converges to no non-negative number, in particular to no spectral radius. -/
theorem sbc6_perStepFactor_not_tendsto (i : Fin 6) (hi : i ∈ ({1, 2, 3, 4} : Finset (Fin 6)))
    (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ¬ Tendsto (fun t => perStepFactor .sbc sbc6_r (traj .sbc sbc6_r sbc6_x0) i t) atTop (𝓝 ρ) :=
  sorry

/-- §5: along the second 7-agent SBI system, the final value at constant topology of every `x(t)`
is the limit `(0, 70, 100, 110, 120, 150, 220)`. -/
theorem sbi7b_fvct (t : ℕ) : fvct .sbi sbi7b_r (traj .sbi sbi7b_r sbi7b_x0 t) = sbi7b_lim := sorry

/-- §5: the per-step convergence factor of each of the agents `1, 2, 4, 5` (the paper's `2, 3, 5, 6`;
index `3`, the paper's agent `4`, sits at its limit) is `λ = (1 − √5)/8` at every `t`. -/
theorem sbi7b_perStepFactor (t : ℕ) (i : Fin 7) (hi : i ∈ ({1, 2, 4, 5} : Finset (Fin 7))) :
    perStepFactor .sbi sbi7b_r (traj .sbi sbi7b_r sbi7b_x0) i t = sbiRate := sorry

/-- §5: that factor converges to no non-negative number. -/
theorem sbi7b_perStepFactor_not_tendsto (i : Fin 7) (hi : i ∈ ({1, 2, 4, 5} : Finset (Fin 7)))
    (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ¬ Tendsto (fun t => perStepFactor .sbi sbi7b_r (traj .sbi sbi7b_r sbi7b_x0) i t) atTop (𝓝 ρ) :=
  sorry

/-! ### Mirtabatabaei–Bullo's Lemma 4.2 and Lemma 4.8, and the sharpness of their condition -/

/-- Lemma 4.2: a point of the equi-topology neighbourhood of `z` has the proximity digraph of `z`. -/
theorem proximityDigraph_eq_of_equiTopologyNbhd (m : Model) {n : ℕ} (r z y : Fin n → ℝ)
    (h : EquiTopologyNbhd r z y) : proximityDigraph m r y = proximityDigraph m r z := sorry

/-- Lemma 4.8(i): a convergent trajectory whose limit has every equi-topology distance positive has,
from some time on, the proximity digraph of its limit. -/
theorem eventually_constant_of_tendsto (m : Model) {n : ℕ} (r x₀ xinf : Fin n → ℝ)
    (hconv : Tendsto (traj m r x₀) atTop (𝓝 xinf))
    (hε : ∀ i, 0 < equiTopologyDistance r xinf i) :
    ∃ T, ∀ t, T ≤ t → proximityDigraph m r (traj m r x₀ t) = proximityDigraph m r xinf := sorry

/-- Lemma 4.8(ii): under the same hypotheses, from some time on the limit is the final value at
constant topology of `x(t)`, and the limit is an equilibrium opinion vector (`A(x_∞) x_∞ = x_∞`). -/
theorem fvct_eq_and_equilibrium_of_tendsto (m : Model) {n : ℕ} (r x₀ xinf : Fin n → ℝ)
    (hconv : Tendsto (traj m r x₀) atTop (𝓝 xinf))
    (hε : ∀ i, 0 < equiTopologyDistance r xinf i) :
    (∃ T, ∀ t, T ≤ t → fvct m r (traj m r x₀ t) = xinf) ∧ step m r xinf = xinf := sorry

/-- The two constant-digraph systems satisfy the hypothesis of Lemma 4.8: every equi-topology
distance of their limits is positive. -/
theorem equiTopologyDistance_pos :
    (∀ i, 0 < equiTopologyDistance sbc6_r sbc6_lim i) ∧
    (∀ i, 0 < equiTopologyDistance sbi7b_r sbi7b_lim i) := sorry

/-- Sharpness of that hypothesis for the digraph conclusion (Hegarty–Ognissanti–Wedin §6): the
limits of the two alternating systems violate it. In the 7-agent SBC system the middle agent (index
`3`) and the two agents it sits on the bound of (indices `2`, `4`) have equi-topology distance `0`;
in the 7-agent SBI system the middle agent and the agents `1` and `5` (the paper's `2` and `6`) do. -/
theorem equiTopologyDistance_eq_zero :
    (∀ i ∈ ({2, 3, 4} : Finset (Fin 7)), equiTopologyDistance sbc7_r sbc7_lim i = 0) ∧
    (∀ i ∈ ({1, 3, 5} : Finset (Fin 7)), equiTopologyDistance sbi7_r sbi7_lim i = 0) := sorry

end HK
