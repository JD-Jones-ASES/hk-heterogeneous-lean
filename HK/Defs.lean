module

public import Mathlib

/-!
# Definitions

The definitions of `Challenge.lean`, restated character for character with the same import
(`Mathlib`), so that every definition elaborates to the same term in both files; the registry's
comparator judges the elaborated constants. `scripts/check_definitions.py` compares the two files.
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
constant from `τ` on, the trajectory is pseudo-stable from some `t₂ ≥ τ` on. -/
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

end HK
