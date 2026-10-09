module

public import HK.Basic

/-!
# Mirtabatabaei–Bullo's Lemma 4.2 and Lemma 4.8

A point of the equi-topology neighbourhood of `z` has the proximity digraph of `z`; a convergent
trajectory whose limit has every equi-topology distance positive has, from some time on, the
proximity digraph of its limit, the limit as the final value at constant topology of `x(t)`, and the
limit is an equilibrium. No positivity of the bounds is assumed: the case `j = i` of Lemma 4.2
reduces, at `y` and at `z`, to the same condition `0 ≤ R`.
-/

@[expose] public section

namespace HK

open Filter Topology

/-- Half the equi-topology distance at `i` bounds `||z i − z j| − R|` for `j ≠ i` and `R` either
bound. -/
theorem two_mul_equiTopologyDistance_le {n : ℕ} (r z : Fin n → ℝ) (i j : Fin n) (hij : j ≠ i) :
    2 * equiTopologyDistance r z i ≤ |(|z i - z j|) - r i| ∧
    2 * equiTopologyDistance r z i ≤ |(|z i - z j|) - r j| := sorry

theorem equiTopologyDistance_nonneg {n : ℕ} (r z : Fin n → ℝ) (i : Fin n) :
    0 ≤ equiTopologyDistance r z i := sorry

theorem proximityDigraph_eq_of_equiTopologyNbhd_internal (m : Model) {n : ℕ} (r z y : Fin n → ℝ)
    (h : EquiTopologyNbhd r z y) : proximityDigraph m r y = proximityDigraph m r z := sorry

theorem eventually_constant_of_tendsto_internal (m : Model) {n : ℕ} (r x₀ xinf : Fin n → ℝ)
    (hconv : Tendsto (traj m r x₀) atTop (𝓝 xinf))
    (hε : ∀ i, 0 < equiTopologyDistance r xinf i) :
    ∃ T, ∀ t, T ≤ t → proximityDigraph m r (traj m r x₀ t) = proximityDigraph m r xinf := sorry

theorem fvct_eq_and_equilibrium_of_tendsto_internal (m : Model) {n : ℕ} (r x₀ xinf : Fin n → ℝ)
    (hconv : Tendsto (traj m r x₀) atTop (𝓝 xinf))
    (hε : ∀ i, 0 < equiTopologyDistance r xinf i) :
    (∃ T, ∀ t, T ≤ t → fvct m r (traj m r x₀ t) = xinf) ∧ step m r xinf = xinf := sorry

end HK
