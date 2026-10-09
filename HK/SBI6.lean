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

theorem sbi6_r_pos : ∀ i, 0 < sbi6_r i := sorry

theorem sbi6Rate_neg : sbi6Rate < 0 := sorry

theorem abs_sbi6Rate_lt_one : |sbi6Rate| < 1 := sorry

theorem sbi6_closed_form_internal (t : ℕ) :
    traj .sbi sbi6_r sbi6_x0 t = fun i => sbi6_lim i + sbi6Rate ^ t * sbi6_v i := sorry

theorem sbi6_neighbors_internal (t : ℕ) :
    neighbors .sbi sbi6_r (traj .sbi sbi6_r sbi6_x0 t) =
      ![{0}, {0, 1, 2, 3}, {0, 1, 2, 3, 4}, {0, 2, 3, 4, 5}, {2, 3, 4, 5}, {5}] := sorry

theorem sbi6_tendsto : Tendsto (traj .sbi sbi6_r sbi6_x0) atTop (𝓝 sbi6_lim) := sorry

theorem sbi6_digraph_constant (t : ℕ) :
    proximityDigraph .sbi sbi6_r (traj .sbi sbi6_r sbi6_x0 t) =
      proximityDigraph .sbi sbi6_r sbi6_x0 := sorry

theorem sbi6_not_fixedFrom (τ : ℕ) : ¬ FixedFrom (traj .sbi sbi6_r sbi6_x0) τ := sorry

theorem sbi6_not_pseudoStableAfter (yinf : Fin 6 → ℝ) (τ : ℕ) :
    ¬ PseudoStableAfter (traj .sbi sbi6_r sbi6_x0) yinf τ := sorry

theorem not_conjecture23_sbi_six_internal : ¬ Conjecture23ForAgents .sbi 6 := sorry

theorem not_theorem64iv_sbi_six_internal : ¬ Theorem64ivForAgents .sbi 6 := sorry

end HK
