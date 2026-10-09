module

public import HK.SBC7
public import HK.SBI7
public import HK.SBC6
public import HK.SBI7b
public import HK.Generic

/-!
# The refutations, assembled; the conjunctions; the sharpness of Lemma 4.8's condition

Conjecture 2.2 fails in each model by the two alternating systems; Conjecture 2.3 and Theorem
6.4(iv) fail in each model by the two constant-digraph systems (Conjecture 2.3 also by the
alternating ones). The literal reading of Theorem 6.4(iv) implies the reading admitting fixed
states, so it fails too. The equi-topology distance of the limit vanishes at the alternating agents
of the two alternating systems.
-/

@[expose] public section

namespace HK

open Filter Topology

theorem tendsto_limits_internal :
    Tendsto (traj .sbc sbc7_r sbc7_x0) atTop (𝓝 sbc7_lim) ∧
    Tendsto (traj .sbi sbi7_r sbi7_x0) atTop (𝓝 sbi7_lim) ∧
    Tendsto (traj .sbc sbc6_r sbc6_x0) atTop (𝓝 sbc6_lim) ∧
    Tendsto (traj .sbi sbi7b_r sbi7b_x0) atTop (𝓝 sbi7b_lim) := sorry

theorem not_fixedFrom_internal (τ : ℕ) :
    ¬ FixedFrom (traj .sbc sbc7_r sbc7_x0) τ ∧ ¬ FixedFrom (traj .sbi sbi7_r sbi7_x0) τ ∧
    ¬ FixedFrom (traj .sbc sbc6_r sbc6_x0) τ ∧ ¬ FixedFrom (traj .sbi sbi7b_r sbi7b_x0) τ := sorry

theorem not_pseudoStableAfter_internal (xinf : Fin 7 → ℝ) (yinf : Fin 6 → ℝ) (τ : ℕ) :
    ¬ PseudoStableAfter (traj .sbc sbc7_r sbc7_x0) xinf τ ∧
    ¬ PseudoStableAfter (traj .sbi sbi7_r sbi7_x0) xinf τ ∧
    ¬ PseudoStableAfter (traj .sbc sbc6_r sbc6_x0) yinf τ ∧
    ¬ PseudoStableAfter (traj .sbi sbi7b_r sbi7b_x0) xinf τ := sorry

theorem not_conjecture22_sbc_internal : ¬ Conjecture22For .sbc := sorry

theorem not_conjecture22_sbi_internal : ¬ Conjecture22For .sbi := sorry

theorem not_conjecture22_internal : ¬ Conjecture22 := sorry

theorem not_conjecture23_sbc_internal : ¬ Conjecture23For .sbc := sorry

theorem not_conjecture23_sbi_internal : ¬ Conjecture23For .sbi := sorry

theorem not_conjecture23_internal : ¬ Conjecture23 := sorry

theorem not_theorem64iv_sbc_internal : ¬ Theorem64ivFor .sbc := sorry

theorem not_theorem64iv_sbi_internal : ¬ Theorem64ivFor .sbi := sorry

theorem not_theorem64iv_internal : ¬ Theorem64iv := sorry

theorem not_theorem64iv_literal_internal : ¬ Theorem64ivLiteral := sorry

theorem alternating_fvct_internal (t : ℕ) :
    fvct .sbc sbc7_r (traj .sbc sbc7_r sbc7_x0 t) = sbc7_lim ∧
    fvct .sbi sbi7_r (traj .sbi sbi7_r sbi7_x0 t) = sbi7_lim := sorry

theorem equiTopologyDistance_pos_internal :
    (∀ i, 0 < equiTopologyDistance sbc6_r sbc6_lim i) ∧
    (∀ i, 0 < equiTopologyDistance sbi7b_r sbi7b_lim i) := sorry

theorem equiTopologyDistance_eq_zero_internal :
    (∀ i ∈ ({2, 3, 4} : Finset (Fin 7)), equiTopologyDistance sbc7_r sbc7_lim i = 0) ∧
    (∀ i ∈ ({1, 3, 5} : Finset (Fin 7)), equiTopologyDistance sbi7_r sbi7_lim i = 0) := sorry

end HK
