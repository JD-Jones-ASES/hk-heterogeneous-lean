module

public import HK.SBC7
public import HK.SBI7
public import HK.SBC6
public import HK.SBI7b
public import HK.SBC5
public import HK.SBI6
public import HK.Generic

/-!
# The refutations, assembled; the conjunctions; the sharpness of Lemma 4.8's condition

Conjecture 2.2 fails in each model by the two alternating systems; Conjecture 2.3 and Theorem
6.4(iv) fail in each model by the constant-digraph systems (Conjecture 2.3 also by the alternating
ones). The literal reading of Theorem 6.4(iv) implies the reading admitting fixed states, so it fails
too. The equi-topology distance of the limit vanishes at the alternating agents of the two alternating
systems and is positive at every agent of the two constant-digraph systems of the source.
-/

@[expose] public section

namespace HK

open Filter Topology

/-- Conjecture 2.2 fails for SBC. -/
theorem not_conjecture22_sbc_internal : ¬ Conjecture22For .sbc := by
  intro h
  obtain ⟨τ, hτ⟩ := h 7 sbc7_r sbc7_x0 sbc7_r_pos
  obtain ⟨t, ht, hne⟩ := sbc7_digraph_not_eventually_constant_internal τ
  exact hne (hτ t ht)

/-- Conjecture 2.3 fails for SBC. -/
theorem not_conjecture23_sbc_internal : ¬ Conjecture23For .sbc := by
  intro h
  obtain ⟨τ, hf | ⟨xinf, hps⟩⟩ := h 7 sbc7_r sbc7_x0 sbc7_r_pos
  · exact sbc7_not_fixedFrom τ hf
  · exact sbc7_not_pseudoStableAfter xinf τ hps

theorem not_conjecture22_sbi_internal : ¬ Conjecture22For .sbi := by
  intro h
  obtain ⟨τ, hτ⟩ := h 7 sbi7_r sbi7_x0 sbi7_r_pos
  obtain ⟨t, ht, hne⟩ := sbi7_digraph_not_eventually_constant_internal τ
  exact hne (hτ t ht)

theorem not_conjecture23_sbi_internal : ¬ Conjecture23For .sbi := by
  intro h
  obtain ⟨τ, hf | ⟨xinf, hps⟩⟩ := h 7 sbi7_r sbi7_x0 sbi7_r_pos
  · exact sbi7_not_fixedFrom τ hf
  · exact sbi7_not_pseudoStableAfter xinf τ hps

theorem not_theorem64iv_sbc_internal : ¬ Theorem64ivFor .sbc := by
  intro h
  have hq : (-1 / 6 : ℝ) < 0 := by norm_num
  have ha : Tendsto (fun t : ℕ => (-1 / 6 : ℝ) ^ t * 1) atTop (𝓝 0) := by
    simpa using tendsto_pow_atTop_nhds_zero_of_abs_lt_one
      (show |(-1 / 6 : ℝ)| < 1 by rw [abs_of_neg hq]; norm_num)
  obtain ⟨t₂, -, hf | ⟨xinf, hps⟩⟩ := h 6 sbc6_r sbc6_x0 sbc6_r_pos 0
    (fun t _ => by simp only [proximityDigraph, sbc6_neighbors_internal])
  · exact not_fixedFrom_of_closed_form _ _ sbc6_v _ sbc6_closed_form_internal'
      (alternating _ _ hq one_ne_zero) 1 (by simp [sbc6_v]) t₂ hf
  · exact not_pseudoStable_of_closed_form _ _ sbc6_v _ ha sbc6_closed_form_internal'
      (alternating _ _ hq one_ne_zero) xinf t₂ hps

theorem not_theorem64iv_sbi_internal : ¬ Theorem64ivFor .sbi := by
  intro h
  have ha : Tendsto (fun t : ℕ => sbiRate ^ t * 1) atTop (𝓝 0) := by
    simpa using tendsto_pow_atTop_nhds_zero_of_abs_lt_one sbiRate_abs_lt_one
  obtain ⟨t₂, -, hf | ⟨xinf, hps⟩⟩ := h 7 sbi7b_r sbi7b_x0 sbi7b_r_pos 0
    (fun t _ => by simp only [proximityDigraph, sbi7b_neighbors_internal])
  · exact not_fixedFrom_of_closed_form _ _ sbi_v _ sbi7b_closed_form_internal'
      (alternating _ _ sbiRate_neg one_ne_zero) 1 (by simp [sbi_v]) t₂ hf
  · exact not_pseudoStable_of_closed_form _ _ sbi_v _ ha sbi7b_closed_form_internal'
      (alternating _ _ sbiRate_neg one_ne_zero) xinf t₂ hps

theorem not_conjecture22_internal : ¬ Conjecture22 := fun h => not_conjecture22_sbc_internal (h .sbc)

theorem not_conjecture23_internal : ¬ Conjecture23 := fun h => not_conjecture23_sbc_internal (h .sbc)

theorem not_theorem64iv_internal : ¬ Theorem64iv := fun h => not_theorem64iv_sbc_internal (h .sbc)

theorem not_theorem64iv_literal_internal : ¬ Theorem64ivLiteral := by
  intro h
  apply not_theorem64iv_sbc_internal
  intro n r x₀ hr τ hτ
  obtain ⟨t₂, ht₂, hps⟩ := h .sbc n r x₀ hr τ hτ
  exact ⟨t₂, ht₂, Or.inr hps⟩

theorem tendsto_limits_internal :
    Tendsto (traj .sbc sbc7_r sbc7_x0) atTop (𝓝 sbc7_lim) ∧
    Tendsto (traj .sbi sbi7_r sbi7_x0) atTop (𝓝 sbi7_lim) ∧
    Tendsto (traj .sbc sbc6_r sbc6_x0) atTop (𝓝 sbc6_lim) ∧
    Tendsto (traj .sbi sbi7b_r sbi7b_x0) atTop (𝓝 sbi7b_lim) := by
  have hq : |(-1 / 6 : ℝ)| < 1 := by rw [abs_of_neg (by norm_num)]; norm_num
  refine ⟨sbc7_tendsto, sbi7_tendsto, ?_, ?_⟩
  · exact tendsto_of_closed_form _ _ sbc6_v _
      (by simpa using tendsto_pow_atTop_nhds_zero_of_abs_lt_one hq) sbc6_closed_form_internal'
  · exact tendsto_of_closed_form _ _ sbi_v _
      (by simpa using tendsto_pow_atTop_nhds_zero_of_abs_lt_one sbiRate_abs_lt_one)
      sbi7b_closed_form_internal'

theorem not_fixedFrom_internal (τ : ℕ) :
    ¬ FixedFrom (traj .sbc sbc7_r sbc7_x0) τ ∧ ¬ FixedFrom (traj .sbi sbi7_r sbi7_x0) τ ∧
    ¬ FixedFrom (traj .sbc sbc6_r sbc6_x0) τ ∧ ¬ FixedFrom (traj .sbi sbi7b_r sbi7b_x0) τ :=
  ⟨sbc7_not_fixedFrom τ, sbi7_not_fixedFrom τ,
    not_fixedFrom_of_closed_form _ _ sbc6_v _ sbc6_closed_form_internal'
      (alternating _ _ (by norm_num) one_ne_zero) 1 (by simp [sbc6_v]) τ,
    not_fixedFrom_of_closed_form _ _ sbi_v _ sbi7b_closed_form_internal'
      (alternating _ _ sbiRate_neg one_ne_zero) 1 (by simp [sbi_v]) τ⟩

theorem not_pseudoStableAfter_internal (xinf : Fin 7 → ℝ) (yinf : Fin 6 → ℝ) (τ : ℕ) :
    ¬ PseudoStableAfter (traj .sbc sbc7_r sbc7_x0) xinf τ ∧
    ¬ PseudoStableAfter (traj .sbi sbi7_r sbi7_x0) xinf τ ∧
    ¬ PseudoStableAfter (traj .sbc sbc6_r sbc6_x0) yinf τ ∧
    ¬ PseudoStableAfter (traj .sbi sbi7b_r sbi7b_x0) xinf τ := by
  have hq : |(-1 / 6 : ℝ)| < 1 := by rw [abs_of_neg (by norm_num)]; norm_num
  refine ⟨sbc7_not_pseudoStableAfter xinf τ, sbi7_not_pseudoStableAfter xinf τ, ?_, ?_⟩
  · exact not_pseudoStable_of_closed_form _ _ sbc6_v _
      (by simpa using tendsto_pow_atTop_nhds_zero_of_abs_lt_one hq) sbc6_closed_form_internal'
      (alternating _ _ (by norm_num) one_ne_zero) yinf τ
  · exact not_pseudoStable_of_closed_form _ _ sbi_v _
      (by simpa using tendsto_pow_atTop_nhds_zero_of_abs_lt_one sbiRate_abs_lt_one)
      sbi7b_closed_form_internal' (alternating _ _ sbiRate_neg one_ne_zero) xinf τ

theorem equiTopologyDistance_eq_zero_three :
    equiTopologyDistance sbc7_r sbc7_lim 3 = 0 ∧
    equiTopologyDistance sbi7_r sbi7_lim 1 = 0 ∧ equiTopologyDistance sbi7_r sbi7_lim 5 = 0 := by
  refine ⟨equiTopologyDistance_eq_zero_of _ _ 3 2 (by decide) ?_,
    equiTopologyDistance_eq_zero_of _ _ 1 3 (by decide) ?_,
    equiTopologyDistance_eq_zero_of _ _ 5 3 (by decide) ?_⟩ <;>
    simp [sbc7_r, sbc7_lim, sbi7_r, sbi7_lim] <;> norm_num [abs_of_pos, abs_of_neg]

theorem alternating_fvct_internal (t : ℕ) :
    fvct .sbc sbc7_r (traj .sbc sbc7_r sbc7_x0 t) = sbc7_lim ∧
    fvct .sbi sbi7_r (traj .sbi sbi7_r sbi7_x0 t) = sbi7_lim := sorry

theorem equiTopologyDistance_pos_internal :
    (∀ i, 0 < equiTopologyDistance sbc6_r sbc6_lim i) ∧
    (∀ i, 0 < equiTopologyDistance sbi7b_r sbi7b_lim i) := sorry

theorem equiTopologyDistance_eq_zero_internal :
    (∀ i ∈ ({2, 3, 4} : Finset (Fin 7)), equiTopologyDistance sbc7_r sbc7_lim i = 0) ∧
    (∀ i ∈ ({1, 3, 5} : Finset (Fin 7)), equiTopologyDistance sbi7_r sbi7_lim i = 0) := sorry

theorem not_conjecture22_sbc_seven_internal : ¬ Conjecture22ForAgents .sbc 7 := sorry

theorem not_conjecture22_sbi_seven_internal : ¬ Conjecture22ForAgents .sbi 7 := sorry

theorem small_tendsto_internal :
    Tendsto (traj .sbc sbc5_r sbc5_x0) atTop (𝓝 sbc5_lim) ∧
    Tendsto (traj .sbi sbi6_r sbi6_x0) atTop (𝓝 sbi6_lim) := sorry

theorem small_digraph_constant_internal (t : ℕ) :
    proximityDigraph .sbc sbc5_r (traj .sbc sbc5_r sbc5_x0 t) =
      proximityDigraph .sbc sbc5_r sbc5_x0 ∧
    proximityDigraph .sbi sbi6_r (traj .sbi sbi6_r sbi6_x0 t) =
      proximityDigraph .sbi sbi6_r sbi6_x0 := sorry

theorem small_not_fixedFrom_internal (τ : ℕ) :
    ¬ FixedFrom (traj .sbc sbc5_r sbc5_x0) τ ∧ ¬ FixedFrom (traj .sbi sbi6_r sbi6_x0) τ := sorry

theorem small_not_pseudoStableAfter_internal (xinf : Fin 5 → ℝ) (yinf : Fin 6 → ℝ) (τ : ℕ) :
    ¬ PseudoStableAfter (traj .sbc sbc5_r sbc5_x0) xinf τ ∧
    ¬ PseudoStableAfter (traj .sbi sbi6_r sbi6_x0) yinf τ := sorry

end HK
