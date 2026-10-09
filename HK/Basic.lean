module

public import HK.Defs

/-!
# Generic lemmas about the models

The mean form of a step, the sign and size of the rates' powers, convergence of a geometric closed form
`L + a(t) v`, the two ways an alternating agent defeats a fixed state and pseudo-stability, the mean form of
`A(y) z`, neighbourhoods from digraphs, and the facts about `sbiRate = (1 − √5)/8`.
-/

@[expose] public section

namespace HK

open Filter Topology

/-- One step, coordinatewise: the average of the out-neighbours' opinions. -/
theorem step_apply (m : Model) {n : ℕ} (r y : Fin n → ℝ) (i : Fin n) :
    step m r y i = (∑ j ∈ neighbors m r y i, y j) / (neighbors m r y i).card := by
  simp only [step, adjMatrix, Matrix.mulVec, dotProduct, Matrix.of_apply, ite_mul, zero_mul]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_div]
  exact Finset.sum_congr rfl (fun j _ => by ring)

/-- The sign and size of `(-1/6)^t` by parity. -/
theorem pow_even {t : ℕ} (ht : Even t) : 0 < (-1 / 6 : ℝ) ^ t ∧ (-1 / 6 : ℝ) ^ t ≤ 1 := by
  rw [neg_div, ht.neg_pow]
  exact ⟨pow_pos (by norm_num) t, pow_le_one₀ (by norm_num) (by norm_num)⟩

theorem pow_odd {t : ℕ} (ht : Odd t) : -1 / 6 ≤ (-1 / 6 : ℝ) ^ t ∧ (-1 / 6 : ℝ) ^ t < 0 := by
  rw [neg_div, ht.neg_pow]
  have hle : (1 / 6 : ℝ) ^ t ≤ 1 / 6 :=
    pow_le_of_le_one (by norm_num) (by norm_num) (by rintro rfl; simp at ht)
  have hpos : 0 < (1 / 6 : ℝ) ^ t := pow_pos (by norm_num) t
  constructor <;> linarith

/-- `λ = (1 − φ)/4`. -/
theorem sbiRate_eq : sbiRate = (1 - Real.goldenRatio) / 4 := by
  unfold sbiRate Real.goldenRatio
  ring

/-- The sign and size of `λ^t / 2` by parity. -/
theorem sbiRate_pow_even {t : ℕ} (ht : Even t) :
    0 < sbiRate ^ t / 2 ∧ sbiRate ^ t / 2 ≤ 1 / 2 := by
  have hφ1 := Real.one_lt_goldenRatio
  have hφ2 := Real.goldenRatio_lt_two
  have h : sbiRate = -((Real.goldenRatio - 1) / 4) := by rw [sbiRate_eq]; ring
  rw [h, ht.neg_pow]
  have h0 : 0 < ((Real.goldenRatio - 1) / 4) ^ t := pow_pos (by linarith) t
  have h1 : ((Real.goldenRatio - 1) / 4) ^ t ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  constructor <;> linarith

theorem sbiRate_pow_odd {t : ℕ} (ht : Odd t) :
    (1 - Real.goldenRatio) / 8 ≤ sbiRate ^ t / 2 ∧ sbiRate ^ t / 2 < 0 := by
  have hφ1 := Real.one_lt_goldenRatio
  have hφ2 := Real.goldenRatio_lt_two
  have h : sbiRate = -((Real.goldenRatio - 1) / 4) := by rw [sbiRate_eq]; ring
  rw [h, ht.neg_pow]
  have h0 : 0 < ((Real.goldenRatio - 1) / 4) ^ t := pow_pos (by linarith) t
  have h1 : ((Real.goldenRatio - 1) / 4) ^ t ≤ (Real.goldenRatio - 1) / 4 :=
    pow_le_of_le_one (by linarith) (by linarith) (by rintro rfl; simp at ht)
  constructor <;> linarith

theorem pow_bounds (t : ℕ) : -1 / 6 ≤ (-1 / 6 : ℝ) ^ t ∧ (-1 / 6 : ℝ) ^ t ≤ 1 := by
  rcases Nat.even_or_odd t with ht | ht
  · obtain ⟨h0, h1⟩ := pow_even ht
    constructor <;> linarith
  · obtain ⟨h0, h1⟩ := pow_odd ht
    constructor <;> linarith

theorem sbiRate_pow_bounds (t : ℕ) :
    (1 - Real.goldenRatio) / 4 ≤ sbiRate ^ t ∧ sbiRate ^ t ≤ 1 := by
  have hφ1 := Real.one_lt_goldenRatio
  rcases Nat.even_or_odd t with ht | ht
  · obtain ⟨h0, h1⟩ := sbiRate_pow_even ht
    constructor <;> linarith
  · obtain ⟨h0, h1⟩ := sbiRate_pow_odd ht
    constructor <;> linarith

theorem tendsto_of_closed_form {n : ℕ} (x : ℕ → Fin n → ℝ) (lim v : Fin n → ℝ) (a : ℕ → ℝ)
    (ha : Tendsto a atTop (𝓝 0)) (hx : ∀ t, x t = fun i => lim i + a t * v i) :
    Tendsto x atTop (𝓝 lim) := by
  rw [tendsto_pi_nhds]
  intro i
  have := (ha.mul_const (v i)).const_add (lim i)
  simpa [hx] using this

theorem not_monotone_side (l a b c : ℝ) (hab : a * b < 0) :
    ¬ ((l + a * c < l + b * c ∧ l + b * c < l) ∨ (l + a * c > l + b * c ∧ l + b * c > l)) := by
  rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> nlinarith [sq_nonneg c, sq_nonneg (b * c)]

theorem not_pseudoStable_of_closed_form {n : ℕ} (x : ℕ → Fin n → ℝ) (lim v : Fin n → ℝ)
    (a : ℕ → ℝ) (ha : Tendsto a atTop (𝓝 0)) (hx : ∀ t, x t = fun i => lim i + a t * v i)
    (hab : ∀ t, a t * a (t + 1) < 0) (xinf : Fin n → ℝ) (τ : ℕ) :
    ¬ PseudoStableAfter x xinf τ := by
  rintro ⟨hlim, F, C, -, ⟨i, hi⟩, -, -, h⟩
  have hx' : xinf = lim := tendsto_nhds_unique hlim (tendsto_of_closed_form x lim v a ha hx)
  subst hx'
  have hc := (h τ le_rfl).2 i hi
  rw [hx, hx] at hc
  exact not_monotone_side _ _ _ _ (hab τ) hc

theorem not_fixedFrom_of_closed_form {n : ℕ} (x : ℕ → Fin n → ℝ) (lim v : Fin n → ℝ)
    (a : ℕ → ℝ) (hx : ∀ t, x t = fun i => lim i + a t * v i)
    (hab : ∀ t, a t * a (t + 1) < 0) (i : Fin n) (hv : v i ≠ 0) (τ : ℕ) :
    ¬ FixedFrom x τ := by
  intro h
  have h1 := congrFun (h (τ + 1) (Nat.le_succ τ)) i
  rw [hx, hx] at h1
  have h2 : a (τ + 1) = a τ := mul_right_cancel₀ hv (by simpa using h1)
  have h3 := hab τ
  rw [h2] at h3
  nlinarith [sq_nonneg (a τ)]

/-- `a t · a (t+1) < 0` for `a t = q^t · c` with `q < 0`, `c ≠ 0`. -/
theorem alternating (q c : ℝ) (hq : q < 0) (hc : c ≠ 0) (t : ℕ) :
    q ^ t * c * (q ^ (t + 1) * c) < 0 := by
  have h : q ^ t * c * (q ^ (t + 1) * c) = q * (q ^ t * c) ^ 2 := by ring
  rw [h]
  have : 0 < (q ^ t * c) ^ 2 := by
    have : q ^ t * c ≠ 0 := mul_ne_zero (pow_ne_zero _ hq.ne) hc
    positivity
  nlinarith

/-- Each coordinate of a pseudo-stable trajectory sits at its limit, or stays strictly below it, or
stays strictly above it, from `τ` on. -/
theorem pseudoStableAfter_coordinate_side {n : ℕ} (x : ℕ → Fin n → ℝ)
    (L : Fin n → ℝ) (τ : ℕ) (hps : PseudoStableAfter x L τ) (i : Fin n) :
    (∀ t, τ ≤ t → x t i = L i) ∨
    (∀ t, τ ≤ t → x t i < L i) ∨ (∀ t, τ ≤ t → L i < x t i) := by
  obtain ⟨-, F, C, -, -, -, hFC, h⟩ := hps
  have himem : i ∈ F ∨ i ∈ C := by
    rw [← Finset.mem_union, hFC]
    exact Finset.mem_univ i
  rcases himem with hi | hi
  · exact Or.inl (fun t ht => (h t ht).1 i hi)
  · rcases (h τ le_rfl).2 i hi with hbelow | habove
    · right; left
      have hs : ∀ s, x (τ + s) i < L i := by
        intro s
        induction s with
        | zero => simpa using lt_trans hbelow.1 hbelow.2
        | succ s ih =>
          rcases (h (τ + s) (by omega)).2 i hi with hb | ha
          · simpa [Nat.add_assoc] using hb.2
          · exfalso; linarith [ha.1, ha.2]
      intro t ht
      have he : τ + (t - τ) = t := by omega
      simpa only [he] using hs (t - τ)
    · right; right
      have hs : ∀ s, L i < x (τ + s) i := by
        intro s
        induction s with
        | zero => simpa using lt_trans habove.2 habove.1
        | succ s ih =>
          rcases (h (τ + s) (by omega)).2 i hi with hb | ha
          · exfalso; linarith [hb.1, hb.2]
          · simpa [Nat.add_assoc] using ha.2
      intro t ht
      have he : τ + (t - τ) = t := by omega
      simpa only [he] using hs (t - τ)

theorem sbiRate_neg : sbiRate < 0 := by
  rw [sbiRate_eq]; linarith [Real.one_lt_goldenRatio]

theorem sbiRate_abs_lt_one : |sbiRate| < 1 := by
  rw [sbiRate_eq, abs_lt]
  constructor <;> linarith [Real.one_lt_goldenRatio, Real.goldenRatio_lt_two]

theorem adj_mulVec (m : Model) {n : ℕ} (r y z : Fin n → ℝ) (i : Fin n) :
    (adjMatrix m r y).mulVec z i = (∑ j ∈ neighbors m r y i, z j) / (neighbors m r y i).card := by
  simp only [adjMatrix, Matrix.mulVec, dotProduct, Matrix.of_apply, ite_mul, zero_mul]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_div]
  exact Finset.sum_congr rfl (fun j _ => by ring)

theorem neighbors_eq_of_digraph_eq (m : Model) {n : ℕ} (r y z : Fin n → ℝ)
    (hd : proximityDigraph m r y = proximityDigraph m r z) : neighbors m r y = neighbors m r z := by
  funext i
  ext j
  have := congrFun (congrFun (congrArg Digraph.Adj hd) i) j
  simp only [proximityDigraph] at this
  exact Iff.of_eq this

end HK
