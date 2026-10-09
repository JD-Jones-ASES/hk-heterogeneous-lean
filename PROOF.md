# The proofs, with the Lean names

The definitions are in `HK/Defs.lean`, identical to those of `Challenge.lean`. Each Challenge theorem is the
`_internal` theorem of the same name in the module named in VERIFICATION.md, restated in `Solution.lean`. Agents
are indexed `0, …, n − 1`; the paper's agent `i` is index `i − 1`. MB is Mirtabatabaei–Bullo (arXiv:1103.2829v2,
the text read; its numbering agrees with what HOW cite from the journal), HOW is Hegarty–Ognissanti–Wedin
(arXiv:2610.03229v1).

## 1. The models and the pinned definitions

`neighbors m r y i` is `{j : |yᵢ − yⱼ| ≤ bound}` over all `j`, with `Model.bound` equal to `rᵢ` (SBC) or `rⱼ`
(SBI): MB §2 with the non-strict inequality; `i ∈ Nᵢ(y)` follows from `rᵢ ≥ 0`, as in MB. `proximityDigraph` has
an arc `i → j` iff `j ∈ Nᵢ(y)`; `adjMatrix` has `aᵢⱼ = 1/|Nᵢ(y)|` on `Nᵢ(y)`; `step m r y = A(y) y` (MB (2.1));
`traj m r x₀ t = stepᵗ x₀`. `FixedFrom x τ`: `x t = x τ` for `t ≥ τ`. `PseudoStableAfter x xinf τ` (MB (2.2)):
`x → xinf`, and two non-empty classes `F`, `C` partition the agents so that for `t ≥ τ` the agents of `F` sit at
`xinf` and each agent of `C` has `xᵢ(t) < xᵢ(t+1) < xinfᵢ` or the mirror. The "or" is read at each `t`, which is
equivalent to choosing a side once per agent (a side, once taken, persists), and `Disjoint F C` follows from the
other clauses. Conjectures 2.2 and 2.3 and Theorem 6.4(iv) are stated for a model and an agent count
(`…ForAgents m n`), for a model (`…For m`, every `n`) and for both models, all with `r > 0`. Theorem 6.4(iv) has
two readings: `Theorem64ivLiteral…` (pseudo-stable from some `t₂ ≥ τ`) and `Theorem64iv…` (fixed or pseudo-stable
from some `t₂ ≥ τ`, the reading HOW's footnote 1 adopts). `fvct m r y = limUnder (A(y)ᵗ y)` (MB Definition 3.1)
is that limit whenever it exists, as it does at every use here. `perStepFactor` (Definition 6.1) is the quotient
`(xᵢ(t+1) − fvctᵢ(x(t)))/(xᵢ(t) − fvctᵢ(x(t)))`, total in Lean (`x/0 = 0`) and used only where the denominator is
nonzero. `equiTopologyDistance r z i = ½ · sInf {||zᵢ − zⱼ| − R| : j ≠ i, R ∈ {rᵢ, rⱼ}}` (Definition 4.1(i);
for `n = 1` the set is empty and `sInf ∅ = 0`), and `EquiTopologyNbhd r z y` asks `|yᵢ − zᵢ| < εᵢ(z)` where
`εᵢ(z) > 0` and `yᵢ = zᵢ` where `εᵢ(z) = 0`. The data of the four systems are HOW's, entry by entry.

**Conventions (`HK/Basic.lean`).** `step_apply` and `adj_mulVec` write `A(y) z` coordinatewise as the mean of `z`
over `Nᵢ(y)`. For `−1/6`: `pow_even`, `pow_odd`, `pow_bounds` (`−1/6 ≤ (−1/6)ᵗ ≤ 1`, positive at even `t`,
negative at odd `t`). For `λ = sbiRate = (1 − √5)/8`: `sbiRate_eq` (`λ = (1 − φ)/4`, `φ` the golden ratio),
`sbiRate_neg`, `sbiRate_abs_lt_one`, `sbiRate_pow_even`, `sbiRate_pow_odd`, `sbiRate_pow_bounds`
(`λ ≤ λᵗ ≤ 1`).

## 2. Closed forms and tables: the one-interval induction

Every trajectory here has the form `x_∞ + u v` with the atom `u = c λᵗ`. Each membership `|xᵢ − xⱼ| ≤ R` is then
affine in `u`, so one table lemma decides the whole neighbourhood table on an interval of `u` (`fin_cases` on `i`
and `j`, `abs_le`, `linarith`), and one step lemma shows that on that interval the step sends `x_∞ + u v` to
`x_∞ + (λu) v`: the mean of `x_∞` over each row is `x_{∞,i}` and the mean of `v` is `λ vᵢ`. Since `λᵗ⁺¹` lies in
the interval whenever `λᵗ` does, induction on `t` (`Function.iterate_succ_apply'`) gives the closed form, and the
table at every `t` follows from the closed form and the table lemma.

- **SBC, six agents (§4).** `sbc6_table` and `sbc6_step` on `−1/6 ≤ u ≤ 1`; `sbc6_closed_form_internal` with
  `pow_bounds`; `sbc6_neighbors_internal`. One table serves both parities.
- **SBI, the second seven-agent system (§5).** `sbi7b_table` and `sbi7b_step` on `(1 − φ)/4 ≤ u ≤ 1`. The
  positions involve the product `u φ`, bounded beforehand (`−1/4 ≤ u φ ≤ 2`, by `nlinarith` from `1 < φ < 2`); the step
  identity uses `φ² = φ + 1` (`Real.goldenRatio_sq`, `linear_combination`). `sbi7b_closed_form_internal` with
  `sbiRate_pow_bounds`; `sbi7b_neighbors_internal`.
- **SBC, seven agents (§2).** Two tables, `sbc7_table_even` on `0 < u ≤ 1` and `sbc7_table_odd` on
  `−1/6 ≤ u < 0`, which differ only in row 3 (`{3}` against `{2, 3, 4}`); `sbc7_step_even`, `sbc7_step_odd`;
  `sbc7_closed_form_internal` splits on `Nat.even_or_odd t` (`pow_even`, `pow_odd`); `sbc7_neighbors_internal`
  carries the `if Even t` row.
- **SBI, seven agents (§3).** Here `u = λᵗ/2`. `sbi7_table_even` on `0 < u ≤ 1/2` (row 3 is `{1, …, 5}`) and
  `sbi7_table_odd` on `λ/2 ≤ u < 0` (row 3 is `{2, 3, 4}`); `sbi7_step_of_table` takes either table;
  `sbi7_closed_form_internal` with `sbiRate_pow_even` and `sbiRate_pow_odd`; `sbi7_neighbors_internal`. The odd
  bound must be `λ ≤ λᵗ`: in terms of `λᵗ` the odd table holds exactly on `[√5 − 3, 0)`, so `λᵗ ≥ −1` would not do.

The digraph statements follow from the tables. `sbc6_digraph_constant_internal` and `sbi7b_digraph_constant_internal`:
the table at `t` equals the table at `0`. `sbc7_digraph_not_eventually_constant_internal`: at `t = τ + 1` the arc
`3 → 2` is present exactly when it is absent at `τ`; `sbi7_digraph_not_eventually_constant_internal` likewise with
the arc `3 → 1`. Convergence: `tendsto_of_closed_form` (`x(t) = L + a(t) v` with `a → 0` tends to `L`), with
`tendsto_pow_atTop_nhds_zero_of_abs_lt_one`; `sbc7_tendsto`, `sbi7_tendsto` and `tendsto_limits_internal`.

## 3. Alternating agents: no fixed state, no pseudo-stability

`alternating`: for `q < 0` and `c ≠ 0`, `qᵗ c · qᵗ⁺¹ c = q (qᵗ c)² < 0`. Write `x(t) = L + a(t) v` with
`a(t) a(t+1) < 0` for every `t`.

- `not_fixedFrom_of_closed_form`: if `vᵢ ≠ 0`, `xᵢ(τ+1) = xᵢ(τ)` forces `a(τ+1) = a(τ)`, against the sign
  condition, so the trajectory is in a fixed state from no `τ` on.
- `not_pseudoStable_of_closed_form`: in `PseudoStableAfter x xinf τ` the limit is `xinf = L`
  (`tendsto_nhds_unique`); take any agent `i` of the non-empty class `C`; at `t = τ` it would need
  `L + a(τ) vᵢ < L + a(τ+1) vᵢ < L` or the mirror, which `not_monotone_side` excludes when `a(τ) a(τ+1) < 0` (if
  `vᵢ = 0` a strict inequality fails; otherwise the two offsets have opposite signs). The class `F` is not used.

Each of the four systems has `vᵢ ≠ 0` at four agents (indices `1, 2, 4, 5` in the 7-agent systems, `1, 2, 3, 4` in
the 6-agent one), with `a(t) = (−1/6)ᵗ` or `λᵗ` (times `1/2` in §3). `sbc7_not_fixedFrom`,
`sbc7_not_pseudoStableAfter` (the same argument, agent by agent), `sbi7_not_fixedFrom`,
`sbi7_not_pseudoStableAfter`; for §4 and §5 the lemmas above are applied directly. Collected:
`not_fixedFrom_internal`, `not_pseudoStableAfter_internal`.

## 4. The refutations, per model and per agent count (`HK/Refute.lean`)

- **Conjecture 2.2.** `not_conjecture22_sbc_internal`: instantiate at `n = 7`, `sbc7_r` (positive: `sbc7_r_pos`)
  and `sbc7_x0`; every `τ` is defeated by `sbc7_digraph_not_eventually_constant_internal`.
  `not_conjecture22_sbi_internal` likewise with the §3 system. `not_conjecture22_sbc_seven_internal` and
  `not_conjecture22_sbi_seven_internal` are the same arguments at the fixed count `7`.
- **Conjecture 2.3.** `not_conjecture23_sbc_internal`, `not_conjecture23_sbi_internal`: the alternating systems are
  neither eventually fixed nor eventually pseudo-stable (§3 above).
- **Theorem 6.4(iv), the reading admitting fixed states.** `not_theorem64iv_sbc_internal`: the §4 system has a
  constant digraph from `τ = 0` (`sbc6_neighbors_internal`), and for every `t₂` it is neither fixed nor
  pseudo-stable from `t₂` on (`not_fixedFrom_of_closed_form`, `not_pseudoStable_of_closed_form` with
  `a(t) = (−1/6)ᵗ`). `not_theorem64iv_sbi_internal` likewise with §5 and `λ`.
- **Both models.** `not_conjecture22_internal`, `not_conjecture23_internal`, `not_theorem64iv_internal` apply the
  SBC refutations.
- **The literal reading.** `not_theorem64iv_literal_internal`: the literal reading implies the reading admitting
  fixed states (take the right disjunct), so it fails too. One agent frozen from the start also violates it, since
  both classes of (2.2) must be non-empty; that remark is not used.
- **Smaller agent counts.** `not_conjecture23_sbc_five_internal` and `not_theorem64iv_sbc_five_internal`
  (`HK/SBC5.lean`), `not_conjecture23_sbi_six_internal` and `not_theorem64iv_sbi_six_internal` (`HK/SBI6.lean`):
  the same arguments on the two smaller systems (§7 below).

## 5. The final value at constant topology and the per-step factor

Along the §4 trajectory the matrix `A = A(x(t))` is the same at every `t`; `sbc6_adj_lim` (`A x_∞ = x_∞`) and
`sbc6_adj_v` (`A v = −(1/6) v`) are the row means again, and `sbc6_adj_pow` gives `Aᵏ (x_∞ + c v) =
x_∞ + ((−1/6)ᵏ c) v` by induction (`Matrix.mulVec_mulVec`). With `x(t) = x_∞ + (−1/6)ᵗ v` the sequence `Aᵏ x(t)`
tends to `x_∞`, which is `sbc6_fvct_internal` (`Filter.Tendsto.limUnder_eq`). Then `xᵢ(t+1) − fvctᵢ = (−1/6)ᵗ⁺¹ vᵢ`
and `xᵢ(t) − fvctᵢ = (−1/6)ᵗ vᵢ ≠ 0` for `i ∈ {1, 2, 3, 4}`, so the quotient is `−1/6`
(`sbc6_perStepFactor_internal`, `field_simp`); a constant sequence tends only to its value, hence to no `ρ ≥ 0`
(`sbc6_perStepFactor_not_tendsto_internal`). The §5 system is the same with `λ` on the agents `1, 2, 4, 5`
(`sbi7b_adj_lim`, `sbi7b_adj_v`, `sbi7b_adj_pow`, `sbi7b_fvct_internal`, `sbi7b_perStepFactor_internal`,
`sbi7b_perStepFactor_not_tendsto_internal`); index 3 (the paper's agent 4) sits at its limit (`v₃ = 0`), where
Definition 6.1 defines no factor. In the alternating systems each of the two parity matrices fixes `x_∞` and scales
`v` by the rate (the step identities hold for both tables), so the same computation gives `fvct(x(t)) = x_∞` at
every `t` (`sbc7_fvct`, `sbi7_fvct`, `alternating_fvct_internal`).

MB's Theorem 6.4(iii)(a) asserts, under a constant digraph, that the per-step factor of such an agent converges to a
spectral radius, a non-negative number; the statements above contradict that conclusion for these agents. The
statement of 6.4(iii) itself is not formalized: its strongly connected components, leader components and spectral
radii (Definition 6.3) are not defined here.

## 6. Lemma 4.2, Lemma 4.8 and the sharpness of their hypothesis (`HK/Generic.lean`)

**Lemma 4.2** (`proximityDigraph_eq_of_equiTopologyNbhd_internal`). For `j ≠ i` and `R ∈ {rᵢ, rⱼ}`,
`εᵢ(z) ≤ ½ ||zᵢ − zⱼ| − R|` (`csInf_le`, the set bounded below by `0`). `abs_band_iff`: if `|a − c|` and `|b − d|`
are at most `½ ||c − d| − R|`, strictly when `|c − d| ≠ R`, then `|a − b| ≤ R ↔ |c − d| ≤ R`. Inside the band
`|a − b| ≤ |c − d| + |a − c| + |b − d| ≤ R`; on its edge both offsets are `0`; outside it `|a − b| > R`. A point of
the neighbourhood meets these bounds: where `εᵢ > 0`, `|yᵢ − zᵢ| < εᵢ`; where `εᵢ = 0`, `yᵢ = zᵢ`. For `j = i` both
memberships read `0 ≤ R`. No positivity of `r` is used.

**Lemma 4.8(i)** (`eventually_constant_of_tendsto_internal`). With every `εᵢ(x_∞) > 0`, convergence gives a `T`
with `|xᵢ(t) − x_{∞,i}| < εᵢ(x_∞)` for all `i` and `t ≥ T` (`Filter.eventually_all` over `Fin n`), and Lemma 4.2
applies. **(ii)** (`fvct_eq_and_equilibrium_of_tendsto_internal`): from `T` on, equal digraphs give equal
neighbourhoods (`neighbors_eq_of_digraph_eq`) and the matrix `A = A(x_∞)`, so `Aᵏ x(t) = x(t + k) → x_∞` and
`fvct(x(t)) = x_∞`; and `A x(t) = x(t+1)` tends both to `A x_∞` (continuity of `mulVec`) and to `x_∞`, so
`step x_∞ = x_∞`. For `n = 1` the hypothesis fails (`ε = 0`), so nothing is asserted there.

**The hypothesis on the four systems** (`HK/Refute.lean`). `equiTopologyDistance_pos_internal`: at the limits of §4
and §5 every distance is positive (the exact values are `5` at every agent, and `15/2, 5/2, …, 5/2, 15/2`).
`equiTopologyDistance_eq_zero_internal`: at the limit of §2 the distance vanishes at indices `2, 3, 4`
(`|84 − 72| = |96 − 84| = 12 = r₃`), and at the limit of §3 at indices `1, 3, 5`
(`|11 − 7| = |15 − 11| = 4 = r₁ = r₅`). The tool is `equiTopologyDistance_eq_zero_of` (one `j ≠ i` at distance
exactly `R` makes the infimum `0`); `equiTopologyDistance_eq_zero_three` covers index `3` of §2 and indices `1`, `5`
of §3. With `tendsto_limits` and the two non-constancy theorems this shows that the hypothesis of Lemma 4.8 cannot
be dropped for the digraph conclusion (i), while `alternating_fvct` shows that the `fvct` conclusion of (ii) still
holds along those systems. The §4 and §5 systems satisfy the hypothesis, and Theorem 6.4(iv) still fails along
them: the equi-topology condition does not restore 6.4(iv).

## 7. The two smaller systems (`HK/SBC5.lean`, `HK/SBI6.lean`)

- **Five SBC agents.** `x(0) = (0, 7, 12 − √2, 19, 24)`, `r = (3, 9, 9, 9, 3)`, `λ = (1 − √2)/3 ≈ −0.138`,
  `x(t) = (0, 6, 12, 18, 24) + λᵗ (0, 1, −√2, 1, 0)`. The table `{0}, {0, 1, 2}, {1, 2, 3}, {2, 3, 4}, {4}` holds
  for every `λᵗ ∈ [λ, 1]`, so one table serves both parities. The step identity uses `√2² = 2`, `3λ − 1 = −√2` and
  `λ √2 = (√2 − 2)/3`; `1.4 < √2 < 1.5` places `λ` in `(−1/6, 0)`. `sbc5_closed_form_internal`,
  `sbc5_neighbors_internal`, then `sbc5_tendsto`, `sbc5_digraph_constant`, `sbc5_not_fixedFrom` and
  `sbc5_not_pseudoStableAfter` (agents `1, 2, 3` alternate) by the lemmas of §3.
- **Six SBI agents.** `x_∞ = (0, 25, 31, 44, 55, 90)`, `v = (0, 10, −5 − √249, 8, 10, 0)/16`,
  `r = (45, 18, 27, 45/2, 27, 54)`, `x(0) = x_∞ + v`, `λ = (13 − √249)/40 ≈ −0.069`, a root of
  `λ² = (13/20) λ + 1/20`; `15 < √249 < 16` gives `−3/40 < λ < −1/20`. The table
  `{0}, {0, 1, 2, 3}, {0, 1, 2, 3, 4}, {0, 2, 3, 4, 5}, {2, 3, 4, 5}, {5}` holds for every `λᵗ ∈ [λ, 1]`.
  `sbi6_closed_form_internal`, `sbi6_neighbors_internal`, `sbi6_tendsto`, `sbi6_digraph_constant`,
  `sbi6_not_fixedFrom`, `sbi6_not_pseudoStableAfter` (agents `1, 2, 3, 4` alternate).

Collected in `HK/Refute.lean`: `small_tendsto_internal`, `small_digraph_constant_internal`,
`small_not_fixedFrom_internal`, `small_not_pseudoStableAfter_internal`.

The note proves on paper, and its certificates check, that within the class of trajectories eventually of the form
`x_∞ + λᵗ v` (`λ ∈ (−1, 0)` real, `v ≠ 0`, one neighbourhood pattern for each sign of `λᵗ`) every system has at
least five agents: the closed classes of the pattern are frozen cliques, there are at least two, and a transient
block of one or two agents has no eigenvalue in `(−1, 0)`. Exact searches over all patterns at five and six agents
(Fourier–Motzkin over `ℚ(λ)`) find four SBC patterns with a constant digraph at five agents, none in SBI at five
agents, 47 SBI patterns at six agents, and no alternating system at five or six agents in either model. None of
this is a Lean theorem, and nothing is claimed outside that class.

## Relation to the sources

What HOW prove about their four systems is proved here along their route (the closed form by induction on `t`, the
neighbourhoods checked at each step); the tables are their arc lists and parity descriptions, and the equi-topology
zeros are their §6 observations, completed to the full zero sets. HOW's spectator systems (§4, §5), which bear on
Theorem 6.4(iii)(b), and their §6 discussion of genericity are not formalized. MB's Lemmas 4.2 and 4.8 are proved
as MB state them but without their standing assumption `r > 0`, with Lemma 4.8's single time `T` split into two
existentials (equivalent). The two smaller systems and the note's results are this development's.
