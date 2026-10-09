# A five-agent SBI trajectory with complex modes and uniformly recurring sign changes

**Label: PROVEN-BY-CERTIFICATE (construction, all times); PROVEN-ON-PAPER (lower bound in Section 6).** The construction and all-time proof below are elementary exact mathematics. The accompanying standard-library certificate `verify.py` checks its finite algebraic and inequality obligations, independently replays the actual SBI update through time 200, and rejects forged controls. The all-time conclusion rests on the invariant-cube induction and the recurrence argument, not on the finite replay. The lower-bound theorem in Section 6 is a paper proof, separate from this certificate and from any Lean formalization.

**Lean coverage.** `HK/SBI5Complex.lean` proves the construction's trajectory, constant topology, convergence, five-window oscillation, and the failure of eventual freezing and of eventual pseudo-stability (verification status: [VERIFICATION.md](../../../VERIFICATION.md)). No Lean claim is made here for the general lower bound in Section 6.

This construction lies outside the note's single-negative-mode class `L + lambda^t v`, in which the least SBI order with a constant digraph is six (note/README.md, B).

## 1. Exact system

Indices are 0 through 4. Let `rho` be the real root in `(57/100, 29/50)` of

\[
 p(s)=60s^3-47s^2+9s-1.
\]

The root exists because

\[
 p(57/100)=-359/12500<0,
 \qquad p(29/50)=1449/12500>0.
\]

The cubic discriminant is `-51683`, so this is its unique real root. Numerically, only for orientation, `rho = 0.57204906048946989...`.

Take

\[
 L=(0,10,18,20,42),\qquad r=(31,9,5,15,28),
\]

and

\[
 x(0)=\left(0,\frac{31}{3}-\rho,\frac{91}{5},20,42\right).
\]

At every time the SBI neighborhood masks are

\[
 P=(1,11,31,29,16),
\]

meaning

\[
 N_0=\{0\},\quad N_1=\{0,1,3\},\quad
 N_2=\{0,1,2,3,4\},\quad N_3=\{0,2,3,4\},\quad N_4=\{4\}.
\]

The transient block on agents 1, 2, 3 is

\[
 Q=\begin{pmatrix}
 1/3&0&1/3\\
 1/5&1/5&1/5\\
 0&1/4&1/4
 \end{pmatrix}.
\]

Put

\[
 z=(1/3-\rho,1/5,0)^T=(Q-\rho I)e_1.
\]

Here `e_1=(1,0,0)^T` in the transient coordinate system. The trajectory is

\[
 x(t)=L+(0,(Q^tz)_1,(Q^tz)_2,(Q^tz)_3,0).
\]

## 2. Strict invariant cube and convergence

The listed averaging matrix fixes `L`, as the three transient equations are

\[
 (0+10+20)/3=10,\qquad
 (0+10+18+20+42)/5=18,\qquad
 (0+18+20+42)/4=20.
\]

For every ordered pair of distinct agents, the SBI membership inequality at `L` has slack at least 1. The minimum is exactly 1. Examples of the tight inequalities are `10 > r_1=9` for `(i,j)=(0,1)` and `(3,1)`, and `|18-10|=8 < r_1=9` for `(2,1)`.

Consequently, any vector differing from `L` by less than `1/3` in every coordinate has the same digraph: a pairwise distance changes by less than `2/3`, smaller than the minimum slack.

The initial transient deviation satisfies `||z||_infinity < 1/3`. The row sums of `Q` are `2/3`, `3/5`, and `1/2`, all nonnegative. Thus

\[
 \|Q^t z\|_\infty\le (2/3)^t\|z\|_\infty
 <\frac13(2/3)^t.
\]

Induction proves the asserted constant digraph and trajectory for every nonnegative integer time. It also proves convergence to `L` with the displayed error bound.

## 3. The real recurrence that removes the Perron mode

The characteristic polynomial of `Q` is `p(s)/60`. Define

\[
 \alpha=\frac{47}{60}-\rho,
 \qquad
 \beta=\rho^2-\frac{47}{60}\rho+\frac3{20}
       =\frac1{60\rho}.
\]

Then

\[
 p(s)/60=(s-\rho)(s^2-\alpha s+\beta).
\]

Since `z=(Q-rho I)e_1`, Cayley-Hamilton gives

\[
 (Q^2-\alpha Q+\beta I)z=0.
\]

This identity can also be checked directly, which is what the certificate does. Multiplication by `Q^t` shows that every transient coordinate deviation `y_t` obeys

\[
 y_{t+2}=\alpha y_{t+1}-\beta y_t.
\]

The root interval supplies rational bounds

\[
 \frac{61}{300}<\alpha<\frac{16}{75},\qquad
 \frac5{174}<\beta<\frac5{171}.
\]

In particular,

\[
 0<\beta<\alpha^2<2\beta.
\]

The strict comparisons follow from the exact positive margins

\[
 (61/300)^2-5/171=20699/1710000,
\]

\[
 2(5/174)-(16/75)^2=1951/163125.
\]

The quadratic roots are a complex conjugate pair. Numerically they are approximately `0.1056421364 ± 0.1340700162 i`, with modulus `0.1706898656`. These approximations play no role in the proof.

## 4. A stronger oscillation theorem: every five consecutive times contain both signs

**Recurrence lemma.** Suppose

\[
 y_{t+2}=\alpha y_{t+1}-\beta y_t,
 \qquad \alpha>0,\quad 0<\beta<\alpha^2<2\beta,
\]

and the initial pair `(y_0,y_1)` is not `(0,0)`. Then, for every `t`, the five values `y_t,...,y_{t+4}` contain a strictly positive value and a strictly negative value.

**Proof.** Iterating the recurrence gives

\[
 y_{t+4}=\alpha(\alpha^2-2\beta)y_{t+1}
          +\beta(\beta-\alpha^2)y_t.
\]

Both coefficients on the right are strictly negative. No adjacent pair can be zero: since `beta>0`, a zero adjacent pair propagates backward to the nonzero initial pair. If a five-term block were all nonnegative, its first two terms would be nonnegative and at least one would be positive. The displayed identity would force its last term to be negative. The same argument applied to `-y` excludes an all-nonpositive block. This proves the claim.

For agents 1 and 2, the initial deviations are nonzero. For agent 3, the initial deviation is zero but the next deviation is

\[
 (Qz)_3=1/20\ne0.
\]

The lemma therefore applies to **all three** transient agents. Each of agents 1, 2, 3 is strictly above and strictly below its own limit in every five-time window. Agents 0 and 4 are frozen. This disproves eventual pseudo-stability despite a graph that is constant from time zero.

For illustration, the first 25 exact signs of `x_i(t)-L_i` are

- agent 1: `---++++---++++---++++---+`;
- agent 2: `+----+++----+++----+++---`;
- agent 3: `0+++---++++---++++---++++`.

These sign strings illustrate the theorem and are not its proof. In particular, no periodic sign pattern is being asserted.

## 5. Verification and provenance

Run from this certificate directory:

```text
python -I verify.py
python -I -O verify.py
```

(Python 3.9+, standard library; about 1.5 s each on the PC.)

The verifier uses rational arithmetic and a degree-three number field, with exact signs obtained by rational interval refinement around `rho`. It first checks that its data and root bracket are the ones stated here. It checks irreducibility by the rational-root test, the root bracket and discriminant, all limit margins, the harmonic limit, the contraction bound, both recurrence identities, and the nonzero initial coordinate pairs. Its independent replay computes neighborhoods from the SBI distance rule rather than assuming the proposed masks.

It rejects two forged controls: changing the second radius from 9 to 15, and shifting the first transient deviation by `1/100`, which destroys the quadratic recurrence and hence the Perron cancellation. A third control runs the replay itself with `rho` replaced by the rational `4/7`, inside the bracket: the digraph stays constant and the deviations still tend to zero, but the uncancelled Perron mode takes over and the replay's five-window sign check rejects the run, first at window `[3, 7]` for agent 1; the same exact run is then reported one-sided, every agent strictly above its limit from `t = 3, 5, 7` (agents 1, 2, 3) through 200. The script exits 1 with a `FAIL:` line naming the failed check if anything does not hold.

Last lines of a run:

```text
Forged control rejected: rho replaced by the rational 4/7 in the replay -> five-window sign theorem replay: agent 1, window [3, 7]
rho = 4/7 (same digraph, exact): agent, sign, one-sided from t through 200: [(1, '+', 3), (2, '+', 5), (3, '+', 7)]
VERDICT: PASS
```

Reflecting and reversing the agent labels gives the mirror system, with masks `(1,23,31,26,16)`.

## 6. Five is the least count among eventually constant-digraph systems, in either model

**Theorem.** For SBC or SBI with positive radii and at most four agents, every trajectory whose proximity digraph is eventually constant eventually reaches a fixed state or becomes pseudo-stable. Consequently, five is the least number of agents, in each model, for a trajectory with an eventually constant digraph that is neither eventually fixed nor eventually pseudo-stable (a counterexample to Conjecture 2.3, or to Theorem 6.4(iv) in the reading admitting fixed states; the literal reading of 6.4(iv) fails already for one frozen agent): the five-agent SBC system S1 of the note (`HK.not_theorem64iv_sbc_five`, `r = (3,9,9,9,3)`) attains it for SBC and the construction above (`HK.not_theorem64iv_sbi_five`) for SBI.

**Scope.** The theorem assumes eventual constancy of the digraph. It does not assert topology stabilization for all systems of order at most four, nor exclude an unrestricted counterexample with endlessly changing topology. It covers arbitrary initial data and arbitrary mixtures of linear modes once the topology becomes constant; it is not restricted to one real negative eigenmode.

**Proof.** The zero-agent case is trivially fixed, so assume at least one agent. Let the digraph be constant from `tau` on and let `A` be its averaging matrix: row-stochastic with positive diagonal (every agent hears itself). Every closed class of `A` is aperiodic, since each of its states has a self-loop, and every transient state leads to a closed class, so the transient block has spectral radius below 1; by the Perron–Frobenius theorem on each closed class and the canonical decomposition of a stochastic matrix, `A^t x(tau)` converges to a vector `L` with `A L = L`.

On each closed class `C`, `L` is constant. Since all radii are positive and the agents of `C` converge to the same value, every agent of `C` hears every other one at all large times; the digraph being constant from `tau`, it does so at every `t >= tau`. Closedness forbids any other outgoing arc, so `N_i = C` for `i` in `C` and `t >= tau`: the class averages to its common value at `tau+1` and is frozen, at `L_C`, from then on. Moreover, no agent outside `C` can share its limit: at all large times its distance from each member of `C` would be below the relevant positive radius, giving an arc out of `C`, against closedness. In particular, distinct closed classes have different limits.

If there is only one closed class `K`, every agent's limit equals `K`'s common value (the limit of `A^t` sends every transient agent to `K`), so by the previous paragraph every agent lies in `K`: the whole system is one closed clique, fixed from `tau+1` on. Otherwise there are at least two closed classes, occupying at least two agents. With at most four agents, the transient block `Q` thus has dimension at most two.

For `t >= tau+1` the closed cliques sit at `L_C`, and `A L = L`, so the deviations `u = x_T - L_T` of the transient agents obey `u(t+1)=Q u(t)`. A transient agent hears at least one other agent (otherwise it would be a closed class of its own), so every diagonal entry of `Q` is at most `1/2`. For one transient agent, `Q=(a)` with `0<a<=1/2`. For two transient agents,

\[
 Q=\begin{pmatrix}a&b\\c&d\end{pmatrix},
 \qquad a,d>0,\qquad b\in\{0,a\},\quad c\in\{0,d\}.
\]

If either off-diagonal entry is zero, `Q` is triangular. Its coordinate sequences are linear combinations of `a^t` and `d^t`, or, when `a=d`, expressions `(c_1+c_2 t)a^t`, with bases in `(0, 1/2]`. Every such sequence is either identically zero or has an eventual nonzero sign and an eventual difference of the opposite sign: if `f(t) = sum_k p_k(t) lam_k^t` with distinct `lam_k` in `(0,1)` and `c t^m lam^t` is its dominant nonzero term, then `f(t) ~ c t^m lam^t` and `f(t+1) - f(t) ~ c (lam - 1) t^m lam^t`, so `f` eventually has the sign of `c` and moves strictly towards `0` (the positivity of the bases is what makes this true; a negative base such as `(1 - sqrt 2)/3` alternates). Thus each coordinate approaches zero strictly monotonically from one side after a sufficiently large time, which cannot be bounded in terms of `tau`: when `a = d` the offset `(c_1 + c_2 t) a^t` changes sign at `t = -c_1/c_2`.

If both off-diagonal entries are nonzero, then

\[
 Q=\begin{pmatrix}a&a\\d&d\end{pmatrix},
 \qquad Q^2=(a+d)Q,
\]

where `0<a+d<=5/6`: the two agents hear each other, and the pair is not closed, so one of them has at least three neighbours. From `tau+2` on, every coordinate is therefore a fixed coefficient times `(a+d)^t`; it either freezes or approaches its limit strictly monotonically.

Choose a time `t_2 >= tau+1` after which all coordinates have their eventual behaviour. If all coordinates are frozen, the state is fixed from `t_2` on. Otherwise take the frozen agents as the class `F` (non-empty: it contains a closed clique) and the remaining agents as the class `C` (non-empty); every member of `F` sits at its limit and every member of `C` moves strictly towards its limit from one side at every `t >= t_2`, which is pseudo-stability after `t_2` as pinned, with `t_2 >= tau` as Theorem 6.4(iv) asks. This proves the theorem.

**Formalization boundary.** The SBI5 trajectory, constant topology, convergence, every-five-window oscillation, and the failure of eventual freezing and pseudo-stability are formalized in `HK/SBI5Complex.lean`, using real polynomial arithmetic, a root supplied by the intermediate value theorem, and the scalar recurrence. The lower bound of this section is a paper proof; its formalization would need the convergence of the powers of a stochastic matrix with positive diagonal, or a direct finite argument. Certificate 0008 checks its structural consequences exhaustively on every neighbourhood pattern with at most four agents.
