# Arbitrarily weak heterogeneity still permits perpetual oscillation

Status: PROVEN-ON-PAPER. §4 is formalized in `HK/SBC5Family.lean` (`HK.sbc5Family_closed_form`, `HK.sbc5Family_neighbors`, `HK.sbc5_near_homogeneous`); §1, §2, §3 and §5 are paper proofs; certificate 0007 replays §4 and §5 exactly and §1 in 260-digit arithmetic for finite times.

The model is the synchronous unweighted SBC or SBI system with positive radii and the non-strict neighbourhood inequality. Agent indices start at zero.

## 1. A weakly connected SBC family at every size n >= 5

Fix an integer n >= 5, put m = n-1, and choose

    0 < delta < 1/2,
    r_0 = r_m = 1-delta,
    r_i = 1+delta for 1 <= i <= m-1.

For any integer k with

    2m/3 < k <= m-1,

define

    theta_k = k*pi/m,
    lambda_k = (1+2*cos(theta_k))/3,
    v_i = sin(i*theta_k), 0 <= i <= m,
    epsilon = delta/4,
    x_i(t) = i + epsilon*lambda_k^t*v_i.

Then -1/3 < lambda_k < 0. Both endpoints have v_i=0, and the initial offset is nonzero because v_1 != 0.

### Exact neighborhood table

For every t >= 0,

    N_0(t) = {0},
    N_m(t) = {m},
    N_i(t) = {i-1,i,i+1}, 1 <= i <= m-1.

In particular, the digraph is constant and weakly connected. It uses precisely two radius values and does not arise by adding disconnected spectator agents.

### Proof of the table

Write z=epsilon*lambda_k^t. Since |lambda_k|<1 and |v_i|<=1, |z|<=delta/4. Therefore, for every pair i,j,

    ||x_i(t)-x_j(t)|-|i-j|| <= |z|*|v_i-v_j| <= delta/2.

Consecutive agents have distance at most 1+delta/2<1+delta and at least 1-delta/2>1-delta. Thus each interior agent hears each existing immediate neighbor, whereas an endpoint hears no other agent. Nonconsecutive agents have distance at least 2-delta/2>1+delta; the final inequality uses delta<2/3, which follows from delta<1/2. Every inclusion and exclusion is strict, uniformly in t.

### Proof of the trajectory

The arithmetic progression L_i=i satisfies

    (L_{i-1}+L_i+L_{i+1})/3=L_i.

The sine addition identity gives

    v_{i-1}+v_i+v_{i+1}=(1+2*cos(theta_k))*v_i=3*lambda_k*v_i.

Consequently, averaging the three opinions at each interior row replaces z by lambda_k*z. The endpoint rows leave their coordinates unchanged. This proves the claimed closed form by induction from t=0.

### Consequences

The opinions converge to L. Every coordinate with v_i!=0 is strictly on opposite sides of its limit at consecutive times. Thus the system never freezes and is never eventually pseudo-stable.

Choosing k=m-1 makes

    lambda_* = (1-2*cos(pi/m))/3,
    v_i = (-1)^(i+1)*sin(i*pi/m), 1 <= i <= m-1.

All n-2 interior agents then have nonzero offsets and alternate forever. This supplies a weakly connected example at **each** n>=5, with a single negative real mode and strictly separated confidence thresholds. The n = 5, k = 3 member has the rate (1-sqrt2)/3 and the mode (0,1,-sqrt2,1,0) of S1 (S1 itself has radii (3,9,9,9,3) and amplitude 1, outside this parametrization); the eigenpairs (1+2cos(k pi/m))/3 with sine vectors are the standard spectrum of the nearest-neighbour path, and the content here is their realization as an HK system. The proof uses only delta < 2/3 and delta < 1.

## 2. The attainable negative factors are dense in (-1/3,0)

The preceding construction realizes every number

    (1+2*cos(pi*k/m))/3,
    m>=4, 2/3<k/m<1.

Rational numbers k/m in (2/3,1) are dense in that interval, and the displayed continuous strictly decreasing map takes (2/3,1) onto (-1/3,0). Hence these realized per-step factors are dense in (-1/3,0).

This is a density statement for the union of finite-size families. It is not a claim that every negative real number in that interval is an eigenvalue of a finite unweighted averaging matrix; such matrix eigenvalues must be algebraic, whereas the interval contains transcendental numbers.

## 3. There is no positive uniform near-homogeneity threshold

In this construction,

    max_i r_i / min_i r_i = (1+delta)/(1-delta) -> 1

as delta decreases to zero. Consequently, for every eta>0 and every n>=5, there is a positive-radius SBC system satisfying

    max_i r_i / min_i r_i < 1+eta

whose graph is constant and weakly connected but whose trajectory fails eventual pseudo-stability.

An explicit choice is any

    0 < delta < min(1/2, eta/(2+eta)).

The negative mode and n can stay fixed while delta decreases. Only the radius gap and perturbation amplitude need shrink.

The quantifiers matter: this disproves a universal guarantee based solely on a sufficiently small radius ratio. It does not say that every perturbation of a fixed homogeneous system is bad, or that a positive-measure set of initial states is non-pseudo-stable. As delta tends to zero, the constructed states approach a threshold configuration where graph continuity fails.

## 4. A five-agent specialization avoiding trigonometry

This version uses the vector of S1 (`HK/SBC5.lean`). Let

    L = (0,6,12,18,24),
    v = (0,1,-sqrt(2),1,0),
    lambda = (1-sqrt(2))/3,
    0 < d <= 1,
    r(d) = (6-3d,6+3d,6+3d,6+3d,6-3d),
    x(t) = L + d*lambda^t*v.

The constant table is

    {0}, {0,1,2}, {1,2,3}, {2,3,4}, {4}.

For |u|<=1, consecutive opinion differences differ from six by at most (1+sqrt(2))*d<3d. Endpoint-to-nearest distances are at least 6-d>6-3d. For nonconsecutive pairs, the crude bound 12-2*sqrt(2)*d>6+3d holds because d<=1 and 2*sqrt(2)+3<6. These inequalities establish the table for u=lambda^t. The eigenvector identities then give the exact evolution. S1 is d=1. The table holds exactly for d < 6/(3+sqrt(2)) (about 1.359, where agent 2 starts to hear agent 0); d<=1 is what the crude bound gives.

Here

    max r/min r = (2+d)/(2-d),
    max r/min r - 1 = 2d/(2-d) <= 2d.

Thus taking d=min(1/2,eta/4) gives a ratio strictly below 1+eta. The trajectory, neighborhood table, and quantified near-homogeneity conclusion are formalized by `HK.sbc5Family_closed_form`, `HK.sbc5Family_neighbors`, and `HK.sbc5_near_homogeneous` in the compared interface.

## 5. The same near-homogeneity conclusion for SBI with six agents

This family is built on the limit and the mode of the note's S2, which has a coincident pair of agents; S2 itself (radii r(1/2), amplitude 1/16) is not a member, since the family's amplitude at delta = 1/2 would be 1/32. It is independent of the five-agent SBI system with complex modes.

Let

    s = sqrt(17), lambda = (3-s)/8,
    L = (0,2,3,3,4,6),
    v = (0,4,1-s,1-s,4,0),
    0 < delta < 1/2,
    epsilon = delta/16,
    r = (2+delta,2-delta,2-delta,2-delta,2-delta,2+delta),
    x(t) = L+epsilon*lambda^t*v.

The constant SBI neighborhood table is

    N_0={0},
    N_1={0,1,2,3},
    N_2=N_3={1,2,3,4},
    N_4={2,3,4,5},
    N_5={5}.

The underlying graph is weakly connected. Agents 2 and 3 coincide for all time, but all four interior agents have nonzero alternating deviations.

### All distance checks

Write z=epsilon*lambda^t, so |z|<=delta/16, and use 4<s<5.

* The nearest anchor/interior distances are 2+4z and 2-4z. Both lie strictly between 2-delta and 2+delta. Thus the anchors influence their nearest interior agents, while the reverse arcs are absent.
* Distances between a middle clone and the nearest anchor are 3+(s-1)z or 3-(s-1)z. These exceed 3-delta/4>2+delta. Thus no anchor influences a clone, and a clone does not influence an anchor.
* The distance between the two outer interior agents is exactly 2, exceeding their radii 2-delta.
* The outer-interior-to-clone distances are 1+(s+3)z and 1-(s+3)z. They are below 1+delta/2<2-delta and remain positive.
* The clone-to-clone distance is zero. Anchor-to-opposite-outer distances are at least 4-delta/4>2+delta; the anchor-to-anchor distance is six.

These exhaust distinct position types and give the displayed table.

### The row means

The limit row means reproduce L. On v, the outer rows have mean

    [4+2(1-s)]/4 = (3-s)/2 = 4*lambda,

and the clone rows have mean

    [4+2(1-s)+4]/4 = (5-s)/2 = lambda*(1-s),

where s^2=17. Endpoints remain zero. This proves the closed form.

The radius ratio is (2+delta)/(2-delta), which tends to one. Thus **both SBC and SBI** admit perpetual non-pseudo-stable oscillation with positive radii having arbitrarily small relative spread. The SBI assertion needs six agents in this construction; it makes no minimality claim under the additional near-homogeneity requirement. The table holds exactly for delta <= 16/(19+sqrt(17)) (about 0.692); delta < 1/2 is what the crude bounds give.

## 6. Relation to the sources

Hegarty, Ognissanti and Wedin (arXiv:2610.03229v1) give constant-digraph oscillating counterexamples with six and seven agents, note "some wiggle-room in the choice of the precise numbers" (Remark 2.1) without pursuing it, and state in their introduction that the homogeneous model freezes in finite time; they do not discuss the spread of the radii or families in n. Mirtabatabaei and Bullo (arXiv:1103.2829v2) supply the models and the definitions; their simulations use 10 to 100 agents. Along their trajectories the SBC systems of §1 and §4 are homogeneous HK systems with two closed-minded agents in the sense of Chazelle and Wang (*Inertial Hegselmann-Krause systems*, IEEE Trans. Automat. Control 62 (2017) 3905-3913): the endpoints never hear anyone and the interior agents share one radius; for that class Chazelle and Wang prove convergence and, in one dimension, an eventually constant network, and note that it need not freeze. The families above are this development's; no search of the literature beyond these sources is claimed.

The main convergence conjecture remains untouched: every constructed trajectory converges explicitly. These examples also have constant topology, so they do not extend the seven-agent refutations of eventual topology constancy.
