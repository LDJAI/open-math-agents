# Exact Steiner trees and the limits of local flow constraints

**Research status, November 26, 2026.** A polynomial-time exact algorithm for Steiner tree on arbitrary undirected graphs with nonnegative, binary-encoded integer edge costs would imply $P=NP$. The converse follows by binary-searching the integer optimum with the decision problem, then deleting dispensable edges while preserving feasibility at that cost. Clay continues to list the underlying problem as open. This note gives a checkable obstruction to one specific algorithmic approach. [Clay Mathematics Institute](https://www.claymath.org/millennium/p-vs-np/) · [Karp, 1972](https://www2.seas.gwu.edu/~simhaweb/champalg/tsp/papers/KarpOriginal.pdf)

## An exact reduction that suggests an algorithm

Given a graph $H$, make one optional hub for every vertex, one required terminal for every edge, and a required root. Join the root to every hub and join each edge-terminal to its two endpoint hubs. Give every edge unit cost. If $q=|E(H)|$ and the minimum vertex-cover size of $H$ is $\tau(H)$, the exact Steiner optimum is

$$
q+\tau(H).
$$

Every connected solution must use a vertex cover of hubs to reach the terminals. A tree with $q+1$ required vertices and $k$ additional hubs has $q+k$ edges. Conversely, from any cover, attach its hubs to the root and each terminal to one chosen endpoint. This constructs a tree of that cost. The resulting bipartite network has routes of length two from the root to every terminal. A polynomial-time algorithm exact even on this architecture would solve Vertex Cover in polynomial time. Karp called the latter decision problem NODE COVER in his original reductions.

A natural approach is to select the cheapest common infrastructure that routes one unit independently to every terminal. Each terminal has its own flow. The paid arc can carry one unit of *each* commodity. Fixed-order Sherali–Adams lifts can strengthen the relaxation in polynomial time. The following construction tests whether enough fixed-order consistency can make this approach exact.

## Proposition

Replace each undirected edge by two directed arcs. Use a binary installation variable $z_a$ for each arc and binary $f_{a,t}$ for the flow of each nonroot terminal $t$. Impose unit flow conservation from the root to $t$, $0\le f_{a,t}\le z_a\le1$, and the variable bounds. Minimize $\sum_a z_a$ on unit-cost instances. An integral feasible solution connects every terminal in its undirected support. Conversely, orienting an optimum tree away from the root gives an integral solution with the same cost.

For every nonnegative integer $d$, on an explicit graph the LP obtained by multiplying these constraints by all products of up to $d$ binary literals and linearizing admits a feasible objective value exactly **one whole unit below** the integer optimum. Here a literal is a variable or its complement, and repeated variable powers are reduced using $x^2=x$. This convention specifies the lift independently of how authors number the first round.

### Construction

Write $r=d+2$ and $m=2r$. Take $H=K_m$ in the reduction and set $q=\binom m2$. At most one hub can be absent from a cover, so the true optimum is $q+m-1$.

Let $T_0$ open every hub and $T_i$ open every hub except $i$, for $1\le i\le m$. In each state, install the arc from the root to every open hub. The terminal for a pair $i<j$ receives a single arc from $i$ if $i$ is open and otherwise from $j$. Give that terminal its unit of flow along the corresponding two-arc path. Every state is a feasible directed tree, even if an optional leaf is unnecessary.

For every multilinear polynomial $p$ in the installation and flow variables, put

$$
 L(p)=\left(1-\frac m r\right)p(T_0)+\frac1r\sum_{i=1}^m p(T_i).
$$

The coefficient of $T_0$ is negative. Suppose a function $g$ is nonnegative in every state and $g(T_i)=g(T_0)$ outside a set $S$ of at most $r$ indices. Then

$$
 L(g)=\left(1-\frac{|S|}r\right)g(T_0)+\frac1r\sum_{i\in S}g(T_i)\ \ge 0.
$$

Each installation or flow variable differs from its baseline at **at most one omitted hub**. A root-to-hub installation changes only when that hub is missing. A terminal attachment or either of its two possible flow paths changes only when its preferred endpoint is missing. Reverse arcs and irrelevant commodities stay zero.

Consequently each capacity slack $z_a-f_{a,t}$ depends on at most two exceptional indices. A variable-bound slack depends on at most one. Multiplying either slack by $d$ literals gives a pointwise nonnegative function with at most $d+2=r$ exceptional indices, hence nonnegative signed expectation. Each flow conservation equation vanishes pointwise, even though it can mention many arcs. It continues to vanish after multiplication by any literal product. Finally $L(1)=1$. Multilinear reductions are valid on all the binary states. Assigning every moment the value of $L$ on its monomial therefore satisfies the entire stated lift.

The baseline costs $q+m$ and each one-deletion tree costs $q+m-1$. The feasible lifted objective value is

$$
 L(\mathrm{cost})=q+m-\frac m r=q+m-2.
$$

Even rounding the lifted optimum up to the nearest integer cannot recover the exact optimum, since the exhibited feasible objective value is already one whole unit below it. This proves the proposition.

## Transfer from any vertex-cover instance

There is a direct explanation using the ordinary vertex-cover relaxation on **any** graph $H$. Let its binary variables be $x_i$ with $x_i+x_j\ge1$ for every edge. On the constructed Steiner graph install the root-to-$i$ arc with value $x_i$. At the terminal for $i<j$, install its incoming arc from $i$ with value $x_i$ and the arc from $j$ with value $1-x_i$. Route that terminal's unit commodity along the two corresponding paths with these same values. Set unused variables to zero.

All flow equalities hold identically. The fallback path obeys the root-to-$j$ capacity exactly when $1-x_i\le x_j$, the original cover inequality. Every other capacity slack is a variable bound, zero, or the slack of a cover inequality. Each Steiner variable becomes a cover variable, its complement, or a constant. After substitution each lifted inequality therefore follows from a cover inequality or bound lifted by at most the same number of literals. The substitution is also compatible with Boolean multilinearization. The resulting objective is $q+\sum_i x_i$.

Thus any feasible degree-$d$ system of cover moments maps to feasible moments in the full Steiner flow formulation at the same degree, including the flow-variable moments. In particular, any additive gap for that cover formulation survives as at least the same additive gap for the Steiner formulation. This concerns additive gaps since the objective incurs the fixed cost $q$.

## Independent finite checks

Run `python3 verify_steiner.py` in this directory. It computes each integer optimum by enumerating hub subsets and testing graph connectivity, constructs the directed trees and flows, and verifies every distinct truth table obtained from the lifted inequalities using integer arithmetic. The mathematical argument covers arbitrary $d$.

| Literal degree | Hubs | Total graph vertices | Integer optimum | Feasible lifted value |
| --- | ---: | ---: | ---: | ---: |
| 0 | 4 | 11 | 9 | 8 |
| 1 | 6 | 22 | 20 | 19 |
| 2 | 8 | 37 | 35 | 34 |
| 3 | 10 | 56 | 54 | 53 |
| 4 | 12 | 79 | 77 | 76 |
| 5 | 14 | 106 | 104 | 103 |

Degrees 0 through 3 run by default. For all six rows use `python3 verify_steiner.py 0 1 2 3 4 5`.

## Prior work and remaining obstacle

The set-cover construction, gaps for the bidirected cut relaxation, and Sherali–Adams gaps for vertex cover all have prior literature. The calculation above was derived for this investigation. Priority for this particular transfer to the full flow-variable formulation has not been established. It gives a certificate against a proposed proof strategy. The proof applies to exactly the stated flow formulation and lift. Other formulations, global valid inequalities, and different exact algorithms are outside its scope. The graph family $H=K_m$ itself has the elementary exact formula above. The corresponding exact algorithm on arbitrary $H$, and therefore the requested general solution, remain unresolved. [Könemann, Pritchard and Tan, section 5.1](https://www.math.uwaterloo.ca/~jochen/docs/zel-jour.pdf) · [Charikar, Makarychev and Makarychev, 2009](https://d3ccyth396mz21.cloudfront.net/publications/integrality-gaps-for-sherali-adams-relaxations) · [Byrka, Grandoni and Traub](https://doi.org/10.1137/24M1717725)
