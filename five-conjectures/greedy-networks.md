# Shortening a cycle block in a network creation game

In the unilateral sum network creation game, each player buys incident edges at a common price and pays the sum of its distances to everyone else. Any change preserving the number of purchased edges has the same link cost as before. Pascal Lenzner proved that a sum-asymmetric swap equilibrium with exactly one cycle has cycle length at most five. The following minimum-pair proof yields the block version directly. [Lenzner, *On Selfish Network Creation*, Theorem 5.3.1](https://hpi.de/friedrich/docs/publications/2014/Lenzner.pdf)

**Proposition.** Let a block of a connected finite graph be a simple cycle of length at least six. For every assignment of single ownership of its edges to their endpoints, some player can strictly decrease its distance cost by replacing one of the cycle edges it owns. In particular, no such cycle block occurs in a Nash equilibrium, whatever the link price.

**Proof.** Delete the cycle edges. The components meeting the cycle each meet it at exactly one vertex, since the cycle is a block. For each cycle vertex $i$, let $w_i$ be the size of its component, including $i$. A path from a cycle vertex into this component can enter it only at $i$, so any change in distance to $i$ is incurred once per member of that component.

Choose a cycle edge $ab$ minimizing $w_a+w_b$ and write the four consecutive vertices, in the direction from its buyer to the other endpoint, as $a,b,c,d$. This naming makes $a$ the buyer. Replace $ab$ by $ac$. The distance from $a$ to $b$ rises by one and the distances to $c,d$ each fall by one. The latter uses the cycle length of at least six, which gives original distances two and three. No other distance to a cycle vertex rises. An old shortest path avoiding $ab$ still exists, and one starting $a,b,c$ can now start $a,c$. Thus the decrease in distance cost is at least

$$w_c+w_d-w_b\ \ge\ w_a>0,$$

by the minimality of the adjacent pair $a,b$. The number of purchased edges stays the same. This proves the proposition.

Every cycle of a cactus graph is a block. Hence a cactus with any cycle of length at least six fails to be an equilibrium, even when shorter cycles coexist elsewhere in the graph. A cyclic equilibrium of girth at least six must have a cyclic block with overlapping cycles. The argument uses the same weighted-cycle reduction as Lenzner's theorem, and no independent priority for this corollary is asserted.

## Screening overlapping cycles

We next allowed an arbitrary positive weight $w_i$ at each vertex of a core. Distances within an attached component do not affect a core player's incentive to change an edge of the core. Normalize $\sum_i w_i=1$ and optimize the smallest weight over continuous weights and binary edge-ownership variables. Each permitted swap produces a linear inequality in the weights conditional on who pays for the edge.

The core search comprised 7 cycles of lengths 6 through 12, 33 theta graphs with three or four internally disjoint paths between two endpoints, and 22 subdivisions of the complete graph on four vertices. All 62 instances had girth at least six. Eight theta graphs passed all one-edge swap inequalities with strictly positive weights. For each of those eight we imposed single-edge addition and deletion constraints with one common price. We also separated simultaneous deviations at candidate optima. None survived the priced screening with positive minimum weight. These are floating-point MILP search results and are reported as computational leads. They supply neither a proof of the full conjecture nor a verified equilibrium.

For implementation details, see `weighted.py`, `price.py` and the two named log files. The scripts import the companion core and distance utilities in `../network/screen.py`. Running `python3 weighted.py` before `python3 price.py` generates the intermediate candidate JSON files. SciPy with the HiGHS MILP solver and NumPy are required.

## Exact profiles that pass every one-edge test

A 15-vertex profile of girth six and a 20-vertex profile of girth eight passed *all* elementary deviations in the original, unweighted network, including deviations by the pendant vertices. The profiles make it possible to test how far a counterexample search based on elementary deviations can go.

| Vertices | Girth | Exact price interval for greedy equilibrium | Elementary deviations checked | Price for full test | All candidate strategies across players | Best saving |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 15 | 6 | $[14,14]$ | 372 | 14 | 135,168 | 7 |
| 20 | 8 | $[22,30]$ | 689 | 24 | 6,029,312 | 14 |

In the 20-player graph, form three paths from 0 to 1 with interior vertices $(2,3,4)$, $(5,6,7)$ and $(8,9,10)$. Attach three pendant vertices to each of 3, 6 and 9. The two outer interior vertices of each path purchase both their incident path edges. Each parent buys its pendant edges. At any price in $[22,30]$, no player profits from adding one edge, deleting one edge, or replacing one edge with one other edge. But player 10 can replace both its edges to $\{1,9\}$ by edges to $\{3,5\}$. Its distance sum drops from 55 to 53 while its link cost stays fixed. This rules out Nash equilibrium for the displayed profile at *every* price. At price 24 the best move from this player instead buys just the link to 0, saving 14.

In the 15-player profile, player 8 can replace $\{1,7\}$ by $\{3,6\}$ and reduce its distance sum from 35 to 34 at unchanged link cost. At price 14 the best move from this player buys only the link to 0, saving 7.

Run `python3 verify_greedy.py` for an independent standard-library verifier. The script records the vertex labels and every buyer, independently checks the girth, computes the exact single-edge stability price interval, evaluates all feasible neighbor-set choices and confirms each best response with direct breadth-first search. The exhaustive strategy count omits double purchases of edges already paid for by the other endpoint, which can only increase cost at these positive prices. The two-for-two alternatives above are also checked directly. The older notion of greedy equilibrium and known distinctions from Nash equilibrium are due to Lenzner. Priority for these particular examples has not been established. [Lenzner, *Greedy Selfish Network Creation*](https://arxiv.org/abs/1210.7970)

A further search added paths with two to four edges to four of the promising core graphs. Of 69 sampled graph modifications, seven admitted positive weights passing the swap-only screen and none yielded a Nash witness. These last results are numerical screens. The prices and deviations in the table are exact integer calculations.

[Search scripts and run logs in the source bundle](research-sources.zip)
