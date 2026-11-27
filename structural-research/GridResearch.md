# A boundary cut reverses the proposed grid inequality

Leandro asked on February 14, 2010 whether a vertex above the diagonal of a square lattice is reachable in at least as many configurations when the larger edge budget is vertical. Consider the grid on the vertices `{0,...,n}²`, rooted at the lower left corner. Write `N=n(n+1)` for the number of edges of each orientation.

For every `n≥4`, take the target `t=(a,n)` with `2≤a≤n−2`. Among configurations retaining `N−1` horizontal and `N−2` vertical edges, **exactly one more configuration connects the root to t** than among configurations with those budgets exchanged. For the smallest grid in the family, `n=4`, the two counts are **3780** and **3779**. Each class has 3800 configurations.

## Why the difference is exactly one

Delete one horizontal and two vertical edges, or two horizontal and one vertical edge. Either way, if the deletions separate the root and the target then there is a vertex partition separating them whose crossing edges all belong to the three deletions. Color the two sides of this partition red and blue.

Each row that contains both colors contributes a horizontal crossing edge. Each column that contains both colors contributes a vertical crossing edge. Thus the number of mixed rows plus the number of mixed columns is at most three. There is a monochromatic row and a monochromatic column, and they have the same color at their intersection. Every row or column containing a vertex of the opposite color is mixed, since it intersects the monochromatic column or row. The opposite color therefore occupies at most two vertices: the two positive numbers of occupied rows and columns have sum at most three.

A singleton with at most three crossing edges lies on the boundary. A pair of nonadjacent vertices would have at least four crossing edges, since each vertex has degree at least two. For adjacent vertices the number of crossing edges is the sum of their degrees minus two. It is at most three exactly when the pair consists of a corner and an adjacent boundary vertex. Since the partition separates root and target, this identifies every possible obstruction:

1. The root is isolated. Both root edges are absent. The spare deletion can be any of the other `N−1` edges of the designated orientation.
2. The root and one neighbor form an isolated pair. The three crossing edges determine exactly one deletion pattern for each inventory. The bottom pair has one horizontal and two vertical crossing edges. The left pair has two horizontal and one vertical crossing edges.
3. The target is isolated. Its two horizontal edges and its one vertical edge must all be absent. This gives one additional configuration in the two-horizontal inventory.

The target cannot belong to a corner pair because it is at least two steps from either top corner. The root remains incident to the internal edge in each isolated-pair pattern, so the first two cases are disjoint. All three target-incident deletions are disjoint from the root obstruction patterns. Consequently the first inventory has `N` disconnected configurations, the swapped inventory `N+1`. Both inventories have `N·binom(N,2)` configurations. Subtracting proves the claim.

The mechanism is a terminal's local boundary geometry. It applies to arbitrarily large grids and uses no approximation. For reliability models conditioned on exact, orientation-specific inventories, a terminal lying above the diagonal does not by itself order the connection probabilities.

## Scope and prior work

Gerhard Paseman’s same-day response on MathOverflow described enumeration ideas, suggested the inequality holds in some cases, and explicitly said he did not have an answer. The Left To Solve listing classified it as open and unformalized when this work began on November 27, 2026. Searches of the title, authors and relevant percolation terminology did not locate a prior answer to the finite fixed-inventory comparison. Searches cannot establish absolute priority. Work on coordinate-wise isotropic percolation inequalities, and on independent directional edge probabilities, concerns different orderings or ensembles.

- [Leandro's original question and Gerhard Paseman's response](https://mathoverflow.net/questions/15242)
- [Left To Solve listing](https://lefttosolve.com/p/mo-15242)
