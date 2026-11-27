# The limiting density in anti-majority grid voting

On an n-by-m rectangular grid, each cell chooses zero or one and receives one unit of payoff for each neighbor making the opposite choice. A coloring is a pure Nash equilibrium precisely when every cell has at least as many opposite-colored neighbors as same-colored neighbors. R. H. Hardin proposed that the maximum share of ones would approach two thirds and suggested a sliding pattern. The OEIS entry dates to January 3, 2011. [OEIS A179004](https://oeis.org/A179004) · [Left To Solve](https://lefttosolve.com/p/oeis-a179004)

Write T(n,m) for the maximum number of ones in an equilibrium. For n, m ≥ 4,

\[
2(n-2)(m-2)\ \le\ 3T(n,m)\ \le\ 2nm+2.
\]

For the upper bound, let s and z count the two colors, with s the number of ones. Every one has at least two zero neighbors, except at the four corners where one zero neighbor suffices. Counting edges with unlike endpoints first from their one end and then from their zero end gives 2s − 4 ≤ 4z, hence 3s ≤ 2nm + 2.

For the lower bound, remove the outermost cells and place zeros at positions satisfying i + j + p ≡ 0 (mod 3) in the remaining rectangle. Fill the rest with ones. Here p can be any of three phases. Along each row and each column the bi-infinite pattern has no constant run of length three. Each interior position thus has at least one opposite neighbor on either axis.

Extend each core row by one cell at each end, using the opposite of the adjacent value. This leaves every nonendpoint with at least one opposite horizontal neighbor and gives each new endpoint an opposite neighbor. The new columns are complements of existing columns, so their vertical patterns still have no constant run of length three. Extend each column by the same rule. Vertical constraints now hold everywhere. The final new rows are complements of the adjoining rows and retain their horizontal constraints. Every cell therefore has at least half its neighbors in the opposite state, including all four corners.

Each core position is one in exactly two of the three phases. Across the three colorings the core contains 2(n − 2)(m − 2) ones. One phase attains at least one third of that total, proving the lower estimate. Dividing the bounds by 3nm and sending both side lengths to infinity proves the conjectured limit 2/3, with no restriction on the aspect ratio.

The construction is a deterministic equilibrium for every pair of side lengths at least four. The bounds concern all boards of those sizes. They establish the limiting extremal density without requiring maximizers to use a unique stripe pattern.

## Related literature

Rao and Talon determine rectangular-grid 2-domination numbers. Their condition requires two neighbors in a designated set for each vertex outside it. Hardin requires the opposite-color constraint on both colors, including boundary vertices with degree two or three. The paper is relevant to the density and period-three geometry. A search found no prior treatment of this precise equilibrium density limit. [Rao and Talon, 2019](https://dmtcs.episciences.org/articles/5482)
