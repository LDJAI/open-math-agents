# Which polynomials count matchings of a bipartite graph?

For each degree $k$, the matching-count vectors of all finite simple bipartite graphs form a finite union of explicitly parametrized polynomial families. Each family uses at most $2^k-1$ nonnegative integer parameters, regardless of the number of edges. The parameters give both an arithmetic test for realizability and a graph witnessing every positive result.

## The inverse problem

Write $R_G(z)=\sum_{j\ge0}m_j(G)z^j$, where $m_j(G)$ counts the matchings of size $j$ in $G$ and $m_0(G)=1$. The question is which positive integer vectors $(m_1,\ldots,m_k)$ occur as the complete list of nonconstant coefficients. Under the correspondence between edges of a bipartite graph and allowed squares of a board, this is the inverse rook problem. For example, a rook placement represents a partial assignment with distinct rows and columns.

Abigail G. Mitchell stated the unrestricted inverse problem as open in 2004 and gave a root-based test for the class of Ferrers boards. In a 2012 discussion of the unrestricted problem, Brendan McKay wrote, “I very much doubt that a complete classification is possible.” McKay earned his PhD at the University of Melbourne in 1980. The questioner, writing as Adam, also specifically requested an algorithm that constructs a graph whenever possible. [Mitchell, *The inverse rook problem on Ferrers boards*](https://arxiv.org/abs/math/0407007) · [Original question and McKay's comment](https://mathoverflow.net/questions/88547/bounds-on-numbers-of-matchings-of-given-sizes-in-bipartite-graphs) · [McKay's ANU biography](https://comp.anu.edu.au/people/brendan-mckay/)

There is an elementary reason that the existence of some recognition algorithm is immediate. A graph with $e=m_1$ edges has at most $e$ nonisolated vertices in either part, so one can inspect the boards in an $e$ by $e$ square. The classification below replaces this edge-dependent board with a fixed list of polynomial maps for each degree.

## Parametric classification

Fix $k\ge1$. Let $C$ be a labeled set of size $k$, divide it into disjoint sets $A,B$ of sizes $a,b$, and choose a subset $H\subseteq A\times B$. For every nonempty $S\subseteq A$ or nonempty $S\subseteq B$, introduce a parameter $p_S\in\mathbb N_0$. These are the only unbounded data. The finite choice of $a$ and $H$ specifies one family. We may fix the labels of $A,B$ once their sizes have been chosen.

Work in the commutative ring

$$
\mathcal R=\mathbb Z[z,x_i:i\in C]\big/(x_i^2:i\in C).
$$

For $U\subseteq C$ let $x_U=\prod_{i\in U}x_i$. Define the $\mathbb Z[z]$-linear map $L$ by $L(x_U)=1$ for every squarefree monomial, including $1$. Thus $L$ sums coefficients after all terms with a repeated $x_i$ have vanished.

**Theorem.** A vector $(m_1,\ldots,m_k)$ of positive integers is realizable if and only if at least one choice above satisfies

$$
1+\sum_{j=1}^k m_j z^j
=L\left[
\prod_{(i,j)\in H}(1+z x_i x_j)
\prod_{\substack{\varnothing\ne S\subseteq A\\\text{or }\varnothing\ne S\subseteq B}}
\left(1+z\sum_{i\in S}x_i\right)^{p_S}
\right].
$$

For each family, the coefficient of $z^j$ on the right is an explicit polynomial over $\mathbb Z$ in the parameters, of total degree at most $j$. To get the family of *exact* degree $k$, retain the outputs with positive $z^k$ coefficient. Degree zero consists solely of $R_G(z)=1$.

**Proof.** If $R_G$ has degree $k$, the largest matching in $G$ has $k$ edges. By Kőnig's theorem, $G$ has a vertex cover $C$ of size $k$. Take $A$ and $B$ to be the members of $C$ in the two parts of the graph. Each edge either belongs to $H$, the edges with both endpoints in $C$, or has exactly one endpoint outside $C$. After discarding isolated vertices, each vertex outside $C$ has a nonempty neighborhood $S$ contained wholly in $A$ or wholly in $B$. Let $p_S$ count the outside vertices with precisely this neighborhood. [Kőnig's theorem and proof](https://math.mit.edu/~goemans/18433S07/matching-notes.pdf)

For a core edge $ij$, the choices to omit or use it give the factor $1+z x_i x_j$. For one outside vertex of type $S$, the choices to leave it unmatched or match it to one of its neighbors give $1+z\sum_{i\in S}x_i$. Multiplication makes choices at all these edges and vertices. Two choices conflict at a cover vertex exactly when they produce a square $x_i^2$, which vanishes. A conflict at an outside vertex is impossible because its own factor allows at most one edge. Each surviving choice therefore specifies a matching, with its size recorded by the exponent of $z$. Applying $L$ establishes the identity.

Conversely, build the core $H$ on $A\sqcup B$. For every $S$, add $p_S$ distinct vertices on the opposite side from $S$, joining each to all members of $S$. The same computation proves that the resulting simple bipartite graph realizes the coefficients. Its cover has size $k$, so larger matchings are impossible. Positivity of $m_k$ gives the requested matching number.

To verify the polynomial assertion, put $(p)_d=p(p-1)\cdots(p-d+1)$ and $(p)_0=1$. The square-zero relations give

$$
\left(1+z\sum_{i\in S}x_i\right)^p
=\sum_{U\subseteq S}(p)_{|U|}\,z^{|U|}x_U.
$$

The falling factorial counts the injections from the chosen cover vertices into the $p$ available outside vertices. In the coefficient of $z^j$, the sum of the degrees contributed by the outside-vertex factors is at most $j$. Finally, the number of parameters is

$$
(2^a-1)+(2^b-1)\le 2^{a+b}-1=2^k-1,
$$

since $(2^a-1)(2^b-1)\ge0$. This proves all the claims. $\square$

## Example

The polynomial $1+4z+z^2$ has only real roots and strictly positive coefficients, yet it cannot occur. To see what the formula detects, consider the two possible splits of a two-vertex cover up to swapping sides.

- For a $2+0$ split let $u,v,w$ count outside vertices adjacent respectively to the first vertex alone, the second alone, and both. Then $m_1=u+v+2w$ and $m_2=(u+w)(v+w)-w$. When $m_1=4$, the possible values of $m_2$ are $0,2,3,4$.
- For a $1+1$ split let $u,v$ count the leaves on the two cover vertices and let $h\in\{0,1\}$ record the core edge. Then $m_1=u+v+h$ and $m_2=uv$. When $m_1=4$, the same four possibilities occur.

In particular there is a gap at $m_2=1$. A positive instance with $m_2=2$ is the four-cycle.

## Recognition, reconstruction and complexity

The linear coefficient supplies the finite parameter budget

$$
e=m_1=|H|+\sum_S |S|p_S.
$$

Enumerate the $k+1$ possible splits, the core choices, and the nonnegative solutions to this equation. Evaluate the polynomial of each family and compare it with the input. When they agree, the construction in the proof gives an explicit graph. If the search terminates without agreement, there is no realization. Different parameters may give the same vector.

For fixed $k$, each parameter is at most $e$. There are at most $(k+1)2^{\lfloor k^2/4\rfloor}$ choices of core and at most $(e+1)^{2^k-1}$ parameter tuples per core. Polynomial evaluation has a number of operations bounded in terms of $k$ alone. After rejecting counts larger than $\binom ej$, the integers in this computation have $O_k(\log(e+1))$ bits. If $L_{\mathrm{in}}$ is the binary input length, the resulting bit-time bound has the form

$$
f(k)(e+1)^{2^k-1}\operatorname{poly}(L_{\mathrm{in}})
$$

for a computable $f$. The dependence on the *value* of $e$ makes this a pseudopolynomial bound at fixed $k$. A compact positive witness uses $O_k(\log(e+1))$ bits and is verifiable in polynomial time at fixed $k$. Expanding it into a labeled edge list costs at least $e$ output entries.

## Scope and reproducibility

The theorem gives an exhaustive parametric classification for arbitrary finite boards. Membership is expressed by fixed-degree integer-polynomial equations with bounded nonnegative unknowns. Eliminating those unknowns to obtain a short intrinsic coefficient test, comparable to Mitchell's criterion for Ferrers boards, is a stronger objective. No such test or binary-polynomial-time algorithm follows here. These distinctions matter when interpreting McKay's informal wording.

Grouping vertices by neighborhood around a bounded vertex cover is an established technique. The argument uses that structure to obtain the displayed polynomial families and an inverse construction. Searches for the inverse rook problem, realizability of matching counts, general board characterizations and citations or extensions of Mitchell's result did not identify an earlier statement of this particular parametrization. This does not establish priority. [Lampis, *Algorithmic Meta-theorems for Restrictions of Treewidth*](https://www.csc.kth.se/~mlampis/papers/metatheorems.pdf)

The accompanying Python program requires only the standard library. Running the following commands from the directory containing it constructs a graph with four edges and two two-edge matchings, then runs the independent check.

~~~sh
python verify_matchings.py realize 4 2
python verify_matchings.py check
~~~

The check enumerates all 68,406 labeled boards with at most five occupied squares in a $5$ by $5$ square, computing matching numbers by inspecting subsets of edges. Every graph with at most five edges fits on such a board after removing isolated vertices. The 29 distinct vectors, including the empty one, agree exactly with the complete output of the parametric families at those edge counts. The checker also reconstructs and recounts a witness for every vector. It separately tests recognition on all 65 positive vectors with one to four edges satisfying the elementary binomial bounds. The recognizer accepts 14 and rejects 51. These are implementation checks; the bidirectional proof gives the result for arbitrary size.
