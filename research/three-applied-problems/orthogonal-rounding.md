# An obstruction to entrywise monotone orthogonal rounding

The answer to the original nearest-target question is **no**. For every dimension $n\ge5$, a Householder reflection has a unique closest signed permutation, and even the first set of monotonicity inequalities is impossible in a neighborhood. A block example shows that the exact monotonicity rule can also fail when the starting and target matrices belong to the same connected component.

## The question and its provenance

On June 29, 2020, MathOverflow user ryanriess asked whether every real orthogonal matrix $A$ that is not a signed permutation can take an arbitrarily small orthogonal step toward a Frobenius-nearest signed permutation $P$ with the following properties.

1. On the support of $P$, every entry of $B$ has magnitude at least that of the corresponding entry of $A$, with a strict improvement somewhere.
2. Outside that support, every entry of $B$ has magnitude at most that of the corresponding entry of $A$.

The MathOverflow and Mathematics Stack Exchange cross-posts both had zero posted answers at the November 26, 2026 check. The original discussion linked by the author contains a counterexample for a prescribed target that is not nearest. Its starting matrix is itself a signed permutation. The author of that earlier discussion explicitly asks about the nearest-target restriction in an edit. Left to Solve lists the problem as open and awaiting a Lean statement. A search of the exact and related formulations found no earlier answer to the nearest-target claim. This establishes the state of the checked sources, rather than a priority claim. [Left to Solve](https://lefttosolve.com/p/mo-364377) · [MathOverflow](https://mathoverflow.net/questions/364377) · [Cross-post](https://math.stackexchange.com/questions/3737954) · [Earlier question and counterexample](https://math.stackexchange.com/questions/3720051)

## Counterexample

Let $J=\mathbf1\mathbf1^\top$, and put
$$
 A_n=I-\frac{2}{n}J,\qquad P=I.
$$
The matrix $A_n$ acts as minus the identity on the span of $\mathbf1$ and as the identity on its orthogonal complement. Hence $A_n$ is orthogonal, $\det A_n=-1$, and $\operatorname{tr}A_n=n-2$. It has no zero entries.

**The target is uniquely nearest.** For any signed permutation $S$,
$$
 \|A_n-S\|_F^2=2n-2\langle A_n,S\rangle_F .
$$
A signed permutation selects one entry per row and per column, with a freely chosen sign. In every row, the positive diagonal entry $(n-2)/n$ is strictly greater than the magnitude $2/n$ of every off-diagonal entry. Thus only $S=I$ maximizes the inner product, and $\|A_n-I\|_F=2$.

**The diagonal has no available improvement.** Every real orthogonal matrix $B$ of determinant $-1$ has eigenvalue $-1$: its nonreal eigenvalues occur in conjugate pairs of product one, and each of its real eigenvalues is $\pm1$. The sum of the real parts of its other eigenvalues is at most $n-1$, so
$$
 \operatorname{tr}B\le n-2.
$$
All orthogonal matrices sufficiently close to $A_n$ have the same determinant, by continuity. All of their diagonal entries are also positive. Condition 1 would force $b_{ii}\ge (n-2)/n$ for all $i$ with at least one strict inequality, which gives $\operatorname{tr}B>n-2$. This contradiction settles the stated question. In particular, the dimension-five matrix has diagonal $3/5$, off-diagonal entries $-2/5$, and trace $3$; no nearby orthogonal step can improve even one diagonal magnitude while maintaining the other four.

An explicit excluded neighborhood in every dimension $n\ge5$ is $\|B-A_n\|_F<1/2$. The bound keeps every diagonal positive. Opposite determinant components are at Frobenius distance at least 2: apply the trace bound just proved to $A_n^\top B$ if its determinant is negative.

## Variants and interpretation

**Slack off the target.** The original proof uses only condition 1. It therefore disproves the author's second edit with any slack $\epsilon>0$ in condition 2 when $P$ is the nearest target from the original question. The first edit changes the quantifier and allows choosing any signed permutation after seeing $A$. The reflection argument does not rule out such a choice.

**Slack with free choice of target.** If the two edits are combined, the answer becomes yes for every orthogonal starting matrix that is not a signed permutation. At least one column then has two nonzero entries. Choose their rows $r,s$. Because the two rows are orthogonal and have a nonzero term in their inner product, there are distinct columns $j,k$ with $a_{rj}a_{sj}>0$ and $a_{rk}a_{sk}<0$. Replace row $r$ by $\cos\theta\,r+\sin\theta\,s$ and row $s$ by $-\sin\theta\,r+\cos\theta\,s$. The derivatives at zero of the squared entries at $(r,j)$ and $(s,k)$ are respectively $2a_{rj}a_{sj}>0$ and $-2a_{sk}a_{rk}>0$. Select both positions in a permutation and complete the matching on the other rows and columns. Those remaining selected entries stay fixed, while both specified entries strictly improve for all sufficiently small positive angles. By continuity, every off-target increase is less than any prescribed positive slack, and the matrix can be kept in any prescribed neighborhood. The same selected permutation works for every slack and every neighborhood. This leaves the first edit alone, with a free target and *zero* off-target slack, separate.

**Same determinant at both endpoints.** Set $A=A_n\oplus A_n$ and $P=I_{2n}$. The same row-by-row argument gives a unique nearest target, and both matrices have determinant $+1$. Every off-block entry is zero, so condition 2 forces a feasible $B$ to stay block diagonal. Its blocks must be orthogonal. For every such $B$ sufficiently close to $A$, both blocks have determinant $-1$ and positive diagonals. The trace bound applies separately in each block; condition 1 again forces a contradiction. This second construction uses the exact off-target inequalities.

**Application.** Orthogonal dictionary learning recovers latent components up to signs and permutation. This counterexample rules out a convergence argument that would require coordinatewise improvement toward the *nearest* signed permutation at every point. It supplies no failure case for a particular trained model or published dictionary-learning algorithm. The aggregate fourth-power objective studied by Zhai and coauthors permits tradeoffs among individual entries. Dian Jin's 2026 preprint studies local maxima of that scalar objective. [Zhai et al., JMLR 2020](https://jmlr.csail.mit.edu/papers/v21/19-755.html) · [Jin, 2026](https://arxiv.org/abs/2607.12431)

## Reproducible checks

Run `python3 verify_rounding.py`. It checks the rational matrix identities, determinant and unique optimum for the dimension-five witness, including all 3,840 signed permutations. It also checks orthogonality, positive determinant, trace and the strict row-maximum condition in the dimension-ten block witness. The neighborhood obstruction in all dimensions follows from the trace inequality in the proof.
