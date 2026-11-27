# Two matrix norms with identical isometries and different evaluation complexity

## Historical question

On December 1, 2010, Nathaniel Johnston asked whether NP-hardness of evaluating one complex matrix norm implies NP-hardness for another having exactly the same isometry group. He wrote, “all unitarily-invariant matrix norms are easy to compute”. He was investigating norms arising in quantum information and explicitly allowed any norm on the underlying complex vector space of matrices. He received his mathematics PhD from the University of Guelph in 2012. We consider surjective complex-linear isometries and rationally encoded matrices of varying dimension. The distinction also holds for surjective real-linear isometries of the complex matrix space. [Question](https://mathoverflow.net/questions/47956/do-isometry-groups-tell-us-how-difficult-norms-are-to-compute) · [All comments](https://mathoverflow.net/posts/47956/comments) · [Johnston’s university biography](https://mta.ca/directory/nathaniel-johnston)

## Theorem

There is one explicitly specified family of normalized, submultiplicative, unitarily invariant norms $F_n$ on $M_n(\mathbb C)$ such that

1. In each dimension its full linear isometry group is exactly the spectral norm’s.
2. Computing $F_n$ to inverse-polynomial additive accuracy is NP-hard even on diagonal nonnegative integer matrices with entries at most $n$.
3. The spectral norm allows polynomial-time exact comparison with a nonnegative rational threshold.

This refutes the proposed transfer in the customary complexity-theoretic sense, unless P equals NP. The reduction and easy algorithm are unconditional. The normalized norms have $F_n(uv^*)=1$ for unit vectors $u,v$. The hard norm is determined by the dimension alone. All information about the input graph goes into a matrix given to this fixed family.

## Construction

Order the unordered pairs of positive integers by their larger endpoint, breaking ties by their smaller endpoint. Write $e_1,e_2,\ldots$ for this sequence. In dimension $n$, only the first $n$ edges occur. Thus all their endpoints lie in $\{1,\ldots,n+1\}$. A subset $S\subseteq\{1,\ldots,n+1\}$ defines bits $c_j(S)$ indicating whether $e_j$ crosses the cut, with $c_0(S)=0$.

Let $s_1\ge\cdots\ge s_n\ge s_{n+1}=0$ be the singular values of $A$ followed by zero. Put $b_j=8n-3j+3$, $\alpha=b_1+1=8n+1$, and set

$$
 F_n(A)=\frac1\alpha\left(\sum_{j=1}^n b_js_j + \max_S\sum_{j=1}^n c_j(S)(s_j-s_{j+1})\right).
$$

For each cut the unnormalized expression has the form $\sum w_j s_j$, with $w_j=b_j+c_j-c_{j-1}$. It has $w_j-w_{j+1}=3+2c_j-c_{j-1}-c_{j+1}\ge1$ for $j<n$. Moreover $w_j\ge5n+2>\alpha/2$ and $w_1\le\alpha$. These order and positivity inequalities are independent of the cut. With $w_{n+1}=0$,

$$
\sum_{j=1}^n w_js_j=\sum_{j=1}^n(w_j-w_{j+1})(s_1+\cdots+s_j).
$$

Each partial sum of singular values is a Ky Fan norm. Positive combination, then maximization over finitely many cuts, proves the norm axioms. Unitary invariance follows from the formula. Choosing a cut separating the endpoints of $e_1$ gives $w_1=\alpha$. In particular $F_n(A)\ge\|A\|_{\rm op}$. Since $s_j(AB)\le\|A\|_{\rm op}s_j(B)$, positivity of all the weights yields $F_n(AB)\le\|A\|_{\rm op}F_n(B)\le F_n(A)F_n(B)$.

## What the isometries preserve

Every linear isometry of either norm preserves the Frobenius norm. Indeed, uniform Lebesgue measure on its unit ball is invariant under the isometry, since a linear bijection carrying that ball onto itself has absolute real determinant 1. Both balls are invariant under independent unitary actions on the left and right. Their real covariance matrices are therefore scalar multiples of the identity in the real and imaginary matrix-entry coordinates. For distinct entries, changing the sign of a row or column containing exactly one shows that the cross-covariance vanishes. Multiplication of the whole matrix by $i$ gives equal real and imaginary variances and zero covariance for one entry. Row and column permutations give equality of all coordinate variances. Covariance is positive definite, so preserving it forces Frobenius orthogonality.

For $A\ne0$, the spectral norm agrees with the Frobenius norm exactly at rank one. The same equality characterizes rank one for $F_n$, now with $F_n(A)\ge\|A\|_F$. To see this, take a cut with $w_1=\alpha$ and write $R=\sum_{j\ge2}s_j$. For rank exceeding one,

$$
\|A\|_F^2\le s_1^2+s_1R\le(s_1+R/2)^2,
\qquad F_n(A)>s_1+R/2.
$$

The second inequality uses $w_j>\alpha/2$. Rank-one equality follows directly since $\max w_1=\alpha$.

Consequently either type of isometry preserves the rank-one cone in both directions. Conversely, any Frobenius-orthogonal linear bijection preserving that cone preserves the set of rank-at-most-$r$ matrices, since that set consists of sums of at most $r$ rank-one matrices and zero. By the Eckart–Young theorem its squared Frobenius distance from $A$ is $\sum_{j>r}s_j(A)^2$. Preservation of all these distances recovers all singular values. Such a bijection therefore preserves both norms. This proves equality of the groups without needing their explicit classification. [Ky Fan norms and singular values](https://case.edu/artsci/math/mwmeckes/matrix-analysis.pdf) · [Low-rank approximation](https://www.sjsu.edu/faculty/guangliang.chen/Math250/lec7matrixnorm.pdf)

## Reduction from MAX-CUT

For an unweighted graph on $v\ge2$ vertices choose $n=\binom v2$. Write $a_j\in\{0,1\}$ for the indicator that $e_j$ is an input edge, and set $s_j=\sum_{k=j}^n a_k$. These numbers are nonnegative and nonincreasing. The diagonal matrix $D=\operatorname{diag}(s_1,\ldots,s_n)$ has precisely these singular values. Hence

$$
 \alpha F_n(D)-\sum_{j=1}^n b_js_j
 =\max_S\sum_{j=1}^n a_jc_j(S)=\operatorname{MaxCut}(G).
$$

The dimension and all entries are polynomially bounded in the size of the source graph in its usual explicit encoding. An approximation of absolute error strictly below $1/(2\alpha)$ allows exact recovery by rounding. Equivalently, threshold comparison of $F_n(D)$ with $(\sum b_js_j+k)/\alpha$ decides the unweighted MAX-CUT instance. For the spectral norm, $\|A\|_{\rm op}\le t$ if and only if $t^2I-A^*A$ is positive semidefinite. Rational positive semidefiniteness is decidable in polynomial bit complexity, for instance from the signs of the coefficients of $\det(zI+t^2I-A^*A)$. This polynomial has only real roots and all its coefficients are nonnegative if and only if all the eigenvalues of $t^2I-A^*A$ are nonnegative. For the same greater-than-or-equal comparison used by MAX-CUT, the spectral norm is at least a positive threshold exactly when this Hermitian matrix fails positive definiteness. Threshold zero is automatic. Both comparisons use the same rational-input model. On the diagonal instances the spectral norm is just $s_1$. [Garey, Johnson and Stockmeyer on simple MAX-CUT](https://doi.org/10.1016/0304-3975%2876%2990059-1)

## Scope and prior art

The original thread showed zero answers. The ten public comments included Yuan’s suggestion of a generic convex body with very few symmetries and a candidate easily computable norm. They contained no hard norm with the same isometry group, no reduction and no example involving unitarily invariant norms. Johnston explicitly noted that the suggested route had not yet disproved the conjecture. The construction above has the full isometry group of a common operator norm.

Isometry classifications for unitarily invariant norms are classical, as are MAX-CUT hardness, the correspondence between symmetric gauges and unitarily invariant norms, Ky Fan norms and low-rank approximation. Their use here is not a priority claim. Targeted searches of the original title, author, matrix norm isometry complexity, hard symmetric gauge evaluation, and NP-hard unitarily invariant norms did not establish a prior explicit pair, or a prior unitarily invariant MAX-CUT encoding on diagonal matrices. The absence of a searchable direct solution is provisional and requires independent review. The result answers the general question. It does not settle the complexity of the specific quantum information norms which motivated Johnston. [Chan, Li and Sze on the classical isometry classification](https://www.polyu.edu.hk/ama/profile/sze/PDF/uinorm_final.pdf) · [Adrian Lewis on invariance](https://people.orie.cornell.edu/aslewis/publications/96-group.pdf) · [Hardness of induced matrix norms](https://epubs.siam.org/doi/10.1137/09076773X) · [Johnston and Kribs on the motivating norms](https://arxiv.org/abs/1006.0898)

## Verification

`NormCutCertificate.lean` verifies the exact edge-gap identity for arbitrary lists of integer weights, the coefficient gap bound and the strict Frobenius inequality for arbitrary finite nonnegative singular-value vectors with nonzero tail. The file compiled with Lean 4.33.1 and mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`. The three axiom checks involve only `propext`, `Classical.choice` and `Quot.sound`; their output is in `NormCutCertificate.log`. The matrix norm, isometry and complexity claims are proved in the note. `check_norm_isometries.py` also independently verified the graph reduction, all cut weights and the equality test with exact integers for all 1,098 labelled simple graphs on two through five vertices.

[Stronger construction with fixed absolute accuracy and stability under zero padding](padding-stable-norm.md)
