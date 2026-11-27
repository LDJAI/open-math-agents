# A hard unitarily invariant norm that is stable under zero padding

**Theorem.** There is one norm $F$ on finite complex matrices, compatible with $A\mapsto A\oplus0$, whose restriction $F_n$ to every $M_n(\mathbb C)$ is unitarily invariant and submultiplicative. The norm takes value one on $uv^*$ for unit vectors $u,v$. Its full complex-linear and real-linear isometry groups in each dimension coincide with those of the spectral norm. Approximating $F_n$ with absolute error at most $1/8$ is NP-hard on diagonal nonnegative integer matrices with entries at most $n$. The spectral norm on those instances is the largest diagonal entry. The normalization here concerns rank-one matrices. In particular, $F_n(I_n)>1$ for $n>1$.

## Formula and norm properties

List the unordered positive-integer pairs $e_j$ in increasing order of their larger endpoint, breaking ties by their smaller endpoint. For a cut $S$ of the positive integers let $c_j$ equal one precisely when $e_j$ crosses the cut. Put $c_0=d_0=0$ and, for $j\ge1$, put
$$
 b_j=2+\frac1j,\qquad d_j=\frac1{4(j+1)(j+2)},\qquad
 \alpha=b_1+d_1=\frac{73}{24}.
$$
Given descending singular values $s_1,\ldots,s_n$ and $s_{n+1}=0$, set
$$
 F_n(A)=\frac1\alpha\max_S\sum_{j=1}^n
 \left[b_js_j+d_jc_j(s_j-s_{j+1})\right].
$$
Only finitely many cut bits enter the formula, so the maximum exists. The same fixed cut ranges over the same positive integers in every dimension. Appending any number of zeros to the spectrum leaves every cut objective unchanged.

For each cut put $w_j=b_j+d_jc_j-d_{j-1}c_{j-1}$. Its objective becomes $\sum_j w_js_j$. For $j\ge1$,
$$
 w_j-w_{j+1}
 \ge \frac1{j(j+1)}-d_{j-1}-d_{j+1}
 \ge \frac1{2j(j+1)}.
$$
For $j\ge2$, each of $d_{j-1}$ and $d_{j+1}$ is at most $1/(4j(j+1))$. For $j=1$, $d_0=0$, $d_2=1/48$, and the first bound is $1/2-1/48=23/48>1/4$. Also $w_1\le\alpha$ and $w_j\ge 2-1/24=47/24>\alpha/2$ for every $j$. Some cut separates the endpoints of $e_1$ and hence attains $w_1=\alpha$.

A decreasing positive weighted sum of the ordered singular values is a positive combination of the Ky Fan norms, by summation by parts. Taking the maximum over cuts and dividing by $\alpha$ gives a unitarily invariant norm. The cut attaining $w_1=\alpha$ shows that $F_n(A)\ge s_1(A)=\lVert A\rVert_{\rm op}$, with equality on every rank-one matrix. The singular-value estimates $s_j(AB)\le\lVert A\rVert_{\rm op}s_j(B)$ applied to each positive-weight sum give $F_n(AB)\le F_n(A)F_n(B)$. The consistent restrictions define a norm on the increasing union via zero padding.

## Isometry groups

The covariance of the uniform measure on the unit ball of either norm is a positive scalar multiple of the identity in real and imaginary matrix-entry coordinates. Indeed a row or column sign kills all cross-covariances between distinct entries, multiplication by $i$ makes the two coordinate variances equal with zero covariance within each entry, and row and column permutations identify the variances across entries. Every real-linear isometry takes the ball onto itself and preserves its normalized uniform measure, hence is orthogonal for the Frobenius norm.

For a nonzero matrix the equality $F_n(A)=\lVert A\rVert_F$ holds exactly at rank one. At higher rank let $R=\sum_{j\ge2}s_j>0$. The cut attaining $w_1=\alpha$ gives $F_n(A)>s_1+R/2$, while
$$
 \lVert A\rVert_F^2\le s_1^2+s_1R\le(s_1+R/2)^2.
$$
The spectral norm also agrees with the Frobenius norm exactly at rank one among nonzero matrices. Hence an isometry for either norm preserves the rank-one cone in both directions. A Frobenius-orthogonal real-linear bijection preserving that cone preserves each set of matrices of rank at most $r$, since these are sums of at most $r$ rank-one matrices. Their squared Frobenius distances from $A$ are $\sum_{j>r}s_j(A)^2$ by Eckart–Young. Taking differences for successive $r$ shows that the bijection preserves all singular values, hence both norms. This proves equality for real-linear maps and for the complex-linear subgroups. Classical isometry classifications give an independent check. [Chan, Li and Sze, Theorems 2.3 and 3.1](https://www.polyu.edu.hk/ama/profile/sze/PDF/uinorm_final.pdf)

## Fixed-accuracy reduction

For a simple unweighted graph on $v\ge2$ vertices, take $m=\binom v2$. Its edges are indicated by bits $a_1,\ldots,a_m$ in the fixed order. Encode those bits as successive singular-value differences by setting
$$
 x_j=4(j+1)(j+2)a_j,\qquad s_j=\sum_{k=j}^m x_k,\qquad
 N=\sum_{k=1}^m4(k+1)(k+2).
$$
Take $D$ to be the $N$-by-$N$ diagonal matrix with initial entries $s_1,\ldots,s_m$ and zero thereafter. Every entry is an integer between zero and $N$. The choice of $N=O(m^3)$ makes even the full dense matrix a polynomial-size output. Zero padding preserves the norm and $d_j(s_j-s_{j+1})=a_j$, so
$$
 \alpha F_N(D)=C+\operatorname{MaxCut}(G),\qquad
 C=\sum_{j=1}^m(2+1/j)s_j.
$$
The exact rational number $C$ is computable in polynomial bit complexity. A common denominator is $m!$, whose bit length is $O(m\log(m+1))$. After clearing this denominator the numerator is at most $3mN\,m!$, of the same polynomial bit length. Repeated integer multiplication, exact division by each $j$, and summation all have polynomial bit cost. There is no graph-dependent norm description.

An approximation $\widehat F$ with $|\widehat F-F_N(D)|\le1/8$ gives
$$
 \left|\alpha\widehat F-C-\operatorname{MaxCut}(G)\right|
 \le \frac{73}{192}<\frac12,
$$
so nearest-integer rounding recovers the exact maximum cut. Exact threshold comparison in the direction $\ge$ against $(C+k)/\alpha$ decides whether $G$ has a cut with at least $k$ edges. The spectral norm permits polynomial-time rational threshold comparison on arbitrary rational complex matrices as well. For $t>0$, the condition $\lVert A\rVert_{\rm op}\ge t$ says precisely that the rational Hermitian matrix $t^2I-A^*A$ fails to be positive definite. Positive definiteness is testable by exact leading principal minors with polynomial bit complexity. For $t\le0$ the comparison is immediate. This establishes the computational distinction under the usual assumption $\mathrm P\ne\mathrm{NP}$. [Garey, Johnson and Stockmeyer, simple MAX-CUT](https://doi.org/10.1016/0304-3975%2876%2990059-1)
