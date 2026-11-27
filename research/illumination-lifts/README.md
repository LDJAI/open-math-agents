# Two counterexamples in Hadwiger illumination

**LDJAI research note · November 26, 2026**  
Independent mathematical work with OpenAI Codex. The general 4D and 5D covering problems remain open.

## 1. A proposed reduction by central symmetry

Write $I(K)$ for the fewest directions that illuminate a convex body $K$. A direction $v$ illuminates $x$ if $x+tv$ is interior for some $t>0$. Equivalently, $I(K)$ is the fewest translates of a smaller positive homothet of $K$ needed to cover it. For a polytope it suffices to illuminate its vertices. Indeed, express any point as a convex combination of vertices and move one positively weighted vertex into the interior. The same convex combination moves the point into the interior along that direction.

Wu and Zhou's 2019 Problem 1.3 asks whether placing a body and its reflection in parallel hyperplanes and taking their convex hull always doubles its illumination number. They observed that a positive answer would transfer a symmetric Hadwiger bound in dimension $n+1$ to arbitrary bodies in dimension $n$. Their upper bound for the lift is valid. The equality they asked about fails. [Original question, p. 191, and Theorem 3.5](https://cdm.ucalgary.ca/article/download/62685/53786/201277)

**Theorem.** Take the standard basis $e_1,\ldots,e_n$ in $\mathbb R^n$, and set

$$T_n=\operatorname{conv}\{e_i,-2e_i:1\le i\le n\},\qquad S_n=\operatorname{conv}\big((T_n,1)\cup(-T_n,-1)\big).$$

Then $I(T_n)=n+\lceil n/2\rceil$ and $I(S_n)=2(n+1)$. The proposed identity fails for every $n\ge3$. Changing the levels from $\{-1,1\}$ to $\{0,1\}$ is an invertible affine map, so this is the construction in the original question.

| Lift dimension | Base $I(T_n)$ | Proposed $2I(T_n)$ | Exact $I(S_n)$ |
|:--|--:|--:|--:|
| 4D | 5 | 10 | **8** |
| 5D | 6 | 12 | **10** |

**The base count.** Call the vertices $e_i$ positive and $-2e_i$ negative. A direction cannot illuminate points on opposite supporting hyperplanes. The functional $\sum x_i$ separates the positive and negative sets in this way. For $i\ne j$, $x_i-x_j$ does the same for $-2e_i$ and $-2e_j$. Thus the negative vertices need $n$ lights of their own.

No light illuminates three positive vertices. For a triple $i,j,k$, the functional $2x_i-x_j-x_k$ is maximized at $e_i$, with value 2. The two cyclic permutations give supporting functionals at $e_j,e_k$. They sum to zero, so a direction cannot decrease all three strictly.

Conversely, $-e_i-e_j$ illuminates both $e_i$ and $e_j$. The body has gauge $p(x)=\sum_k\max(x_k,-x_k/2)$, as is seen by taking its intersection with each orthant. Moving a small distance $t$ along this direction from either vertex gives $p=1-t/2<1$. A leftover positive vertex and each negative vertex can be lit toward the origin. This proves the first formula.

<!-- page -->

## 2. Why the lift uses fewer lights

**Upper bound.** In the top layer of $S_n$, every positive vertex $(e_i,1)$ is lit by the same downward direction. Indeed, $e_i$ is interior to $-T_n$, halfway from its interior origin to $2e_i$. The midpoint $(e_i,0)$ is therefore interior to $S_n$. To see this, any supporting hyperplane there would have to support both endpoints $(e_i,\pm1)$. At the lower endpoint only the horizontal base hyperplane can support, and it misses the top endpoint.

Direct one more light from each of the $n$ negative top vertices toward the origin of $S_n$. Central reflection supplies $n+1$ lights for the bottom. Together these give the claimed $2(n+1)$ directions.

**Lower bound.** Within the top layer, the $n$ negative vertices are pairwise on opposite supports, witnessed by $x_i-x_j$. Every one of them is also on a support opposite to every positive top vertex. This time the functional is

$$L(x,t)=2\sum_i x_i+t.$$

It takes values $3$ and $-3$ on the positive and negative top vertices, respectively, and takes the opposite values on their reflections. Hence the top needs at least $n+1$ lights. The bottom needs as many, and a top light must have negative last coordinate while a bottom light must have positive last coordinate. This proves equality.

**Why 4D is the first possible failure.** In fact any opposite-base lift of any full-dimensional $T\subset\mathbb R^n$ needs at least $n+1$ lights on its top layer. Normalize these directions as $(w_j,-2)$ and write $h(u)=\max_{x\in T}u\cdot x$. At a top point maximizing $u\cdot x$, use the horizontal section $(1-s)T+s(-T)$ at height $1-2s$. For a light entering this section's interior, its slope satisfies $u\cdot w_j<h(-u)-h(u)$. Applying the same argument at $-u$ gives

$$\min_j u\cdot w_j<h(-u)-h(u)<\max_j u\cdot w_j\quad(u\ne0).$$

The slopes must affinely span $\mathbb R^n$. Otherwise a nonzero vector perpendicular to their affine differences violates the strict inequalities. So our lifts attain the smallest possible count for their dimension. For a planar base other than a parallelogram, Levi's planar result gives $I(T)=3$, and Wu and Zhou's upper bound gives six for its lift, matching the lower bound. A parallelogram lifts to a parallelepiped, which needs eight. In dimension one, an interval lifts to a parallelogram. [Planar theorem and lift upper bound](https://cdm.ucalgary.ca/article/download/62685/53786/201277)

**Exact computational check.** The accompanying `verify.py` constructs the polytopes from their integer vertices, enumerates all supporting facets by determinants, checks the strict inequalities for every assigned light, and verifies the lower-bound witnesses. The 4D example has 8 base and 16 lift facets. The 5D example has 16 base and 32 lift facets. The proof above establishes the result for every $n$. The checks use Python's standard library and can be run with `python3 verify.py`.

<!-- page -->

## 3. A projection can retain the full illumination number

Wu, Fan and He proved $I(K+\lambda J)\ge I(\pi K)$, where $J=[-u,u]$ and $\pi$ projects along $u$. Their 2020 Remark 1 asks whether the inequality is always strict. The following family attains equality for every finite $\lambda\ge0$, including positive lengths. Varying the same construction realizes a full interval of counts over one fixed projection. [Original Proposition 2 and Remark 1, p. 1148](https://files.ele-math.com/articles/mia-23-88.pdf)

**Construction.** Fix $m\ge2$ and $Q=[-1,1]^m$. Over each vertex $s$ place the point $(s,\prod_i s_i)$. Over any $j$ selected vertices, also place the point at the opposite height. Let $P_j$ be the convex hull and $J$ the vertical segment with endpoints $(0,\pm1)$. Then

$$\pi(P_j+\lambda J)=Q,\qquad I(P_j+\lambda J)=2^m+j,\qquad 0\le j\le2^m.$$

The initial points affinely span $\mathbb R^{m+1}$. The height cannot be affine in $s$: its average against the constant and each coordinate on the sign cube is zero, but its square averages to one. Thus all these sets are convex bodies. For $m=2$, the initial four points are a tetrahedron projecting to a square.

**Lower bound.** Project any smaller copy onto $Q$. In each base coordinate its width is strictly less than two, so it cannot contain two distinct cube vertices. Each projected corner requires its own copy. Over every doubled corner, the two ends of the vertical fiber are separated by $2(1+\lambda)$, the full vertical width of the entire body. No smaller copy can contain both. This requires a second copy at each of the $j$ doubled corners.

**Upper bound.** A polytope generated by $N$ points can be lit by $N$ directions, one toward an interior point from each vertex. Also $I(A+B)\le I(A)$ for any full-dimensional $A$ and compact convex $B$. At a boundary point $a+b$, an illuminating ray for $a$ enters $\operatorname{int}(A)+b\subset\operatorname{int}(A+B)$. The original $2^m+j$ generating points therefore suffice after any vertical extension. Taking $j=0$ disproves strictness.

| Ambient dimension | Fixed projection | Exact counts attained | Equality example |
|:--|:--|:--|:--|
| 4D | 3D cube | Every integer from 8 to 16 | 8 lights in both |
| 5D | 4D cube | Every integer from 16 to 32 | 16 lights in both |

These statements concern the *number* of smaller homothets. Their shrinkage can deteriorate as the segment length increases. For example, with $j=0$, each corner has a fiber of length $2\lambda$ that must be covered by a single copy in a minimal cover. Its scale is at least $\lambda/(1+\lambda)$.

<!-- page -->

## 4. What does follow for Hadwiger's conjecture?

The 1957 conjecture bounds $I(K)$ by $2^d$ for an arbitrary convex body in $\mathbb R^d$. The cube shows the bound would be sharp. Aiger, Har-Peled and Žužić's November 2026 preprint proves the eight-copy bound in 3D and reports a Lean verification. Its shadow boundary is a curve cut into six short arcs. In 4D and 5D the corresponding shadow generally has dimension two or three, and that partition step needs a replacement. [3D proof](https://arxiv.org/abs/2611.32334)

| Dimension | Sharp target | Published general upper bound located |
|:--|--:|--:|
| 3 | 8 | 8 |
| 4 | 16 | 96 |
| 5 | 32 | 933 |

The 4D bound is due to Prymak and Shepelska. The 5D bound is due to Arman, Bondarenko and Prymak. The two counterexamples in this note leave both general bounds unchanged. [4D bound](https://arxiv.org/abs/1811.08962) · [5D bound](https://arxiv.org/abs/2404.00547)

**A positive consequence of the 3D result.** Suppose $K=C+F$ is full-dimensional, where $F$ lies in a linear subspace $E$ and spans it affinely. Write $Q$ for the projection of $C$ to $E^\perp$, and take $I(F),I(Q)$ in their own spaces. Then

$$I(C+F)\le I(Q\times F)\le I(Q)I(F).$$

Here is a proof. First, $I(C+tF)$ is constant for $t>0$. For $0<s<t$, adding $(t-s)F$ to $C+sF$ gives $C+tF$. In the reverse direction, adding $(t/s-1)C$ to $C+tF$ gives $(t/s)(C+sF)$. Use the summand inequality on page 3 and affine invariance in each direction. Now contract the $E$ coordinates of $C+tF$ by $1/t$. The images converge in Hausdorff distance to $Q\times F$ as $t\to\infty$ because $C$ is bounded. An illuminating cover of the limit works for sufficiently close bodies after a small increase of scale: center the limit $L$ at an interior origin and sandwich the nearby body between $(1-\delta)L$ and $(1+\delta)L$. A cover of $L$ at scale $r<1$ then covers the nearby body at scale $r(1+\delta)/(1-\delta)<1$ for small $\delta$, after scaling the translations. The product bound follows by taking Cartesian products of covers of the two factors at a common scale below one.

Consequently, **16 suffices in 4D** when the body has a Minkowski summand of dimension 1, 2, or 3. **32 suffices in 5D** when it has a summand of dimension 2 or 3. For example, adding a planar disk to an arbitrary full-dimensional 5D convex body produces a body in the latter class. A separate application of Wu and Zhou's Theorem 3.5 gives 16 for every 4D convex hull of two 3D bases in parallel hyperplanes.

**Status and priority.** Left to Solve lists the general covering conjecture as unformalized. Its live brief showed zero agents on that entry when checked. The two questions answered here appear in the 2019 and 2020 papers linked above. Searches of their titles, formulas, citing literature and subsequent work by the authors located no earlier explicit answers. Priority remains unverified. This note is an AI-assisted research manuscript with exact finite checks and has not undergone peer review or Lean verification. [Left to Solve entry](https://lefttosolve.com/p/wp-hadwiger-conjecture)
