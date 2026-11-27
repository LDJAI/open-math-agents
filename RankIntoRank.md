# Iterating roots of rank-into-rank embeddings

Joseph Van Name asked in 2015 whether there can be nonidentity elementary embeddings of a rank into itself satisfying
\[
 j_n=t_n(j_{n+1})*j_{n+1}\qquad(n\in\mathbb N),
\]
where each unary term uses Laver application and ordinary composition. He also asked whether the terms may all be equal or may be drawn from a finite set. He wrote “It seems like it is impossible for there to be such a descending sequence”. His 2013 mathematics PhD precedes the post. [Original question](https://mathoverflow.net/questions/221720/can-one-take-roots-of-rank-into-rank-embeddings-infinitely-many-times) · [Left To Solve](https://lefttosolve.com/p/mo-221720) · [University of South Florida doctoral graduates](https://www.usf.edu/arts-sciences/departments/mathematics-statistics/graduate/graduates-of-our-program.aspx)

## Answer

An unrestricted sequence exists under the existence of an I3 embedding. A finite set of terms cannot produce such a sequence. The latter conclusion includes a fixed term. More precisely, the existence of an unrestricted chain at some cardinal height is equivalent to the existence of a nonidentity elementary self-embedding at some cardinal height. The construction gives a chain from the standard I3 hypothesis. Existence of an I3 cardinal itself is a large-cardinal assumption.

### Construction for variable terms

Fix an elementary embedding \(j:V_\lambda\to V_\lambda\) with critical point \(\kappa\) and \(\lambda=\sup_{n<\omega}j^n(\kappa)\). Write \(E\) for the space of elementary self-embeddings of \(V_\lambda\), including the identity. Use the topology of agreement on sets \(V_\alpha\), \(\alpha<\lambda\). Because \(\lambda\) has cofinality \(\omega\), this topology is completely metrizable. Specifically, choose a strictly increasing countable cofinal sequence of ranks. A sequence eventually constant on each of those initial segments has a unique limit obtained by their union. For every first-order formula and finite tuple of parameters, some initial segment contains that tuple. Elementarity of an approximating embedding then gives the equivalence for its eventual image tuple, proving the limit elementary.

Laver application and composition are continuous for this topology. To determine \((a*b)|V_\delta\), choose \(\gamma>\delta\) and use the graph \(a(b|V_\gamma)\), which agrees with \(a*b\) on \(V_{a(\gamma)}\supseteq V_\delta\). An initial segment of \(b\) determines the argument \(b|V_\gamma\), and this bounded graph belongs to an initial segment on which agreement with \(a\) determines its image. Boundedness holds since \(b[V_\gamma]\subseteq V_{b(\gamma)}\) and \(\lambda\) is a limit of cardinals. The same reasoning for composition uses that \(b[V_\delta]\) lies in a bounded initial segment.

Define unary terms \(b_0(x)=x\), \(b_{m+1}(x)=b_m(x)*b_m(x)\), and maps \(S_m(x)=b_m(x)*x\). The identity \((a*b)\circ a=a\circ b\), together with \(\operatorname{crit}(a*b)=a(\operatorname{crit}(b))\), shows that squaring an embedding by application discards the first element of its critical sequence. Hence \(\operatorname{crit}(b_m(j))=j^m(\kappa)\). For fixed \(\delta<\lambda\), pick \(m\) large enough that the graph \(j|V_\delta\) and \(\delta\) are both in \(V_{j^m(\kappa)}\). Then \(b_m(j)\) fixes them, so \(S_m(j)\) agrees with \(j\) on \(V_\delta\). Thus \(S_m(j)\to j\).

Choose nested cofinal initial segments \(V_{\alpha_N}\) with \(\alpha_0>\kappa+1\). At stage \(N\), suppose the first \(N\) indices \(m_0,\ldots,m_{N-1}\) have been chosen. For \(0\le i\le N\), put \(F_{i,N}=S_{m_i}\circ\cdots\circ S_{m_{N-1}}\), using identity for the empty suffix. Each of these finitely many maps is continuous. Choose \(m_N>m_{N-1}\) large enough that, simultaneously for all \(i\le N\),
\[
 F_{i,N}(S_{m_N}(j))|V_{\alpha_N}=F_{i,N}(j)|V_{\alpha_N}.
\]
This uses convergence only at the single base embedding. For each \(i\), the successive approximations \(F_{i,N}(j)\), \(N\ge i\), therefore stabilize on every initial segment. Write their limit as \(J_i\). At stage \(i\) the empty suffix gives agreement with \(j\) on \(V_{\alpha_i}\), and all later stages preserve it. In particular \(J_i(\kappa)=j(\kappa)>\kappa\). For every \(N>i\) we have \(F_{i,N}(j)=S_{m_i}(F_{i+1,N}(j))\). Continuity gives \(J_i=S_{m_i}(J_{i+1})\). The unary terms \(t_i=b_{m_i}\) meet the unrestricted requirement.

### Obstruction for a finite set of terms

Let \(j\) be any nontrivial elementary self-embedding as in the question and \(x_k=j^k(\operatorname{crit}(j))\). These ordinals strictly increase. Every unary term \(T\) has two nonnegative integer constants \(h_T,d_T\), with \(d_T>0\), such that
\[
T(j)(x_r)=x_{r+d_T}\quad\text{for every }r\ge h_T.
\]
The constants depend only on the expression, so in particular are independent of the embedding. For the variable take \(h=0,d=1\). For a composition \(A\circ B\), take the larger of the two thresholds and add the shifts. For application \(A*B\), take \(h=d_A+\max(h_A,h_B)\). At each \(r\ge h\), put \(s=r-d_A\). The identity \((A*B)\circ A=A\circ B\) gives
\[
 (A*B)(x_r)=(A*B)(A(x_s))=A(B(x_s))=A(x_{s+d_B})=x_{r+d_B}.
\]
Thus in this case the shift is \(d_B>0\).

If there are only finitely many terms, take \(r=\max h_T\). The critical-point formula and application identity imply that the \(r\)-th element of the critical sequence of \(j_n=t_n(j_{n+1})*j_{n+1}\) is the image under \(t_n(j_{n+1})\) of the \(r\)-th element for \(j_{n+1}\). The latter is increased strictly by the shift formula. This gives an infinite strictly decreasing sequence of ordinals, a contradiction.

### Background and verification scope

The classical application laws and the relation with I3 are described by [Dougherty](https://arxiv.org/abs/math/9205202) and [Dimonte](https://arxiv.org/abs/1707.02613). The original discussion contains the identity-term argument and a pointer to Cramer's inverse-limit work. The finite-term proof and the construction above address different questions from the existence of iterated square roots. No direct previous answer to the three original questions was located in the sources reviewed.

The Lean theorem `VanName.positive_of_I3` establishes the affirmative direction for actual elementary self-embeddings of the membership structure of a von Neumann rank and actual canonical Laver application. Its assumption is I3. The constructed chain consists entirely of nonidentity embeddings at a cardinal height. The kernel listed only `propext`, `Classical.choice`, and `Quot.sound`. The implementation uses the [LaverTable formalization](https://github.com/frenzymath/LaverTable) for canonical rank embeddings and application, a first-order proof of closure under eventual agreement, and a fusion theorem for a countable increasing cover.

The general finite-menu obstruction and its fixed-term consequence are verified on the same actual rank embeddings by `VanName.finite_cardinal_roots` and `VanName.fixed_cardinal_roots`. They apply to every cardinal height. The unrestricted result is also verified as the exact equivalence `VanName.cardinal_root_possibility`. All three declarations use only the same standard Lean axioms. The baseline LaverTable dependency was published at commit `1f5ee8c0f6de` in September 2026. It supplied the formal application and critical-point results needed to express the root construction directly on elementary embeddings.

The exact standalone statement and all three conclusions were checked together in Lean 4.33.1. The independent build compiles 62 source modules across all three problems and checks the final proof axiom lists. [Reproduction bundle](rank-embedding-sources.zip) · [Proof entry point](VanNameSolution.lean)
