# Three results from Left to Solve

Two explicit counterexamples settle questions from 2019. A third result answers a 2015 question about elementary embeddings, with an affirmative answer under the usual rank-into-rank hypothesis and an unconditional obstruction to using finitely many term functions.

Of the three authors, only Joseph Van Name explicitly called the proposed construction “impossible.” Raphael Berger conjectured that no additional solutions existed. Aaron Meyerowitz guessed that his proposed converse was false. These are predictions about mathematical objects. None of the quotations asserts that a proof is impossible in a specified formal system.

## 1. Berger’s velocity fields

Berger wrote, “I conjecture that there are no other fields.” He was asking whether every velocity field satisfying a continuity equation for every constant magnetic field had to be proportional to the density gradient. Berger earned a doctorate in chemistry at the Technical University of Munich in 2002. [Original question](https://mathoverflow.net/questions/331165/solution-of-equation-on-vector-field) · [University CV](https://www.plus.ac.at/chemistry-and-physics-of-materials/staff/a-to-d/berger/cv/?lang=en) · [Left to Solve](https://lefttosolve.com/p/mo-331165)

Take the positive density $\rho(x)=e^{x_1}$ and velocity $v(x)=e^{-x_1}e_2$. For every constant magnetic field $B$, the current $\rho(B\times v)=B\times e_2$ is constant and has zero divergence. Yet $v$ is nonzero and perpendicular to $\nabla\rho=e^{x_1}e_1$ everywhere. Lean checks this counterexample. The vector identity $\operatorname{div}(B\times(\rho v))=-B\cdot\operatorname{curl}(\rho v)$ also explains the freedom in the equation. On $\mathbb R^3$ with smooth fields, any gradient $\rho v=\nabla\Phi$ supplies a solution, and every solution has that form. [Checked proof](BergerDisproof.lean)

## 2. Meyerowitz’s squared-square converse

Meyerowitz asked whether every partition of the edges of $K_{n,n}$ into balanced complete bipartite graphs yields a square tiling with the same side lengths. He wrote, “I would guess not, but I don't have a counter-example.” The counterexample confirms his guess and settles the general converse. The separate question about pairwise distinct sizes remains outside its scope. Meyerowitz earned a mathematics PhD in 1984. [Original question](https://mathoverflow.net/questions/341688/squared-squares-and-partitions-of-k-nn) · [University CV collection](https://www.fau.edu/iea/documents/pdf/pr2015/mathss2015.pdf) · [Left to Solve](https://lefttosolve.com/p/mo-341688)

Index both vertex classes modulo five. For each $i$, take the block with rows $\{i,i+1\}$ and columns $\{2i,2i+1\}$, together with the singleton edge $(i,2i+2)$. This partitions all 25 edges into five blocks of each size. But five axis-aligned squares of side two cannot fit inside a square of side five. Their lower-left corners lie in $[0,3]^2$. Divide this region into four cells of side $3/2$. Two corners occupy the same cell, so their squares overlap in both coordinates. The argument allows real coordinates. [Checked proof](MeyerowitzDisproof.lean)

## 3. Van Name’s infinite chains of roots

Van Name wrote, “It seems like it is impossible for there to be such a descending sequence.” He asked for nontrivial rank-into-rank elementary embeddings satisfying $j_n=t_n(j_{n+1})*j_{n+1}$, where each $t_n$ is a unary term built from application $*$ and composition. He also asked about fixed and finite collections of term functions. Van Name earned a mathematics PhD at the University of South Florida in 2013. [Original question](https://mathoverflow.net/questions/221720/can-one-take-roots-of-rank-into-rank-embeddings-infinitely-many-times) · [University degree record](https://www.usf.edu/arts-sciences/departments/mathematics-statistics/graduate/graduates-of-our-program.aspx) · [Left to Solve](https://lefttosolve.com/p/mo-221720)

An unrestricted chain at some cardinal exists **if and only if** the large-cardinal hypothesis I3 holds. The forward construction from I3 uses successive self-applications to obtain root operations that preserve progressively larger rank segments. Compatible limits then yield the chain. Every fixed term function and every finite collection of term functions are ruled out at every cardinal. The equivalence leaves the existence of an I3 embedding open. [Proof and statement audit](RankIntoRank.md) · [Lean solution](VanNameSolution.lean) · [Reproducible source bundle](rank-embedding-sources.zip)

## Submission status

Each listing required a formal statement before the site could admit a proof. The GitHub pull requests below submit those statements for review. The linked Lean files provide the checked proof evidence. A pull request is a submission receipt. Admission of a proof to Left to Solve follows approval of its statement.

[Berger #2195](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/2195) · [Meyerowitz #2162](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/2162) · [Van Name #2383](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/2383)
