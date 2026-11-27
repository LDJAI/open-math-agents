# Three applied mathematics problems

Research notes prepared with Codex for [LDJAI](https://github.com/LDJAI), November 26, 2026. Each problem was listed by Left to Solve as awaiting formalization. The original mathematics questions date to 2015, 2015, and 2020. Independent review and priority remain open.

| Original question | Result and proof |
| :-- | :-- |
| Does a shortest straight equal-area cut give positive local coverage at every radius? | [A universal guarantee of at least 2.9437%](solberg-disk-bisection.md). An equilateral triangle gives a 1/3 upper bound on the optimal constant. The proposed 25% bound remains open. |
| Does pooling heterogeneous parallel sums have a unique worst parameter? | [Unimodality and a strictly decreasing scalar root equation](parallel-sum-estimation.md). In scalar Gaussian estimation, the parameter is the measurement-noise variance. |
| Can an orthogonal matrix always take an entrywise monotone step toward its nearest signed permutation? | [Counterexamples from Householder reflections](orthogonal-rounding.md). A unique nearest target can be locally inaccessible under the prescribed rule. |

The detailed notes identify the target, proof, scope, and related research. To reproduce the finite arithmetic checks, run [check-jensen.py](check-jensen.py) and [verify_rounding.py](verify_rounding.py) with Python 3.

[Geometry listing](https://lefttosolve.com/p/mo-201359) · [Estimation listing](https://lefttosolve.com/p/mo-204379) · [Rounding listing](https://lefttosolve.com/p/mo-364377)

## Formal verification

- [Jensen.lean](Jensen.lean) proves uniqueness of the worst positive parameter for every admissible finite list. The proof's derivative lemmas establish the increase and decrease on opposite sides of the maximizer. The [registry-format proof](mo-204379.lean) independently checks the same conclusion against the [proposed Left to Solve statement](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/1168).
- [OrthogonalRounding.lean](OrthogonalRounding.lean) disproves the universal nearest-target conjecture using the dimension-five counterexample. Its [registry-format disproof](mo-364377.lean) checks against the [proposed registry statement](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/1152). The general reflection family, equal-determinant example, and slack variants are proved in the [rounding note](orthogonal-rounding.md).
- [LocalArea.lean](LocalArea.lean) proves the footprint-contraction lemma with real Euclidean area. The global depth and shortest-bisector estimates appear in the [geometry proof](solberg-disk-bisection.md).

The listed Lean conclusions depend only on propositional extensionality, classical choice, and quotient soundness. Local Lean verification and upstream acceptance are separate steps.

[Printable version of all three proofs](three-applied-math-proofs.pdf)
