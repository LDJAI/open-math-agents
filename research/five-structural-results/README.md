# Five questions about symmetry, measurement and computation

Research notes for LDJAI, November 26, 2026. These are proposed mathematical results with proofs and links to earlier work. Each question has an individual Left to Solve entry and was posed between 2010 and 2015. [Read the six-page research brief](five-structural-results.pdf).

| Question and registry entry | Result | Scope |
| :-- | :-- | :-- |
| [Matrix norm symmetries, 2010](https://lefttosolve.com/p/mo-47956) | [An efficient norm and an NP-hard norm have identical linear isometries.](matrix-norms.md) | A [padding-stable construction](padding-stable-norm.md) is NP-hard to approximate within a fixed absolute error of 1/8 on integer diagonal matrices. Inspired by quantum information. |
| [A local square of a rough field, 2015](https://lefttosolve.com/p/mo-201997) | [The requested covariance is possible, but a nonzero even square is impossible in the finite-variance supercritical range studied.](gaussian-fields.md) | Full classification under translation equivariance. The weaker integrability variant remains open in these notes. |
| [A simultaneous law of large numbers, 2012](https://lefttosolve.com/p/mo-107177) | [A class of compact subsets of the unit interval admits no countable cover by uniformly convergent subclasses.](empirical-convergence.md) | A single infinite data sequence estimates all fixed members consistently. After seeing any finite sample one can choose a member with error exactly one under uniform sampling. |
| [Gaussian change-point location, 2013](https://lefttosolve.com/p/mo-142880) | [One fixed additive correction transfers every confidence level between continuous and discrete locations.](change-points.md) | Coupling of the marginal distributions for each fixed positive drift. A positive multiplicative slope other than one fails for the signed order. |
| [Measurable policy selection, 2013](https://lefttosolve.com/p/mo-136792) | [Analytically measurable choices can fail even for a continuous surjection.](measurable-selection.md) | For continuous maps out of a Polish action space, the general lifting property holds exactly when that space is a countable union of compact sets. The universal-measurability guarantee follows from classical work. |

## Verification and publication status

The five individual Left to Solve API records reported category `unformalized`, zero live agents and no recorded solution when checked. The linked notes give the original authors' words, proofs, literature checks, and unresolved variants. A registry status is an observation about the registry. The research notes have not been peer reviewed, and publication priority for the specific results remains unverified.

For the matrix construction, [three algebraic lemmas](NormCutCertificate.lean) were checked in Lean 4.33.1, using mathlib revision `0df444a360eaa60ab8c11dca51a86af692955474`. The [axiom output](NormCutCertificate.log) and a [finite regression check](check_norm_isometries.py) are included. Reproduce the latter with `python3 check_norm_isometries.py`. It checks the encoding and rank-one equality criterion on every labelled simple graph with two through five vertices, 1,098 graphs in total. The proof for arbitrary graph sizes is in the matrix note.

For the empirical convergence result, [four Lean lemmas](PrussCertificate.lean) cover the deterministic truncation estimate and the sample-count obstruction to a countable uniform cover. See the [axiom output](PrussCertificate.log). The construction of the probability-one event and the classification for countable partitions are proved in the accompanying research note.

[Registry pull request 1497](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/1497) submits the Lean statement of Pruss's original question for human review. Its single placeholder is required for a statement submission. The proof and component certificates in this folder are separate from that submission.
