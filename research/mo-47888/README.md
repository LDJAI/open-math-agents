# When does multinomial averaging preserve monotonicity?

For every positive sample size, averaging over multinomial counts preserves **every** monotone vector field exactly when there are at most two categories. With three categories, one field and one pair of probability vectors reverse the monotonicity inequality at every sample size.

[Two-page proof (PDF)](multinomial-monotonicity.pdf) · [LaTeX source](multinomial-monotonicity.tex) · [Original 2010 conjecture](https://mathoverflow.net/questions/47888/expectation-multinomial-distribution-and-monotonicity-a-conjecture) · [Left to Solve](https://lefttosolve.com/p/mo-47888) · [Statement submission](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/1010)

## The example

Give the three categories scores of −1, 0 and +1. Compare a sample made entirely of zeroes with a sample drawn from a 3-to-1 mixture of negative and positive scores. The mixture has a lower mean score, yet its expected positive part is strictly larger, because all draws can be positive. Multiplying that positive part by the score vector turns this reversal into a violation of the original monotonicity inequality. For two categories the argument goes the other way. Increasing the probability of the first category increases its count under a shared-uniform coupling, and the relevant contrast between the two field components is nondecreasing in that count.

The paper also gives an analytic, strongly convex potential whose averaged gradient fails the inequality for two fixed, strictly positive probability vectors at every positive sample size. This example permits costs that are nonnegative on nonnegative counts and nondecreasing in each count.

## Verification

| File | Contents |
| --- | --- |
| [Statement.lean](Statement.lean) | Translation of the original conjecture. The registry requires a placeholder for the statement being proposed. |
| [Disproof.lean](Disproof.lean) | The three-category field, its violation for every positive sample size, and the formal negation of the conjecture. |
| [Binary.lean](Binary.lean) | Preservation for one or two categories. |
| [Classification.lean](Classification.lean) | Extension to every larger category set and the exact classification. |
| [verify.sh](verify.sh) | Setup instructions, pinned dependencies, fresh compilation and axiom audit. |
| [verification.log](verification.log) | Lean's output for the full classification. |
| [Statement check](official-statement.json) and [disproof check](official-proof.json) | Results from running the registry checker locally. |

Run `bash verify.sh /path/to/formal-conjectures` after the setup steps in the script. Lean checks the disproof and classification with its usual axioms and without relying on the statement placeholder. The analytic example is proved in the paper.

## History and scope

Daizhuo posed the general conjecture on December 1, 2010, and suggested the affine and separable cases. The paper proves both. On November 26, 2026, the original post had zero answers, and the Left to Solve catalog had no solution. Searches for the question and for equivalent Bernstein-operator and population-game formulations found no earlier resolution of this exact conjecture. Priority remains open to an earlier reference.

Scalar shape preservation for Bernstein polynomials and convexification of monotone graphs are related questions. For context see [Floater and Peña on directionally monotone scalar functions](https://doi.org/10.1090/S0025-5718-99-01176-X). For the role of monotone costs, or equivalently payoffs with the opposite sign, in population games, see [Hofbauer and Sandholm, *Stable Games and their Dynamics*](https://users.ssc.wisc.edu/~whs/research/sg.pdf). Here the sampling probabilities themselves vary. Monotonicity verified on count vectors does not by itself certify that the expected cost obeys the same inequality in those probabilities.

Prepared with OpenAI Codex at LDJAI's request.
