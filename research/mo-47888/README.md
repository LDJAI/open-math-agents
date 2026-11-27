# When does multinomial averaging preserve monotonicity?

For every positive sample size, averaging over multinomial counts preserves **every** monotone vector field exactly when there are at most two categories. With three categories, one field and one pair of probability vectors reverse the monotonicity inequality at every sample size.

[Three-page proof (PDF)](multinomial-monotonicity.pdf) · [LaTeX source](multinomial-monotonicity.tex) · [Original 2010 conjecture](https://mathoverflow.net/questions/47888/expectation-multinomial-distribution-and-monotonicity-a-conjecture) · [Left to Solve](https://lefttosolve.com/p/mo-47888) · [Statement submission](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/1010)

## The example

Give the three categories scores of −1, 0 and +1. Compare a sample made entirely of zeroes with a sample drawn from a 3-to-1 mixture of negative and positive scores. The mixture has a lower mean score, yet its expected positive part is strictly larger, because all draws can be positive. Multiplying that positive part by the score vector turns this reversal into a violation of the original monotonicity inequality. For two categories the argument goes the other way. Increasing the probability of the first category increases its count under a shared-uniform coupling, and the relevant contrast between the two field components is nondecreasing in that count.

The paper also gives an analytic, strongly convex potential whose averaged gradient fails the inequality for two fixed, strictly positive probability vectors at every positive sample size. This example permits costs that are nonnegative on nonnegative counts and nondecreasing in each count.

## What survives for network routing?

Let each route's cost be a sum of link costs, each nondecreasing in the number of travelers on that link. With independent route choices, the expected route costs remain monotone for any number of routes, including when many routes share the same links. Each link's load has a binomial distribution, even though two links' loads can be correlated.

More generally, for a real matrix $A$ of per-route resource loads, consider the cost field $A^\top c(Ax)$ where each resource has a separate nondecreasing cost function. The expected field is monotone for **every** such choice of costs if and only if each row of $A$ takes at most two different values. With three load levels, strict convexity of the exponential produces a fixed pair of probability mixtures that reverses the sign for every sample size. Page 3 gives the proof. Stochastic route choice appears in [Daizhuo Chen’s 2010 MIT thesis](https://dspace.mit.edu/handle/1721.1/61889).

## Verification

| File | Contents |
| --- | --- |
| [Statement.lean](Statement.lean) | Translation of the original conjecture. The registry requires a placeholder for the statement being proposed. |
| [Disproof.lean](Disproof.lean) | The three-category field, its violation for every positive sample size, and the formal negation of the conjecture. |
| [Binary.lean](Binary.lean) | Preservation for one or two categories. |
| [Classification.lean](Classification.lean) | Extension to every larger category set and the exact classification. |
| [Routing.lean](Routing.lean) | Exact binomial aggregation and monotonicity of expected additive route costs for arbitrary overlapping links. |
| [verify.sh](verify.sh) | Setup instructions, pinned dependencies, fresh compilation and axiom audit. |
| [verification.log](verification.log) | Lean's output for the full classification. |
| [Statement check](official-statement.json) and [disproof check](official-proof.json) | Results from running the registry checker locally. |

Run `bash verify.sh /path/to/formal-conjectures` after the setup steps in the script. Lean checks the disproof, classification, and network-routing corollary with its usual axioms and without relying on the statement placeholder. The paper gives analytic proofs of the smooth example and the real-matrix criterion.

## History and scope

Daizhuo posed the general conjecture on December 1, 2010, and suggested the affine and separable cases. The paper proves both. On November 26, 2026, the original post had zero answers, and the Left to Solve catalog had no solution. Searches for the question and for equivalent Bernstein-operator and population-game formulations found no earlier resolution of this exact conjecture. Priority remains open to an earlier reference.

Scalar shape preservation for Bernstein polynomials and convexification of monotone graphs are related questions. For context see [Floater and Peña on directionally monotone scalar functions](https://doi.org/10.1090/S0025-5718-99-01176-X). For the role of monotone costs, or equivalently payoffs with the opposite sign, in population games, see [Hofbauer and Sandholm, *Stable Games and their Dynamics*](https://users.ssc.wisc.edu/~whs/research/sg.pdf). Here the sampling probabilities themselves vary. Monotonicity verified on count vectors does not by itself certify that the expected cost obeys the same inequality in those probabilities.

Prepared with OpenAI Codex at LDJAI's request.
