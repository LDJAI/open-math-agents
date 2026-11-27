# Three questions about matchings, random strings, and surface slices

Research notes prepared for LDJAI with OpenAI Codex, 26 November 2026. All three questions were posted to MathOverflow between 2012 and 2014 and catalogued by Left to Solve. Each original thread contains a named mathematician’s prediction. The two combinatorial results give constructive answers in the senses specified below. The geometric construction confirms its author’s negative prediction.

| Question | Result in this project | Interpretation |
|:--|:--|:--|
| Which lists can count the matchings of a bipartite graph? | At maximum matching size $k$, a finite union of polynomial families with at most $2^k-1$ nonnegative integer parameters each generates precisely the realizable lists of degree $k$. A finite search reconstructs a witness. | This is a parametric classification. A short test directly in the supplied coefficients and a fast algorithm for arbitrary $k$ remain separate questions. |
| What is the expected closest Hamming distance across overlapping windows? | A sum over the even edge sets of the alignment graph gives the exact expectation. The window distances are jointly independent exactly when the graph is a forest. | Pairwise independence and earlier ways to calculate finite probabilities were known. The contribution here is the joint formula and the overlap criterion. |
| Must the arclength of a parallel slice of a $C^1$ graph vary differentiably? | The attainable lengths of the slices of a unit-square graph are exactly the continuous functions into $[1,\infty)$. This holds even with both ends of every slice fixed. | The answer is negative. The construction also realizes every continuous nowhere-differentiable profile above the lower bound. |

Read the [combined manuscript](three-skeptical-problems.pdf) or the individual notes on [matchings](matchings.md), [overlapping Hamming windows](hamming.md), and [slice length](slices.md). The notes link each prediction, discuss earlier work and distinguish published facts from the proofs presented here. No claim to independent peer review or exhaustive historical priority is made.

Left to Solve entries: [matchings](https://lefttosolve.com/p/mo-88547), [random strings](https://lefttosolve.com/p/mo-128755), [surface slices](https://lefttosolve.com/p/mo-184507). The [registry pull request](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/1119) contains the formal statement of the original slice question. The mathematical proof of its negative answer is in the research note. The two other source questions ask for forms of answers, whose words “classification” and “explicit” admit different interpretations.

## Reproduce the checks

With standard-library Python 3, run:

~~~sh
python verify_matchings.py check
python verify_matchings.py realize 4 2
python hamming_check.py
~~~

The matching test compares the parameter formulas to 68,406 boards and checks reconstruction. The Hamming test checks 20 pattern-length/window-count combinations and 90 arbitrary-shift cases. Examples and code are auxiliary to the general proofs.

The file [SliceBounds.lean](SliceBounds.lean) proves continuity, the lower bound of one, and a conditional implication from profile realization to failure of the original smoothness assertion. The realization construction is given in prose. To reproduce these Lean checks with the pinned dependencies indicated in the [script](verify-slices.sh), run:

~~~sh
bash verify-slices.sh /path/to/formal-conjectures ./mo-184507.lean
~~~
