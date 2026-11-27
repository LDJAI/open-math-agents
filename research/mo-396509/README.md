# How much does averaging reduce absolute error?

For three independent observations from the same log-concave density on the real line, predicting the third by the mean of the first two cuts expected absolute error by at least **one ninth** relative to predicting it with the first alone. Every exponential law gives equality. The proof also works for dependent triples whose joint density is exchangeable and has convex superlevel sets.

[Read the three-page proof and diagram](pinelis-averaging.pdf) · [LaTeX source](pinelis-averaging.tex)

## Why the exponential law is extremal

Sort the three observations, and call the adjacent gaps $u,v$. Averaging over the possible choices of target reduces the conjecture to $9\,\mathbb E|u-v|\leq5\,\mathbb E(u+v)$. Slice each density level at fixed sample mean. A chord through the two directions where the integrand changes sign compares every resulting convex region to a triangle. Permutation symmetry keeps the ratio of the triangle’s axis intercepts between one half and two. For exponential observations the slices are already triangles, and their intercepts have ratio exactly two.

## Verification

[Angular.lean](Angular.lean) proves the central angular integral inequality using Lean 4.33.1 and Mathlib at commit 0df444a360eaa60ab8c11dca51a86af692955474. The PDF supplies the complete mathematical proof, including the passage from iid densities to planar sections. [check_sections.py](check_sections.py) independently integrates the two gap functionals on 2,324 finite selections of permutation orbits using exact rational arithmetic. Run it with Python 3.10 or later. To check the Lean file, run `lake env lean /absolute/path/to/Angular.lean` in the pinned [formal-conjectures checkout](https://github.com/google-deepmind/formal-conjectures/tree/9097e2f90e66d2f6244209cb1c07f7120d17ec53).

## Problem history

Iosif Pinelis posed the conjecture on June 30, 2021. Oleg Orlov proved the lower bound one tenth in 2025. The original question showed no posted answer when checked on November 26, 2026. A search by the stated inequality, the Gini dissipation functional, and citations to Cao’s repeated-averaging model located no earlier sharp proof. [Original conjecture](https://mathoverflow.net/q/396509) · [Orlov's bound](https://mathoverflow.net/a/488763) · [Cao's model](https://arxiv.org/abs/2108.07904)

[Left to Solve problem](https://lefttosolve.com/p/mo-396509) · [Formal statement submission #869](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/869)

Research by LDJAI with OpenAI Codex, November 26, 2026.
