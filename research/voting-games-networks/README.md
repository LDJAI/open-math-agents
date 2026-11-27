# Majority shortlists, adversarial search, and optical routing

Three investigations of open problems listed on Left To Solve. Each note gives a partial result, the exact remaining question, and the scope of formal verification. None of the three full conjectures was submitted as solved.

| Problem | Result |
| --- | --- |
| [Majority-tournament shortlists, 2014](Tournament.md) | Any prescribed pair can belong to a minimum dominating committee in an extremal tournament. A four-candidate obstruction in the 67-vertex Paley tournament tests the limit of that guarantee. |
| [Adaptive search with adversarial lies, 2014](LiarGame.md) | Even splitting is optimal with one positive remaining lie allowance and any number of candidates unable to tolerate another lie. |
| [Ordered trails in optical networks, 2002](ordered-trail-notes.md) | A direct ring-routing construction and a reduction for odd connectivity that removes terminal-free layers between saturated minimum cuts. |

The Lean sources use Lean 4.33.1 and mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`. From a project with that revision, run `lake env python3 /path/to/check.py`. The notes give commands for the independent Python and C++ verifiers.
