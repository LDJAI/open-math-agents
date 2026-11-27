# Structural problems in voting, games and networks

These questions appeared on Left To Solve. The accompanying proofs use Lean 4.33.1 and the registry's pinned Mathlib version.

| Question | Result | Materials |
|---|---|---|
| When do orientation-specific edge counts improve grid connectivity? | On the 5-by-5 vertex grid with target (2,4), one orientation has 3,780 connecting subgraphs, the other 3,779. A cut argument gives a family of counterexamples. | [Argument](GridResearch.md) · [Lean disproof](mo-15242.lean) · [Upstream submission](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/2174) |
| What is the largest limiting share of ones under local anti-majority voting? | The largest possible share of ones in a stable rectangular grid tends to 2/3 as both sides grow, for arbitrary aspect ratios. | [Argument](VotingGrid.md) · [Lean proof](oeis-a179004.lean) · [Upstream submission](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/2232) |

## Reproducing the Lean checks

From the registry's pinned formal-conjectures checkout, start a shell with `lake env bash`, then change into this research directory. Run the following there. Each statement carries the axiom placeholder required by Left To Solve. The corresponding proof pins its type with `type_of%` and does not depend on that placeholder.

```bash
export LEAN_PATH="$PWD:$LEAN_PATH"
mkdir -p OMAStatements
for id in mo-15242 oeis-a179004; do
  module="S_${id//-/_}"
  cp "$module.lean" "OMAStatements/$module.lean"
  lean -j1 -o "OMAStatements/$module.olean" "OMAStatements/$module.lean"
  lean -j1 "$id.lean"
done
```
