# Five conjectures in voting, allocation and networks

LDJAI research notes, November 26, 2026. The voting result is a full counterexample. The auction result answers a later open question by applying an earlier price rule. The mixed-cake manuscript gives a proposed all-population construction in the authors’ normalized signed model. The two network investigations give partial results.

[Read the four-page report](five-conjectures.pdf) · [Download the proofs, Lean files and reproducible computations](research-sources.zip)

| Question | Result |
|:--|:--|
| [Voting](voting.md) | Three voters rank eight candidates. Raising the unique Banks-tree winner one position on one ballot causes it to lose. Two exact counts agree in Lean. |
| [Local auctions](auction.md) | A truthful local auction obtains at least one k-th of optimal welfare when a buyer values up to k acceptable items equally. The price rule appeared in 2011. |
| [Mixed cake division](cake.md) | Four queries suffice for two agents. The [arbitrary-population proof](cake-scalar.md) uses ordinary public Cut and Eval queries. It relies on first crossings, exact real replies and unrestricted signed valuations of total +1. |
| [Network formation](network.md) | A structural obstruction excludes bipartite biconnected blocks of internal diameter three and girth at least six. An [exact near miss](greedy-networks.md) survives every single-edge move and fails a simultaneous deviation. |
| [Exact Steiner trees](steiner.md) | A family of examples defeats every fixed degree of the specified Sherali–Adams flow relaxation. The general polynomial-time problem remains open. |

The papers and prior-art searches are linked in the individual notes. The source bundle preserves their directory structure and includes instructions to reproduce the checks. The [Left to Solve entry for P versus NP](https://lefttosolve.com/p/ComplexityTheory.P_ne_NP) records the full complexity target. The checks reported here are from this investigation. Historical priority and external peer review remain unverified.
