# One more head-to-head win can cost a Banks-tree election

Justin Kruger and Stéphane Airiau (2016, §4.4) wrote, “we conjecture that all the trees we have considered are monotonic under argmax.” The following eight-candidate majority tournament refutes that conjecture for their Banks tree. Both elections have a unique winner. Raising candidate D above A in their head-to-head contest changes the election winner from D to C. [COMSOC 2016 paper](https://archive.illc.uva.nl/COMSOC/proceedings/comsoc-2016/KrugerEtAlCOMSOC2016.pdf) · [AAMAS 2017 paper](https://www.ifaamas.org/Proceedings/aamas2017/pdfs/p1584.pdf)

## Construction

Three voters rank the eight candidates in the following orders, from best to worst.

| Voter | Ranking |
|:--|:--|
| 1 | B H C F E **A D** G |
| 2 | G F D E H B A C |
| 3 | A C D E G B H F |

Voter 1 moves D one place up, swapping it with A. Every other ranking stays fixed. In the resulting majority tournaments, each entry in the second column below beats the candidate on its left. These 28 directed edges specify the entire tournament. To obtain the second tournament, reverse A's win over D. For every candidate permutation, run the paper's Banks tree, then elect whoever wins the most permutations.

| Candidate | Beaten by, before the change | Winning share before, in units of 1/480 | Winning share after, in units of 1/480 |
|:--|:--|--:|--:|
| A | B, E, F, H | 50 | 15 |
| B | D, E, G | 90 | 87 |
| C | A, B, H | 110 | **165** |
| D | A, C, F | **120** | 159 |
| E | C, D, F | 45 | 0 |
| F | B, C, G, H | 35 | 24 |
| G | A, C, D, E | 30 | 30 |
| H | B, D, E, G | 0 | 0 |

D's winning share rises from 25% to 33.125%. C's rises from about 22.92% to 34.375%. C overtakes D.

## Proof by conditioning on the first candidate examined

The paper's Proposition 4.17 describes the Banks tree by reading a permutation from right to left. Retain the first candidate, then retain a later candidate precisely when it beats every previously retained one. The last retained candidate wins. Conditional on first retaining candidate X, only the candidates that beat X can win, and their relative order is still uniform. Apply the same procedure recursively on those candidates. If nobody beats X, X wins immediately.

The following table conditions on the first retained candidate. Each entry gives a candidate and its share in units of 1/60. Since each row has probability 1/8, summing each candidate's entries gives the columns in the construction, in units of 1/480.

| First | Before | After |
|:--|:--|:--|
| A | B 15, E 30, F 15 | B 12, D 24, F 24 |
| B | D 60 | D 60 |
| C | B 60 | B 60 |
| D | A 20, C 20, F 20 | C 60 |
| E | C 60 | C 60 |
| F | B 15, C 15, G 30 | B 15, C 15, G 30 |
| G | A 30, C 15, E 15 | A 15, C 30, D 15 |
| H | D 60 | D 60 |

The D row explains the reversal. Originally D's challengers A, C, and F form a cycle. Once D can eliminate A, C beats its sole remaining rival F. This gives C 40 more units from that row alone. Over all rows, D gains 39 units and C gains 55, wiping out D's 10-unit lead.

An independent enumeration in `verify_banks.py` directly evaluates the published binary-tree recurrence on all 40,320 permutations, before and after the reversal. Run `python3 verify_banks.py` with Python 3. The code checks the tournament, both complete count vectors, and uniqueness of the two winners.

The standard-library file `BanksVoting.lean` checks validity of the three ballots, the single edge reversal, both complete score vectors, and the change of unique winner. Run `lean BanksVoting.lean` with Lean 4.33.1. The kernel checks the scores using two recurrences, each proved by `decide`. The first conditions on the first retained candidate as above. The second counts all original orders by working directly with the two children of the published tree.

For the second recurrence, fix a suffix of an agenda. For each unused label X, let F(X) denote the winner of the subtree formed by placing X before that suffix. With empty suffix F(X) is X. Once the next label Y is chosen, the defining Banks recurrence replaces F(X) by the winner of the contest between F(X) and F(Y). Group unused labels according to F. Picking a member of a group of size m gives m equal contributions to the count. Groups that beat F(Y) retain their members. All other remaining labels merge into the F(Y) group, with the selected label removed. When a single group remains, every ordering of its labels has the same winner. This is exactly the branching calculation in `treeCount`. The kernel verifies this finite instance; the preceding invariant gives its connection to the tree definition for arbitrary agenda lengths.

## Scope and literature

The counterexample resolves the authors' blanket conjecture. The calculation concerns the Banks tree specifically. The strengthened candidate's individual winning probability increases, consistent with the probability monotonicity proved in the authors' Proposition 4.17 and its preceding discussion. The other three unresolved rows in their Table 2 concern the simple, balanced and iterative Condorcet trees.

A November 2026 literature search for the named conjecture, its authors, Banks-tree argmax monotonicity and randomized King of the Hill found the original articles and related probability-monotonicity results. I found no earlier resolution of the Banks-tree argmax question. The same random elimination procedure is studied in the tournament literature. [Schvartzman et al., ITCS 2020](https://doi.org/10.4230/LIPIcs.ITCS.2020.3) · [Xue, COMSOC 2023](https://archive.illc.uva.nl/COMSOC/proceedings/comsoc-2023/EricXue.pdf)

## Minimum number of candidates

Eight candidates are necessary for this particular Banks-tree reversal. A second exhaustive check enumerates all tournaments on at most seven labels, retaining every labelling with nondecreasing indegrees. Every tournament has such a labelling. For each initial argmax member, including tied winners, it reverses each pairwise loss and recomputes the winner set. At seven labels the program tested 11,559 retained labellings and 51,064 improvements. In every case the improved candidate remained an argmax member. Larger changes favorable to one candidate decompose into single-edge changes. Run the C++20 program `verify_minimum.cpp` to reproduce the finite check. This lower bound is independent of the proof that the displayed election is a counterexample.
